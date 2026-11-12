#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Check committed theorem contracts against compiled Lean declarations.
The inventory's textual integrity check is a separate, cheaper gate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from package import PACKAGE
MANIFEST = PACKAGE / 'theorems.json'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+")


def digest(value):
    return hashlib.sha256(json.dumps(value, ensure_ascii=True, sort_keys=True,
                                     separators=(',', ':')).encode()).hexdigest()


def source_inputs(imports):
    pending = list(imports)
    paths = {PACKAGE / name for name in ('lean-toolchain', 'lakefile.lean', 'lake-manifest.json')}
    paths |= {Path(__file__).resolve(), PACKAGE / 'scripts/package.py', PACKAGE / 'target.json'}
    while pending:
        module = pending.pop()
        path = PACKAGE / (module.replace('.', '/') + '.lean')
        if path in paths:
            continue
        if not path.is_file():
            if module.split('.')[0] in ('Solidity', 'Contract'):
                raise ValueError('missing project import: ' + module)
            continue  # Other imports belong to the pinned Lean standard library.
        paths.add(path)
        for line in re.findall(r'^import\s+([^\n]+)', path.read_text(), re.MULTILINE):
            modules = line.split('--', 1)[0].split()
            if any(not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", name) for name in modules):
                raise ValueError('unsupported import spelling: ' + module)
            pending.extend(modules)
    return {str(path.relative_to(PACKAGE)): hashlib.sha256(path.read_bytes()).hexdigest() for path in sorted(paths)}


def validate(manifest, recording=False):
    if manifest.get('schema') != 'oksolc.solidity-theorem-contracts.v1':
        raise ValueError('wrong theorem manifest schema')
    if manifest.get('toolchain') != (PACKAGE / 'lean-toolchain').read_text().strip():
        raise ValueError('wrong theorem manifest toolchain')
    if set(manifest.get('allowedAxioms', [])) != ALLOWED:
        raise ValueError('wrong global axiom policy')
    roots = manifest.get('roots', [])
    if not roots or len({root['name'] for root in roots}) != len(roots):
        raise ValueError('missing or duplicate theorem roots')
    for root in roots:
        if not NAME.fullmatch(root['name']) or not NAME.fullmatch(root['module']):
            raise ValueError('invalid Lean declaration/module name')
        if not root.get('contract') or not (PACKAGE / (root['module'].replace('.', '/') + '.lean')).is_file():
            raise ValueError('missing theorem contract or owning module')
        if not recording and (not isinstance(root.get('expectedStatement'), str) or
                not re.fullmatch(r'[0-9a-f]{64}', root.get('kernelStatementSha256', '')) or
                not set(root.get('permittedAxioms', ['invalid'])) <= ALLOWED):
            raise ValueError('missing/invalid expected compiled contract')
    return roots


def check_records(roots, records):
    if [root['name'] for root in roots] != [record['name'] for record in records]:
        raise ValueError('compiled audit omitted, duplicated or reordered a root')
    for root, record in zip(roots, records):
        if (record['statement'] != root['expectedStatement'] or
                digest(record['kernelStatement']) != root['kernelStatementSha256']):
            raise ValueError('compiled statement changed: ' + root['name'])
        if not set(record['axioms']) <= set(root['permittedAxioms']):
            raise ValueError('unpermitted transitive axiom: ' + root['name'])
        if record['dependencyCount'] <= 0:
            raise ValueError('empty dependency closure: ' + root['name'])


def check_source_closure(manifest, inputs):
    expected = manifest.get('sourceClosure')
    if expected != inputs:
        changed = sorted(set(expected or {}) | set(inputs))
        changed = [name for name in changed if (expected or {}).get(name) != inputs.get(name)]
        raise ValueError('source definition closure changed: ' + ', '.join(changed[:4]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, default=MANIFEST)
    parser.add_argument('--lean-bin', type=Path)
    parser.add_argument('--output', type=Path)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--record-source-closure', action='store_true',
                       help='Review-only source rebinding; compiled statements and axioms must still match.')
    modes.add_argument('--record-contracts', action='store_true',
                        help='Explicitly replace expected contracts for review; never an acceptance run.')
    args = parser.parse_args()
    if args.output is None:
        args.output = Path(tempfile.mkdtemp(prefix='solidity-theorems-')) / 'audit'
    args.output.mkdir(parents=True, exist_ok=False)
    output = args.output.resolve()
    raw_manifest = args.manifest.read_bytes()
    manifest = json.loads(raw_manifest)
    roots = validate(manifest, args.record_contracts)
    imports = sorted({'Solidity.Proofs.Audit'} | {root['module'] for root in roots})
    inputs = source_inputs(imports)
    if not args.record_contracts and not args.record_source_closure:
        check_source_closure(manifest, inputs)
    source = '\n'.join(['import ' + module for module in imports] + [
        'set_option format.width 100', 'set_option pp.universes true',
        *['#audit_semantics_theorem ' + root['name'] for root in roots], ''])
    (output / 'Audit.lean').write_text(source)
    env = dict(os.environ, LEAN_NUM_THREADS='4')
    lake = str(args.lean_bin / 'lake') if args.lean_bin else 'lake'
    if args.lean_bin:
        env['PATH'] = str(args.lean_bin) + os.pathsep + env.get('PATH', '')
    # Build the exact import roots; Lean still performs the compiled audit below.
    commands = [('build', [lake, 'build', *imports]),
                ('audit', [lake, 'env', 'lean', '-M4096', '-DwarningAsError=true', str(output / 'Audit.lean')])]
    statuses = {}
    for label, command in commands:
        with (output / (label + '.stdout')).open('wb') as stdout, (output / (label + '.stderr')).open('wb') as stderr:
            process = subprocess.run(command, cwd=PACKAGE, env=dict(env, LEAN_NUM_THREADS='1' if label == 'audit' else '4'),
                                     stdout=stdout, stderr=stderr, timeout=3600)
        statuses[label] = process.returncode
        (output / 'processes.json').write_text(json.dumps(statuses, indent=2) + '\n')
        if process.returncode:
            raise SystemExit('theorem ' + label + ' failed; retained diagnostics: ' + str(output))
    records = [json.loads(line) for line in (output / 'audit.stdout').read_text().splitlines() if line.startswith('{')]
    if args.manifest.read_bytes() != raw_manifest:
        raise ValueError('manifest changed during audit')
    if source_inputs(imports) != inputs:
        raise ValueError('imported source/tool inputs changed during audit')
    if args.record_contracts:
        if [root['name'] for root in roots] != [record['name'] for record in records]:
            raise ValueError('incomplete recording')
        for root, record in zip(roots, records):
            root['expectedStatement'] = record['statement']
            root['kernelStatementSha256'] = digest(record['kernelStatement'])
            root['permittedAxioms'] = sorted(record['axioms'])
        status = 'contractsRecordedForReview'
    else:
        check_records(roots, records)
        status = 'passed'
    if args.record_contracts or args.record_source_closure:
        manifest['sourceClosure'] = inputs
        args.manifest.write_text(json.dumps(manifest, indent=2) + '\n')
        status = 'contractsRecordedForReview' if args.record_contracts else 'sourceClosureRecordedForReview'
    report = {'status': status, 'assurance': 'compiledDeclarationContractsAndSourceClosure', 'roots': len(roots),
              'manifestSha256': hashlib.sha256(args.manifest.read_bytes()).hexdigest(),
              'sourceInputs': inputs,
              'axioms': sorted({axiom for record in records for axiom in record['axioms']}),
              'processExitCodes': statuses}
    (output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: value for key, value in report.items() if key != 'sourceInputs'} |
                     {'sourceInputCount': len(inputs), 'output': str(output)}))


if __name__ == '__main__':
    main()
