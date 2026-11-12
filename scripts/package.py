"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""
"""Local package identities and retained command execution for release checks."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

PACKAGE = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def target():
    profile = json.loads((PACKAGE / 'target.json').read_text())
    lean = (PACKAGE / 'Solidity/Target.lean').read_text()
    for key in ('solidityVersion', 'referenceCompilerVersion', 'evmVersion', 'leanVersion'):
        if re.findall(r'^def ' + key + r' : String := "([^"]+)"$', lean, re.M) != [profile[key]]:
            raise ValueError('Lean target differs from metadata: ' + key)
    settings = {'viaIR': ('Bool', 'true'), 'optimizerRuns': ('Nat', '200'),
                'optimizerEnabled': ('List Bool', '[false, true]')}
    if (profile['viaIR'] is not True or profile['optimizerRuns'] != 200 or
            profile['optimizerEnabled'] != [False, True] or profile['evmVersion'] != 'cancun'):
        raise ValueError('unsupported compiler compatibility profile')
    for key, (kind, value) in settings.items():
        if re.findall(r'^def ' + re.escape(key + ' : ' + kind + ' := ') + r'([^\n]+)$', lean, re.M) != [value]:
            raise ValueError('Lean compiler settings differ from metadata: ' + key)
    if (PACKAGE / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v' + profile['leanVersion']:
        raise ValueError('Lean toolchain differs from metadata')
    return profile


def inputs():
    paths = {PACKAGE / name for name in ('target.json', 'lean-toolchain', 'lakefile.lean', 'lake-manifest.json')}
    paths.update(p for root in ('Solidity', 'Contract') for p in (PACKAGE / root).rglob('*.lean'))
    paths.update((PACKAGE / 'scripts').glob('*.py'))
    return {str(p.relative_to(PACKAGE)): sha(p) for p in sorted(paths)}


def command(args, output, label, *, data=None, env=None):
    try:
        result = subprocess.run(list(map(str, args)), input=data, capture_output=True,
                                cwd=PACKAGE, env=env, timeout=3600)
    except subprocess.TimeoutExpired as error:
        (output / (label + '.stdout')).write_bytes(error.stdout or b'')
        (output / (label + '.stderr')).write_bytes(error.stderr or b'')
        save(output / (label + '.process.json'), {'command': list(map(str, args)), 'timedOut': True})
        raise
    (output / (label + '.stdout')).write_bytes(result.stdout)
    (output / (label + '.stderr')).write_bytes(result.stderr)
    save(output / (label + '.process.json'), {'command': list(map(str, args)), 'exitCode': result.returncode})
    if result.returncode:
        raise RuntimeError(f'{label} exited {result.returncode}; see {output}')
    return result.stdout


def lean_environment(binary):
    return dict(os.environ, PATH=str(binary) + os.pathsep + os.environ.get('PATH', ''), LEAN_NUM_THREADS='4')
