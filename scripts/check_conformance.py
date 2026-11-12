#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""
"""Compare selected machine witnesses with pinned solc on a private Cancun EVM.

Requires Python 3, Lean, solc and Anvil. No remote RPC or funded wallet is used.
The source/model pairing is manual. Membership in the exported finite witness
set is evidence of conformance for these cases, not an exhaustive semantics test.
"""
import argparse
import json
from pathlib import Path
import re
import shutil
import socket
import subprocess
import time
import urllib.request

from package import PACKAGE, command, inputs, lean_environment, save, sha, target

CASES = (
    'capture_once_compound', 'assignment_operand_order', 'compound_old_value_order',
    'struct_argument_conversion_after_effects', 'struct_argument_copy_length',
    'internal_argument_conversion_after_effects', 'tuple_conditional_conversion_after_effects',
    'tuple_same_target', 'tuple_storage_copies', 'memory_reference_parameter',
    'internal_alias_revert', 'checked_overflow_after_effect', 'aliased_order_overflow',
    'emit_storage_rollback',
)
COPY_CASES = CASES[3:6]


class ModelFailure(ValueError):
    def __init__(self, category, message):
        super().__init__(message)
        self.category = category


def model_outcome(value):
    if value['status'] == 'returned':
        return {'status': 'returned', 'bytes': '0x' + int(value['word']).to_bytes(32, 'big').hex()}
    if value['status'] == 'reverted':
        return {'status': 'reverted', 'bytes': '0x' + bytes(value['bytes']).hex()}
    category = {'exhausted': 'hostExhaustions', 'targetResource': 'targetResourceFailures'}.get(
        value.get('reason'), 'modelUnsupported')
    raise ModelFailure(category, 'model execution failed: ' + str(value))


def call_outcome(response):
    if ('result' in response) == ('error' in response):
        raise ValueError('ambiguous RPC result')
    if 'result' in response:
        status, data = 'returned', response['result']
    else:
        error = response['error']
        if error.get('code') != 3:
            raise ValueError('RPC failure is not a source revert')
        status, data = 'reverted', error.get('data')
    if not isinstance(data, str) or not re.fullmatch(r'0x(?:[0-9a-fA-F]{2})*', data):
        raise ValueError('malformed observation bytes')
    return {'status': status, 'bytes': data.lower()}


def select(core):
    by_name = {case['name']: case for case in core['cases']}
    if len(by_name) != len(core['cases']):
        raise ValueError('duplicate model case')
    cases = [by_name[name] for name in CASES]
    for case in cases:
        if case.get('admitted') is not True or not case['outcomes']:
            raise ModelFailure('modelRejections', 'model admission failed or empty witness set: ' + case['name'])
        for value in case['outcomes']:
            model_outcome(value)
    return cases


def check_rejection(control):
    if (control.get('admission') != 'rejected' or
            control.get('unreachableAdmission') != 'rejected' or
            control.get('modelError') != 'rejected' or not control.get('diagnostics')):
        raise ValueError('invalid static rejection control')
    if model_outcome(control['unreachableOutcome']) != {'status': 'returned', 'bytes': '0x' + '00' * 32}:
        raise ValueError('unreachable rejection control did not return zero')


class Rpc:
    def __init__(self, port, output):
        self.url, self.output, self.serial = f'http://127.0.0.1:{port}', output, 0

    def raw(self, method, params):
        self.serial += 1
        request = {'jsonrpc': '2.0', 'id': self.serial, 'method': method, 'params': params}
        req = urllib.request.Request(self.url, json.dumps(request).encode(), {'Content-Type': 'application/json'})
        with urllib.request.urlopen(req, timeout=10) as response:
            result = json.load(response)
        with (self.output / 'rpc.jsonl').open('a') as handle:
            handle.write(json.dumps({'request': request, 'response': result}) + '\n')
        return result

    def result(self, method, params):
        response = self.raw(method, params)
        if 'error' in response or 'result' not in response:
            raise ValueError('RPC operation failed: ' + method)
        return response['result']

    def receipt(self, transaction):
        for _ in range(100):
            receipt = self.result('eth_getTransactionReceipt', [transaction])
            if receipt is not None:
                return receipt
            time.sleep(0.05)
        raise RuntimeError('transaction did not complete')


def compile_source(solc, profile, source, via_ir, optimized, output, label):
    request = {'language': 'Solidity', 'sources': {'Cases.sol': {'content': source}}, 'settings': {
        'evmVersion': profile['evmVersion'], 'viaIR': via_ir,
        'optimizer': {'enabled': optimized, 'runs': profile['optimizerRuns']},
        'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}}}}
    save(output / (label + '.request.json'), request)
    response = json.loads(command([solc, '--standard-json'], output, label, data=json.dumps(request).encode()))
    return response


def run(args, report):
    output = args.output
    profile = target()
    frozen = inputs()
    env = lean_environment(args.lean_bin)
    report.update(profile=profile, sourceInputs=frozen, assurance='externalConformanceEvidence',
                  observation='return/revert bytes; reverted transactions: empty logs and selected storage slots',
                  sourcePairing='manually paired resolved programs; source parsing is not verified',
                  modelSchedules='membership in finitely many executed permitted schedule witnesses')
    for name, path in [('solc', args.solc), ('anvil', args.anvil), ('lean', args.lean_bin / 'lean')]:
        version = command([path, '--version'], output, name + '-version', env=env).decode()
        report.setdefault('tools', {})[name] = {'path': str(path), 'sha256': sha(path), 'version': version.strip()}
        if name == 'solc' and not re.search(r'Version: ' + re.escape(profile['referenceCompilerVersion']) + r'(?:\.|\s|$)', version):
            raise ValueError('wrong Solidity compiler identity')
        if name == 'lean' and 'version ' + profile['leanVersion'] + ',' not in version:
            raise ValueError('wrong Lean version')
    command([args.lean_bin / 'lake', 'build', 'Solidity.Conformance.Effects'], output, 'model-build', env=env)
    core = json.loads(command([args.lean_bin / 'lake', 'env', 'lean', '--run', 'Solidity/Conformance/Effects.lean'],
                              output, 'model', env=env))
    for key in ('solidityVersion', 'referenceCompilerVersion', 'evmVersion'):
        if core[key] != profile[key]:
            raise ValueError('model target mismatch')
    report['counts'] = dict(compilerRejections=0, modelRejections=0, modelUnsupported=0,
                          hostExhaustions=0, targetResourceFailures=0,
                          runtimeReturns=0, runtimeReverts=0, discrepancies=0)
    try:
        cases = select(core)
    except ModelFailure as error:
        report['counts'][error.category] += 1
        raise
    report['modelCaseCount'] = len(cases)
    for check in core['modelChecks']:
        if not check['passed'] or check['actualFailure'] != check['expectedFailure']:
            raise ValueError('model boundary control failed')
    report['modelBoundaryControls'] = core['modelChecks']
    declarations = core['declarations']
    report['rejectionControls'] = []
    for rejected in core['rejections']:
        check_rejection(rejected)
        rejected_source = ('pragma solidity ' + profile['solidityVersion'] + ';\ncontract C {\n' + declarations +
                           'function probe() external returns(uint256) { ' + rejected['body'] + ' }\n}\n')
        response = compile_source(args.solc, profile, rejected_source, True, False, output, 'reject-' + rejected['name'])
        errors = [e for e in response.get('errors', []) if e['severity'] == 'error']
        row = {'name': rejected['name'], 'modelRejected': True, 'compilerDiagnostics': errors,
               'admission': rejected['admission'], 'unreachableAdmission': rejected['unreachableAdmission'],
               'unreachableOutcome': rejected['unreachableOutcome']}
        report['rejectionControls'].append(row)
        save(output / 'report.json', report)
        if not all(any(e.get('errorCode') == expected['errorCode'] and e['type'] == expected['type']
                       for e in errors) for expected in rejected['diagnostics']):
            raise ValueError('compiler rejection control changed: ' + rejected['name'])
    # Expected rejection controls are counted separately from runtime-corpus failures.
    report['expectedCompilerRejections'] = len(report['rejectionControls'])
    source = 'pragma solidity ' + profile['solidityVersion'] + ';\ncontract C {\n' + declarations
    for case in cases:
        mutability = '' if case['mutability'] == 'nonpayable' else case['mutability'] + ' '
        source += f"function case_{case['name']}() external {mutability}returns(uint256) {{ {case['body']} }}\n"
    source += '}\n'
    (output / 'Cases.sol').write_text(source)
    with socket.socket() as sock:
        sock.bind(('127.0.0.1', 0))
        port = sock.getsockname()[1]
    rpc = Rpc(port, output)
    with (output / 'anvil.log').open('wb') as log:
        process = subprocess.Popen([str(args.anvil), '--host', '127.0.0.1', '--port', str(port),
                                    '--hardfork', profile['evmVersion'], '--silent'], stdout=log, stderr=log)
        try:
            for _ in range(100):
                if process.poll() is not None:
                    raise RuntimeError('Anvil stopped during startup')
                try:
                    account = rpc.result('eth_accounts', [])[0]
                    break
                except OSError:
                    time.sleep(0.05)
            else:
                raise RuntimeError('Anvil startup timeout')
            # Legacy is an explicit negative compatibility control, never an admitted profile.
            for via_ir in (profile['viaIR'], False):
                for optimized in profile['optimizerEnabled']:
                    label = ('ir' if via_ir else 'legacy') + ('-optimized' if optimized else '-unoptimized')
                    response = compile_source(args.solc, profile, source, via_ir, optimized, output, label)
                    if any(e['severity'] == 'error' for e in response.get('errors', [])):
                        report['counts']['compilerRejections'] += 1
                        raise ValueError('runtime corpus rejected by compiler: ' + label)
                    artifact = response['contracts']['Cases.sol']['C']['evm']
                    tx = rpc.result('eth_sendTransaction', [{'from': account, 'data': '0x' + artifact['bytecode']['object'], 'gas': hex(12_000_000)}])
                    receipt = rpc.receipt(tx)
                    if receipt['status'] != '0x1':
                        raise ValueError('deployment failed')
                    address = receipt['contractAddress']
                    for case in cases:
                        if not via_ir and case['name'] not in COPY_CASES:
                            continue
                        invocation = {'from': account, 'to': address, 'data': '0x' + artifact['methodIdentifiers']['case_' + case['name'] + '()'], 'gas': hex(2_000_000)}
                        actual = call_outcome(rpc.raw('eth_call', [invocation, 'latest']))
                        witnesses = [model_outcome(value) for value in case['outcomes']]
                        row = dict(configuration=label, name=case['name'], compilerAdmitted=True,
                                   modelAdmitted=case['admitted'], modelSupported=True, actual=actual,
                                   permittedWitnesses=witnesses, member=actual in witnesses, profileSupported=via_ir)
                        report.setdefault('observations', []).append(row)
                        save(output / 'report.json', report)
                        if via_ir:
                            report['counts']['runtimeReturns' if actual['status'] == 'returned' else 'runtimeReverts'] += 1
                            if not row['member']:
                                report['counts']['discrepancies'] += 1
                                raise ValueError('target observation outside exported witnesses: ' + case['name'])
                        else:
                            expected = ({'status': 'reverted', 'bytes': '0x4e487b71' + format(0x32, '064x')}
                                        if case['name'] == COPY_CASES[0] else {'status': 'returned', 'bytes': '0x' + format(1, '064x')})
                            if row['member'] or actual != expected:
                                raise ValueError('legacy pipeline boundary control changed')
                        if actual['status'] == 'reverted':
                            slots = [hex(int(slot)) for slot in case['storageProbes']]
                            before = [rpc.result('eth_getStorageAt', [address, slot, 'latest']) for slot in slots]
                            tx = rpc.result('eth_sendTransaction', [invocation])
                            receipt = rpc.receipt(tx)
                            after = [rpc.result('eth_getStorageAt', [address, slot, 'latest']) for slot in slots]
                            row['rollback'] = {'slots': slots, 'before': before, 'after': after, 'receipt': receipt}
                            save(output / 'report.json', report)
                            if receipt['status'] != '0x0' or receipt['logs'] or before != after:
                                raise ValueError('transaction rollback discrepancy')
        finally:
            process.terminate()
            process.wait(timeout=10)
    if inputs() != frozen:
        raise ValueError('package inputs changed during validation')
    report['status'] = 'passed'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--solc', type=Path, required=True)
    parser.add_argument('--lean-bin', type=Path, required=True)
    parser.add_argument('--anvil', type=Path, default=Path(shutil.which('anvil') or 'anvil'))
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    for key in ('solc', 'lean_bin', 'anvil', 'output'):
        setattr(args, key, getattr(args, key).resolve())
    args.output.mkdir(parents=True, exist_ok=False)
    report = {'status': 'failed'}
    try:
        run(args, report)
    except Exception as error:
        report['failure'] = str(error)
        raise
    finally:
        save(args.output / 'report.json', report)
    print(json.dumps({'status': report['status'], 'cases': report['modelCaseCount'], 'counts': report['counts']}))


if __name__ == '__main__':
    main()
