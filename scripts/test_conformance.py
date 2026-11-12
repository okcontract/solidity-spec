"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""
import unittest
from check_conformance import CASES, ModelFailure, call_outcome, model_outcome, select


class ConformanceControls(unittest.TestCase):
    def test_rpc_errors_cannot_become_source_reverts(self):
        for response in ({'error': {'code': -32000, 'data': '0x'}},
                         {'result': '0x', 'error': {'code': 3, 'data': '0x'}},
                         {'error': {'code': 3, 'data': 'not bytes'}}, {'result': '0x1'}):
            with self.subTest(response=response), self.assertRaises(ValueError):
                call_outcome(response)

    def test_source_revert_is_an_observation(self):
        self.assertEqual(call_outcome({'error': {'code': 3, 'data': '0xab'}}),
                         {'status': 'reverted', 'bytes': '0xab'})

    def test_model_exhaustion_and_unsupported_are_distinct_failures(self):
        for reason, category in [('exhausted', 'hostExhaustions'), ('targetResource', 'hostExhaustions'),
                                 ('unsupported:reference', 'modelUnsupported')]:
            with self.assertRaises(ModelFailure) as error:
                model_outcome({'status': 'modelFailure', 'reason': reason})
            self.assertEqual(error.exception.category, category)

    def test_membership_accepts_either_witness(self):
        witnesses = [model_outcome({'status': 'returned', 'word': str(n)}) for n in (1, 11)]
        for n in (1, 11):
            self.assertIn(call_outcome({'result': '0x' + format(n, '064x')}), witnesses)
        self.assertNotIn(call_outcome({'result': '0x' + format(12, '064x')}), witnesses)

    def test_missing_admission_empty_or_unsupported_witnesses_fail_closed(self):
        cases = [dict(name=name, admitted=True, outcomes=[dict(status='returned', word='1')]) for name in CASES]
        self.assertEqual(len(select({'cases': cases})), len(CASES))
        for fields in ({'admitted': False}, {'outcomes': []},
                       {'outcomes': [dict(status='modelFailure', reason='exhausted')]}):
            changed = [dict(case) for case in cases]
            changed[0].update(fields)
            with self.assertRaises(ModelFailure):
                select({'cases': changed})


if __name__ == '__main__':
    unittest.main()
