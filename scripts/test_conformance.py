"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""
import unittest
from check_conformance import CASES, ModelFailure, call_outcome, check_rejection, model_outcome, select


class ConformanceControls(unittest.TestCase):
    def test_static_rejection_requires_admission_even_for_unreachable_code(self):
        control = dict(admission='rejected', unreachableAdmission='rejected', modelError='rejected',
                       diagnostics=[{'type': 'TypeError', 'errorCode': '7366'}],
                       unreachableOutcome={'status': 'returned', 'word': '0'})
        check_rejection(control)
        for field in ('admission', 'unreachableAdmission'):
            for result in ('admitted', 'exhausted', 'unsupported:type', None):
                with self.subTest(field=field, result=result), self.assertRaisesRegex(ValueError, 'static rejection'):
                    check_rejection(dict(control, **{field: result}))
            missing = dict(control)
            del missing[field]
            with self.assertRaisesRegex(ValueError, 'static rejection'):
                check_rejection(missing)
        for outcome in ({'status': 'reverted', 'bytes': []}, {'status': 'returned', 'word': '1'}):
            with self.subTest(outcome=outcome), self.assertRaisesRegex(ValueError, 'did not return zero'):
                check_rejection(dict(control, unreachableOutcome=outcome))

    def test_rpc_errors_cannot_become_source_reverts(self):
        for response in ({'error': {'code': -32000, 'data': '0x'}},
                         {'result': '0x', 'error': {'code': 3, 'data': '0x'}},
                         {'error': {'code': 3, 'data': 'not bytes'}}, {'result': '0x1'}):
            with self.subTest(response=response), self.assertRaises(ValueError):
                call_outcome(response)

    def test_source_revert_is_an_observation(self):
        self.assertEqual(call_outcome({'error': {'code': 3, 'data': '0xab'}}),
                         {'status': 'reverted', 'bytes': '0xab'})

    def test_host_target_and_unsupported_are_distinct_failures(self):
        for reason, category in [('exhausted', 'hostExhaustions'), ('targetResource', 'targetResourceFailures'),
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
                       {'outcomes': [dict(status='modelFailure', reason='exhausted')]},
                       {'outcomes': [dict(status='modelFailure', reason='targetResource')]}):
            changed = [dict(case) for case in cases]
            changed[0].update(fields)
            with self.assertRaises(ModelFailure):
                select({'cases': changed})


if __name__ == '__main__':
    unittest.main()
