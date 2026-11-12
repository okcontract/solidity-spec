"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""
"""Negative controls for compiled statement and axiom contract comparison."""
import copy
import unittest

from check_theorems import check_records, check_source_closure, digest, source_inputs


class TheoremContractControls(unittest.TestCase):
    def setUp(self):
        self.record = dict(name='Fixture.universal', statement='∀ n : Nat, n = n',
                           kernelStatement={'term': ['forall', 'Nat', 'Eq']},
                           axioms=['propext'], dependencyCount=9)
        self.root = dict(name=self.record['name'], expectedStatement=self.record['statement'],
                         kernelStatementSha256=digest(self.record['kernelStatement']),
                         permittedAxioms=['propext'])

    def test_matching_compiled_contract(self):
        check_records([self.root], [self.record])

    def test_pretty_identical_changed_kernel_statement_rejects(self):
        changed = copy.deepcopy(self.record)
        changed['kernelStatement']['term'].append('HiddenPremise')
        with self.assertRaisesRegex(ValueError, 'statement changed'):
            check_records([self.root], [changed])

    def test_changed_rendered_contract_rejects(self):
        changed = dict(self.record, statement='True')
        with self.assertRaisesRegex(ValueError, 'statement changed'):
            check_records([self.root], [changed])

    def test_new_transitive_axiom_rejects_even_when_globally_standard(self):
        changed = dict(self.record, axioms=['propext', 'Classical.choice'])
        with self.assertRaisesRegex(ValueError, 'unpermitted transitive axiom'):
            check_records([self.root], [changed])

    def test_missing_duplicate_or_reordered_roots_reject(self):
        for records in ([], [self.record, self.record], [dict(self.record, name='Fixture.other')]):
            with self.subTest(records=records), self.assertRaisesRegex(ValueError, 'root'):
                check_records([self.root], records)

    def test_changed_definition_or_missing_source_binding_rejects(self):
        original = {'Solidity/Predicate.lean': 'a' * 64}
        check_source_closure({'sourceClosure': original}, original)
        for manifest in ({}, {'sourceClosure': {}},
                         {'sourceClosure': {'Solidity/Predicate.lean': 'b' * 64}}):
            with self.assertRaisesRegex(ValueError, 'definition closure changed'):
                check_source_closure(manifest, original)

    def test_missing_project_source_cannot_hide_behind_cached_object(self):
        with self.assertRaisesRegex(ValueError, 'missing project import'):
            source_inputs(['Solidity.NoSuchAuditModule'])


if __name__ == '__main__':
    unittest.main()
