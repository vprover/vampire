"""Tests for independent mode output contracts and generated witnesses."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from mode_cases import (atoms, evaluate, mode_cases, parse_formula, validate_mode_output,
                        valuations)
from run import Case, write_input


class FormulaOracleTests(unittest.TestCase):
    def test_boolean_operators_have_independent_truth_tables(self):
        formulas = {'p&q': [False, False, False, True],
                    'p|q': [False, True, True, True],
                    'p=>q': [True, True, False, True],
                    'p<=q': [True, False, True, True],
                    'p<=>q': [True, False, False, True],
                    'p<~>q': [False, True, True, False],
                    'p~&q': [True, True, True, False],
                    'p~|q': [True, False, False, False]}
        for text, expected in formulas.items():
            with self.subTest(text=text):
                self.assertEqual([evaluate(parse_formula(text), v) for v in valuations({'p', 'q'})], expected)

    def test_precedence_parentheses_and_constants(self):
        self.assertEqual(atoms(parse_formula('~(p | q) & $true')), {'p', 'q'})
        for value in valuations({'p', 'q', 'r'}):
            self.assertEqual(evaluate(parse_formula('p | q & ~r'), value),
                             value['p'] or (value['q'] and not value['r']))
        self.assertFalse(evaluate(parse_formula('$false'), {}))

    def test_formula_parser_rejects_unsupported_or_truncated_output(self):
        for text in ('', 'p(a)', '![X]:p(X)', 'p)', '(p', 'p q', 'p &', '__import__', 'p; q'):
            with self.subTest(text=text), self.assertRaises(ValueError):
                parse_formula(text)
        with self.assertRaises(ValueError):
            list(valuations({f'p{i}' for i in range(13)}))


class ModeOutputTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.folder = Path(self.temp.name)
        self.source = self.folder / 'input.p'
        self.source.write_text('fof(a,axiom,p).\n')

    def check(self, kind, oracle, output, mutate=None):
        contract = {'schema_version': 1, 'kind': kind, 'oracle': oracle,
                    'source_sha256': hashlib.sha256(self.source.read_bytes()).hexdigest()}
        if mutate:
            mutate(contract)
        self.source.with_suffix('.mode.json').write_text(json.dumps(contract))
        return validate_mode_output(output, self.folder, self.source)

    @staticmethod
    def interpolation(formula='p', status='Unsatisfiable'):
        return (f'% SZS status {status} for input\n'
                f'Symbol-weight minimized interpolant: {formula}\nActual weight: 1\n')

    def test_valid_interpolant_satisfies_both_craig_obligations(self):
        oracle = {'left': ['a', 'a=>p'], 'right': ['p=>b', '~b'], 'status': 'Unsatisfiable'}
        self.assertEqual(self.check('interpolant', oracle, self.interpolation())[0], 'pass')
        details = json.loads((self.folder / 'mode-validation.json').read_text())
        self.assertEqual(details['valuations_checked'], 8)
        self.assertEqual(details['shared_atoms'], ['p'])

    def test_interpolant_rejects_each_wrong_obligation_and_local_symbol(self):
        oracle = {'left': ['a', 'a=>p'], 'right': ['~p'], 'status': 'Unsatisfiable'}
        for text, reason in (('$false', 'A does not imply'),
                             ('$true', 'jointly satisfiable'),
                             ('a', 'nonshared')):
            with self.subTest(text=text):
                outcome, diagnostic = self.check('interpolant', oracle, self.interpolation(text))
                self.assertEqual(outcome, 'fail')
                self.assertIn(reason, diagnostic)

    def test_interpolant_rejects_status_and_missing_or_duplicate_output(self):
        oracle = {'left': ['p'], 'right': ['~p'], 'status': 'Unsatisfiable'}
        for text in ('% SZS status Unsatisfiable for x\n', self.interpolation(status='Satisfiable'),
                     self.interpolation() + self.interpolation(),
                     self.interpolation() + '% SZS status Satisfiable for x\n'):
            with self.subTest(text=text):
                self.assertEqual(self.check('interpolant', oracle, text)[0], 'fail')

    def test_invalid_satisfiable_interpolation_oracle_cannot_pass(self):
        oracle = {'left': ['p'], 'right': ['p'], 'status': 'Unsatisfiable'}
        self.assertEqual(self.check('interpolant', oracle, self.interpolation())[0], 'fail')

    def test_normalization_requires_preservation_and_observable_reordering(self):
        units = [{'name': 'a', 'kind': 'cnf', 'role': 'axiom', 'formula': 'p|~q'}]
        oracle = {'units': units, 'normalize': True, 'minimum_reordered_clauses': 1}
        self.assertEqual(self.check('selection', oracle, 'cnf(a,axiom,(~q|p)).\n')[0], 'pass')
        for output in ('cnf(a,axiom,(p|~q)).\n', 'cnf(a,axiom,(~q|r)).\n',
                       'cnf(a,axiom,(~q|p|p)).\n', 'cnf(other,axiom,(~q|p)).\n', ''):
            with self.subTest(output=output):
                self.assertEqual(self.check('selection', oracle, output)[0], 'fail')

    def test_disabled_normalization_checks_original_literal_order(self):
        oracle = {'units': [{'name': 'a', 'kind': 'cnf', 'role': 'axiom', 'formula': 'p|~q'}],
                  'normalize': False}
        self.assertEqual(self.check('selection', oracle, 'cnf(a,axiom,(p|~q)).\n')[0], 'pass')
        self.assertEqual(self.check('selection', oracle, 'cnf(a,axiom,(~q|p)).\n')[0], 'fail')

    def test_selection_checks_multiset_roles_and_ignores_formula_renaming(self):
        oracle = {'units': [{'name': 'goal', 'kind': 'fof', 'role': 'conjecture', 'formula': 'p=>q'}]}
        self.assertEqual(self.check('selection', oracle, 'tff(u3,conjecture,(~p|q)).\n')[0], 'pass')
        for text in ('tff(u3,axiom,(~p|q)).\n',
                     'tff(u3,conjecture,(~p|q)).\ntff(u4,conjecture,(~p|q)).\n',
                     'tff(u3,conjecture,(~p|q)).\nerror'):
            self.assertEqual(self.check('selection', oracle, text)[0], 'fail')

    def test_empty_output_requires_explicit_empty_boundary(self):
        self.assertEqual(self.check('selection', {'units': [], 'empty_boundary': True}, '% comment\n')[0], 'pass')
        self.assertEqual(self.check('selection', {'units': []}, '')[0], 'fail')
        self.assertEqual(self.check('selection', {}, '')[0], 'fail')

    def test_profile_requires_exact_atom_count_and_one_record(self):
        self.assertEqual(self.check('profile', {'atoms': 3}, 'EPR 123 3\n')[0], 'pass')
        for text in ('', 'EPR 123 4\n', 'EPR 123 3\nEPR 123 3\n', 'EPR invalid 3\n'):
            self.assertEqual(self.check('profile', {'atoms': 3}, text)[0], 'fail')

    def test_disabled_interpolation_requires_status_and_absent_output(self):
        oracle = {'status': 'Unsatisfiable'}
        self.assertEqual(self.check('interpolation-disabled', oracle,
                                    '% SZS status Unsatisfiable for x\n')[0], 'pass')
        self.assertEqual(self.check('interpolation-disabled', oracle, self.interpolation())[0], 'fail')

    def test_missing_changed_and_unknown_contracts_cannot_pass(self):
        self.assertEqual(validate_mode_output('', self.folder, self.source)[0], 'fail')
        self.source.with_suffix('.mode.json').write_text('{')
        self.assertEqual(validate_mode_output('', self.folder, self.source)[0], 'fail')
        self.assertEqual(self.check('unknown', {}, '')[0], 'fail')
        self.assertEqual(self.check('profile', {'atoms': 0}, 'UEQ 0 0\n',
                                    lambda c: c.update(source_sha256='changed'))[0], 'fail')


class ModeGenerationTests(unittest.TestCase):
    def generate(self, folder, optimized=True):
        options = [{'name': 'show_interpolant',
                    'values': ['new_heur', 'off'] + (['new_opt'] if optimized else [])}]
        return mode_cases(Path('/vampire'), folder, Case, folder, write_input, options)

    def test_cases_have_unique_names_inputs_and_hashed_contracts(self):
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            cases = self.generate(folder)
            self.assertEqual(len(cases), 52)
            self.assertEqual(len({case.name for case in cases}), len(cases))
            self.assertEqual(len({case.source for case in cases}), len(cases))
            for case in cases:
                source = Path(case.source)
                contract = json.loads(source.with_suffix('.mode.json').read_text())
                self.assertEqual(contract['source_sha256'], hashlib.sha256(source.read_bytes()).hexdigest())
                self.assertTrue(contract['source_targets'])
                self.assertTrue(contract['activation_witness'])
                self.assertIn(case.check, ('mode-contract', 'roundtrip'))
            self.assertEqual(self.generate(folder), cases)

    def test_cnf_and_fof_witnesses_share_independent_semantic_contracts(self):
        with tempfile.TemporaryDirectory() as directory:
            cases = {case.name: case for case in self.generate(Path(directory))}
            for name in ('literal', 'disjunction'):
                fof = cases[f'mode/interpolant/{name}-new_heur']
                cnf = cases[f'mode/interpolant/cnf-{name}-new_heur']
                self.assertIn('fof(a0,axiom,', Path(fof.source).read_text())
                self.assertIn('cnf(a0,axiom,', Path(cnf.source).read_text())
                fof_contract = json.loads(Path(fof.source).with_suffix('.mode.json').read_text())
                cnf_contract = json.loads(Path(cnf.source).with_suffix('.mode.json').read_text())
                self.assertEqual(fof_contract['oracle'], cnf_contract['oracle'])

    def test_no_z3_marks_unavailable_feature_without_claiming_interpolation(self):
        with tempfile.TemporaryDirectory() as directory:
            cases = self.generate(Path(directory), optimized=False)
            self.assertEqual(len(cases), 40)
            unavailable = [case for case in cases if 'unavailable' in case.name]
            self.assertEqual(len(unavailable), 1)
            self.assertEqual(unavailable[0].check, 'reject')
            contract = json.loads(Path(unavailable[0].source).with_suffix('.mode.json').read_text())
            self.assertFalse(contract['oracle']['exercised'])
            self.assertEqual(contract['kind'], 'capability-unavailable')
            self.assertFalse(any('-new_opt' in case.name for case in cases))


if __name__ == '__main__':
    unittest.main()
