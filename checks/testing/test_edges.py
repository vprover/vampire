"""Check oracle semantics, parser contracts, and coverage gap accounting."""
from pathlib import Path
import sys
import tempfile
import unittest

from campaign import coverage_gaps
from edge_cases import finite_answer, finite_formulas, holds, render
from run import Case, run_case, write_input


class EdgeOracles(unittest.TestCase):
    def test_nonempty_domain_and_quantifier_order(self):
        unequal = ('not', ('eq', 'X', 'Y'))
        every_has_another = ('all', 'X', ('exists', 'Y', unequal))
        one_differs_from_all = ('exists', 'Y', ('all', 'X', unequal))
        self.assertFalse(finite_answer(every_has_another, 1))
        self.assertTrue(finite_answer(every_has_another, 2))
        self.assertFalse(finite_answer(one_differs_from_all, 2))

    def test_serial_asymmetric_relation_needs_three_elements(self):
        formula = finite_formulas(1)[3]
        self.assertFalse(finite_answer(formula, 1))
        self.assertFalse(finite_answer(formula, 2))
        self.assertTrue(finite_answer(formula, 3))

    def test_finite_strict_order_cannot_be_serial(self):
        formula = finite_formulas(1)[4]
        for size in (1, 2, 3): self.assertFalse(finite_answer(formula, size))

    def test_shadowed_variable_does_not_escape_binder(self):
        expr = ('and', ('exists', 'X', ('r', 'X', 'X')), ('eq', 'X', 'Y'))
        self.assertTrue(holds(expr, 2, {(1, 1)}, {'X': 0, 'Y': 0}))

    def test_alpha_renaming_updates_quantifiers_and_terms(self):
        expr = ('all', 'X', ('exists', 'Y', ('r', 'X', 'Y')))
        self.assertEqual(render(expr, {'X': 'U', 'Y': 'V'}), '![U]:(?[V]:(r(U,V)))')

    def test_preserve_crlf_on_resume(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'input.p'
            write_input(path, 'first\r\nsecond\r\n')
            write_input(path, 'first\r\nsecond\r\n')
            with self.assertRaises(ValueError): write_input(path, 'first\nsecond\n')

    def test_coverage_records_uncovered_exception_branches(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'coverage.info'
            path.write_text('SF:/source.cpp\nDA:2,0\nDA:3,8\nFNDA:0,unused\n'
                'BRDA:3,0,0,-\nBRDA:3,0,1,8\nLF:2\nLH:1\nFNF:1\nFNH:0\nBRF:2\nBRH:1\nend_of_record\n')
            data = coverage_gaps(path)
            self.assertEqual(data['percentages'], {'lines': 50, 'functions': 0, 'function_groups': 0, 'branches': 50})
            self.assertEqual(data['files'][0]['branches'], [{'line': 3, 'block': '0', 'branch': '0'}])

    def classify(self, source, check, expected):
        with tempfile.TemporaryDirectory() as directory:
            case = Case('fixture', [sys.executable, '-c', source], directory, check, expected, '', True)
            return run_case(case, Path(directory), 5, False)

    def test_rejection_requires_diagnostic_and_error_exit(self):
        for code in (1, 4):
            result = self.classify(f"print('User error: bad token'); raise SystemExit({code})", 'reject', 'bad token')
            self.assertEqual(result['outcome'], 'pass')
        self.assertEqual(self.classify("print('bad token')", 'reject', 'bad token')['outcome'], 'fail')
        self.assertEqual(self.classify('raise SystemExit(4)', 'reject', 'bad token')['outcome'], 'fail')

    def test_conflicting_answers_cannot_pass(self):
        source = "print('% SZS status Satisfiable for x'); print('% SZS status Unsatisfiable for x')"
        self.assertEqual(self.classify(source, 'szs', 'Satisfiable')['outcome'], 'fail')

    def test_numeric_boundary_requires_an_explicit_outcome(self):
        self.assertEqual(self.classify("print('Usage: vampire')", 'option-boundary', 'number')['outcome'], 'pass')
        self.assertEqual(self.classify("print('unexpected error'); raise SystemExit(4)", 'option-boundary', 'number')['outcome'], 'fail')


if __name__ == '__main__': unittest.main()
