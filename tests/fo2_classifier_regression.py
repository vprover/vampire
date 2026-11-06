"""Scope and clause variable bounds, exercised through the TPTP parser."""
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class ClassifierRegression(unittest.TestCase):
    def check(self, body, expected=True, kind='fof', equality=False):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'case.p'
            path.write_text(f'{kind}(a,axiom,({body})).\n')
            result = subprocess.run(
                [str(ROOT / 'build/vampire'), '--mode', 'fo2_classifier', str(path)],
                capture_output=True, text=True, timeout=10)
            output = result.stdout + result.stderr
            self.assertEqual(result.returncode, 0, output)
            message = ('The problem is in FO2 fragment.' if expected else
                       'The problem is not in FO2 fragment.')
            self.assertIn(message, output)
            if expected:
                self.assertIn(f'FO2_HAS_EQUALITY: {int(equality)}', output)

    def test_clause_variables_are_shared_across_literals(self):
        self.check('p(X,Y) | q(Y,Z)', False, 'cnf')
        self.check('p(X) | q(Y) | r(Z)', False, 'cnf')
        self.check('p(X,Y) | q(Y,X)', kind='cnf')
        self.check('p(X,Y) | Y = Z', False, 'cnf')

    def test_independent_quantified_branches(self):
        for connective in ('&', '|', '=>', '<=>'):
            with self.subTest(connective=connective):
                self.check(f'(! [X,Y] : p(X,Y)) {connective} '
                           '(? [Z,W] : q(Z,W))')

    def test_bound_variable_does_not_leak_to_sibling(self):
        self.check('! [Z,W] : ((! [X,Y] : p(X,Y)) & q(Z,W))')
        self.check('! [Z,W] : (q(Z,W) & (! [X,Y] : p(X,Y)))')

    def test_three_free_variables_in_subformula(self):
        self.check('! [X,Y,Z] : (p(X,Y) | q(Y,Z))', False)
        self.check('! [X,Y,Z] : (p(X,Y) & q(Y,Z))', False)
        self.check('! [X,Y] : (p(X,Y) & (? [Z] : (q(X,Z) & r(Y,Z))))', False)

    def test_nested_binding_and_renaming(self):
        self.check('! [X,Y] : (p(X,Y) & (? [X] : q(X,Y)))')
        self.check('! [X,Y] : (p(X,Y) & (? [Z] : q(Z,Y)))')
        self.check('! [X,Y,Z] : p(X,Y)')  # Vacuous binder needs no variable slot.

    def test_predicate_arity_restriction(self):
        for kind in ('fof', 'cnf'):
            with self.subTest(kind=kind):
                self.check(('! [X,Y] : (r(a,X,Y) | s(Y,X,Y,X))' if kind == 'fof'
                            else 'r(a,X,Y) | s(Y,X,Y,X)'), False, kind=kind)
                self.check(('! [X,Y,Z] : r(X,Y,Z)' if kind == 'fof'
                            else 'r(X,Y,Z)'), False, kind=kind)
                self.check(('! [X,Y] : r(a,f(X),Y)' if kind == 'fof'
                            else 'r(a,f(X),Y)'), False, kind=kind)
        self.check('! [X,Y] : (r(a,X,Y) <=> X = Y)', False)

    def test_equality_and_term_restrictions(self):
        self.check('(! [X,Y] : X = Y) & (? [Z] : p(Z))', equality=True)
        self.check('! [X,Y] : p(f(X),Y)', False)
        self.check('! [X] : p(a,X)')


if __name__ == '__main__':
    unittest.main()
