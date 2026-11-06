"""Regression cases for equality removal's diagonal/distinct witness choice."""
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class EqualityRemovalRegression(unittest.TestCase):
    def check(self, formula, expected):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'case.p'
            path.write_text(f'fof(a,axiom,({formula})).\n')
            for mode in ('vampire', 'fo2_remove_equality'):
                with self.subTest(mode=mode):
                    result = subprocess.run(
                        [str(ROOT / 'build/vampire'), '--mode', mode,
                         '--saturation_algorithm', 'otter', '-av', 'off', '-updr', 'off',
                         '-bs', 'on', '-fsr', 'off', '-t', '10', str(path)],
                        capture_output=True, text=True, timeout=15)
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertEqual(re.findall(r'SZS status (\w+)', result.stdout), [expected],
                                     result.stdout + result.stderr)

    def test_quantified_equality_contradiction(self):
        a = '(! [X] : ! [Y] : (X = Y => ? [Y] : (Y = X & Y = X)))'
        self.check(f'{a} & ~{a}', 'Unsatisfiable')

    def test_diagonal_witness_remains_available(self):
        self.check('! [X] : ? [Y] : (X = Y & p(X,Y))', 'Satisfiable')

    def test_distinct_witness_conflicts_with_universal(self):
        self.check('(! [X] : ? [Y] : (X != Y & p(X,Y))) & '
                   '(! [X,Y] : ~p(X,Y))', 'Unsatisfiable')

    def test_distinct_witness_can_be_satisfied(self):
        self.check('! [X] : ? [Y] : (X != Y & p(X,Y))', 'Satisfiable')


if __name__ == '__main__':
    unittest.main()
