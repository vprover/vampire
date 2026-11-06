"""Round-trip and guard checks for the shared-CNF experiment."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class SharedCNFRegression(unittest.TestCase):
    def run_vampire(self, path, extra, classic=False):
        env = {k: v for k, v in os.environ.items()
               if not k.startswith('FO2_') and k != 'SOLVER_SEARCH_TIMING'}
        options = (['--saturation_algorithm', 'otter', '-av', 'off'] if classic
                   else ['--mode', 'fo2'])
        result = subprocess.run([str(ROOT / 'build/vampire'), *options, '-t', '5', str(path)],
                                env={**env, **extra}, capture_output=True, text=True, timeout=10)
        return result.returncode, result.stdout + result.stderr

    def test_round_trip_skolem_and_unsat(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'input.p'
            cnf = Path(directory) / 'prepared.p'
            source.write_text('fof(a,axiom, ![X]: ?[Y]: r(X,Y)).\n'
                              'fof(b,axiom, ![X,Y]: ~r(X,Y)).\n')
            code, output = self.run_vampire(source, {'FO2_EXPORT_CNF': str(cnf)})
            self.assertEqual(code, 0, output)
            self.assertIn('FO2_EXPORT_CNF complete', output)
            self.assertIn('sK', cnf.read_text())
            for classic in (False, True):
                extra = {'SOLVER_SEARCH_TIMING': '1'}
                if not classic:
                    extra['FO2_PREPARED_CNF'] = '1'
                code, output = self.run_vampire(cnf, extra, classic)
                self.assertEqual(code, 0, output)
                self.assertRegex(output, r'SZS status (Unsatisfiable|Theorem)')
                self.assertIn('SOLVER_SEARCH solver=', output)
                if not classic:
                    self.assertIn('FO2_PREPARED_CNF: direct FO2 solver', output)

    def test_prepared_input_rejects_formulas_and_equality(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'invalid.p'
            for source, message in [('fof(a,axiom,p(a)).', 'requires clauses only'),
                                    ('cnf(a,axiom,a=b).', 'requires equality-free clauses')]:
                path.write_text(source)
                code, output = self.run_vampire(path, {'FO2_PREPARED_CNF': '1'})
                self.assertNotEqual(code, 0, output)
                self.assertIn(message, output)
                self.assertNotIn('SZS status Satisfiable', output)


if __name__ == '__main__':
    unittest.main()
