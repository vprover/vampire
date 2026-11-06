"""Check FO2 statistics against known inputs, including split and early UNSAT."""
import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class FO2StatisticsRegression(unittest.TestCase):
    def run_case(self, source):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'case.p'
            path.write_text(source)
            env = {k: v for k, v in os.environ.items() if not k.startswith('FO2_')}
            result = subprocess.run([str(ROOT / 'build/vampire'), '--mode', 'fo2',
                                     '--statistics', 'full', '-t', '5', str(path)],
                                    capture_output=True, text=True, env=env, timeout=10)
            output = result.stdout + result.stderr
            self.assertEqual(result.returncode, 0, output)
            counters = {key.strip(): int(value) for key, value in
                        re.findall(r'^%\s*([^|\n]+?)\s*\|\s*(\d+)\s*$', output, re.M)}
            return output, counters

    def test_single_unit_saturates(self):
        output, counts = self.run_case('cnf(a,axiom,p(a)).\n')
        self.assertIn('SZS status Satisfiable', output)
        for key in ('Initial clauses', 'Activations started', 'Active clauses',
                    'Passive clauses', 'Final active clauses'):
            self.assertEqual(counts.get(key), 1, output)
        self.assertEqual(counts.get('Final passive clauses', 0), 0)

    def test_initial_count_precedes_branching(self):
        output, counts = self.run_case('cnf(a,axiom,(p(X) | q(Y))).\n')
        self.assertIn('SZS status Satisfiable', output)
        self.assertEqual(counts.get('Initial clauses'), 1, output)

    def test_early_refutation_keeps_full_input_count(self):
        output, counts = self.run_case('cnf(a,axiom,p(a)).\ncnf(b,axiom,~p(a)).\n')
        self.assertIn('SZS status Unsatisfiable', output)
        self.assertEqual(counts.get('Initial clauses'), 2, output)
        # Complementary units are detected before given-clause saturation.
        self.assertEqual(counts.get('Activations started', 0), 0, output)


if __name__ == '__main__':
    unittest.main()
