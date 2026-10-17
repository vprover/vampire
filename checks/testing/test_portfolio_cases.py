import tempfile
import unittest
from pathlib import Path

from portfolio_cases import SMT_LOGICS, portfolio_cases, property_fixtures
from run import Case, artifact_name


class PortfolioTests(unittest.TestCase):
    def test_known_models_and_opposites_are_paired(self):
        fixtures = property_fixtures()
        self.assertEqual(sum(row[3] for row in fixtures), len(fixtures) // 2)
        for name, _, text, sat, reason in fixtures:
            self.assertTrue(reason)
            if name.startswith('unit-equality'):
                count = int(name.split('-atoms')[1].split('-')[0])
                self.assertEqual(text.count('cnf('), count)
                self.assertEqual('!=' in text, not sat)

    def test_inventory_is_unique_and_records_independent_oracles(self):
        import json
        with tempfile.TemporaryDirectory() as tmp:
            folder = Path(tmp)
            cases = portfolio_cases(Path('/vampire'), folder, Case, folder,
                                    lambda path, text: path.write_text(text))
            self.assertEqual(len({artifact_name(c.name).casefold() for c in cases}), len(cases))
            oracles = json.loads((folder / 'oracles.json').read_text())
            self.assertEqual(len(oracles), len(cases))
            for oracle in oracles:
                self.assertIn(oracle.get('formula_answer', oracle['expected']), ('Satisfiable', 'Unsatisfiable'))
                self.assertTrue(oracle['justification'])
            for case in cases:
                self.assertEqual(case.command[case.command.index('--cores') + 1], '1')
                self.assertTrue(Path(case.source).is_file())
            logic_cases = [c for c in cases if c.name.startswith('portfolio/smt-logic/')]
            self.assertEqual(len(logic_cases), 2 * len(SMT_LOGICS))


if __name__ == '__main__': unittest.main()
