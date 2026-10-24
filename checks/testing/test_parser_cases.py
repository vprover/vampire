"""Tests for independent parser oracles and portable generated artifacts."""
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import tempfile
import unittest

from parser_cases import parser_cases, parser_specs


@dataclass
class StubCase:
    name: str
    command: list
    cwd: str
    check: str
    expected: str
    source: str
    allow_error_exit: bool


class ParserCasesTests(unittest.TestCase):
    def test_exact_numeral_oracles(self):
        for spec in parser_specs():
            oracle = spec['oracle']
            if oracle['method'] != 'exact-rational':
                continue
            rational = Fraction(oracle['numerator'], oracle['denominator'])
            self.assertEqual(Fraction(oracle['token']), rational)
            self.assertEqual(Fraction(oracle['reference']), rational)
        # These signed/scientific boundaries are easy to misread lexically.
        self.assertEqual(Fraction('-2.5e-1'), Fraction(-1, 4))
        self.assertEqual(Fraction('+10/4'), Fraction(5, 2))

    def test_connective_truth_tables(self):
        # Explicit tables are separate from the generator's lambdas.
        tables = {'xor': (False, True, True, False),
                  'reverse-implies': (True, False, True, True),
                  'nand': (True, True, True, False),
                  'nor': (True, False, False, False)}
        assignments = list(itertools.product((False, True), repeat=2))
        seen = set()
        for spec in parser_specs():
            oracle = spec['oracle']
            if oracle['method'] != 'truth-table':
                continue
            assignment = tuple(oracle['assignment'][v] for v in ('p', 'q'))
            answer = tables[oracle['operator']][assignments.index(assignment)]
            self.assertEqual(oracle['value'], answer)
            self.assertEqual(spec['expected'], 'Satisfiable' if answer else 'Unsatisfiable')
            seen.add((oracle['operator'], assignment))
        self.assertEqual(len(seen), 16)

    def test_floor_handles_negative_fraction(self):
        floors = {}
        for spec in parser_specs():
            oracle = spec['oracle']
            if oracle['method'] == 'rational-floor':
                value = Fraction(oracle['token'])
                floor = oracle['floor']
                self.assertLessEqual(floor, value)
                self.assertLess(value, floor + 1)
                floors[oracle['token']] = floor
        self.assertEqual(floors, {'2.0': 2, '-0.5': -1, '1.75': 1, '-2.25': -3})

    def test_divisibility_oracles(self):
        seen = 0
        for spec in parser_specs():
            oracle = spec['oracle']
            if oracle['method'] != 'integer-remainder':
                continue
            n, d, remainder = (oracle[k] for k in ('dividend', 'divisor', 'remainder'))
            self.assertEqual(n, (n // d) * d + remainder)
            self.assertTrue(0 <= remainder < d)
            self.assertEqual(spec['expected'] == 'Satisfiable', remainder == 0)
            seen += 1
        self.assertEqual(seen, 12)

    def test_rejections_require_diagnostic_and_user_exit(self):
        for spec in parser_specs():
            if not spec['reject']:
                continue
            oracle = spec['oracle']
            self.assertEqual(oracle['method'], 'rejection-contract')
            self.assertEqual(oracle['exit_codes'], [1, 4])
            self.assertFalse(oracle['assertions_or_signals_allowed'])
            self.assertEqual(spec['expected'], oracle['diagnostic'])
            self.assertGreater(len(spec['expected']), 12)
            self.assertTrue(oracle['argument'])

    def test_standard_arithmetic_rejections_are_capability_limits(self):
        selected = {s['name']: s for s in parser_specs()
                    if s['family'] == 'reject-tptp' and s['name'] in ('quotient-integer', 'abs-real')}
        self.assertEqual(set(selected), {'quotient-integer', 'abs-real'})
        # Integer exact quotient has rational result. A bare RHS 1 would make
        # the old fixture ill-typed before any conformance claim is possible.
        self.assertIn('$quotient(1,2)=1/2', selected['quotient-integer']['text'])
        self.assertIn('$abs(1.0)=1.0', selected['abs-real']['text'])
        for spec in selected.values():
            self.assertTrue(spec['reject'])
            self.assertEqual(spec['oracle']['classification'], 'unsupported-capability-rejection')
            self.assertEqual(spec['oracle']['standard_input'], 'well-typed')
            self.assertEqual(spec['oracle']['standard_expected'], 'Satisfiable')
            self.assertIn('does not establish TPTP conformance', spec['oracle']['contract_scope'])
        self.assertEqual(selected['quotient-integer']['expected'], '$quotient cannot be used with integer type')
        self.assertEqual(selected['abs-real']['expected'], '$abs can only be used with integer type')

    def test_identity_cases_have_positive_and_negative_controls(self):
        pairs = {}
        for spec in parser_specs():
            if 'assert_identity' in spec['oracle']:
                key = (spec['family'], spec['name'].rsplit('-', 1)[0])
                pairs.setdefault(key, set()).add(spec['expected'])
        self.assertGreater(len(pairs), 30)
        self.assertTrue(all(values == {'Satisfiable', 'Unsatisfiable'} for values in pairs.values()))

    def test_declared_status_agrees_with_semantic_oracle(self):
        statuses = {'Satisfiable': 'sat', 'Unsatisfiable': 'unsat'}
        checked = 0
        for spec in parser_specs():
            if '(set-info :status ' in spec['text']:
                self.assertIn('(set-info :status ' + statuses[spec['expected']] + ')', spec['text'])
                checked += 1
        self.assertEqual(checked, 2)

    def test_case_names_are_unique_on_case_insensitive_filesystems(self):
        names = [s['family'] + '-' + s['name'] for s in parser_specs()]
        self.assertEqual(len(names), len(set(n.casefold() for n in names)))
        self.assertEqual(parser_specs(), parser_specs())

    def test_portable_materialization_and_hashes(self):
        with tempfile.TemporaryDirectory(prefix='parser cases ') as directory:
            root = Path(directory)
            folder = root / 'generated'
            def write(path, content):
                if path.exists():
                    self.assertEqual(path.read_text(), content)
                else:
                    path.write_text(content)
            cases = parser_cases(root / 'fake binary', folder, StubCase, root, write)
            repeated = parser_cases(root / 'another binary', folder, StubCase, root, write)
            self.assertEqual([c.name for c in cases], [c.name for c in repeated])
            oracles = json.loads((folder / 'oracles.json').read_text())
            self.assertEqual(len(cases), len(oracles))
            for case, record in zip(cases, oracles):
                self.assertEqual(case.source, record['source'])
                self.assertEqual(case.expected, record['expected'])
                self.assertEqual(Path(case.source).parent, folder)
                self.assertEqual(case.command[-1], case.source)
                self.assertEqual(record['sha256'], hashlib.sha256(Path(case.source).read_bytes()).hexdigest())
                self.assertEqual(case.allow_error_exit, case.check == 'reject')
                if case.name in ('parser/reject-tptp/quotient-integer', 'parser/reject-tptp/abs-real'):
                    self.assertEqual(record['oracle']['classification'], 'unsupported-capability-rejection')
                    self.assertEqual(record['oracle']['standard_expected'], 'Satisfiable')


if __name__ == '__main__':
    unittest.main()
