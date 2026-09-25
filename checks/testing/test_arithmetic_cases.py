import hashlib
import json
from pathlib import Path
import re
import tempfile
import unittest
from collections import namedtuple
from fractions import Fraction

from arithmetic_cases import (arithmetic_cases, arithmetic_specs, array_specs,
                              division, evaluate, integral, literal, number,
                              numeric_fixture, operation)


class ArithmeticTests(unittest.TestCase):
    def test_division_conventions_by_independent_bounds(self):
        for n in range(-15, 16):
            for d in range(-7, 8):
                if not d: continue
                for scale in (1, 2, 3):
                    numerator, denominator = Fraction(n, scale), Fraction(d, scale)
                    for convention in ('e', 't', 'f'):
                        q, r = division(numerator, denominator, convention)
                        self.assertEqual(numerator, denominator * q + r)
                        self.assertEqual(q.denominator, 1)
                        self.assertLess(abs(r), abs(denominator))
                        if convention == 'e': self.assertGreaterEqual(r, 0)
                        if convention == 't': self.assertGreaterEqual(r * numerator, 0)
                        if convention == 'f': self.assertGreaterEqual(r * denominator, 0)
        self.assertEqual(division(-7, -3, 'e'), (3, 2))
        self.assertEqual(division(-7, -3, 't'), (2, -1))
        self.assertEqual(division(7, -3, 'f'), (-3, -2))

    def test_rounding_against_bounded_integer_search(self):
        integers = list(range(-12, 13))
        for numerator in range(-35, 36):
            for denominator in (2, 3, 4, 5, 7):
                value = Fraction(numerator, denominator)
                if not -10 <= value <= 10: continue
                below = max(i for i in integers if i <= value)
                above = min(i for i in integers if i >= value)
                distance = min(abs(value - i) for i in integers)
                nearest = [i for i in integers if abs(value - i) == distance]
                expected = nearest[0] if len(nearest) == 1 else next(i for i in nearest if i % 2 == 0)
                self.assertEqual(integral(value, 'floor'), below)
                self.assertEqual(integral(value, 'ceiling'), above)
                self.assertEqual(integral(value, 'round'), expected)
                self.assertEqual(integral(value, 'truncate'), below if value >= 0 else above)

    def test_exact_literal_roundtrips(self):
        for sort in ('rat', 'real'):
            for value in (Fraction(-7, 4), Fraction(1, 1000), Fraction(-7, 3), Fraction(2**128 + 1)):
                text = literal(sort, value)
                if text.startswith('$quotient('):
                    args = text[len('$quotient('):-1].split(',')
                    actual = Fraction(args[0]) / Fraction(args[1])
                else:
                    actual = Fraction(text)
                self.assertEqual(actual, value)
                if sort == 'rat': self.assertIn('/', text)
                else: self.assertIn('.', text)
        with self.assertRaises(ValueError): number('int', Fraction(1, 2))

    def test_excluded_underspecified_numeric_oracles(self):
        with self.assertRaises(ValueError): division(3, 0, 'e')
        with self.assertRaises(ValueError):
            evaluate(operation('to_int', 'int', number('rat', Fraction(-1, 2))))

    def test_well_typed_numeric_expressions(self):
        def check(expr):
            op, sort, *args = expr
            if op == 'number':
                if sort == 'int': self.assertEqual(Fraction(args[0]).denominator, 1)
                return sort
            inputs = [check(arg) for arg in args]
            if op.startswith('to_'):
                self.assertEqual(len(inputs), 1)
                self.assertEqual(sort, op[3:])
            elif sort == 'bool':
                self.assertTrue(all(item == inputs[0] for item in inputs))
            else:
                self.assertTrue(all(item == sort for item in inputs))
            return sort
        for spec in arithmetic_specs(): check(spec['expression'])

    def test_symbolic_operands_remain_bounded(self):
        for spec in arithmetic_specs():
            text = numeric_fixture(spec, False, 'z3')
            names = re.findall(r'tff\((v[0-9]+)_type,type,', text)
            self.assertTrue(names)
            for name in names:
                self.assertIn(f'$lesseq({name},', text)
                self.assertRegex(text, r'\$lesseq\([^\n]+,' + name + r'\)')
            self.assertIn('$' + spec['expression'][0] + '(', text.split('tff(check,axiom,')[1])

    def test_array_identities_with_independent_functional_models(self):
        def parse(text):
            tokens = iter(re.findall(r'[()]|[^\s()]+', text))
            def term(token):
                if token != '(': return token
                values = []
                for item in tokens:
                    if item == ')': return values
                    values.append(term(item))
                raise ValueError('unclosed term')
            return term(next(tokens))
        def run(expr, a):
            if isinstance(expr, str):
                if expr == 'a': return a
                if expr in ('true', 'false'): return expr == 'true'
                return int(expr)
            op, *args = expr
            values = [run(arg, a) for arg in args]
            if op == '-': return -values[0]
            if op == 'store':
                array, index, value = values
                return lambda key: value if key == index else array(key)
            if op == 'select': return values[0](values[1])
            if op == '=':
                left, right = values
                if callable(left): return all(left(i) == right(i) for i in range(-8, 9))
                return left == right
            raise ValueError(op)
        for spec in array_specs():
            for default in (0, 19, -7):
                if spec['name'] == 'nested-array-update': a = lambda i: lambda j: default + i - j
                elif spec['name'] == 'boolean-overwrite': a = lambda i: bool(i % 2)
                else: a = lambda i: default + i
                self.assertTrue(run(parse(spec['identity']), a), spec['name'])

    def test_portable_generation_controls_and_capability_filter(self):
        Case = namedtuple('Case', 'name command cwd check expected source')
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            def write(path, text): path.write_text(text)
            native = arithmetic_cases('vampire', root / 'native', Case, root, write)
            options = [{'name': 'sat_solver', 'values': ['minisat', 'z3']}, {'name': 'show_z3'}]
            all_cases = arithmetic_cases('vampire', root / 'all', Case, root, write, options)
            self.assertEqual(len(native), 286)
            self.assertEqual(len(all_cases), 572)
            self.assertEqual(len({case.name.casefold() for case in all_cases}), len(all_cases))
            self.assertEqual(sum(case.expected == 'Satisfiable' for case in all_cases), 286)
            records = json.loads((root / 'all/oracles.json').read_text())
            for case, record in zip(all_cases, records):
                self.assertEqual(hashlib.sha256(Path(case.source).read_bytes()).hexdigest(), record['sha256'])
                self.assertEqual(case.name, record['name'])
                self.assertEqual(case.expected, record['expected'])
                if '/z3/' in case.name:
                    self.assertIn('--show_z3', case.command)
                    self.assertEqual(case.command[case.command.index('-ev') + 1], 'off')
            self.assertFalse(json.loads((root / 'native/capabilities.json').read_text())['z3_variants'])


if __name__ == '__main__':
    unittest.main()
