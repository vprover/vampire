"""Independent checks of finite datatype witnesses and cycle certificates."""
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import tempfile
import unittest

from datatype_cases import (LENGTHS, MODES, SHAPES, constructor_graph,
                            datatype_cases, datatype_specs, graph_oracle)


@dataclass
class StubCase:
    name: str
    command: list
    cwd: str
    check: str
    expected: str
    source: str


def parse_ground_tree(text):
    tokens = iter(re.findall(r'[()]|[^ ()]+', text))
    def expression(token):
        if token == '(':
            head = next(tokens)
            children = []
            token = next(tokens)
            while token != ')':
                children.append(expression(token))
                token = next(tokens)
            return (head, *children)
        if token in ('true', 'false'):
            return token == 'true'
        return (token,)
    result = expression(next(tokens))
    if next(tokens, None) is not None:
        raise AssertionError('extra term tokens')
    return result


def substitute(term, environment):
    if isinstance(term, str):
        return environment[term]
    if isinstance(term, tuple):
        return (term[0], *(substitute(x, environment) for x in term[1:]))
    return term


class DatatypeCasesTests(unittest.TestCase):
    def test_every_finite_witness_satisfies_each_equation(self):
        checked = 0
        for spec in datatype_specs():
            if spec['cyclic']:
                continue
            witness = {name: parse_ground_tree(term)
                       for name, term in spec['oracle']['witness'].items()}
            self.assertEqual(set(witness), set(spec['equations']))
            for name, term in spec['equations'].items():
                self.assertEqual(witness[name], substitute(term, witness))
            self.assertEqual(spec['expected'], 'Satisfiable')
            checked += 1
        self.assertEqual(checked, len(SHAPES) * len(LENGTHS))

    def test_cycle_certificate_closes_with_positive_height_gain(self):
        for spec in datatype_specs():
            if not spec['cyclic']:
                continue
            oracle = spec['oracle']
            cycle = oracle['cycle']
            self.assertEqual(cycle[0], cycle[-1])
            self.assertEqual(len(cycle) - 1, spec['length'])
            self.assertEqual(spec['expected'], 'Unsatisfiable')
            total = 0
            for inequality, left, right in zip(oracle['inequalities'], cycle, cycle[1:]):
                self.assertEqual(inequality['larger'], left)
                self.assertEqual(inequality['smaller'], right)
                self.assertIn(right, repr(spec['equations'][left]))
                gain = inequality['minimum_height_difference']
                self.assertGreater(gain, 0)
                total += gain
            self.assertEqual(total, oracle['contradictory_height_increment'])
            self.assertEqual(total, spec['length'] * (2 if spec['shape'] == 'tree-nested' else 1))

    def test_ground_heights_match_chain_lengths(self):
        for spec in datatype_specs():
            if spec['cyclic']:
                continue
            multiplier = 2 if spec['shape'] == 'tree-nested' else 1
            for i in range(spec['length'] + 1):
                self.assertEqual(spec['oracle']['heights']['x' + str(i)],
                                 multiplier * (spec['length'] - i))

    def test_generated_equations_are_well_typed(self):
        signatures = {'zero': ('Nat', ()), 'succ': ('Nat', ('Nat',)),
                      'leaf': ('Tree', ()), 'branch': ('Tree', ('Tree', 'Tree')),
                      'tagged': ('Tree', ('Bool', 'Tree'))}
        for spec in datatype_specs():
            sort = 'Nat' if spec['shape'] == 'nat-unary' else 'Tree'
            def check(term, expected):
                if isinstance(term, bool):
                    self.assertEqual(expected, 'Bool')
                elif isinstance(term, str):
                    self.assertIn(term, spec['equations'])
                    self.assertEqual(expected, sort)
                else:
                    result, arguments = signatures[term[0]]
                    self.assertEqual(result, expected)
                    self.assertEqual(len(arguments), len(term) - 1)
                    for child, child_sort in zip(term[1:], arguments):
                        check(child, child_sort)
            for term in spec['equations'].values():
                check(term, sort)

    def test_repeated_subterms_are_preserved(self):
        term = constructor_graph('tree-shared', 3, True)['x0']
        self.assertEqual(term, ('branch', 'x1', 'x1'))
        oracle = graph_oracle({'x0': ('branch', 'x1', 'x1'), 'x1': ('leaf',)})
        self.assertTrue(oracle['satisfiable'])
        self.assertEqual(oracle['witness']['x0'], '(branch leaf leaf)')

    def test_oracle_depends_on_graph_not_requested_case_label(self):
        self.assertFalse(graph_oracle({'a': ('succ', 'b'), 'b': ('succ', 'a')})['satisfiable'])
        oracle = graph_oracle({'a': ('succ', 'b'), 'b': ('zero',)})
        self.assertTrue(oracle['satisfiable'])
        self.assertEqual(oracle['witness']['a'], '(succ zero)')

    def test_mode_matrix_and_artifact_integrity(self):
        with tempfile.TemporaryDirectory(prefix='datatype cases ') as directory:
            root = Path(directory)
            def write(path, content):
                if path.exists():
                    self.assertEqual(path.read_text(), content)
                else:
                    path.write_text(content)
            cases = datatype_cases(root / 'fake binary', root / 'inputs', StubCase, root, write)
            records = json.loads((root / 'inputs/oracles.json').read_text())
            self.assertEqual(len(cases), 320)
            self.assertEqual(len({case.source for case in cases}), 40)
            self.assertEqual(len({case.name.casefold() for case in cases}), len(cases))
            self.assertEqual({r['mode'] for r in records}, set(MODES))
            for case, record in zip(cases, records):
                self.assertEqual(case.expected, record['expected'])
                self.assertEqual(case.check, 'szs')
                self.assertEqual(case.command[-1], case.source)
                self.assertEqual(hashlib.sha256(Path(case.source).read_bytes()).hexdigest(),
                                 record['sha256'])
                mode_index = case.command.index('--term_algebra_acyclicity') + 1
                self.assertEqual(case.command[mode_index], record['mode'])


if __name__ == '__main__':
    unittest.main()
