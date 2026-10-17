"""Constructor-equation graphs with finite witnesses or strict-height cycles."""
import hashlib
import itertools
import json


SHAPES = ('nat-unary', 'tree-left', 'tree-shared', 'tree-tagged', 'tree-nested')
MODES = ('off', 'axiom', 'rule', 'light')
LENGTHS = (1, 2, 3, 5)


def constructor_graph(shape, length, cyclic):
    """Build well-typed equations; each recursive edge crosses a constructor."""
    if shape not in SHAPES or length < 1:
        raise ValueError('unknown shape or nonpositive graph length')
    equations = {}
    for i in range(length):
        child = 'x0' if cyclic and i == length - 1 else 'x' + str(i + 1)
        if shape == 'nat-unary':
            term = ('succ', child)
        elif shape == 'tree-left':
            term = ('branch', child, ('leaf',))
        elif shape == 'tree-shared':
            term = ('branch', child, child)
        elif shape == 'tree-tagged':
            term = ('tagged', bool(i % 2), child)
        else:
            term = ('branch', ('tagged', bool(i % 2), child),
                    ('branch', child, ('leaf',)))
        equations['x' + str(i)] = term
    if not cyclic:
        equations['x' + str(length)] = ('zero',) if shape == 'nat-unary' else ('leaf',)
    return equations


def _references(term, depth=0):
    if isinstance(term, str):
        yield term, depth
    elif isinstance(term, tuple):
        for child in term[1:]:
            yield from _references(child, depth + 1)


def graph_oracle(equations):
    """Expand a DAG into finite trees, or return a positive-height cycle."""
    edges = {name: sorted(set(_references(term))) for name, term in equations.items()}
    for outgoing in edges.values():
        for target, depth in outgoing:
            if target not in equations or depth <= 0:
                raise ValueError('a graph edge must name a defined node under a constructor')
    active, done, cycle = [], set(), []

    def visit(name):
        if name in active:
            cycle[:] = active[active.index(name):] + [name]
            return False
        if name in done:
            return True
        active.append(name)
        for target, _ in edges[name]:
            if not visit(target):
                return False
        active.pop()
        done.add(name)
        return True

    for name in equations:
        if not visit(name):
            strict = []
            for left, right in zip(cycle, cycle[1:]):
                depth = min(d for target, d in edges[left] if target == right)
                strict.append({'larger': left, 'smaller': right, 'minimum_height_difference': depth})
            return {'method': 'strict-constructor-height', 'satisfiable': False,
                    'cycle': cycle, 'inequalities': strict,
                    'contradictory_height_increment': sum(x['minimum_height_difference'] for x in strict),
                    'argument': 'Each constructor is strictly taller than each recursive child. Summing the cycle inequalities requires a finite height to exceed itself.'}

    model = {}

    def expand(term):
        if isinstance(term, str):
            if term not in model:
                model[term] = expand(equations[term])
            return model[term]
        if isinstance(term, tuple):
            return tuple([term[0], *(expand(t) for t in term[1:])])
        return term

    for name in equations:
        if name not in model:
            model[name] = expand(equations[name])
    return {'method': 'finite-constructor-witness', 'satisfiable': True,
            'witness': {name: render(term) for name, term in sorted(model.items())},
            'heights': {name: term_height(term) for name, term in sorted(model.items())},
            'argument': 'Substituting the displayed finite constructor tree for each constant satisfies every equation.'}


def term_height(term):
    if isinstance(term, bool):
        return 0
    if not isinstance(term, tuple):
        raise ValueError('height requires a ground constructor tree')
    recursive_children = [child for child in term[1:] if isinstance(child, tuple)]
    return 0 if not recursive_children else 1 + max(map(term_height, recursive_children))


def render(term):
    if isinstance(term, bool):
        return str(term).lower()
    if isinstance(term, str):
        return term
    if len(term) == 1:
        return term[0]
    return '(' + term[0] + ' ' + ' '.join(map(render, term[1:])) + ')'


def datatype_specs():
    specs = []
    for shape, length, cyclic in itertools.product(SHAPES, LENGTHS, (False, True)):
        equations = constructor_graph(shape, length, cyclic)
        oracle = graph_oracle(equations)
        sort = 'Nat' if shape == 'nat-unary' else 'Tree'
        declaration = ('(declare-datatype Nat ((zero) (succ (pred Nat))))\n' if sort == 'Nat' else
                       '(declare-datatype Tree ((leaf) (branch (left Tree) (right Tree)) (tagged (flag Bool) (child Tree))))\n')
        text = declaration + ''.join(f'(declare-const {name} {sort})\n' for name in equations)
        for i, (name, term) in enumerate(equations.items()):
            # Both orientations denote the same equation and exercise matching.
            left, right = (name, render(term)) if i % 2 == 0 else (render(term), name)
            text += f'(assert (= {left} {right}))\n'
        text += '(check-sat)\n'
        specs.append({'name': f'{shape}-n{length}-' + ('cycle' if cyclic else 'finite'),
                      'shape': shape, 'length': length, 'cyclic': cyclic,
                      'equations': equations, 'text': text, 'oracle': oracle,
                      'expected': 'Satisfiable' if oracle['satisfiable'] else 'Unsatisfiable'})
    return specs


def datatype_cases(binary, folder, Case, root, write_input):
    """Return Case objects for all acyclicity modes and both clausifiers."""
    folder.mkdir(parents=True, exist_ok=True)
    cases, records = [], []
    for spec in datatype_specs():
        path = folder / (spec['name'] + '.smt2')
        write_input(path, spec['text'])
        for mode, newcnf in itertools.product(MODES, ('off', 'on')):
            name = f'datatype/{spec["name"]}/acyclicity-{mode}-cnf-{newcnf}'
            command = [str(binary), '-t', '2', '-p', 'off', '--input_syntax', 'smtlib2',
                       '--term_algebra_acyclicity', mode, '-newcnf', newcnf,
                       '-fd', 'off', '-bd', 'off', str(path)]
            cases.append(Case(name, command, str(root), 'szs', spec['expected'], str(path)))
            records.append({'name': name, 'source': str(path), 'expected': spec['expected'],
                            'sha256': hashlib.sha256(spec['text'].encode()).hexdigest(),
                            'mode': mode, 'newcnf': newcnf, 'equations': spec['equations'],
                            'oracle': spec['oracle'],
                            'controls': {'forward_demodulation': 'off', 'backward_demodulation': 'off'},
                            'qualification': 'Disabling acyclicity may leave a cyclic case incomplete. GaveUp and time limits remain inconclusive; they never satisfy the expected answer.'})
    write_input(folder / 'oracles.json', json.dumps(records, indent=2) + '\n')
    return cases
