"""Generated mode tests with independent output contracts.

Interpolation is checked by propositional truth tables, not by asking Vampire
to prove its own interpolant. Normalization checks formula preservation and
literal polarity ordering. Coverage targets are intent, not measured coverage.
"""
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path
import re


_TOKEN = re.compile(r"\s*(<=>|<~>|=>|<=|~&|~[|]|[()~&|]|\$true|\$false|[a-z][A-Za-z0-9_]*)")
_PRECEDENCE = {'<=>': 1, '<~>': 1, '=>': 2, '<=': 2,
               '|': 3, '~|': 3, '&': 4, '~&': 4}


def parse_formula(text):
    """Parse only the bounded propositional language used by these fixtures."""
    if not isinstance(text, str) or len(text) > 16384:
        raise ValueError('formula exceeds the propositional contract')
    tokens, position = [], 0
    while position < len(text):
        if not text[position:].strip():
            break
        match = _TOKEN.match(text, position)
        if match is None:
            raise ValueError('unsupported propositional syntax')
        tokens.append(match.group(1))
        position = match.end()
    cursor = 0

    def parse(minimum=0, depth=0):
        nonlocal cursor
        if depth > 128 or cursor >= len(tokens):
            raise ValueError('incomplete or excessively nested formula')
        token = tokens[cursor]
        cursor += 1
        if token == '~':
            left = ('not', parse(5, depth + 1))
        elif token == '(':
            left = parse(0, depth + 1)
            if cursor >= len(tokens) or tokens[cursor] != ')':
                raise ValueError('unbalanced formula')
            cursor += 1
        elif token in ('$true', '$false') or re.fullmatch(r'[a-z][A-Za-z0-9_]*', token):
            left = token
        else:
            raise ValueError('expected an atom')
        while cursor < len(tokens) and _PRECEDENCE.get(tokens[cursor], -1) >= minimum:
            operator = tokens[cursor]
            cursor += 1
            precedence = _PRECEDENCE[operator]
            right = parse(precedence if operator in ('=>', '<=') else precedence + 1, depth + 1)
            left = (operator, left, right)
        return left

    result = parse()
    if cursor != len(tokens):
        raise ValueError('trailing formula tokens')
    return result


def atoms(formula):
    if isinstance(formula, str):
        return set() if formula.startswith('$') else {formula}
    return set().union(*(atoms(child) for child in formula[1:]))


def evaluate(formula, valuation):
    if isinstance(formula, str):
        return formula == '$true' if formula.startswith('$') else valuation[formula]
    operator = formula[0]
    left = evaluate(formula[1], valuation)
    if operator == 'not':
        return not left
    right = evaluate(formula[2], valuation)
    if operator == '&': return left and right
    if operator == '|': return left or right
    if operator == '=>': return not left or right
    if operator == '<=': return left or not right
    if operator == '<=>': return left == right
    if operator == '<~>': return left != right
    if operator == '~&': return not (left and right)
    if operator == '~|': return not (left or right)
    raise ValueError('unknown connective')


def valuations(names):
    names = sorted(names)
    if len(names) > 12:
        raise ValueError('more than 12 atoms exceeds the truth-table bound')
    for values in itertools.product((False, True), repeat=len(names)):
        yield dict(zip(names, values))


def _truth_vector(formula, names):
    return tuple(evaluate(formula, value) for value in valuations(names))


def _units(text):
    text = '\n'.join(line for line in text.splitlines() if not line.lstrip().startswith('%'))
    pattern = re.compile(r'\s*(cnf|fof|tff)\(\s*([a-z][A-Za-z0-9_]*)\s*,\s*'
                         r'(axiom|conjecture|negated_conjecture)\s*,(.*?)\)\s*[.]', re.S)
    units, position = [], 0
    while text[position:].strip():
        match = pattern.match(text, position)
        if match is None:
            raise ValueError('unexpected text in transformed output')
        kind, name, role, body = match.groups()
        units.append({'kind': kind, 'name': name, 'role': role, 'tree': parse_formula(body)})
        position = match.end()
    return units


def _literals(formula):
    if isinstance(formula, tuple) and formula[0] == '|':
        return _literals(formula[1]) + _literals(formula[2])
    if isinstance(formula, str) or (formula[0] == 'not' and isinstance(formula[1], str)):
        return [formula]
    raise ValueError('nonliteral in a CNF normalization fixture')


def _interpolant(text, oracle):
    statuses = re.findall(r'^% SZS status (\w+)', text, re.M)
    if statuses != [oracle['status']]:
        raise ValueError(f'expected {oracle["status"]}; got {statuses}')
    emitted = re.findall(r'^Symbol-weight minimized interpolant: (.+)$', text, re.M)
    weights = re.findall(r'^Actual weight: (\d+)$', text, re.M)
    if len(emitted) != 1 or len(weights) != 1 or int(weights[0]) < 1:
        raise ValueError('missing or ambiguous interpolant/weight output')
    left = [parse_formula(item) for item in oracle['left']]
    right = [parse_formula(item) for item in oracle['right']]
    interpolant = parse_formula(emitted[0])
    left_names = set().union(*(atoms(item) for item in left))
    right_names = set().union(*(atoms(item) for item in right))
    shared = left_names & right_names
    if atoms(interpolant) - shared:
        raise ValueError('interpolant contains a nonshared symbol')
    checked = 0
    for value in valuations(left_names | right_names):
        a = all(evaluate(item, value) for item in left)
        b = all(evaluate(item, value) for item in right)
        i = evaluate(interpolant, value)
        if a and b:
            raise ValueError('invalid oracle: A and B are jointly satisfiable')
        if a and not i:
            raise ValueError('A does not imply the emitted interpolant')
        if i and b:
            raise ValueError('interpolant and B are jointly satisfiable')
        checked += 1
    return {'interpolant': emitted[0], 'shared_atoms': sorted(shared),
            'valuations_checked': checked, 'craig_obligations': 'pass'}


def _selection(text, oracle):
    expected = oracle['units']
    if not isinstance(expected, list) or not expected and not oracle.get('empty_boundary'):
        raise ValueError('missing expected output units')
    actual = _units(text)
    wanted = [dict(unit, tree=parse_formula(unit['formula'])) for unit in expected]
    names = set().union(*(atoms(unit['tree']) for unit in actual + wanted))
    signature = lambda unit: (unit['role'], _truth_vector(unit['tree'], names))
    if Counter(map(signature, actual)) != Counter(map(signature, wanted)):
        raise ValueError('selected formulas differ from the expected formula multiset')
    normalized = oracle.get('normalize')
    reordered = 0
    if normalized is not None:
        by_name = {unit['name']: unit for unit in wanted if unit['kind'] == 'cnf'}
        actual_clauses = [unit for unit in actual if unit['kind'] == 'cnf']
        if len(actual_clauses) != len(by_name):
            raise ValueError('normalization changed the number of CNF clauses')
        for unit in actual_clauses:
            if unit['name'] not in by_name:
                raise ValueError('normalization changed a clause name')
            before = _literals(by_name[unit['name']]['tree'])
            after = _literals(unit['tree'])
            if Counter(before) != Counter(after):
                raise ValueError('normalization changed a clause literal multiset')
            negatives = [isinstance(item, tuple) and item[0] == 'not' for item in after]
            if normalized and negatives != sorted(negatives, reverse=True):
                raise ValueError('normalized clause has a positive literal before a negative literal')
            if not normalized and before != after:
                raise ValueError('disabled normalization changed literal order')
            reordered += before != after
        if normalized and reordered < oracle.get('minimum_reordered_clauses', 0):
            raise ValueError('normalization did not show the required literal reordering')
    return {'units_checked': len(actual), 'valuations_per_unit': 2 ** len(names),
            'reordered_clauses': reordered}


def validate_mode_output(text, folder, source):
    """Return a runner outcome and save the independent contract result."""
    details = {}
    try:
        source = Path(source)
        contract = json.loads(source.with_suffix('.mode.json').read_text())
        if contract['schema_version'] != 1:
            raise ValueError('unsupported mode contract version')
        if contract['source_sha256'] != hashlib.sha256(source.read_bytes()).hexdigest():
            raise ValueError('mode input hash differs from its contract')
        kind, oracle = contract['kind'], contract['oracle']
        if kind == 'interpolant':
            details = _interpolant(text, oracle)
        elif kind == 'selection':
            details = _selection(text, oracle)
        elif kind == 'profile':
            lines = [line.strip() for line in text.splitlines()
                     if line.strip() and not line.lstrip().startswith('%')]
            match = re.fullmatch(r'([A-Z]{3}) ([0-9]+) ([0-9]+)', lines[0]) if len(lines) == 1 else None
            if match is None or int(match[3]) != oracle['atoms']:
                raise ValueError('profile output does not match the independently counted atoms')
            details = {'category': match[1], 'property_bits': int(match[2]), 'atoms': int(match[3])}
        elif kind == 'interpolation-disabled':
            statuses = re.findall(r'^% SZS status (\w+)', text, re.M)
            if statuses != [oracle['status']] or 'interpolant:' in text:
                raise ValueError('disabled interpolation output contract failed')
            details = {'status': statuses[0], 'interpolant_absent': True}
        else:
            raise ValueError('unknown mode output contract')
        outcome, reason = 'pass', ''
    except (OSError, ValueError, KeyError, TypeError, IndexError, RecursionError) as error:
        outcome, reason = 'fail', f'mode output contract: {error}'
    details.update(outcome=outcome, reason=reason)
    (Path(folder) / 'mode-validation.json').write_text(json.dumps(details, indent=2) + '\n')
    return outcome, reason


def mode_cases(binary, folder, Case, root, write_input, options=()):
    folder.mkdir(parents=True, exist_ok=True)
    cases = []

    def add(name, text, flags, kind, oracle, targets, witness, check='mode-contract', expected=''):
        path = folder / (name.replace('/', '-') + '.p')
        write_input(path, text)
        contract = {'schema_version': 1, 'kind': kind, 'oracle': oracle,
                    'source_sha256': hashlib.sha256(text.encode()).hexdigest(),
                    'source_targets': targets, 'activation_witness': witness,
                    'coverage_note': 'Targets are source intent; a fresh coverage capture must measure hits.'}
        write_input(path.with_suffix('.mode.json'), json.dumps(contract, indent=2) + '\n')
        case = Case('mode/' + name, [str(binary), '--input_syntax', 'tptp', '-t', '5',
                    *flags, str(path)], str(root), check, expected, str(path))
        cases.append(case)
        return case

    interpolation = [
        ('literal', ['p'], ['~p'], False),
        ('cnf-literal', ['p'], ['~p'], False),
        ('cnf-disjunction', ['p|q'], ['~p', '~q'], False),
        ('conjunction', ['p', 'q'], ['~(p&q)'], False),
        ('disjunction', ['p|q'], ['~p', '~q'], False),
        ('implication', ['p=>q', 'p'], ['~q'], False),
        ('equivalence', ['p<=>q', 'p'], ['~q'], False),
        ('exclusive-or', ['p<~>q'], ['p<=>q'], False),
        ('local-chain', ['a', 'a=>p'], ['p=>b', '~b'], False),
        ('left-inconsistent', ['p', '~p'], ['q'], False),
        ('right-inconsistent', ['p'], ['q', '~q'], False),
        ('diamond', ['p|q', 'p=>r', 'q=>r'], ['~r'], False),
        ('conjecture', ['p|q'], ['~(p|q)'], True),
    ]
    show = next((option for option in options if option['name'] == 'show_interpolant'), None)
    modes = ['new_heur'] + (['new_opt'] if show and 'new_opt' in show.get('values', []) else [])
    for name, left, right, conjecture in interpolation:
        syntax = 'cnf' if name.startswith('cnf-') else 'fof'
        left_names = set().union(*(atoms(parse_formula(item)) for item in left))
        right_names = set().union(*(atoms(parse_formula(item)) for item in right))
        declarations = [f'vampire(symbol,predicate,{atom},0,{color}).'
                        for names, color in ((left_names - right_names, 'left'),
                                             (right_names - left_names, 'right'))
                        for atom in sorted(names)]
        text = '\n'.join(declarations + ['vampire(left_formula).'] +
                        [f'{syntax}(a{i},axiom,({item})).' for i, item in enumerate(left)] +
                        ['vampire(right_formula).'] +
                        ([f'fof(goal,conjecture,({left[0]})).'] if conjecture else
                         [f'{syntax}(b{i},axiom,({item})).' for i, item in enumerate(right)])) + '\n'
        oracle = {'left': left, 'right': right, 'status': 'Theorem' if conjecture else 'Unsatisfiable'}
        for mode in modes:
            targets = ['Shell/Interpolants.cpp']
            if mode == 'new_opt': targets.append('Shell/InterpolantMinimizer.cpp')
            add(f'interpolant/{name}-{mode}', text,
                ['--show_interpolant', mode, '-av', 'off', '-p', 'off'],
                'interpolant', oracle, targets,
                'One emitted interpolant satisfies both Craig obligations over all valuations and uses shared atoms only.',
                expected=oracle['status'])
        if name == 'literal':
            add('interpolant/disabled', text, ['--show_interpolant', 'off', '-av', 'off', '-p', 'off'],
                'interpolation-disabled', {'status': 'Unsatisfiable'}, ['Shell/UIHelper.cpp'],
                'Unsatisfiable status is present; no interpolant is emitted.', expected='Unsatisfiable')
            if show and 'new_opt' not in show.get('values', []):
                case = add('interpolant/new_opt-unavailable', text, ['--show_interpolant', 'new_opt'],
                    'capability-unavailable', {'feature': 'new_opt', 'exercised': False},
                    ['Shell/Options.cpp'], 'Explicit rejection only; optimized interpolation remains unavailable.',
                    check='reject', expected='new_opt is an invalid value for show_interpolant')
                case.allow_error_exit = True

    def unit(name, formula, role='axiom', kind='fof'):
        return {'name': name, 'formula': formula, 'role': role, 'kind': kind}

    def render(units):
        return ''.join(f'{u["kind"]}({u["name"]},{u["role"]},({u["formula"]})).\n' for u in units)

    normalization = {
        'clauses': [unit('z', 'r|~q|p', kind='cnf'), unit('b', 'q|~p', kind='cnf'),
                    unit('a', 'p', kind='cnf'), unit('goal', '~p|~q|~r', 'negated_conjecture', 'cnf')],
        'mixed': [unit('z', 'p=>q'), unit('b', 'q|~p', kind='cnf'),
                  unit('a', 'p'), unit('goal', 'q', 'conjecture')],
    }
    for name, units in normalization.items():
        for enabled in (False, True):
            add(f'normalize/{name}-{"on" if enabled else "off"}', render(units),
                ['--mode', 'axiom_selection', '--normalize', 'on' if enabled else 'off', '--sine_tolerance', '-1'],
                'selection', {'units': units, 'normalize': enabled,
                              'minimum_reordered_clauses': 1 if enabled else 0},
                ['Shell/Normalisation.cpp', 'Shell/SineUtils.cpp'],
                'Formula/literal multisets are preserved; enabled normalization reorders a mixed-polarity clause.')
    chain = [unit('a', 'p'), unit('b', 'p=>q'), unit('c', 'q=>r'),
             unit('unused', 'z'), unit('goal', 'r', 'conjecture')]
    for depth, selected in ((0, [0, 1, 2, 4]), (1, [2, 4]), (2, [1, 2, 4])):
        add(f'axiom-selection/depth-{depth}', render(chain),
            ['--mode', 'axiom_selection', '--sine_depth', str(depth)],
            'selection', {'units': [chain[index] for index in selected]}, ['Shell/SineUtils.cpp'],
            'Only the expected dependency prefix is emitted; the disconnected z axiom is absent.')
    add('normalize/empty', '', ['--mode', 'axiom_selection', '--normalize', 'on'],
        'selection', {'units': [], 'empty_boundary': True}, ['Shell/Normalisation.cpp'],
        'The empty problem emits no units; this is the explicit empty-input boundary.')

    profiles = [
        ('empty', '', 0),
        ('unit', 'cnf(a,axiom,p(a)).\n', 1),
        ('terms', 'cnf(a,axiom,(p(f(X))|~p(Y)|q(X,a))).\ncnf(b,axiom,(~p(g(a))|q(a,a))).\n', 5),
        ('quantified', 'fof(a,axiom,![X]:(p(X)=>?[Y]:(r(X,Y)&q(Y)))).\nfof(b,axiom,![X,Y]:(p(X)=>r(X,Y))).\n', 5),
        ('numeric', 'tff(p_t,type,p:$int>$o).\ntff(a,axiom,p(1)).\ntff(b,axiom,p(2)).\n', 2),
        ('equality', 'cnf(a,axiom,(a=b|p(a))).\ncnf(b,axiom,(c!=d|~p(b))).\n', 4),
        ('functions', 'cnf(a,axiom,p(f(a))).\ncnf(b,axiom,p(g(b))).\n', 2),
        ('fool', 'fof(a,axiom,p($ite(q,a,b))).\nfof(b,axiom,p($ite(~q,a,b))).\n', 4),
    ]
    for name, text, count in profiles:
        add('profile/' + name, text, ['--mode', 'profile'], 'profile', {'atoms': count},
            ['Shell/Normalisation.cpp', 'Shell/Property.cpp', 'Shell/TheoryFinder.cpp'],
            'Profile mode returns the independently counted atom occurrences; its entry invokes normalization.')

    transforms = {
        'typed-unsat': ('tff(s,type,s:$tType).\ntff(a_t,type,a:s).\ntff(p_t,type,p:s>$o).\n'
                        'tff(a,axiom,p(a)).\ntff(b,axiom,~p(a)).\n', 'Unsatisfiable'),
        'typed-sat': ('tff(s,type,s:$tType).\ntff(a_t,type,a:s).\ntff(p_t,type,p:s>$o).\n'
                      'tff(a,axiom,p(a)).\n', 'Satisfiable'),
        'integer-unsat': ('tff(p_t,type,p:$int>$o).\ntff(a,axiom,![X:$int]:p(X)).\ntff(b,axiom,~p(1)).\n', 'Unsatisfiable'),
    }
    for mode in ('preprocess2', 'tpreprocess', 'tclausify'):
        for name, (text, expected) in transforms.items():
            # Reparse/solve is instrumented by the existing roundtrip runner.
            add(f'transform/{mode}-{name}', text, ['--mode', mode], 'roundtrip',
                {'status': expected}, ['vampire.cpp', 'Shell/Preprocess.cpp'],
                'Transformed TPTP is reparsed and retains the independently known satisfiability answer.',
                check='roundtrip', expected=expected)
    return cases
