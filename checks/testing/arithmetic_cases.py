"""Exact arithmetic controls for evaluator and Z3 translation branches.

Expected answers use integer arithmetic and Fraction. Source targets describe
intent; a Z3 trace or later isolated coverage capture must establish activation.
"""
from fractions import Fraction
import hashlib
import itertools
import json


ARITHMETIC_SPEC = 'https://tptp.org/UserDocs/TPTPLanguage/ArithmeticSystem.html'
NATIVE_OPTIONS = ('-ev', 'simple')
Z3_OPTIONS = ('-sas', 'z3', '-tha', 'off', '-ev', 'off', '-fd', 'off',
              '-bd', 'off', '--show_z3', 'on')


def integral(value, convention):
    """Round a rational using integer comparisons, including ties to even."""
    value = Fraction(value)
    floor = value.numerator // value.denominator
    if convention == 'floor':
        return floor
    if convention == 'ceiling':
        return -((-value.numerator) // value.denominator)
    if convention == 'truncate':
        return (1 if value >= 0 else -1) * (abs(value.numerator) // value.denominator)
    if convention == 'round':
        twice_remainder = 2 * (value.numerator - floor * value.denominator)
        if twice_remainder < value.denominator:
            return floor
        if twice_remainder > value.denominator:
            return floor + 1
        return floor if floor % 2 == 0 else floor + 1
    raise ValueError('unknown rounding convention')


def division(numerator, denominator, convention):
    """Return q,r with n=d*q+r under the TPTP E/T/F conventions."""
    numerator, denominator = Fraction(numerator), Fraction(denominator)
    if denominator == 0:
        raise ValueError('zero division has no fixed numeric oracle')
    rounding = {'t': 'truncate', 'f': 'floor'}.get(convention)
    if convention == 'e':
        rounding = 'floor' if denominator > 0 else 'ceiling'
    if rounding is None:
        raise ValueError('unknown division convention')
    quotient = integral(numerator / denominator, rounding)
    return Fraction(quotient), numerator - denominator * quotient


def number(sort, value):
    value = Fraction(value)
    if sort == 'int' and value.denominator != 1:
        raise ValueError('nonintegral integer literal')
    if sort not in ('int', 'rat', 'real'):
        raise ValueError('unknown numeric sort')
    return ('number', sort, str(value))


def operation(name, sort, *args):
    return (name, sort, *args)


def evaluate(expr):
    """Evaluate the small fixture language independently of Vampire."""
    op, sort, *args = expr
    if op == 'number':
        return Fraction(args[0])
    values = [evaluate(arg) for arg in args]
    if op == 'sum': return values[0] + values[1]
    if op == 'difference': return values[0] - values[1]
    if op == 'product': return values[0] * values[1]
    if op == 'quotient':
        if values[1] == 0: raise ValueError('zero denominator')
        return values[0] / values[1]
    if op == 'uminus': return -values[0]
    if op.startswith(('quotient_', 'remainder_')):
        q, r = division(*values, op[-1])
        return q if op.startswith('quotient_') else r
    if op in ('floor', 'ceiling', 'truncate', 'round'):
        return Fraction(integral(values[0], op))
    if op == 'to_int':
        # The fixtures use positive fractions or exact integers. TPTP's prose
        # and truncate equation disagree for negative nonintegral arguments.
        if values[0] < 0 and values[0].denominator != 1:
            raise ValueError('ambiguous TPTP negative nonintegral cast excluded')
        return Fraction(integral(values[0], 'floor'))
    if op in ('to_rat', 'to_real'): return values[0]
    if op == 'less': return values[0] < values[1]
    if op == 'lesseq': return values[0] <= values[1]
    if op == 'greater': return values[0] > values[1]
    if op == 'greatereq': return values[0] >= values[1]
    if op == 'is_int': return values[0].denominator == 1
    if op == 'is_rat': return True  # All generated real values are rational.
    raise ValueError('unsupported oracle operation: ' + op)


def literal(sort, value):
    value = Fraction(value)
    if sort == 'int':
        if value.denominator != 1: raise ValueError('nonintegral integer result')
        return str(value.numerator)
    if sort == 'rat':
        return f'{value.numerator}/{value.denominator}'
    if sort != 'real': raise ValueError('unknown numeric sort')
    denominator, places = value.denominator, 0
    while denominator % 2 == 0:
        denominator //= 2
    while denominator % 5 == 0:
        denominator //= 5
    if denominator != 1:
        return f'$quotient({value.numerator}.0,{value.denominator}.0)'
    scaled = value
    while scaled.denominator != 1:
        scaled *= 10
        places += 1
    digits = str(abs(scaled.numerator)).rjust(places + 1, '0')
    body = digits[:-places] + '.' + digits[-places:] if places else digits + '.0'
    return ('-' if value < 0 else '') + body


def render(expr, symbolic=None):
    op, sort, *args = expr
    if op == 'number':
        if symbolic is None: return literal(sort, args[0])
        key = (sort, args[0])
        if key not in symbolic: symbolic[key] = 'v' + str(len(symbolic))
        return symbolic[key]
    return '$' + op + '(' + ','.join(render(arg, symbolic) for arg in args) + ')'


def arithmetic_specs():
    """Return bounded mathematical identities, each later paired with its negation."""
    specs = []

    def add(name, expression, family):
        value = evaluate(expression)
        specs.append({'name': name, 'expression': expression, 'value': value,
                      'family': family})

    for sort, signs, convention, part in itertools.product(
            ('int', 'rat', 'real'), ((1, 1), (1, -1), (-1, 1), (-1, -1)),
            ('e', 't', 'f'), ('quotient', 'remainder')):
        a, b = (Fraction(7), Fraction(3)) if sort == 'int' else (Fraction(7, 2), Fraction(3, 2))
        a, b = a * signs[0], b * signs[1]
        label = ('p' if a > 0 else 'n') + ('p' if b > 0 else 'n')
        op = part + '_' + convention
        add(f'{sort}-{op}-{label}', operation(op, sort, number(sort, a), number(sort, b)), 'signed-division')

    for sort, value, op in itertools.product(('rat', 'real'),
            (Fraction(-5, 2), Fraction(-3, 2), Fraction(3, 2), Fraction(5, 2)),
            ('floor', 'ceiling', 'truncate', 'round')):
        label = ('n' if value < 0 else 'p') + str(abs(value.numerator))
        add(f'{sort}-{op}-{label}-halves', operation(op, sort, number(sort, value)), 'rounding')
    for sort, value in itertools.product(('rat', 'real'), (Fraction(1499, 1000), Fraction(1501, 1000))):
        add(f'{sort}-round-neighbor-{value.numerator}', operation('round', sort, number(sort, value)), 'rounding')

    casts = [('int', 'rat', -3), ('int', 'real', 2**80 + 1),
             ('rat', 'int', Fraction(7, 2)), ('real', 'int', Fraction(7, 2)),
             ('rat', 'int', -3), ('real', 'int', -3),
             ('rat', 'real', Fraction(-7, 3)), ('real', 'rat', Fraction(-7, 4)),
             ('int', 'rat', 2**128 + 1)]
    for index, (source, target, value) in enumerate(casts):
        add(f'cast-{source}-to-{target}-{index}', operation('to_' + target, target, number(source, value)), 'conversion')

    for sort in ('rat', 'real'):
        a, b = number(sort, Fraction(-7, 4)), number(sort, Fraction(5, 2))
        for op in ('sum', 'difference', 'product', 'quotient'):
            add(f'{sort}-{op}-fractional', operation(op, sort, a, b), 'fractional-arithmetic')
        for op in ('less', 'lesseq', 'greater', 'greatereq'):
            add(f'{sort}-{op}-fractional', operation(op, 'bool', a, b), 'comparison')
        for value in (Fraction(-3), Fraction(-7, 4)):
            add(f'{sort}-is-int-{abs(value.numerator)}', operation('is_int', 'bool', number(sort, value)), 'integrality')
    add('real-is-rat-fractional', operation('is_rat', 'bool', number('real', Fraction(-7, 4))), 'integrality')
    return specs


def numeric_fixture(spec, positive, backend):
    aliases = {} if backend == 'z3' else None
    expression = render(spec['expression'], aliases)
    prefix = ''
    if aliases is not None:
        for (sort, value), name in aliases.items():
            token = literal(sort, value)
            prefix += f'tff({name}_type,type,{name}: ${sort}).\n'
            # Equal lower and upper bounds force the exact witness while
            # retaining symbols through equality propagation in preprocessing.
            prefix += f'tff({name}_bound,axiom,($lesseq({name},{token}) & $lesseq({token},{name}))).\n'
    value = spec['value']
    if isinstance(value, bool):
        identity = expression if value else '~(' + expression + ')'
    else:
        identity = expression + ' = ' + literal(spec['expression'][1], value)
    assertion = identity if positive else '~(' + identity + ')'
    return prefix + 'tff(check,axiom,(' + assertion + ')).\n'


def array_specs():
    """Store laws with explicit finite-map witnesses, beyond single read-over-write."""
    prefix = '(declare-const a (Array Int Int))\n'
    # Expected values are obtained by updating finite Python maps with default0.
    specs = []
    for name, updates, index in [('overwrite', [(4, 7), (4, -2)], 4),
                                  ('distinct-updates', [(4, 7), (-3, 11)], 4)]:
        model = {}
        term = 'a'
        for key, value in updates:
            model[key] = value
            term = f'(store {term} {smt_int(key)} {smt_int(value)})'
        result = model.get(index, 0)
        specs.append({'name': name, 'prefix': prefix,
                      'identity': f'(= (select {term} {smt_int(index)}) {smt_int(result)})',
                      'witness': {'default': 0, 'updates': updates, 'read': index, 'result': result}})
    specs.append({'name': 'commuting-distinct-stores', 'prefix': prefix,
                  'identity': '(= (store (store a 4 7) (- 3) 11) (store (store a (- 3) 11) 4 7))',
                  'witness': {'default': 0, 'distinct_indices': [4, -3], 'pointwise_argument': 'Both updates assign 7 at4, 11 at-3 and preserve all other entries.'}})
    specs.append({'name': 'boolean-overwrite', 'prefix': '(declare-const a (Array Int Bool))\n',
                  'identity': '(select (store (store a 2 false) 2 true) 2)',
                  'witness': {'default': False, 'updates': [[2, False], [2, True]], 'read': 2, 'result': True}})
    specs.append({'name': 'nested-array-update',
                  'prefix': '(declare-const a (Array Int (Array Int Int)))\n',
                  'identity': '(= (select (select (store a 2 (store (select a 2) 3 17)) 2) 3) 17)',
                  'witness': {'default': 0, 'updated_path': [2, 3], 'result': 17}})
    return specs


def smt_int(value):
    return str(value) if value >= 0 else f'(- {-value})'


def arithmetic_cases(binary, folder, Case, root, write_input, options=()):
    """Create native cases and Z3 variants only when advertised by the binary."""
    folder.mkdir(parents=True, exist_ok=True)
    advertised = {option['name']: option for option in options}
    z3 = ('z3' in advertised.get('sat_solver', {}).get('values', [])
          and 'show_z3' in advertised)
    backends = ['native'] + (['z3'] if z3 else [])
    cases, records = [], []

    def add(name, text, positive, backend, oracle, targets, syntax):
        full_name = f'arithmetic/{name}/{backend}/' + ('sat' if positive else 'unsat')
        path = folder / (name + '-' + backend + ('-sat' if positive else '-unsat') + ('.p' if syntax == 'tptp' else '.smt2'))
        write_input(path, text)
        controls = NATIVE_OPTIONS if backend == 'native' else Z3_OPTIONS
        command = [str(binary), '-t', '2', '-p', 'off', '--input_syntax', syntax, *controls, str(path)]
        expected = 'Satisfiable' if positive else 'Unsatisfiable'
        cases.append(Case(full_name, command, str(root), 'szs', expected, str(path)))
        records.append({'name': full_name, 'source': str(path), 'expected': expected,
                        'sha256': hashlib.sha256(text.encode()).hexdigest(), 'oracle': oracle,
                        'backend': backend, 'options': list(controls), 'target_branches': targets,
                        'activation': {'required_trace': '[Z3] add (naming):' if backend == 'z3' else None,
                                       'qualification': 'Intent only until logs or isolated coverage establish execution. Missing traces remain an activation gap.'}})

    for spec, positive, backend in itertools.product(arithmetic_specs(), (True, False), backends):
        value = spec['value']
        oracle = {'method': 'exact-integer-and-Fraction', 'expression': spec['expression'],
                  'value': value if isinstance(value, bool) else str(value),
                  'assert_identity': positive, 'family': spec['family'], 'semantics': ARITHMETIC_SPEC,
                  'qualification': 'GaveUp and resource limits remain inconclusive.'}
        targets = ['Kernel/InterpretedLiteralEvaluator.cpp:' + spec['expression'][0],
                   'Kernel/Theory.cpp:numeric interpretation']
        if backend == 'z3': targets.append('SAT/Z3Interfacing.cpp:' + spec['expression'][0])
        add(spec['name'], numeric_fixture(spec, positive, backend), positive, backend, oracle, targets, 'tptp')
    for spec, positive, backend in itertools.product(array_specs(), (True, False), backends):
        identity = spec['identity'] if positive else '(not ' + spec['identity'] + ')'
        text = spec['prefix'] + '(assert ' + identity + ')\n(check-sat)\n'
        oracle = {'method': 'finite-map-updates-and-pointwise-array-laws',
                  'witness': spec['witness'], 'assert_identity': positive}
        add('array-' + spec['name'], text, positive, backend, oracle,
            ['SAT/Z3Interfacing.cpp:ARRAY_SELECT/ARRAY_STORE', 'Kernel/Theory.cpp:array interpretations'], 'smtlib2')
    write_input(folder / 'oracles.json', json.dumps(records, indent=2) + '\n')
    write_input(folder / 'capabilities.json', json.dumps({'z3_variants': z3,
                'missing_capability': None if z3 else 'sat_solver=z3 and show_z3 must both be advertised',
                'standalone_z3_algorithm': 'Not requested: baseline Kernel/MainLoop.cpp disables its completeness precondition.'}, indent=2) + '\n')
    return cases
