"""Bounded semantic oracles and input transformations for upstream Vampire."""
import itertools
import json
from pathlib import Path
import random


def holds(expr, size, relation, env=None):
    """Evaluate a first-order formula in one explicitly enumerated finite model."""
    env = {} if env is None else env
    op, *args = expr
    if op == 'r': return (env[args[0]], env[args[1]]) in relation
    if op == 'eq': return env[args[0]] == env[args[1]]
    if op == 'not': return not holds(args[0], size, relation, env)
    if op == 'and': return all(holds(a, size, relation, env) for a in args)
    if op == 'or': return any(holds(a, size, relation, env) for a in args)
    if op == 'implies': return not holds(args[0], size, relation, env) or holds(args[1], size, relation, env)
    if op in ('all', 'exists'):
        var, body = args
        values = (holds(body, size, relation, {**env, var: value}) for value in range(size))
        return all(values) if op == 'all' else any(values)
    raise ValueError(op)


def render(expr, rename=None):
    rename = rename or {}
    op, *args = expr
    if op == 'r': return 'r(' + ','.join(rename.get(a, a) for a in args) + ')'
    if op == 'eq': return f'({rename.get(args[0], args[0])} = {rename.get(args[1], args[1])})'
    if op == 'not': return f'~({render(args[0], rename)})'
    if op in ('and', 'or', 'implies'):
        connective = {'and': ' & ', 'or': ' | ', 'implies': ' => '}[op]
        return '(' + connective.join(render(a, rename) for a in args) + ')'
    if op in ('all', 'exists'):
        return ('!' if op == 'all' else '?') + f'[{rename.get(args[0], args[0])}]:({render(args[1], rename)})'
    raise ValueError(op)


def finite_formulas(seed):
    rxy, ryx = ('r', 'X', 'Y'), ('r', 'Y', 'X')
    serial = ('all', 'X', ('exists', 'Y', rxy))
    reflexive = ('all', 'X', ('r', 'X', 'X'))
    irreflexive = ('all', 'X', ('not', ('r', 'X', 'X')))
    symmetric = ('all', 'X', ('all', 'Y', ('implies', rxy, ryx)))
    asymmetric = ('all', 'X', ('all', 'Y', ('implies', rxy, ('not', ryx))))
    transitive = ('all', 'X', ('all', 'Y', ('all', 'Z',
        ('implies', ('and', rxy, ('r', 'Y', 'Z')), ('r', 'X', 'Z')))))
    formulas = [serial, ('exists', 'Y', ('all', 'X', rxy)),
        ('and', serial, irreflexive), ('and', serial, asymmetric),
        ('and', serial, asymmetric, transitive), ('and', reflexive, irreflexive),
        ('and', symmetric, irreflexive, serial),
        ('all', 'X', ('exists', 'Y', ('not', ('eq', 'X', 'Y')))),
        ('exists', 'Y', ('all', 'X', ('eq', 'X', 'Y'))),
        ('all', 'X', ('exists', 'X', ('eq', 'X', 'X'))),
        ('not', ('all', 'X', ('eq', 'X', 'X'))),
        ('and', serial, ('not', serial))]
    rng = random.Random(seed)
    def body(depth):
        if depth == 0 or rng.randrange(4) == 0:
            return (rng.choice(('r', 'eq')), rng.choice(('X', 'Y')), rng.choice(('X', 'Y')))
        op = rng.choice(('and', 'or', 'implies', 'not'))
        return (op, *(body(depth - 1) for _ in range(1 if op == 'not' else 2)))
    for _ in range(16):
        formulas.append((rng.choice(('all', 'exists')), 'X',
                         (rng.choice(('all', 'exists')), 'Y', body(3))))
    return formulas


def finite_answer(expr, size):
    pairs = list(itertools.product(range(size), repeat=2))
    for mask in range(1 << len(pairs)):
        relation = {pair for bit, pair in enumerate(pairs) if mask & (1 << bit)}
        if holds(expr, size, relation): return True
    return False


def edge_cases(binary, folder, seed, Case, root, corpus_cases, write_input):
    folder.mkdir(parents=True, exist_ok=True)
    cases, oracles = [], []
    def add(group, name, text, sat, options=(), suffix='.p', evidence='construction'):
        path = folder / (group + '-' + name + suffix)
        write_input(path, text)
        expected = 'Satisfiable' if sat else 'Unsatisfiable'
        cases.append(Case(f'edge/{group}/{name}',
            [str(binary), '-t', '5', '-p', 'off', *options, str(path)],
            str(root), 'szs', expected, str(path)))
        oracles.append({'name': cases[-1].name, 'source': str(path),
                        'expected': expected, 'evidence': evidence})

    # Domain closure and pairwise distinct constants make enumeration exact.
    for size in (1, 2, 3):
        domain = ' | '.join(f'X = a{i}' for i in range(size))
        distinct = ' & '.join(f'a{i} != a{j}' for i in range(size) for j in range(i)) or '$true'
        prefix = f'fof(domain,axiom,![X]:({domain})).\nfof(distinct,axiom,({distinct})).\n'
        for index, expr in enumerate(finite_formulas(seed)):
            sat = finite_answer(expr, size)
            for newcnf in ('off', 'on'):
                for renamed in (False, True):
                    mapping = {'X': 'U', 'Y': 'V', 'Z': 'W'} if renamed else {}
                    add('finite', f'n{size}-f{index:02}-cnf{newcnf}-rename{int(renamed)}',
                        prefix + f'fof(test,axiom,{render(expr, mapping)}).\n', sat,
                        ('-sa', 'fmb', '-newcnf', newcnf),
                        evidence=f'enumerated every binary relation on an explicit {size}-element domain')

    # Pigeonhole constraints over all total unary functions on a closed domain.
    for size in (1, 2, 3):
        domain = ' | '.join(f'X = a{i}' for i in range(size))
        distinct = ' & '.join(f'a{i} != a{j}' for i in range(size) for j in range(i)) or '$true'
        properties = {
            'no-fixed-point': ('![X]: f(X) != X', lambda f: all(f[x] != x for x in range(size))),
            'involution-no-fixed': ('(![X]: f(f(X)) = X) & (![X]: f(X) != X)',
                lambda f: all(f[f[x]] == x and f[x] != x for x in range(size))),
            'injective-not-surjective': ('(![X,Y]: (f(X) = f(Y) => X = Y)) & (?[Y]: ![X]: f(X) != Y)',
                lambda f: len(set(f)) == size and len(set(f)) < size),
            'constant-injective': ('(![X,Y]: f(X) = f(Y)) & (![X,Y]: (f(X) = f(Y) => X = Y))',
                lambda f: len(set(f)) == 1 and len(set(f)) == size),
        }
        for name, (formula, predicate) in properties.items():
            sat = any(predicate(f) for f in itertools.product(range(size), repeat=size))
            for cnf in ('off', 'on'):
                add('functions', f'n{size}-{name}-{cnf}',
                    f'fof(domain,axiom,![X]:({domain})).\nfof(distinct,axiom,({distinct})).\n'
                    f'fof(test,axiom,({formula})).\n', sat, ('-sa', 'fmb', '-newcnf', cnf),
                    evidence=f'enumerated all {size}**{size} total unary functions')

    # Metamorphic transformations have an independent truth-table expectation.
    clauses = list(itertools.product((0, 1, -1), repeat=2))
    rng = random.Random(seed)
    masks = sorted({0, 1, 2, 4, 128, 256, 510, 511, *rng.sample(range(512), 24)})
    for mask in masks:
        selected = [c for bit, c in enumerate(clauses) if mask & (1 << bit)]
        sat = any(all(any(lit and ((lit > 0) == val) for lit, val in zip(clause, assignment))
                      for clause in selected) for assignment in itertools.product((False, True), repeat=2))
        for change in ('identity', 'rename', 'reverse', 'duplicate', 'tautology', 'unused-symbol'):
            variables = ('renamed_first', 'renamed_second') if change == 'rename' else ('p', 'q')
            bodies = []
            for clause in selected:
                literals = [('' if lit > 0 else '~') + var for var, lit in zip(variables, clause) if lit]
                if change == 'reverse': literals.reverse()
                bodies.append(' | '.join(literals) or '$false')
            if change == 'reverse': bodies.reverse()
            if change == 'duplicate': bodies *= 2
            if change == 'tautology': bodies.append('p | ~p')
            if change == 'unused-symbol': bodies.append('fresh_atom')
            text = ''.join(f'cnf(c{i},axiom,({body})).\n' for i, body in enumerate(bodies)) or 'cnf(empty,axiom,$true).\n'
            for strategy in ('lrs', 'discount', 'otter'):
                add('metamorphic', f'{mask:03}-{change}-{strategy}', text, sat, ('-sa', strategy),
                    evidence='all four Boolean assignments; transformation preserves satisfiability')

    # Congruence, long equality chains, and complete literal-selection settings.
    for size in (1, 2, 8, 32):
        chain = ''.join(f'fof(e{i},axiom,a{i} = a{i+1}).\n' for i in range(size))
        for sat in (False, True):
            tail = f'fof(end,axiom,f(a0) {"=" if sat else "!="} f(a{size})).\n'
            for strategy in ('lrs', 'discount', 'otter'):
                for selection in ('0', '10', '11'):
                    add('equality', f'{size}-{sat}-{strategy}-s{selection}', chain + tail, sat,
                        ('-sa', strategy, '-s', selection))

    def smt_case(name, declarations, fact, logic='ALL'):
        for positive in (True, False):
            add('theory', f'{name}-{positive}', f'(set-logic {logic})\n{declarations}\n'
                f'(assert {fact if positive else "(not " + fact + ")"})\n(check-sat)\n', positive,
                suffix='.smt2', evidence='valid identity or ground evaluation; cross-checked with Z3')
    def numeral(n): return str(n) if n >= 0 else f'(- {-n})'
    for value in (0, 1, -1, 2**31-1, 2**31, -2**31, 2**63-1, 2**63, -2**63, 10**100):
        x = numeral(value)
        smt_case(f'int-sub-{value}', '', f'(= (- (+ {x} 1) 1) {x})', 'QF_LIA')
        for divisor in (1, 2, 7):
            smt_case(f'div-{value}-{divisor}', '',
                f'(and (= (div {x} {divisor}) {numeral(value // divisor)})'
                f' (= (mod {x} {divisor}) {value % divisor}))', 'QF_LIA')
    smt_case('real-rational', '', '(= (+ (/ 1.0 3.0) (/ 2.0 3.0)) 1.0)', 'QF_LRA')
    smt_case('real-negative', '', '(= (* (- 0.5) 2.0) (- 1.0))', 'QF_LRA')
    smt_case('nonlinear-square', '(declare-const x Int)', '(>= (* x x) 0)', 'QF_NIA')
    smt_case('uf-congruence', '(declare-sort U 0)\n(declare-const a U)\n(declare-const b U)\n(declare-fun f (U) U)',
             '(=> (= a b) (= (f a) (f b)))', 'QF_UF')
    array = '(declare-const a (Array Int Int))\n(declare-const i Int)\n(declare-const j Int)\n(declare-const v Int)'
    smt_case('array-read-write', array, '(= (select (store a i v) i) v)')
    smt_case('array-other-index', array, '(=> (distinct i j) (= (select (store a i v) j) (select a j)))')
    smt_case('array-store-back', array, '(= (store a i (select a i)) a)')
    smt_case('array-extensionality', array + '\n(declare-const b (Array Int Int))',
             '(=> (forall ((k Int)) (= (select a k) (select b k))) (= a b))')
    datatype = '(declare-datatypes ((List 0)) (((nil) (cons (head Int) (tail List)))))'
    smt_case('datatype-disjoint', datatype, '(distinct nil (cons 0 nil))')
    smt_case('datatype-selector', datatype, '(= (head (cons 7 nil)) 7)')
    smt_case('datatype-injective', datatype, '(distinct (cons 0 nil) (cons 1 nil))')
    smt_case('datatype-acyclic', datatype + '\n(declare-const x List)', '(distinct x (cons 0 x))')
    for depth in (1, 8, 32, 128):
        term = 'p'
        for i in range(depth): term = f'(let ((x{i} {term})) (and x{i} x{i}))'
        smt_case(f'let-depth-{depth}', '(declare-const p Bool)', f'(= {term} p)', 'QF_UF')
    smt_case('let-simultaneous', '(declare-const p Bool)', '(let ((p true)) (let ((p false) (q p)) q))', 'QF_UF')
    smt_case('let-shadowing', '', '(let ((p false)) (let ((p true)) p))', 'QF_UF')

    # Valid lexical boundaries plus semantic contradiction ensure the full input was read.
    for length in (1, 255, 4096):
        name = 'p' + 'x' * (length - 1)
        add('parser', f'identifier-{length}', f'fof(a,axiom,{name}).\nfof(b,axiom,~{name}).\n', False)
    for depth in (1, 32, 128, 512):
        atom = '(' * depth + 'p' + ')' * depth
        add('parser', f'parentheses-{depth}', f'fof(a,axiom,{atom}).\nfof(b,axiom,~p).\n', False)
    for label, text in {
        'empty': '', 'whitespace': ' \t\n\r\n', 'comment-eof': '% no newline',
        'block-comment': '/* stars ** and / characters */\nfof(a,axiom,$true).\n',
        'crlf': 'fof(a,axiom,p).\r\nfof(b,axiom,~p).\r\n',
        'quoted-name': "fof('first name',axiom,'atom with spaces').\nfof(b,axiom,~'atom with spaces').\n",
        'no-final-newline': 'fof(a,axiom,p).\nfof(b,axiom,~p).',
    }.items():
        add('parser', label, text, label in ('empty', 'whitespace', 'comment-eof', 'block-comment'),
            ('--input_syntax', 'tptp'))
    include = folder / 'included axioms.p'
    write_input(include, 'fof(keep,axiom,p).\nfof(discard,axiom,$false).\n')
    add('parser', 'include-selection', f"include('{include}',[keep]).\nfof(a,axiom,p).\n", True)
    add('parser', 'include-all', f"include('{include}').\n", False)

    # Preserve established rejection diagnostics under whitespace/line-ending changes.
    for old in corpus_cases(binary)[0]:
        if not old.allow_error_exit or not old.source or 'line ' in old.expected: continue
        original = root / 'checks' / old.source
        if original.suffix != '.p': continue
        text = original.read_text()
        for variant, changed in (('newline', text + '\n'), ('crlf', text.replace('\n', '\r\n')),
                                 ('comment', '% leading comment\n' + text)):
            path = folder / (original.stem + '-' + variant + '.p')
            write_input(path, changed)
            command = [str(path) if arg == old.source else arg for arg in old.command]
            cases.append(Case(f'edge/rejection/{original.stem}-{variant}', command, old.cwd,
                              'reject', old.expected, str(path), True))
    # Full Cartesian product of these five supported inference controls.
    fixtures = {
        'resolution': ('cnf(a,axiom,p(a)).\ncnf(b,axiom,(~p(X) | p(f(X)))).\ncnf(c,axiom,~p(f(f(a)))).\n', False),
        'congruence': ('cnf(a,axiom,a=b).\ncnf(b,axiom,f(a)!=f(b)).\n', False),
        'saturation': ('cnf(a,axiom,p(a)).\ncnf(b,axiom,(~p(X) | q(X))).\ncnf(c,axiom,q(a)).\n', True),
        'quantified': ('fof(a,axiom,![X]:(p(X) => ?[Y]:r(X,Y))).\nfof(b,axiom,p(a)).\nfof(c,axiom,![Y]:~r(a,Y)).\n', False),
    }
    for strategy, cnf, avatar, selection, ordering in itertools.product(
            ('lrs', 'discount', 'otter'), ('off', 'on'), ('off', 'on'), ('0', '10', '11'), ('kbo', 'lpo')):
        for name, (text, sat) in fixtures.items():
            add('interactions', f'{name}-{strategy}-cnf{cnf}-av{avatar}-s{selection}-{ordering}', text, sat,
                ('-sa', strategy, '-newcnf', cnf, '-av', avatar, '-s', selection, '--term_ordering', ordering),
                evidence='constructed contradiction or explicit satisfiable Horn model; 72 option configurations')
    # Exercise alternate HOL clausification paths on the shipped semantic regressions.
    for old in corpus_cases(binary)[0]:
        if old.check != 'szs' or not old.source.startswith('hol/'): continue
        for mode in ('eager', 'lazy_gen', 'lazy_simp', 'lazy_not_gen', 'conj_eager'):
            cases.append(Case('edge/hol/' + old.name.split('/')[-1] + '-' + mode,
                [*old.command, '-cnfonf', mode], old.cwd, old.check, old.expected, old.source))
    write_input(folder / 'oracles.json', json.dumps(oracles, indent=2))
    return cases
