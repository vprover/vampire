"""Exercise solver behavior, stream input, output conversion, and proof obligations."""
import itertools


def behavior_cases(binary, folder, Case, root, write_input, options):
    folder.mkdir(parents=True, exist_ok=True)
    cases = []
    def add(group, name, text, expected, flags=(), check='szs', stdin=False):
        path = folder / (group + '-' + name + '.p')
        write_input(path, text)
        command = [str(binary), '-t', '5', *flags]
        if not stdin: command.append(str(path))
        case = Case(f'behavior/{group}/{name}', command, str(root), check, expected, str(path))
        if stdin: case.stdin_text = text
        cases.append(case)

    # The timer thread remains live during cleanup; repeat both exit paths.
    for repeat in range(8):
        for sat, text in ((True, 'cnf(a,axiom,$true).\n'), (False, 'cnf(a,axiom,$false).\n')):
            add('shutdown', f'{sat}-{repeat}', text, 'Satisfiable' if sat else 'Unsatisfiable', ('-p', 'off'))
    for cnf, renamed in itertools.product(('off', 'on'), (False, True)):
        x, y = ('U', 'V') if renamed else ('X', 'Y')
        add('fmb-memory', f'{cnf}-{renamed}',
            f'fof(domain,axiom,![{x}]:({x}=a)).\nfof(serial,axiom,![{x}]:(?[{y}]:r({x},{y}))).\n',
            'Satisfiable', ('-sa', 'fmb', '-newcnf', cnf))

    # Closed domains give exact SAT/UNSAT answers while exercising sort options.
    fmb_names = {'fmb_adjust_sorts', 'fmb_detect_sort_bounds', 'fmb_enumeration_strategy',
                 'fmb_keep_sbeam_generators', 'fmb_symmetry_ratio', 'fmb_symmetry_symbol_order',
                 'fmb_use_simplifying_solver', 'fmb_size_weight_ratio', 'fmb_detect_sort_bounds_time_limit'}
    for option in options:
        if option['name'] not in fmb_names: continue
        values = option['values'] or (['off', 'on'] if option['kind'] == 'bool' else
                                     ['1s'] if option['kind'] == 'time' else ['0', '1', '2'])
        for value in values:
            for size, sat in ((1, True), (1, False), (2, True)):
                domain = ' | '.join(f'X=a{i}' for i in range(size))
                different = '$true' if size == 1 else 'a0 != a1'
                text = f'fof(domain,axiom,![X]:({domain})).\nfof(distinct,axiom,{different}).\n'
                text += 'fof(relation,axiom,![X]:?[Y]:(X ' + ('=' if sat else '!=') + ' Y)).\n'
                add('fmb-options', f'{option["name"]}-{value}-n{size}-{sat}', text,
                    'Satisfiable' if sat else 'Unsatisfiable', ('-sa', 'fmb', '--' + option['name'], value))

    fixtures = {
        'resolution': ('cnf(a,axiom,p(a)).\ncnf(b,axiom,(~p(X)|q(X))).\ncnf(c,axiom,~q(a)).\n', 'Unsatisfiable'),
        'equality': ('cnf(a,axiom,a=b).\ncnf(b,axiom,p(f(a))).\ncnf(c,axiom,~p(f(b))).\n', 'Unsatisfiable'),
        'quantified': ('fof(a,axiom,![X]:(p(X)=>?[Y]:r(X,Y))).\nfof(b,axiom,p(a)).\nfof(c,axiom,![Y]:~r(a,Y)).\n', 'Unsatisfiable'),
        'satisfiable': ('fof(a,axiom,![X]:(p(X)=>q(X))).\nfof(b,axiom,p(a)).\n', 'Satisfiable'),
        'typed': ('tff(s,type,s:$tType).\ntff(a_t,type,a:s).\ntff(p_t,type,p:s>$o).\ntff(a,axiom,p(a)).\ntff(b,axiom,~p(a)).\n', 'Unsatisfiable'),
        'polymorphic': ('tff(id_t,type,id:!>[A:$tType]:(A>A)).\ntff(a_t,type,a:$i).\ntff(id,axiom,![X:$i]:id($i,X)=X).\ntff(b,axiom,id($i,a)!=a).\n', 'Unsatisfiable'),
    }
    for name, (text, expected) in fixtures.items():
        for mode, cnf in itertools.product(('output', 'clausify', 'preprocess'), ('off', 'on')):
            add('roundtrip', f'{name}-{mode}-{cnf}', text, expected,
                ('--mode', mode, '-newcnf', cnf), 'roundtrip')
        for syntax in ('auto', 'tptp'):
            add('stdin', f'{name}-{syntax}', text, expected, ('--input_syntax', syntax), stdin=True)
    # Test actual timeout/memory option use on a bounded contradiction.
    for option, values in (('time_limit', ('0', '1s', '10d', '0.1s')),
                           ('memory_limit', ('0', '19', '20', '128')),
                           ('random_seed', ('0', '1', '2147483647'))):
        for value in values:
            add('resources', f'{option}-{value}', fixtures['resolution'][0], 'Unsatisfiable', ('--' + option, value))

    schedules = next((entry['values'] for entry in options if entry['name'] == 'schedule'), [])
    for schedule in schedules:
        if schedule == 'file': continue  # Exercised separately below.
        for name in ('resolution', 'satisfiable'):
            text, expected = fixtures[name]
            syntax = ()
            if schedule.startswith('smtcomp'):
                text = '(set-logic UF)\n(declare-sort S 0)\n(declare-fun p (S) Bool)\n(assert (forall ((x S)) (p x)))\n' + ('(assert (exists ((x S)) (not (p x))))\n' if expected == 'Unsatisfiable' else '') + '(check-sat)\n'
                syntax = ('--input_syntax', 'smtlib2')
            add('portfolio', f'{schedule}-{name}', text, expected,
                ('--mode', 'portfolio', '--schedule', schedule, '--cores', '1', '-p', 'off', *syntax))

    # Encoded file schedules also exercise comments, blank lines, and rejection.
    valid_schedule = folder / 'valid.schedule'
    write_input(valid_schedule, '% first strategy\n\nlrs+10_1_5\n')
    for name in ('resolution', 'satisfiable'):
        text, expected = fixtures[name]
        add('portfolio', 'file-' + name, text, expected,
            ('--mode', 'portfolio', '--schedule', 'file', '--schedule_file', str(valid_schedule), '--cores', '1'))
    for name, contents, diagnostic in (
            ('empty', '% no strategies\n\n', 'The schedule is empty.'),
            ('invalid', 'invalid-strategy\n', 'Bad strategy: invalid-strategy'),
            ('missing', None, 'Cannot open schedule file:')):
        schedule_file = folder / (name + '.schedule')
        if contents is not None: write_input(schedule_file, contents)
        add('portfolio', 'file-' + name, fixtures['resolution'][0], diagnostic,
            ('--mode', 'portfolio', '--schedule', 'file', '--schedule_file', str(schedule_file), '--cores', '1'), 'reject')
        cases[-1].allow_error_exit = True

    proof_inputs = {name: pair[0] for name, pair in fixtures.items() if pair[1] == 'Unsatisfiable' and name != 'polymorphic'}
    # A variable-renaming case forces nontrivial substitutions in proof reconstruction.
    proof_inputs['substitution'] = ('cnf(a,axiom,(p(X,Y)|q(X))).\ncnf(b,axiom,~p(f(Z),Z)).\n'
                                    'cnf(c,axiom,~q(f(a))).\n')
    proof_inputs['factoring'] = 'cnf(a,axiom,(p(X)|p(Y))).\ncnf(b,axiom,(~p(X)|~p(Y))).\n'
    for name, text in proof_inputs.items():
        for strategy, avatar in itertools.product(('lrs', 'discount', 'otter'), ('off', 'on')):
            add('proof', f'{name}-{strategy}-{avatar}', text, 'Unsatisfiable',
                ('-sa', strategy, '-av', avatar, '-p', 'smtcheck', '--proof_extra', 'full'), 'smt-proof')
    from model_cases import model_cases
    cases += model_cases(binary, folder / "models", Case, root, write_input)
    return cases
