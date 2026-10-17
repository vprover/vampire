"""Portfolio dispatch tests with known models and contradictions."""
import json

from runtime_options_cases import truth_table


# Each formula uses only propositional Boolean symbols, a common fragment of
# these logics. The declared logic exercises dispatch, not its entire theory.
SMT_LOGICS = (
    'AUFDTLIA', 'AUFDTLIRA', 'AUFDTNIRA', 'UFDTLIA', 'UFDTLIRA',
    'UFDTNIA', 'UFDTNIRA', 'UFDT', 'LIA', 'UFNIA', 'ALIA', 'UFLIA',
    'UFIDL', 'LRA', 'NIA', 'UFLRA', 'NRA', 'ANIA', 'ALL', 'AUFLIA',
    'AUFNIA', 'AUFNIRA', 'UF', 'AUFLIRA', 'QF_ALIA', 'QF_ANIA',
    'QF_AUFLIA', 'QF_AUFNIA', 'QF_AX', 'QF_IDL', 'QF_LIA', 'QF_LIRA',
    'QF_LRA', 'QF_NIA', 'QF_NIRA', 'QF_NRA', 'QF_RDL', 'QF_UF',
    'QF_UFIDL', 'QF_UFLIA', 'QF_UFLRA', 'QF_UFNIA', 'QF_UFNRA',
    'QF_ABV', 'QF_AUFBV', 'QF_BV', 'QF_UFBV', 'BV', 'UFBV',
)
PROPERTY_SCHEDULES = ('casc_2024', 'casc_2025', 'casc_sat_2024',
                      'casc_sat_2025', 'snake_tptp_uns', 'snake_tptp_sat')


def propositional_smt(logic, clauses):
    def literal(value):
        return f'(not {value[1:]})' if value.startswith('~') else value
    lines = [f'(set-logic {logic})', '(declare-const p Bool)', '(declare-const q Bool)']
    for clause in clauses:
        formula = '(or ' + ' '.join(map(literal, clause)) + ')' if clause else 'false'
        lines.append(f'(assert {formula})')
    return '\n'.join([*lines, '(check-sat)', ''])


def property_fixtures():
    """Each SAT variant has an explicit interpretation; UNSAT adds its opposite."""
    result = []
    for sat in (True, False):
        tag = 'sat' if sat else 'unsat'
        result.extend([
            (f'arithmetic-{tag}', '.p',
             'tff(p_t,type,p:$int>$o).\ntff(pos,axiom,p($sum(1,1))).\n' +
             ('' if sat else 'tff(neg,axiom,~p(2)).\n'), sat,
             'Integer addition fixes 1+1=2. Interpret p as true everywhere for SAT; the negative instance contradicts p(2).'),
            (f'fof-functions-{tag}', '.p',
             'fof(pos,axiom,![X]:p(f(X))).\n' +
             ('' if sat else 'fof(neg,axiom,~p(f(a))).\n'), sat,
             'The universal instance at a contradicts the negative literal. A singleton with p true is a model of the SAT input.'),
            (f'hol-application-{tag}', '.p',
             'thf(p_t,type,p:$i>$o).\nthf(a_t,type,a:$i).\n'
             'thf(pos,axiom,((^[X:$i]:(p @ X)) @ a)).\n' +
             ('' if sat else 'thf(neg,axiom,~(p @ a)).\n'), sat,
             'Beta reduction gives p(a). The all-true predicate is a SAT model; its negation makes the UNSAT variant contradictory.'),
            (f'datatype-{tag}', '.smt2',
             '(set-logic UFDT)\n(declare-datatype Colour ((red) (blue)))\n'
             '(declare-fun p (Colour) Bool)\n(assert (p red))\n' +
             ('' if sat else '(assert (not (p red)))\n') + '(check-sat)\n', sat,
             'The datatype has the two distinct constructors red and blue. Set p true on both for SAT; the opposite red literal is contradictory.'),
        ])
        # Counts immediately around both atom thresholds used by CASC 2024.
        for count in (9, 10, 11, 13, 14, 15):
            for variable in (False, True):
                first = 'X' if variable else 'a'
                equations = [f'cnf(e{i},axiom,f{i}({first})={first}).' for i in range(count - 1)]
                last = f'cnf(last,axiom,f0(a){"=" if sat else "!="}a).'
                result.append((f'unit-equality-{tag}-atoms{count}-variables{int(variable)}', '.p',
                               '\n'.join([*equations, last, '']), sat,
                               'Interpret every unary function as identity for SAT. For UNSAT instantiate the first equation at a and use its disequality.'))
    return result


def portfolio_cases(binary, folder, Case, root, write_input, options=()):
    folder.mkdir(parents=True, exist_ok=True)
    cases, oracles = [], []
    schedules = next((set(row['values']) for row in options if row['name'] == 'schedule'), None)

    def add(name, text, expected, suffix, flags, reason, evidence=None):
        path = folder / (name.replace('/', '-') + suffix)
        write_input(path, text)
        syntax = 'smtlib2' if suffix == '.smt2' else 'tptp'
        command = [str(binary), '--mode', 'portfolio', '--cores', '1', '-t', '3', '-p', 'off',
                   '--input_syntax', syntax, *flags, str(path)]
        case = Case('portfolio/' + name, command, str(root), 'szs', expected, str(path))
        cases.append(case)
        oracles.append({'name': case.name, 'expected': expected, 'justification': reason,
                        'witness': evidence, 'target': 'CASC/Schedules.cpp',
                        'scope': 'Schedule construction and the selected solver result, not execution of every strategy in the schedule.'})

    square = [['p', 'q'], ['~p', 'q'], ['p', '~q'], ['~p', '~q']]
    for logic in SMT_LOGICS:
        for sat in (True, False):
            clauses = square[:3] if sat else square
            witness = truth_table(clauses)
            expected = 'Satisfiable' if witness is not None else 'Unsatisfiable'
            add(f'smt-logic/{logic}-{"sat" if sat else "unsat"}', propositional_smt(logic, clauses),
                expected, '.smt2', ['--schedule', 'smtcomp_2018'],
                'Exhaustive truth table over the complete propositional input. The logic declaration selects the schedule branch.', witness)
            # This historical schedule deliberately rejects these logic classes.
            # Record the formula's answer separately: rejection is a capability
            # contract, not successful semantic validation of the Boolean input.
            if logic.startswith('QF_') or logic in ('BV', 'UFBV'):
                diagnostic = ('unsupported logic ' + logic if 'BV' in logic else
                              'use Z3 for quantifier-free problems')
                cases[-1].check, cases[-1].expected, cases[-1].allow_error_exit = 'reject', diagnostic, True
                oracles[-1]['formula_answer'] = expected
                oracles[-1]['expected'] = diagnostic
                oracles[-1]['scope'] = 'Explicit unsupported-schedule rejection; this does not check the formula answer.'
                if 'BV' in logic:
                    oracles[-1]['target'] = 'Parse/SMTLIB2.cpp'
                    oracles[-1]['scope'] = 'Parser rejects the bit-vector logic before portfolio dispatch. The corresponding schedule branch is not reached.'
    for schedule in PROPERTY_SCHEDULES:
        if schedules is not None and schedule not in schedules:
            continue
        for name, suffix, text, sat, reason in property_fixtures():
            add(f'properties/{schedule}-{name}', text, 'Satisfiable' if sat else 'Unsatisfiable',
                suffix, ['--schedule', schedule], reason)
    # Unlike the datatype-only sample, this reaches the mixed induction branch.
    for schedule in ('induction', 'struct_induction', 'integer_induction'):
        for mixed in (False, True):
            text = '(set-logic ALL)\n(declare-datatype Nat ((zero) (succ (pred Nat))))\n'
            text += '(declare-fun p (Nat) Bool)\n(assert (p zero))\n(assert (not (p zero)))\n'
            if mixed: text += '(declare-const n Int)\n(assert (> n 0))\n'
            text += '(check-sat)\n'
            add(f'induction/{schedule}-mixed{int(mixed)}', text, 'Unsatisfiable', '.smt2',
                ['--schedule', schedule], 'p(zero) and its negation contradict, independently of the optional integer constraint.')
    (folder / 'oracles.json').write_text(json.dumps(oracles, indent=2) + '\n')
    return cases
