"""Deterministic parser families with exact arithmetic and Boolean oracles."""
from fractions import Fraction
import hashlib
import itertools
import json


def _row(family, name, text, expected, oracle, syntax='tptp', flags=(), reject=False):
    return dict(family=family, name=name, text=text, expected=expected,
                oracle=oracle, syntax=syntax, flags=list(flags), reject=reject)


def parser_specs():
    """Return portable input recipes; expectations never depend on a solver."""
    rows = []

    def pair(family, name, prefix, fact, reason, syntax='tptp', oracle=None):
        for positive in (True, False):
            suffix = 'true' if positive else 'false'
            body = fact if positive else ('(not ' + fact + ')' if syntax == 'smtlib2' else '~(' + fact + ')')
            actual_prefix = prefix.replace('(set-info :status sat)',
                                           '(set-info :status ' + ('sat' if positive else 'unsat') + ')')
            text = actual_prefix + (f'(assert {body})\n(check-sat)\n' if syntax == 'smtlib2'
                             else f'{"thf" if family == "lambda" else "tff"}(test,axiom,({body})).\n')
            proof = {'method': 'identity', 'argument': reason, 'assert_identity': positive}
            if oracle:
                proof.update(oracle)
            rows.append(_row(family, name + '-' + suffix, text,
                             'Satisfiable' if positive else 'Unsatisfiable', proof, syntax))

    # Exact rationals interpret the lexical representation independently.
    numerals = [
        ('signed-zero', '+0', '0', 'int'), ('signed-int', '+17', '17', 'int'),
        ('negative-int', '-17', '-17', 'int'), ('rational', '6/9', '2/3', 'rat'),
        ('negative-rational', '-14/6', '-7/3', 'rat'),
        ('signed-rational', '+10/4', '5/2', 'rat'),
        ('decimal', '1.250', '1.25', 'real'), ('exponent-upper', '1.25E+2', '125.0', 'real'),
        ('exponent-lower', '-2.5e-1', '-0.25', 'real'),
        ('integer-exponent', '2E3', '2000.0', 'real'),
        ('tiny-exponent', '1.0e-12', '0.000000000001', 'real'),
    ]
    for name, token, canonical, sort in numerals:
        value, reference = Fraction(token), Fraction(canonical)
        assert value == reference
        pair('numeral', name, '', f'{token} = {canonical}',
             'The two lexical numerals denote the same exact rational.',
             oracle={'method': 'exact-rational', 'token': token, 'reference': canonical,
                     'numerator': value.numerator, 'denominator': value.denominator, 'sort': sort})

    # Both truth values occur for each connective. Fixed atomic assignments
    # prevent a SAT result from hiding an incorrectly parsed operator.
    operators = {'xor': ('<~>', lambda p, q: p != q),
                 'reverse-implies': ('<=', lambda p, q: (not q) or p),
                 'nand': ('~&', lambda p, q: not (p and q)),
                 'nor': ('~|', lambda p, q: not (p or q))}
    for name, (operator, evaluate) in operators.items():
        for p, q in itertools.product((False, True), repeat=2):
            value = evaluate(p, q)
            prefix = f'fof(p_value,axiom,{"p" if p else "~p"}).\nfof(q_value,axiom,{"q" if q else "~q"}).\n'
            text = prefix + f'fof(test,axiom,(p {operator} q)).\n'
            rows.append(_row('connective', f'{name}-{int(p)}{int(q)}', text,
                             'Satisfiable' if value else 'Unsatisfiable',
                             {'method': 'truth-table', 'operator': name, 'assignment': {'p': p, 'q': q},
                              'value': value}))

    for name, source in [
        ('file', "file('input source.p',original)"),
        ('inference', 'inference(resolution,[status(thm),info([one,[two]])],[first,2])'),
        ('introduced', 'introduced(definition,[new_symbols(definition,[fresh])])'),
        ('unknown', 'external(tool(nested(value)),[one,[two]])'),
    ]:
        for sat in (True, False):
            text = f'fof(first,axiom,p(a),{source}).\nfof(second,axiom,{"p(a)" if sat else "~p(a)"}).\n'
            rows.append(_row('annotation', name + ('-sat' if sat else '-unsat'), text,
                             'Satisfiable' if sat else 'Unsatisfiable',
                             {'method': 'ground-polarity', 'argument': 'Source annotations do not change p(a).',
                              'atom_truth': True, 'second_polarity': sat}))

    typed = [
        ('nested-type-constructor',
         'tff(s,type,s:$tType).\ntff(box,type,box:$tType>$tType).\n'
         'tff(a,type,a:box(box(s))).\n', 'a = a'),
        ('polymorphic-application',
         'tff(id,type,id:!>[A:$tType]:(A>A)).\ntff(a,type,a:$i).\n'
         'tff(instance,axiom,id($i,a)=a).\n', 'id($i,a) = a'),
        ('polymorphic-predicate',
         'tff(p,type,p:!>[A:$tType]:(A>$o)).\ntff(a,type,a:$i).\n'
         'tff(instance,axiom,p($i,a)).\n', 'p($i,a)'),
        ('distinct-objects', '', '"first object" != "second object"'),
    ]
    for name, prefix, fact in typed:
        pair('typed', name, prefix, fact,
             'Reflexivity, an explicit ground premise, or distinct-object semantics fixes the formula.')
    for name, fact in [
        ('tuple-literal', '[1,2] = [1,2]'),
        ('tuple-binding', '$let([x:$int,y:$int],[x,y]:=[2,3],$sum(x,y)) = 5'),
        ('function-binding', '$let(f:$int>$int,f(X):=$sum(X,1),f(3)) = 4'),
        ('nested-function', '$let(f:$int>$int,f(X):=$sum(X,1),$let(g:$int>$int,g(Y):=f(Y),g(4))) = 5'),
        ('tuple-simultaneous', '$let([x:$int,y:$int,f:$int>$int],[[x,y]:=[2,3],f(X):=X],$sum(f(x),y)) = 5'),
        ('tuple-after-function', '$let([f:$int>$int,x:$int,y:$int],[f(X):=X,[x,y]:=[2,3]],$sum(f(x),y)) = 5'),
    ]:
        pair('binding', name, '', fact, 'Capture-free substitution of the displayed bindings gives the ground identity.')

    for name, term in [
        ('identity', '((^[X:$i]:X) @ a)'),
        ('nested', '((^[X:$i]:(^[Y:$i]:X)) @ a @ b)'),
        ('shadow', '((^[X:$i]:(^[X:$i]:X)) @ b @ a)'),
    ]:
        pair('lambda', name, 'thf(a_type,type,a:$i).\nthf(b_type,type,b:$i).\n',
             term + ' = a', 'Beta reduction, respecting the inner binder scope, yields a.')

    for name, declarations, fact, why in [
        ('define-const', '(define-const c Bool true)\n', 'c', 'The defined constant is true.'),
        ('define-fun', '(define-fun flip ((x Bool)) Bool (not x))\n', '(flip false)', 'Boolean negation maps false to true.'),
        ('define-fun-rec', '(define-fun-rec flip ((x Bool)) Bool (not x))\n', '(flip false)', 'The nonrecursive body is a total Boolean negation, even in recursive declaration syntax.'),
        ('define-funs-rec', '(define-funs-rec ((f ((x Bool)) Bool) (g ((x Bool)) Bool)) ((g x) (not x)))\n',
         '(f false)', 'The simultaneous equations give g(false)=true and f(false)=g(false).'),
        ('define-sort', '(define-sort Flag () Bool)\n(declare-const a Flag)\n', '(= a a)', 'Sort alias expansion preserves Boolean reflexivity.'),
        ('quoted-symbol', '(declare-const |a symbol with spaces| Bool)\n', '(or |a symbol with spaces| (not |a symbol with spaces|))', 'Excluded middle on the same quoted identifier.'),
        ('named-annotation', '(declare-const p Bool)\n', '(! (or p (not p)) :named annotated)', 'The named annotation does not change excluded middle.'),
        ('info', '(set-info :source "parser test")\n(set-info :category crafted)\n(set-info :status sat)\n', 'true', 'Input metadata does not change Boolean true.'),
    ]:
        pair('smt-definition', name, declarations, fact, why, 'smtlib2')

    # SMT-LIB 2.7 permits an empty sequence inside a quoted symbol.
    # Every positive formula has a one-element uninterpreted-sort model;
    # Bool retains its standard two values. Adding the formula's negation
    # supplies an UNSAT control without assuming that the formula is valid.
    uf = '(set-logic QF_UF)\n(declare-sort U 0)\n'
    empty_symbols = [
        ('sort', '(set-logic QF_UF)\n(declare-sort || 0)\n(declare-fun a () ||)\n', '(= a a)'),
        ('constant', uf + '(declare-fun || () U)\n(declare-fun a () U)\n', '(= || a)'),
        ('unary-function', uf + '(declare-fun || (U) U)\n(declare-fun a () U)\n', '(= (|| a) a)'),
        ('predicate', uf + '(declare-fun || (U) Bool)\n(declare-fun a () U)\n', '(|| a)'),
        ('let-binding', '(set-logic QF_UF)\n', '(let ((|| true)) ||)'),
        ('quantified-variable', '(set-logic UF)\n(declare-sort U 0)\n', '(forall ((|| U)) (= || ||))'),
    ]
    for position, prefix, fact in empty_symbols:
        for sat in (True, False):
            text = prefix + '(assert ' + fact + ')\n'
            if not sat:
                text += '(assert (not ' + fact + '))\n'
            text += '(check-sat)\n'
            rows.append(_row('smt-empty-symbol', position + ('-sat' if sat else '-unsat'),
                text, 'Satisfiable' if sat else 'Unsatisfiable',
                {'method': 'finite-witness' if sat else 'formula-and-negation',
                 'position': position, 'domain': [0], 'constants': 0,
                 'unary_functions': 0, 'predicate_value': True,
                 'argument': 'A one-element uninterpreted sort, constant functions and true predicates satisfy the positive formulas; Bool has its standard two values. A formula and its negation cannot both hold.',
                 'standard_reference': 'https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-07-07.pdf#page=24'},
                'smtlib2'))

    tag = '(declare-datatype Tag ((red) (blue)))\n'
    box = '(declare-datatype Box ((empty) (box (value Bool))))\n'
    maybe = '(declare-datatype Maybe (par (T) ((none) (some (value T)))))\n'
    for name, declarations, fact, why in [
        ('enumerated-match', tag, '(match red ((red true) (blue false)))', 'The red branch is selected.'),
        ('default-match', tag, '(match blue ((red false) (x true)))', 'The unmatched blue constructor selects the default branch.'),
        ('bound-match', box, '(match (box true) ((empty false) ((box x) x)))', 'Pattern binding maps x to true.'),
        ('tester-true', tag, '((_ is red) red)', 'A constructor satisfies its own discriminator.'),
        ('tester-false', tag, '(not ((_ is red) blue))', 'Distinct constructors have disjoint discriminator values.'),
        ('polymorphic-as', maybe, '(= (as none (Maybe Bool)) (as none (Maybe Bool)))', 'Explicit type instantiation resolves the nullary polymorphic constructor; reflexivity holds.'),
        ('polymorphic-selector', maybe, '(= (value (some true)) true)', 'The constructor selector returns its stored Boolean.'),
        ('mutual-datatypes', '(declare-datatypes ((First 0) (Second 0)) (((first (next Second))) ((last))))\n',
         '(= (next (first last)) last)', 'Selecting the field of first returns last.'),
        ('codatatype', '(declare-codatatypes ((Stream 0)) (((stream (head Bool) (tail Stream)))))\n(declare-const s Stream)\n',
         '(= (head (stream true s)) true)', 'A codatatype constructor selector returns its supplied head.'),
    ]:
        pair('smt-datatype', name, declarations, fact, why, 'smtlib2')

    def integer(n):
        return str(n) if n >= 0 else f'(- {-n})'
    for divisor in (2, 3, 7):
        for n in (0, 1, 14, -7):
            value = n % divisor == 0
            fact = f'((_ divisible {divisor}) {integer(n)})'
            text = f'(set-logic QF_LIA)\n(assert {fact})\n(check-sat)\n'
            rows.append(_row('smt-ranked', f'divisible-{divisor}-{n}', text,
                             'Satisfiable' if value else 'Unsatisfiable',
                             {'method': 'integer-remainder', 'dividend': n, 'divisor': divisor,
                              'remainder': n % divisor}, 'smtlib2'))
    for token in ('2.0', '-0.5', '1.75', '-2.25'):
        value = Fraction(token)
        term = token if value >= 0 else f'(- {token[1:]})'
        floor = value.numerator // value.denominator
        pair('smt-conversion', 'floor-' + token.replace('-', 'minus'), '',
             f'(= (to_int {term}) {integer(floor)})', 'to_int is floor, computed with exact integer division.', 'smtlib2',
             {'method': 'rational-floor', 'token': token, 'floor': floor})
    pair('smt-conversion', 'to-real', '', '(= (to_real (- 3)) (- 3.0))', 'Integer-to-real embedding preserves -3.', 'smtlib2')
    pair('smt-conversion', 'abs', '', '(= (abs (- 17)) 17)', 'The absolute value of -17 is 17.', 'smtlib2')
    pair('smt-conversion', 'is-int', '', '(not (is_int (- 0.5)))', 'The exact rational -1/2 is not an integer.', 'smtlib2')

    # Each rejection targets a documented local type/scope/arity boundary.
    # run.py also requires exit 1 or 4 and rejects assertions/signals first.
    bad_tptp = [
        ('tuple-singleton-sort', 'tff(x,type,x:[$int]).\n', 'Tuple sort with less than two arguments', 'A tuple sort requires at least two components.'),
        ('let-duplicate-type', 'tff(x,axiom,$let([a:$int,a:$int],a:=1,a)=1).\n', 'is defined twice in a $let-expression', 'A local symbol declaration must be unique.'),
        ('let-missing-type', 'tff(x,axiom,$let(a:$int,b:=1,a)=1).\n', 'is used in a let definition without a declared type', 'The binding name b has no local declaration.'),
        ('tuple-duplicate-binding', 'tff(x,axiom,$let([a:$int,b:$int],[a,a]:=[1,2],a)=1).\n', 'is defined twice in a tuple $let-expression', 'Tuple binding names must be distinct.'),
        ('tuple-missing-type', 'tff(x,axiom,$let(a:$int,[a,b]:=[1,2],a)=1).\n', 'is used in a tuple let definition without a declared sort', 'The second tuple binding lacks a sort.'),
        ('let-definition-sort', 'tff(x,axiom,$let(a:$int,a:=$true,a)=1).\n', 'is used as definition of the symbol', 'A Boolean cannot define an integer symbol.'),
        ('equality-sort', 'tff(a,type,a:$i).\ntff(x,axiom,a=1).\n', 'Cannot create equality between terms of different types', 'Equality operands must have the same sort.'),
        ('formula-sort', 'tff(a,type,a:$int).\ntff(x,axiom,a).\n', 'Non-boolean term', 'An integer term cannot be an asserted formula.'),
        ('undeclared-type', 'tff(a,type,a:missing).\n', 'Undeclared type constructor', 'The referenced sort has no declaration.'),
        ('arithmetic-arity', 'tff(x,axiom,$sum(1,2,3)=6).\n', 'is used with 3 argument(s) when there were 2 expected', 'The interpreted sum operator has fixed binary arity.'),
        ('non-numeric-sum', 'tff(a,type,a:$i).\ntff(x,axiom,$sum(a,a)=a).\n', 'is used with a non-numeric type', 'Arithmetic arguments must be numeric.'),
        ('quotient-integer', 'tff(x,axiom,$quotient(1,2)=1/2).\n', '$quotient cannot be used with integer type', 'TPTP defines integer exact quotient with a rational result; Vampire rejects this standard overload.'),
        ('abs-real', 'tff(x,axiom,$abs(1.0)=1.0).\n', '$abs can only be used with integer type', 'TPTP defines real absolute value; Vampire rejects this standard overload.'),
        ('unquantified-variable', 'fof(x,axiom,p(X)).\n', 'unquantified variable detected', 'A FOF variable must be explicitly bound.'),
    ]
    bad_smt = [
        ('duplicate-logic', '(set-logic QF_UF)\n(set-logic QF_UF)\n', 'set-logic can appear only once', 'One problem has one logic declaration.'),
        ('builtin-sort', '(declare-sort Bool 0)\n', 'Redeclaring built-in, declared or defined sort symbol', 'Built-in sorts cannot be redeclared.'),
        ('invalid-sort-arity', '(declare-sort S -1)\n', 'Unrecognized declared sort arity', 'Sort arity is a nonnegative numeral.'),
        ('duplicate-sort-parameter', '(declare-sort-parameter A)\n(declare-sort-parameter A)\n', 'Redeclaring built-in, declared or defined sort parameter', 'Global sort parameters must be unique.'),
        ('duplicate-function', '(declare-const p Bool)\n(declare-const p Bool)\n', 'Redeclaring function symbol', 'A function declaration cannot reuse a declared name.'),
        ('definition-sort', '(define-fun f () Bool 1)\n', 'has different sort than declared', 'An integer body cannot define a Boolean result.'),
        ('mutual-definition-sort', '(define-funs-rec ((f () Bool)) (1))\n', 'has different sort than declared', 'Each simultaneous definition must match its declared result sort.'),
        ('duplicate-parameter', '(define-funs-rec ((f ((x Bool) (x Bool)) Bool)) (x))\n', 'Multiple occurrence of variable', 'A function argument list cannot bind the same name twice.'),
        ('assert-sort', '(assert 1)\n', 'Asserted expression of non-boolean sort', 'Only Boolean expressions can be asserted.'),
        ('assert-not-sort', '(assert-not 1)\n', 'Asserted expression of non-boolean sort', 'Negated assertions still require Boolean expressions.'),
        ('claim-sort', '(assert-claim 1)\n', 'Asserted expression of non-boolean sort', 'Claim expressions must be Boolean.'),
        ('match-nondatatype', '(assert (match true ((x x))))\n', 'is not of a term algebra type', 'Pattern matching requires a datatype value.'),
        ('match-integer', '(assert (match 1 ((x true))))\n', 'is not of a term algebra type', 'An integer is not a user datatype value.'),
        ('match-missing', tag + '(assert (match red ((red true))))\n', 'Missing ctors in match expression', 'All constructors need a branch or default.'),
        ('match-duplicate', tag + '(assert (match red ((red true) (red false) (blue true))))\n', 'is either not ctor or was listed twice', 'A constructor pattern cannot be repeated.'),
        ('match-unknown', tag + '(assert (match red (((missing x) true) (blue false))))\n', 'Unrecognized term algebra constructor', 'A structured pattern must name a known constructor.'),
        ('match-nested', box + '(assert (match (box true) ((empty false) ((box (nested x)) true))))\n', 'in match patterns are disallowed', 'Nested constructor patterns are outside the supported grammar.'),
        ('ranked-numeral', '(assert ((_ divisible -2) 4))\n', 'Expected numeral as an argument of a ranked function', 'The divisor index must be an unsigned numeral.'),
        ('ranked-sort', '(assert ((_ divisible 2) true))\n', 'Not enough arguments or wrong sorts', 'Divisibility requires an integer argument.'),
        ('tester-unknown', '(assert ((_ is missing) true))\n', 'is not a datatype constructor', 'A tester must name a declared constructor.'),
        ('unbound-term', '(assert unknown)\n', 'Unrecognized term identifier', 'The asserted symbol has no binding or declaration.'),
        ('extra-argument', '(declare-const p Bool)\n(assert (p true))\n', 'Too many arguments', 'A nullary declaration cannot accept an argument.'),
        ('color-unknown', '(color-symbol missing :left)\n', 'is not a user symbol', 'Only declared user symbols can be colored.'),
        ('color-invalid', '(declare-const p Bool)\n(color-symbol p :middle)\n', 'is not a color keyword', 'Only the supported left/right colors are accepted.'),
    ]
    for syntax, rejected in (('tptp', bad_tptp), ('smtlib2', bad_smt)):
        for name, text, diagnostic, why in rejected:
            oracle = {'method': 'rejection-contract', 'argument': why,
                      'exit_codes': [1, 4], 'diagnostic': diagnostic,
                      'assertions_or_signals_allowed': False}
            if syntax == 'tptp' and name in ('quotient-integer', 'abs-real'):
                # A pass here confirms Vampire's known capability diagnostic;
                # both formulas are valid standard inputs with a true equality.
                oracle.update(classification='unsupported-capability-rejection',
                              standard_input='well-typed', standard_expected='Satisfiable',
                              standard_reference='https://tptp.org/UserDocs/TPTPLanguage/ArithmeticSystem.html',
                              contract_scope='Checks the local rejection diagnostic only; does not establish TPTP conformance.')
            rows.append(_row('reject-' + syntax, name, text, diagnostic, oracle, syntax, reject=True))
    return rows


def parser_cases(binary, folder, Case, root, write_input):
    """Build Case objects and exact oracle metadata using the shared runner."""
    folder.mkdir(parents=True, exist_ok=True)
    cases, oracles = [], []
    for spec in parser_specs():
        name = 'parser/' + spec['family'] + '/' + spec['name']
        suffix = '.smt2' if spec['syntax'] == 'smtlib2' else '.p'
        path = folder / (spec['family'] + '-' + spec['name'] + suffix)
        write_input(path, spec['text'])
        case = Case(name, [str(binary), '-t', '5', '-p', 'off',
                          '--input_syntax', spec['syntax'], *spec['flags'], str(path)],
                    str(root), 'reject' if spec['reject'] else 'szs',
                    spec['expected'], str(path), spec['reject'])
        cases.append(case)
        oracles.append({'name': name, 'source': str(path), 'expected': spec['expected'],
                        'check': case.check, 'syntax': spec['syntax'],
                        'sha256': hashlib.sha256(spec['text'].encode()).hexdigest(),
                        'oracle': spec['oracle']})
    write_input(folder / 'oracles.json', json.dumps(oracles, indent=2) + '\n')
    return cases
