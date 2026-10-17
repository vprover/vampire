"""Independent, bounded checker for Vampire's single-sort finite-model tables.

This deliberately accepts only the TFF fragment used by model_cases.py.
It does not call Vampire or an SMT solver to validate a model.
"""
import itertools
import json
import re


class InvalidModel(ValueError):
    pass


TOKEN = re.compile(r"\s*(('[^'\\]*(?:\\.[^'\\]*)*')|[A-Za-z_$][A-Za-z0-9_$]*|<=>|=>|!=|[(),.:\[\]!~?&|=*>])")


def tokens(text):
    result, pos = [], 0
    while text[pos:].strip():
        match = TOKEN.match(text, pos)
        if not match:
            raise InvalidModel('unsupported or malformed model syntax near ' + repr(text[pos:pos + 30]))
        word = match.group(1)
        if word.startswith("'"):
            word = word[1:-1].replace("\\'", "'").replace('\\\\', '\\')
        result.append(word)
        pos = match.end()
    return result


class Parser:
    precedence = {'<=>': 1, '=>': 2, '|': 3, '&': 4, '=': 5, '!=': 5}

    def __init__(self, words):
        self.words, self.pos = words, 0

    def peek(self):
        return self.words[self.pos] if self.pos < len(self.words) else None

    def take(self, expected=None):
        value = self.peek()
        if value is None or expected is not None and value != expected:
            raise InvalidModel(f'expected {expected}, got {value}')
        self.pos += 1
        return value

    def expression(self, minimum=0):
        word = self.take()
        if word == '(':
            left = self.expression()
            self.take(')')
        elif word == '~':
            left = ('~', self.expression(6))
        elif word in ('!', '?'):
            self.take('[')
            variables = []
            while True:
                name = self.take()
                if not name[0].isupper(): raise InvalidModel('quantifier variable is not uppercase')
                if self.peek() == ':':
                    self.take(':'); self.take('$i')
                variables.append(name)
                if len(variables) > 2: raise InvalidModel('quantifier block exceeds checker scope')
                if self.peek() != ',': break
                self.take(',')
            self.take(']'); self.take(':')
            left = (word, variables, self.expression())
        else:
            if word[0] not in '_$' and not word[0].isalpha():
                raise InvalidModel('expected a symbol')
            args = []
            if self.peek() == '(':
                self.take('(')
                if self.peek() != ')':
                    while True:
                        args.append(self.expression(6))
                        if self.peek() != ',': break
                        self.take(',')
                self.take(')')
            left = ('call', word, args)
        while self.peek() in self.precedence and self.precedence[self.peek()] >= minimum:
            op = self.take()
            left = (op, left, self.expression(self.precedence[op] + 1))
        return left


def read_units(body):
    parser = Parser(tokens(body))
    declarations, axioms = {}, []
    while parser.peek() is not None:
        parser.take('tff'); parser.take('('); parser.take(); parser.take(',')
        role = parser.take(); parser.take(',')
        if role == 'type':
            name = parser.take(); parser.take(':')
            parts, depth = [], 0
            while parser.peek() != ')' or depth:
                word = parser.take()
                if word == '(': depth += 1
                elif word == ')': depth -= 1
                else: parts.append(word)
            if '>' in parts:
                index = parts.index('>')
                args, result = parts[:index], parts[index + 1:]
                if not args or len(args) % 2 == 0 or args[::2] != ['$i'] * len(args[::2]) or args[1::2] != ['*'] * len(args[1::2]):
                    raise InvalidModel('unsupported argument sorts')
                arity = len(args[::2])
                if arity > 2: raise InvalidModel('symbol arity exceeds checker scope')
            else:
                arity, result = 0, parts
            if result not in (['$i'], ['$o']): raise InvalidModel('unsupported result sort')
            if name in declarations: raise InvalidModel('duplicate symbol declaration')
            declarations[name] = (arity, result[0])
        elif role == 'axiom':
            axioms.append(parser.expression())
        else:
            raise InvalidModel('unexpected model role ' + role)
        parser.take(')'); parser.take('.')
    return declarations, axioms


def check_model(text, oracle):
    starts = list(re.finditer(r'^% SZS output start FiniteModel[^\n]*\n', text, re.M))
    ends = list(re.finditer(r'^% SZS output end FiniteModel[^\n]*$', text, re.M))
    if len(starts) != 1 or len(ends) != 1 or starts[0].end() > ends[0].start():
        raise InvalidModel('missing or ambiguous finite-model boundaries')
    declarations, axioms = read_units(text[starts[0].end():ends[0].start()])
    domain = sorted(name for name, declaration in declarations.items()
                    if name.startswith('fmb_$i_') and declaration == (0, '$i'))
    size = oracle['size']
    if not 1 <= size <= 3 or len(domain) != size:
        raise InvalidModel(f'expected exactly {size} domain elements, found {len(domain)}')
    functions = {(name, ()): index for index, name in enumerate(domain)}
    predicates = {}

    def term(expr, env):
        if expr[0] != 'call': raise InvalidModel('non-term used as an argument')
        _, name, args = expr
        if name in env and not args: return env[name]
        key = (name, tuple(term(arg, env) for arg in args))
        if key not in functions: raise InvalidModel('missing function interpretation: ' + repr(key))
        return functions[key]

    def truth(expr, env):
        op, *args = expr
        if op == 'call':
            name, terms = args
            if name in ('$true', '$false') and not terms: return name == '$true'
            key = (name, tuple(term(arg, env) for arg in terms))
            if key not in predicates: raise InvalidModel('missing predicate interpretation: ' + repr(key))
            return predicates[key]
        if op == '~': return not truth(args[0], env)
        if op in ('=', '!='): return (term(args[0], env) == term(args[1], env)) == (op == '=')
        if op in ('&', '|', '=>', '<=>'):
            left, right = truth(args[0], env), truth(args[1], env)
            return {'&': left and right, '|': left or right,
                    '=>': not left or right, '<=>': left == right}[op]
        if op in ('!', '?'):
            names, body = args
            values = [truth(body, {**env, **dict(zip(names, assignment))})
                      for assignment in itertools.product(range(size), repeat=len(names))]
            return all(values) if op == '!' else any(values)
        raise InvalidModel('unsupported connective ' + op)

    def assign(table, lhs, value, env):
        if lhs[0] != 'call': raise InvalidModel('invalid definition head')
        key = (lhs[1], tuple(term(arg, env) for arg in lhs[2]))
        expected_sort = '$o' if table is predicates else '$i'
        if declarations.get(lhs[1]) != (len(lhs[2]), expected_sort):
            raise InvalidModel('undeclared symbol or wrong arity in definition: ' + lhs[1])
        if key in table and table[key] != value: raise InvalidModel('conflicting definition: ' + repr(key))
        table[key] = value

    def definitions(expr, env):
        op, *args = expr
        if op == '&':
            definitions(args[0], env); definitions(args[1], env)
        elif op == '!':
            for assignment in itertools.product(range(size), repeat=len(args[0])):
                definitions(args[1], {**env, **dict(zip(args[0], assignment))})
        elif op == '=' and args[0][0] == 'call' and args[0][1] not in env:
            assign(functions, args[0], term(args[1], env), env)
        elif op == 'call' and args[0] not in ('$true', '$false'):
            assign(predicates, expr, True, env)
        elif op == '~' and args[0][0] == 'call':
            assign(predicates, args[0], False, env)
        elif op == '<=>' and args[0][0] == 'call':
            assign(predicates, args[0], truth(args[1], env), env)
        # Domain closure and distinctness are assertions, checked below.

    for axiom in axioms: definitions(axiom, {})
    for name, (arity, result) in declarations.items():
        table = predicates if result == '$o' else functions
        for args in itertools.product(range(size), repeat=arity):
            if (name, args) not in table: raise InvalidModel('incomplete interpretation: ' + name + repr(args))
    for axiom in axioms:
        if not truth(axiom, {}): raise InvalidModel('an emitted model axiom is false')

    names = oracle['names']
    constants = [functions.get((name, ())) for name in names['constants']]
    if len(constants) != size or set(constants) != set(range(size)):
        raise InvalidModel('input constants do not enumerate distinct domain elements')
    for x in range(size):
        if functions.get((names['function'], (constants[x],))) != constants[oracle['function'][x]]:
            raise InvalidModel(f'input function equation fails at element {x}')
        for y in range(size):
            key = (names['relation'], (constants[x], constants[y]))
            if predicates.get(key) is not oracle['relation'][x][y]:
                raise InvalidModel(f'input relation literal fails at pair ({x}, {y})')
    return {'domain_size': size, 'function_equations': size, 'relation_literals': size * size,
            'emitted_axioms': len(axioms), 'scope': 'Complete generated single-sort structure; no general TPTP model certification.'}


def validate_model(text, folder, oracle_path):
    try:
        report = check_model(text, json.loads(oracle_path.read_text()))
    except (InvalidModel, KeyError, TypeError, ValueError) as error:
        report = {'error': str(error)}
        outcome, reason = 'fail', 'independent finite-model checker: ' + str(error)
    else:
        outcome, reason = 'pass', ''
    (folder / 'model-validation.json').write_text(json.dumps(report, indent=2))
    return outcome, reason
