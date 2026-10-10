"""Known finite structures with independently checked emitted interpretations."""
import itertools
import json
import random


def model_cases(binary, folder, Case, root, write_input):
    folder.mkdir(parents=True, exist_ok=True)
    cases = []
    for size, style in itertools.product((1, 2, 3), range(5)):
        rng = random.Random(7100 + 10 * size + style)
        functions = [list(range(size)), [(x + 1) % size for x in range(size)],
                     [0] * size, list(reversed(range(size))), [rng.randrange(size) for _ in range(size)]]
        relation = [[(False, x == y, True, x < y, bool(rng.randrange(2)))[style]
                     for y in range(size)] for x in range(size)]
        function = functions[style]
        constants = [f'a{x}' if style % 2 == 0 else f'element_{x}' for x in range(size)]
        fun, rel = ('f', 'r') if style % 2 == 0 else ('successor', 'related')
        domain = ' | '.join('X=' + a for a in constants)
        formulas = [f'fof(domain,axiom,![X]:({domain})).']
        for x in range(size):
            for y in range(x): formulas.append(f'fof(d{x}_{y},axiom,{constants[x]}!={constants[y]}).')
            formulas.append(f'fof(f{x},axiom,{fun}({constants[x]})={constants[function[x]]}).')
            for y in range(size):
                formulas.append(f'fof(r{x}_{y},axiom,{"" if relation[x][y] else "~"}{rel}({constants[x]},{constants[y]})).')
        for cnf, adjustment in itertools.product(('off', 'on'), ('off', 'group', 'expand')):
            name = f'n{size}-structure{style}-cnf{cnf}-{adjustment}'
            path = folder / (name + '.p')
            write_input(path, '\n'.join(formulas) + '\n')
            oracle = {'size': size, 'function': function, 'relation': relation,
                      'names': {'constants': constants, 'function': fun, 'relation': rel}}
            write_input(path.with_suffix('.model.json'), json.dumps(oracle, indent=2) + '\n')
            cases.append(Case('behavior/model/' + name,
                [str(binary), '-t', '5', '-sa', 'fmb', '-newcnf', cnf,
                 '--fmb_adjust_sorts', adjustment, '-p', 'tptp', str(path)],
                str(root), 'finite-model', 'Satisfiable', str(path)))
    return cases
