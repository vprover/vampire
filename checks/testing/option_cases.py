"""Inventory compiled options and test their CLI parsing separately from behavior."""
import json
from pathlib import Path
import re
import subprocess


def catalogue(binary, log_folder=None, timeout=30):
    command = [str(binary), '--show_options', 'on', '--show_experimental_options',
               'on', '--show_options_line_wrap', 'off']
    try:
        result = subprocess.run(command, capture_output=True, text=True, timeout=timeout)
        raw, errors, code = result.stdout, result.stderr, result.returncode
        expired = False
    except subprocess.TimeoutExpired as error:
        raw = (error.stdout or b'').decode(errors='replace')
        errors = (error.stderr or b'').decode(errors='replace')
        code, expired = None, True
    if log_folder is not None:
        log_folder.mkdir(parents=True, exist_ok=True)
        (log_folder / 'stdout.log').write_text(raw)
        (log_folder / 'stderr.log').write_text(errors)
        (log_folder / 'discovery.json').write_text(json.dumps({
            'command': command, 'exit': code, 'timeout': expired}, indent=2))
    if expired: raise ValueError('option discovery timed out; diagnostics were saved')
    # A sanitizer can report an error at exit after the full catalogue was printed.
    # Keep those options; the same command is also an instrumented test case.
    if not raw.strip(): raise ValueError(f'option discovery produced no catalogue (exit {code})')
    entries = []
    source_root = Path(__file__).resolve().parents[2]
    declarations = (source_root / 'Shell/Options.hpp').read_text()
    constructors = (source_root / 'Shell/Options.cpp').read_text()
    string_members = set(re.findall(r'StringOptionValue\s+(_\w+)\s*;', declarations))
    string_names = {name for member, name in re.findall(r'(_\w+)\("([a-z][a-z0-9_]*)",this\b', constructors)
                    if member in string_members}
    for match in re.finditer(r'^--(\w+)(?: \(-([^ )]+)\))?\n(.*?)(?=^--\w|\Z)', raw, re.M | re.S):
        name, short, body = match.groups()
        default = re.search(r'^\tdefault: (.*)$', body, re.M)
        values = re.search(r'^\tvalues: (.*)$', body, re.M)
        left = re.search(r'^\tdefault left: (.*)$', body, re.M)
        right = re.search(r'^\tdefault right: (.*)$', body, re.M)
        if not default and not (left and right): raise ValueError(f'no default in option documentation: {name}')
        value = default.group(1).strip() if default else left.group(1).strip() + ':' + right.group(1).strip()
        kind = ('switch' if name == 'help' else 'string' if name in string_names else 'ratio' if left and right else 'enum' if values else 'bool' if value in ('on', 'off') else
                'number' if re.fullmatch(r'-?\d+(\.\d+)?', value) else
                'time' if re.fullmatch(r'\d+[dsmhD]', value) else 'string')
        entries.append({'name': name, 'short': short, 'default': value,
                        'values': values.group(1).split(',') if values else [],
                        'kind': kind, 'documentation': body.strip()})
    if not entries or len({e['name'] for e in entries}) != len(entries):
        raise ValueError('empty or duplicate option catalogue')
    return entries, raw


def option_cases(binary, folder, Case, root, write_input, discovered=None):
    folder.mkdir(parents=True, exist_ok=True)
    entries, raw = discovered if discovered is not None else catalogue(binary, folder / "discovery")
    write_input(folder / 'options.txt', raw)
    source = (root / 'Shell/Options.cpp').read_text()
    declared = sorted(set(re.findall(r'\b_\w+\("([a-z][a-z0-9_]*)",this\b', source)))
    cases = []
    for entry in entries:
        name, default, kind = entry['name'], entry['default'], entry['kind']
        values = entry['values'] if kind == 'enum' else ['off', 'on'] if kind == 'bool' else [default]
        values = ['' if value == '<empty>' else value for value in values]
        # Help is evaluated after command-line parsing and before solver/file actions.
        # Testing the help option itself uses show_options as the exit path.
        exit_args = ['--show_options', 'on'] if name == 'help' else ['--help', 'on']
        expected = '--mode' if name == 'help' else 'Usage: vampire'
        for index, value in enumerate(values):
            cases.append(Case(f'options/values/{name}-{index}',
                [str(binary), '--' + name, value, *exit_args], str(root),
                'contains', expected, str(root / 'Shell/Options.cpp')))
        if name == 'decode' and values == ['']:
            cases[-1].check, cases[-1].expected, cases[-1].allow_error_exit = 'reject', 'bad test id', True
        if name == 'print_theory_axioms':
            cases[-1].check, cases[-1].expected = 'unsupported', 'Sorry, not implemented yet!'
        if entry['short']:
            cases.append(Case(f'options/aliases/{name}',
                [str(binary), '-' + entry['short'], values[0], *exit_args], str(root),
                'contains', expected, str(root / 'Shell/Options.cpp')))
        if kind in ('bool', 'enum', 'number', 'time', 'ratio'):
            cases.append(Case(f'options/rejection/{name}',
                [str(binary), '--' + name, '__invalid_test_value__', *exit_args], str(root),
                'reject', 'wrong value for time limit:' if kind == 'time' else f'is an invalid value for {name}', str(root / 'Shell/Options.cpp'), True))
        if kind in ('number', 'time', 'ratio'):
            boundaries = ['-1', '0', '1', '2147483647', '2147483648', '4294967295',
                          '4294967296', '9223372036854775808', '1e309', 'nan']
            if kind == 'time': boundaries += ['1d', '1s', '1m', '1h', '1D', '0.1s']
            if kind == 'ratio': boundaries = ['0:0', '0:1', '1:0', '-1:1', '1:-1', '2147483648:1', '1:4294967296', '1:', ':1', '1:1:1']
            for value in boundaries:
                cases.append(Case(f'options/boundary/{name}-{value}',
                    [str(binary), '--' + name, value, *exit_args], str(root),
                    'option-boundary', name, str(root / 'Shell/Options.cpp'), True))
        entry['planned_parser_cases'] = sum(c.name.split('/')[2] == name or
            c.name.split('/')[2].startswith(name + '-') for c in cases)
        entry['behavior_status'] = 'not established by parser tests; see option-audit.json'
    # Help exits before cross-option validation, so use a real input here.
    if {'newcnf', 'inline_let', 'bad_option'} <= {entry['name'] for entry in entries}:
        path = folder / 'inline-let-constraint.p'
        write_input(path, 'fof(trivial,axiom,$true).\n')
        cases.append(Case('options/rejection/inline_let-without-newcnf',
            [str(binary), '--bad_option', 'hard', '--newcnf', 'off',
             '--inline_let', 'off', str(path)], str(root), 'reject',
            'Broken Constraint: if inline_let(off)', str(path), True))
    write_input(folder / 'catalogue.json', json.dumps({
        'compiled_options': entries, 'source_declarations': declared,
        'not_in_this_binary': sorted(set(declared) - {e['name'] for e in entries}),
        'scope': 'Parser acceptance/rejection only. Does not establish execution of an option feature.'}, indent=2))
    return cases
