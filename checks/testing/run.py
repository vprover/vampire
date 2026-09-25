#!/usr/bin/env python3
"""Run Vampire's tests and retain commands, outputs, and machine-readable results."""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, asdict
from datetime import datetime, timezone
import hashlib
import fcntl
import itertools
import json
import math
import os
from pathlib import Path
import random
import re
import shlex
import signal
import subprocess
import sys
import threading
import time
import xml.etree.ElementTree as ET

from report import TerminalReporter
from diagnostics import ASSERTION, sanitizer_messages, sanitizer_warnings, combine

ROOT = Path(__file__).resolve().parents[2]
SZS = re.compile(r'^% SZS status (\w+)', re.MULTILINE)
CANCELLED = threading.Event()


def artifact_name(name):
    """Keep exact case identities distinct on case-insensitive filesystems too."""
    prefix = re.sub(r'[^A-Za-z0-9_.-]', '_', name)[:96]
    return prefix + '-' + hashlib.sha256(name.encode('utf-8')).hexdigest()[:16]


def atomic_json(path, value):
    """Commit one JSON record without exposing a partial replacement."""
    temporary = path.with_name(path.name + '.tmp')
    with temporary.open('w') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)
    descriptor = os.open(path.parent, os.O_RDONLY)
    try: os.fsync(descriptor)
    finally: os.close(descriptor)


def file_hash(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()



def case_evidence_hashes(folder):
    """Hash the complete case artifact tree, excluding its self-referential row."""
    if not folder.is_dir() or folder.is_symlink():
        raise ValueError(f'case artifact directory is missing or linked: {folder}')
    hashes = {}
    for path in sorted(folder.rglob('*')):
        if path.is_symlink():
            raise ValueError(f'case evidence contains a symbolic link: {path}')
        if path.is_file() and path != folder / 'result.json':
            hashes[path.relative_to(folder).as_posix()] = file_hash(path)
    return hashes


def process_identity(pid=None):
    pid = os.getpid() if pid is None else pid
    try:
        stat = Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()
        if stat[0] == 'Z': return None
        return {'pid': pid, 'start_ticks': stat[19],
                'boot_id': Path('/proc/sys/kernel/random/boot_id').read_text().strip()}
    except (OSError, IndexError):
        return None


def process_alive(identity):
    return bool(identity and process_identity(identity['pid']) == identity)


def source_fingerprint(root=ROOT):
    """Include tracked working-tree bytes, so dirty inputs cannot change on resume."""
    paths = subprocess.check_output(['git', 'ls-files', '--stage', '-z'], cwd=root).split(b'\0')
    digest = hashlib.sha256()
    for record in sorted(path for path in paths if path):
        stage, raw = record.split(b'\t', 1)
        path = root / os.fsdecode(raw)
        digest.update(stage + b'\t' + raw + b'\0')
        if stage.startswith(b'160000 ') and (path / '.git').exists():
            head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=path).strip()
            digest.update(head + b'\0' + source_fingerprint(path).encode())
        else:
            digest.update(file_hash(path).encode() if path.is_file() else b'<missing>')
    return digest.hexdigest()


def binary_hashes(binaries):
    """Hash executable bytes and the shared libraries resolved in this environment."""
    paths = set(Path(path).resolve() for path in binaries if Path(path).is_file())
    for binary in list(paths):
        with binary.open('rb') as stream:
            if stream.read(4) != b'\x7fELF': continue
        linked = subprocess.run(['ldd', str(binary)], capture_output=True, text=True, timeout=10)
        if 'not found' in linked.stdout:
            raise ValueError(f'unresolved shared library for {binary}: {linked.stdout.strip()}')
        if linked.returncode and not any(text in linked.stderr + linked.stdout for text in ('not a dynamic executable', 'statically linked')):
            raise ValueError(f'cannot inspect shared libraries for {binary}: {linked.stderr.strip()}')
        for line in linked.stdout.splitlines():
            match = re.search(r'(?:=>\s*)?(/\S+)\s+\(', line)
            if match: paths.add(Path(match.group(1)).resolve())
    return {str(path): file_hash(path) for path in sorted(paths)}


def harness_hashes(root=ROOT):
    folder = root / 'checks/testing'
    paths = [*folder.glob('*.py'), *folder.glob('*.sh'), *(folder / 'fixtures').rglob('*')]
    return {str(path.relative_to(folder)): file_hash(path) for path in paths if path.is_file()}


def input_hashes(cases, output):
    paths = set()
    for case in cases:
        for value in [case.source, *case.command[1:]]:
            if not value: continue
            path = Path(value)
            path = path if path.is_absolute() else Path(case.cwd) / path
            try:
                if path.is_file(): paths.add(path.resolve())
            except OSError: pass  # Arguments such as schedules need not be valid filenames.
        if case.source:
            path = Path(case.source)
            path = path if path.is_absolute() else Path(case.cwd) / path
            for suffix in ('.model.json', '.mode.json'):
                if path.with_suffix(suffix).is_file(): paths.add(path.with_suffix(suffix).resolve())
    for folder in output.iterdir():
        if folder.is_dir() and (folder.name == 'inputs' or folder.name.endswith('-inputs')):
            paths.update(path.resolve() for path in folder.rglob('*') if path.is_file())
    return {str(path): file_hash(path) for path in sorted(paths)}


@dataclass
class Case:
    name: str
    command: list
    cwd: str
    check: str = 'exit'
    expected: str = ''
    source: str = ''
    allow_error_exit: bool = False
    stdin_text: str = None


def checked_output(command, cwd=ROOT):
    return subprocess.check_output(command, cwd=cwd, text=True).strip()


def unit_cases(build):
    data = json.loads(checked_output(['ctest', '--test-dir', str(build), '--show-only=json-v1']))
    return [Case('unit/' + t['name'], t['command'], str(ROOT)) for t in data['tests']]


def corpus_cases(binary):
    """Import literal assertions; retain unsupported shell constructs as explicit gaps."""
    cases, skipped = [], []
    script = (ROOT / 'checks/sanity').read_text().replace('\\\n', ' ')
    kinds = {'check_szs_status': 'szs', 'check_rejected': 'contains',
             'check_output_contains': 'contains', 'check_output_contains_once': 'once',
             'check_exact_output': 'exact'}
    for number, line in enumerate(script.splitlines(), 1):
        line = line.strip()
        if not any(line.startswith(k + ' ') for k in kinds):
            continue
        tokens = shlex.split(line, comments=True)
        if len(tokens) < 3 or any('$' in t and not t.startswith('$distinct') for t in tokens[2:]):
            skipped.append({'line': number, 'command': line, 'reason': 'requires shell expansion'})
            continue
        kind, expected, *args = tokens
        sources = [t for t in args if (ROOT / 'checks' / t).is_file()]
        # Tight sanity timeouts test release performance. This suite tests correctness.
        args += ['-t', '10']
        if kinds[kind] == 'exact':
            expected = (ROOT / 'checks' / expected).read_text()
        cases.append(Case(f'corpus/{number:03d}-{Path(sources[-1]).stem if sources else kind}',
                          [str(binary), *args], str(ROOT / 'checks'), kinds[kind], expected,
                          sources[-1] if sources else '', kind == 'check_rejected'))
    return cases, skipped


def boolean_formula(rng, depth):
    if not depth or rng.randrange(5) == 0:
        return rng.choice(['p', 'q', 'r', True, False])
    op = rng.choice(['not', 'and', 'or', 'xor', '=>', '=', 'ite', 'let'])
    arity = 1 if op == 'not' else 3 if op == 'ite' else 2
    return (op, *(boolean_formula(rng, depth - 1) for _ in range(arity)))


def evaluate(expr, env):
    if isinstance(expr, bool):
        return expr
    if isinstance(expr, str):
        return env[expr]
    op, *children = expr
    values = [evaluate(c, env) for c in children]
    if op == 'not': return not values[0]
    if op == 'and': return all(values)
    if op == 'or': return any(values)
    if op == 'xor': return values[0] != values[1]
    if op == '=>': return not values[0] or values[1]
    if op == '=': return values[0] == values[1]
    if op == 'ite': return values[1] if values[0] else values[2]
    # Rendered let uses its bound expression twice, with opposite polarity.
    if op == 'let': return (not values[0] or values[1]) and (values[0] or not values[1])
    raise ValueError(op)


def smt(expr):
    if isinstance(expr, bool): return str(expr).lower()
    if isinstance(expr, str): return expr
    op, *children = expr
    args = [smt(c) for c in children]
    if op == 'let':
        return f'(let ((b {args[0]})) (and (=> b {args[1]}) (or b (not {args[1]}))))'
    return f'({op} {" ".join(args)})'


def write_input(path, text):
    if path.exists():
        if path.read_bytes() != text.encode():
            raise ValueError(f'input changed since the earlier run: {path}')
    else:
        path.write_text(text)


def generated_cases(binary, folder, seed):
    folder.mkdir(parents=True, exist_ok=True)
    cases = []
    # Every subset of the nine non-tautological clauses over two variables.
    clauses = list(itertools.product((0, 1, -1), repeat=2))
    for mask in range(1 << len(clauses)):
        selected = [c for n, c in enumerate(clauses) if mask & (1 << n)]
        sat = any(all(any(lit and (lit > 0) == value for lit, value in zip(c, values))
                      for c in selected) for values in itertools.product((False, True), repeat=2))
        lines = []
        for n, clause in enumerate(selected):
            literals = [('' if lit > 0 else '~') + var for var, lit in zip(('p', 'q'), clause) if lit]
            lines.append(f'cnf(c{n},axiom,({" | ".join(literals) if literals else "$false"})).')
        path = folder / f'cnf-{mask:03d}.p'
        write_input(path, '\n'.join(lines or ['cnf(empty,axiom,$true).']) + '\n')
        for strategy in ('lrs', 'discount', 'otter'):
            cases.append(Case(f'generated/cnf-{mask:03d}-{strategy}',
                [str(binary), '-sa', strategy, '-t', '5', '-p', 'off', str(path)], str(ROOT),
                'szs', 'Satisfiable' if sat else 'Unsatisfiable', str(path)))
    rng = random.Random(seed)
    for index in range(96):
        expr = boolean_formula(rng, 4)
        sat = any(evaluate(expr, dict(zip(('p', 'q', 'r'), values)))
                  for values in itertools.product((False, True), repeat=3))
        path = folder / f'bool-{index:03d}.smt2'
        write_input(path, '(set-logic QF_UF)\n' + ''.join(f'(declare-const {v} Bool)\n' for v in ('p', 'q', 'r'))
                        + f'(assert {smt(expr)})\n(check-sat)\n')
        # inline_let is only useful with the new clausifier. Even explicitly
        # selecting its default violates the option constraint with newcnf off.
        for newcnf, inline in (('off', None), ('on', 'off'), ('on', 'on')):
            inline_args = ['-ile', inline] if inline is not None else []
            cases.append(Case(f'generated/bool-{index:03d}-cnf-{newcnf}-inline-{inline or "default"}',
                [str(binary), '-newcnf', newcnf, *inline_args, '-t', '5', '-p', 'off', str(path)],
                str(ROOT), 'szs', 'Satisfiable' if sat else 'Unsatisfiable', str(path)))
    for number in (0, 1, -1, 2**31-1, 2**31, -(2**31), 2**63-1, 2**63, -(2**63), 10**100):
        for satisfiable in (True, False):
            path = folder / f'int-{number}-{satisfiable}.smt2'
            numeral = str(number) if number >= 0 else f'(- {-number})'
            relation = '=' if satisfiable else 'distinct'
            write_input(path, f'(set-logic QF_LIA)\n(assert ({relation} (+ {numeral} 1) {number + 1 if number + 1 >= 0 else "(- " + str(-(number + 1)) + ")"}))\n(check-sat)\n')
            cases.append(Case(f'generated/int-{number}-{satisfiable}',
                [str(binary), '-t', '5', '-p', 'off', str(path)], str(ROOT), 'szs',
                'Satisfiable' if satisfiable else 'Unsatisfiable', str(path)))
    return cases


def feature_cases(binary, folder):
    folder.mkdir(parents=True, exist_ok=True)
    cases = []
    # Explicit domain closure makes these quantifier/cardinality answers exact.
    for size in (1, 2, 3):
        constants = [f'a{i}' for i in range(size)]
        domain = ' | '.join(f'X = {c}' for c in constants)
        distinct = ' & '.join(f'{a} != {b}' for a, b in itertools.combinations(constants, 2)) or '$true'
        for different in (False, True):
            relation = '!=' if different else '='
            problem = (f'fof(domain,axiom, ![X]:({domain})).\n'
                       f'fof(distinct,axiom, ({distinct})).\n'
                       f'fof(witness,axiom, ![X]: ?[Y]: (X {relation} Y)).\n')
            path = folder / f'finite-{size}-{different}.p'
            write_input(path, problem)
            expected = 'Unsatisfiable' if size == 1 and different else 'Satisfiable'
            for newcnf in ('off', 'on'):
                cases.append(Case(f'features/finite-{size}-{different}-cnf-{newcnf}',
                    [str(binary), '-sa', 'fmb', '-newcnf', newcnf, '-t', '10', str(path)],
                    str(ROOT), 'szs', expected, str(path)))
    problem = ROOT / 'checks/Problems/PUZ/PUZ001+1.p'
    for cores in (1, 2):
        cases.append(Case(f'features/portfolio-{cores}',
            [str(binary), '--mode', 'casc', '--cores', str(cores), '-t', '10', str(problem)],
            str(ROOT / 'checks'), 'szs', 'Theorem', str(problem)))
    for proof in ('tptp', 'on'):
        cases.append(Case(f'features/proof-{proof}',
            [str(binary), '--proof', proof, '-t', '10', str(problem)],
            str(ROOT / 'checks'), 'szs', 'Theorem', str(problem)))
    return cases


def run_case(case, output, timeout, memcheck, z3="z3", asan=False, sanitizer_error_grace=None):
    if CANCELLED.is_set(): raise KeyboardInterrupt('run interrupted')
    if not math.isfinite(timeout): raise ValueError('timeout must be finite')
    if sanitizer_error_grace is not None and (not math.isfinite(sanitizer_error_grace) or sanitizer_error_grace <= 0):
        raise ValueError('sanitizer error grace must be finite and positive')
    name = artifact_name(case.name)
    folder = output / name
    if folder.exists():
        folder.rename(folder.with_name(folder.name + f'.interrupted-{time.time_ns()}'))
    folder.mkdir()
    command = list(case.command)
    if memcheck:
        command = ['valgrind', '--tool=memcheck', '--leak-check=full', '--show-leak-kinds=all',
                   '--errors-for-leak-kinds=definite,indirect,possible', '--track-origins=yes',
                   '--error-exitcode=97', '--trace-children=yes', '--xml=yes',
                   f'--xml-file={folder}/valgrind.%p.xml', *command]
    (folder / 'command.json').write_text(json.dumps({'argv': command, 'cwd': case.cwd}, indent=2))
    start = time.monotonic()
    timed_out = False
    error_deadline = False
    first_diagnostic_seconds = None
    stdin_path = folder / 'stdin.txt'
    if case.stdin_text is not None: stdin_path.write_text(case.stdin_text)
    with (stdin_path if case.stdin_text is not None else Path(os.devnull)).open('r') as stdin, (folder / 'stdout.log').open('w') as stdout, (folder / 'stderr.log').open('w') as stderr:
        process = subprocess.Popen(command, cwd=case.cwd, stdin=stdin, stdout=stdout, stderr=stderr, start_new_session=True)
        atomic_json(folder / 'process.json', process_identity(process.pid))
        try:
            with (folder / 'stdout.log').open(errors='replace') as observed_out, (folder / 'stderr.log').open(errors='replace') as observed_err:
                tails = ['', '']
                while True:
                    elapsed = time.monotonic() - start
                    if CANCELLED.is_set(): raise KeyboardInterrupt('run interrupted')
                    if asan and sanitizer_error_grace is not None and first_diagnostic_seconds is None:
                        for index, stream in enumerate((observed_out, observed_err)):
                            text = tails[index] + stream.read()
                            if sanitizer_messages(text, ''):
                                first_diagnostic_seconds = elapsed
                            tails[index] = text[-4096:]
                    error_deadline = (first_diagnostic_seconds is not None and
                                      elapsed >= first_diagnostic_seconds + sanitizer_error_grace)
                    timed_out = elapsed >= timeout
                    if error_deadline or timed_out:
                        try: os.killpg(process.pid, signal.SIGKILL)
                        except ProcessLookupError: pass
                        code = process.wait()
                        break
                    try:
                        code = process.wait(timeout=min(0.1, timeout - elapsed))
                        break
                    except subprocess.TimeoutExpired:
                        pass
        except BaseException:
            if process.poll() is None:
                try: os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError: pass
            process.wait()
            raise
    stdout = (folder / 'stdout.log').read_text(errors='replace')
    stderr = (folder / 'stderr.log').read_text(errors='replace')
    statuses = SZS.findall(stdout)
    resource_limited = bool(re.search(r'Termination reason: (Time limit|Memory limit|Instruction limit|Activation limit)', stdout))
    outcome, reason = 'pass', ''
    if error_deadline:
        outcome, reason = 'inconclusive', 'terminated after sanitizer error grace expired'
    elif timed_out:
        outcome, reason = 'inconclusive', 'wall timeout'
    elif code < 0:
        outcome, reason = 'fail', f'signal {-code}'
    elif ASSERTION.search(stdout + stderr):
        outcome, reason = 'fail', 'assertion or sanitizer error'
    elif case.check == 'exit' and code != 0:
        outcome, reason = ('inconclusive' if resource_limited else 'fail'), f'exit {code}'
    elif case.check in ('szs', 'smt-proof', 'finite-model') and case.expected not in statuses:
        outcome = 'inconclusive' if resource_limited or any(s in ('Timeout', 'ResourceOut', 'GaveUp', 'MemoryOut') for s in statuses) else 'fail'
        reason = f'expected {case.expected}; got {statuses} (exit {code})'
    elif case.check == 'unsupported':
        outcome, reason = ('inconclusive', case.expected) if case.expected in stdout + stderr else ('fail', 'unsupported-feature diagnostic changed')
    elif case.check == 'reject-regex' and (code not in (1, 4) or re.search(case.expected, stdout + stderr) is None):
        outcome, reason = 'fail', 'missing expected unavailable-option rejection'
    elif case.check == 'reject' and (code not in (1, 4) or case.expected not in stdout + stderr):
        outcome, reason = 'fail', f'expected a user-error exit and diagnostic: {case.expected}; exit {code}'
    elif case.check == 'option-boundary' and not (
            (code == 0 and 'Usage: vampire' in stdout) or
            (code in (1, 4) and f'is an invalid value for {case.expected}' in stdout + stderr)):
        outcome, reason = 'fail', f'option boundary neither accepted nor explicitly rejected (exit {code})'
    elif case.check in ('szs', 'smt-proof', 'finite-model') and case.expected in ('Satisfiable', 'Unsatisfiable', 'Theorem', 'CounterSatisfiable') and any(
            status in ({'Satisfiable', 'CounterSatisfiable'} if case.expected in ('Unsatisfiable', 'Theorem')
                       else {'Unsatisfiable', 'Theorem', 'ContradictoryAxioms'}) for status in statuses):
        outcome, reason = 'fail', f'conflicting SZS answers: {statuses}'
    elif case.check == 'contains' and case.expected not in stdout:
        outcome, reason = 'fail', f'missing expected diagnostic: {case.expected}'
    elif case.check == 'once' and stdout.count(case.expected) != 1:
        outcome, reason = 'fail', 'expected substring exactly once'
    elif case.check == 'exact' and stdout != case.expected:
        outcome, reason = 'fail', 'output differs'
    # Rejection tests can return nonzero; successful proof/output tests cannot.
    elif code != 0 and not case.allow_error_exit and not (case.check in ('szs', 'smt-proof', 'finite-model') and case.expected in ('GaveUp', 'Timeout', 'ResourceOut', 'MemoryOut') and code == 1):
        outcome, reason = ('inconclusive' if resource_limited else 'fail'), f'exit {code}'
    sanitizers = sanitizer_messages(stdout, stderr)
    warnings = sanitizer_warnings(stdout, stderr)
    validator_result = None
    lsan_failed = any('LeakSanitizer has encountered a fatal error.' in warning for warning in warnings)
    if ((code in (97, 98) and (memcheck or sanitizers or warnings)) or lsan_failed) and not ASSERTION.search(stdout + stderr):
        wrong_status = case.check in ('szs', 'smt-proof', 'finite-model') and any(
            status in ({'Satisfiable', 'CounterSatisfiable'} if case.expected in ('Unsatisfiable', 'Theorem', 'ContradictoryAxioms')
                       else {'Unsatisfiable', 'Theorem', 'ContradictoryAxioms'}) for status in statuses)
        if wrong_status:
            outcome, reason = 'fail', f'wrong or conflicting SZS answers: {statuses}'
        elif case.check in ('szs', 'smt-proof', 'finite-model') and case.expected in statuses:
            outcome, reason = 'pass', ''
        elif reason == f'exit {code}' or outcome == 'fail':
            outcome, reason = 'inconclusive', 'instrumentation interrupted the check or replaced the program exit code'
    if outcome == 'pass' and case.check in ('smt-proof', 'roundtrip'):
        from validation import validate_smt_script, validate_roundtrip
        if case.check == 'smt-proof':
            outcome, reason = validate_smt_script(stdout, folder, z3, min(timeout, 30))
        else:
            def reparse(command):
                nonlocal validator_result
                child = Case('validator', command, case.cwd, 'szs', case.expected, str(folder / 'transformed.p'))
                validator_result = run_case(child, folder, timeout, memcheck, z3, asan, sanitizer_error_grace)
                return validator_result
            outcome, reason = validate_roundtrip(stdout, folder, case.command[0], case.expected,
                                                 timeout, reparse, asan)
    if outcome == 'pass' and case.check == 'finite-model':
        from finite_model_validation import validate_model
        outcome, reason = validate_model(stdout, folder, Path(case.source).with_suffix('.model.json'))

    if outcome == 'pass' and case.check == 'mode-contract':
        from mode_cases import validate_mode_output
        outcome, reason = validate_mode_output(stdout, folder, Path(case.source))

    semantic_outcome, semantic_reason = outcome, reason
    errors = []
    if memcheck:
        xmls = list(folder.glob('valgrind.*.xml'))
        for path in xmls:
            try:
                tree = ET.parse(path)
                for error in tree.findall('error'):
                    kind = error.findtext('kind')
                    if kind != 'Leak_StillReachable':
                        errors.append({'kind': kind, 'message': error.findtext('what') or error.findtext('xwhat/text'), 'file': str(path)})
            except ET.ParseError:
                errors.append({'kind': 'invalid-xml', 'file': str(path)})
        if not xmls:
            errors.append({'kind': 'missing-xml'})
    if validator_result:
        sanitizers += validator_result.get('sanitizer_messages', [])
        warnings += validator_result.get('sanitizer_warnings', [])
        errors += validator_result.get('valgrind_errors', [])
    outcome, reason, memory_outcome = combine(semantic_outcome, semantic_reason, sanitizers, errors,
                                             timed_out or bool(validator_result and validator_result.get('wall_timeout')), warnings)
    if error_deadline: reason += '; terminated after sanitizer error grace expired'
    if not memcheck and not asan and not sanitizers and not warnings: memory_outcome = 'not-instrumented'
    result = {**asdict(case), 'outcome': outcome, 'reason': reason, 'exit': code,
              'seconds': round(time.monotonic() - start, 3), 'statuses': statuses,
              'valgrind_errors': errors, 'artifacts': str(folder),
              'semantic_outcome': semantic_outcome, 'semantic_reason': semantic_reason,
              'memory_outcome': memory_outcome, 'sanitizer_messages': sanitizers,
              'sanitizer_warnings': warnings, 'wall_timeout': timed_out,
              'sanitizer_error_deadline': error_deadline,
              'timeout_policy': {'wall_seconds': timeout,
                                 'sanitizer_error_grace_seconds': sanitizer_error_grace if asan else None,
                                 'first_diagnostic_seconds': first_diagnostic_seconds},
              'validator_result': validator_result,
              'option_value_accepted': ('Usage: vampire' in stdout) if case.check == 'option-boundary' else None}
    if case.name.startswith('unit/'):
        from unit_output import parse_unit_output
        result['unit_test_summary'] = parse_unit_output(stdout, stderr, code, timed_out or error_deadline)
    result['evidence_sha256'] = case_evidence_hashes(folder)
    atomic_json(folder / 'result.json', result)
    return result


def inventory(build, output):
    corpus, skipped = corpus_cases(build / 'vampire')
    inputs = sorted(p for p in (ROOT / 'checks').rglob('*') if p.suffix in ('.p', '.smt2', '.ax', '.out'))
    used = {str(ROOT / 'checks' / c.source) for c in corpus if c.source}
    data = {'commit': checked_output(['git', 'rev-parse', 'HEAD']),
            'units': [c.name for c in unit_cases(build)],
            'literal_sanity_assertions': len(corpus), 'dynamic_sanity_assertions': skipped,
            'inputs': [{'path': str(p.relative_to(ROOT)), 'bytes': p.stat().st_size,
                        'sha256': hashlib.sha256(p.read_bytes()).hexdigest(),
                        'direct_assertion': str(p) in used} for p in inputs]}
    output.write_text(json.dumps(data, indent=2))
    print(f'{len(data["units"])} unit suites, {len(corpus)} literal sanity assertions, {len(inputs)} corpus files')


def recover_results(output, cases):
    selected = {case.name: asdict(case) for case in cases}
    if len(selected) != len(cases): raise ValueError('duplicate case names')
    names = {artifact_name(name): name for name in selected}
    if len({name.casefold() for name in names}) != len(selected):
        raise ValueError('case artifact names collide')
    completed = {}
    journal = output / 'results.jsonl'
    raw = journal.read_bytes() if journal.exists() else b''
    rows = []
    lines = raw.splitlines(keepends=True)
    for index, line in enumerate(lines):
        try: rows.append(json.loads(line))
        except (ValueError, UnicodeDecodeError):
            if index != len(lines) - 1 or line.endswith(b'\n'):
                raise ValueError('invalid completed journal record')
    disk = []
    for path in output.glob('*/result.json'):
        if '.interrupted-' in path.parent.name: continue
        if path.parent.name not in names: raise ValueError(f'unknown case result: {path}')
        try: disk.append(json.loads(path.read_text()))
        except (ValueError, OSError): continue  # Preserve incomplete bytes when this case is rerun.
    for source, records in [('journal', rows), ('result.json', disk)]:
        seen = set()
        for row in records:
            name = row.get('name')
            if name not in selected: raise ValueError(f'unknown completed case: {name}')
            if name in seen: raise ValueError(f'duplicate case in {source}: {name}')
            seen.add(name)
            if any(row.get(key) != value for key, value in selected[name].items()):
                raise ValueError(f'case definition changed for {name}')
            if name in completed and completed[name] != row:
                raise ValueError(f'journal/result.json disagreement for {name}')
            if row.get('outcome') not in ('pass', 'fail', 'inconclusive'):
                raise ValueError(f'invalid completed outcome for {name}')
            completed[name] = row
    for name, row in completed.items():
        folder = output / artifact_name(name)
        expected = row.get('evidence_sha256')
        if not isinstance(expected, dict):
            raise ValueError(f'completed case lacks raw evidence hashes: {name}; use a new output')
        if row.get('artifacts') != str(folder):
            raise ValueError(f'completed case artifact path changed: {name}')
        if case_evidence_hashes(folder) != expected:
            raise ValueError(f'completed case raw evidence changed: {name}')
    return list(completed.values()), raw


def validate_resume(args):
    previous = json.loads((args.output / 'run.json').read_text())
    current = {k: str(v) if isinstance(v, Path) else v for k, v in vars(args).items()}
    for key, value in previous['arguments'].items():
        if key not in ('resume', 'verbose') and current.get(key) != value:
            raise ValueError(f'cannot resume with a different {key}')
    if previous['commit'] != checked_output(['git', 'rev-parse', 'HEAD']):
        raise ValueError('cannot resume after changing the source commit')
    if previous.get('source_sha256') != source_fingerprint():
        raise ValueError('cannot resume after changing source or tracked inputs')
    if previous.get('harness_sha256') != harness_hashes():
        raise ValueError('cannot resume after changing the harness')
    environment = {key: os.environ.get(key) for key in ('ASAN_OPTIONS', 'UBSAN_OPTIONS', 'LSAN_OPTIONS', 'LD_LIBRARY_PATH', 'LD_PRELOAD', 'GCOV_PREFIX', 'GCOV_PREFIX_STRIP', 'GCOV_ERROR_FILE', 'GCOV_EXIT_AT_ERROR')}
    if previous['environment'] != environment:
        raise ValueError('cannot resume after changing the instrumentation environment')
    for label in ('binary_sha256', 'input_sha256'):
        if label not in previous: raise ValueError(f'run lacks {label}; start a new output directory')
        for name, digest in previous[label].items():
            path = Path(name)
            if not path.is_file() or file_hash(path) != digest:
                raise ValueError(f'cannot resume after changing {label}: {name}')
    if previous['binary_sha256'] != binary_hashes([args.build / 'vampire', args.build / 'vtest']):
        raise ValueError('cannot resume after changing binary or shared-library resolution')
    raw_cases = json.loads((args.output / 'cases.json').read_text())
    if file_hash(args.output / 'cases.json') != previous['cases_sha256']:
        raise ValueError('saved case inventory changed')
    cases = [Case(**case) for case in raw_cases]
    if len(cases) != previous['selected']: raise ValueError('saved case count changed')
    for path in args.output.rglob('process.json'):
        if process_alive(json.loads(path.read_text())):
            raise ValueError(f'a case worker is still alive: {path}')
    completed, raw = recover_results(args.output, cases)
    return previous, cases, completed, raw


def execute_cases(args, metadata, cases, results):
    all_cases = [asdict(case) for case in cases]
    done = {row['name'] for row in results}
    pending = [case for case in cases if case.name not in done]
    reporter = TerminalReporter(all_cases, results, args.output, metadata)
    state_path = args.output / 'run-state.json'
    state = {'status': 'running', 'active_process': process_identity(), 'completed': len(results),
             'selected': len(cases), 'started': datetime.now(timezone.utc).isoformat()}
    atomic_json(state_path, state)
    CANCELLED.clear()
    def interrupt(signum, frame):
        CANCELLED.set()
        raise KeyboardInterrupt(f'interrupted by signal {signum}')
    handlers = {sig: signal.signal(sig, interrupt) for sig in (signal.SIGINT, signal.SIGTERM)}
    pool = ThreadPoolExecutor(max_workers=args.jobs)
    try:
        with (args.output / 'results.jsonl').open('a') as journal:
            futures = {pool.submit(run_case, case, args.output, args.timeout, args.memcheck, args.z3,
                                   args.asan, args.sanitizer_error_grace): case for case in pending}
            for future in as_completed(futures):
                try:
                    result = future.result()
                except Exception as error:
                    case = futures[future]
                    folder = args.output / artifact_name(case.name)
                    result = {**asdict(case), 'outcome': 'fail', 'reason': f'harness error: {error}', 'artifacts': str(folder)}
                    folder.mkdir(exist_ok=True)
                    result['evidence_sha256'] = case_evidence_hashes(folder)
                    atomic_json(folder / 'result.json', result)
                results.append(result)
                journal.write(json.dumps(result) + '\n')
                journal.flush()
                os.fsync(journal.fileno())
                state['completed'] = len(results)
                atomic_json(state_path, state)
                reporter.record(result)
    except BaseException as error:
        CANCELLED.set()
        state.update(status='interrupted', interruption=repr(error), active_process=None)
        atomic_json(state_path, state)
        raise
    finally:
        pool.shutdown(wait=True, cancel_futures=True)
        for sig, handler in handlers.items(): signal.signal(sig, handler)
    if len(results) != len(cases) or {row['name'] for row in results} != {case.name for case in cases}:
        raise ValueError('combined result inventory does not match the selected cases')
    totals = dict(Counter(row['outcome'] for row in results))
    summary = {**metadata, 'totals': totals, 'results': sorted(results, key=lambda row: row['name']),
               'exactly_once_verified': True}
    atomic_json(args.output / 'summary.json', summary)
    reporter.finish()
    state.update(status='completed', active_process=None, finished=datetime.now(timezone.utc).isoformat())
    atomic_json(state_path, state)
    return int(bool(metadata['discovery_errors']) or any(row['outcome'] != 'pass' for row in results))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('inventory', 'run'))
    parser.add_argument('--build', type=Path, default=ROOT / 'build/testing/coverage')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--suite', choices=('units', 'corpus', 'generated', 'features', 'edges', 'options', 'behavior', 'parsers', 'modes', 'portfolios', 'datatypes', 'arithmetic', 'sanity', 'all'), default='all')
    parser.add_argument('--jobs', type=int, default=4)
    parser.add_argument('--timeout', type=float, default=180)
    parser.add_argument('--solver-timeout', type=int, help='override solver seconds (0 disables its timer); Memcheck defaults to 0')
    parser.add_argument('--seed', type=int, default=764971)
    parser.add_argument('--filter', default='')
    parser.add_argument('--limit', type=int)
    parser.add_argument('--memcheck', action='store_true')
    parser.add_argument('--asan', action='store_true', help='ASan environment and unlimited default solver memory; explicit memory tests keep their limits')
    parser.add_argument('--sanitizer-error-grace', type=float, default=None,
                        help='ASan only: terminate a process this many seconds after its first actual sanitizer diagnostic')
    settings_file = ROOT / 'build/testing/local-tools.json'
    settings = json.loads(settings_file.read_text()) if settings_file.exists() else {}
    parser.add_argument('--z3', default=settings.get('z3', 'z3'))
    parser.add_argument('--verbose', action='store_true', help='print every passing test as well as failures')
    parser.add_argument('--resume', action='store_true', help='resume unfinished cases in a matching run directory')
    args = parser.parse_args()
    if not math.isfinite(args.timeout): parser.error('timeout must be finite')
    if args.asan and args.memcheck: parser.error('run ASan and Valgrind separately')
    if args.sanitizer_error_grace is not None and (not args.asan or not math.isfinite(args.sanitizer_error_grace) or args.sanitizer_error_grace <= 0):
        parser.error('--sanitizer-error-grace requires --asan and a finite positive number')
    if args.asan:
        os.environ.setdefault('ASAN_OPTIONS', 'detect_leaks=1:halt_on_error=1:abort_on_error=0:exitcode=98')
    args.build = args.build.resolve()
    args.output = args.output.resolve()
    if args.action == 'inventory':
        args.output.parent.mkdir(parents=True, exist_ok=True)
        inventory(args.build, args.output)
        return 0
    if args.output.exists() and not args.resume:
        parser.error('output already exists; choose a new directory or use --resume')
    if args.resume and not (args.output / 'run.json').exists():
        parser.error('--resume requires a run.json in the output directory')
    if args.jobs < 1 or args.timeout <= 0 or (args.limit is not None and args.limit < 1):
        parser.error('jobs, timeout, and limit must be positive')
    args.output.mkdir(parents=True, exist_ok=True)
    lock = (args.output / '.run.lock').open('a')
    try: fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError: parser.error('a runner already owns this output directory')
    binary = args.build / 'vampire'
    if args.resume:
        try: previous, cases, results, raw = validate_resume(args)
        except (ValueError, OSError, KeyError) as error: parser.error(str(error))
        # Keep the previous journal bytes, including any interrupted final record.
        stamp = str(time.time_ns())
        (args.output / f'results-before-resume-{stamp}.jsonl').write_bytes(raw)
        temporary = args.output / 'results.jsonl.tmp'
        with temporary.open('w') as stream:
            for row in results: stream.write(json.dumps(row) + '\n')
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, args.output / 'results.jsonl')
        metadata = {**previous, 'previously_completed': len(results),
                    'resumed': datetime.now(timezone.utc).isoformat()}
        atomic_json(args.output / f'resume-{stamp}.json', metadata)
        print(f'Resuming {len(cases) - len(results)} cases; preserving {len(results)} completed results', flush=True)
        return execute_cases(args, metadata, cases, results)
    cases, skipped = [], []
    discovered, discovery_errors = None, []
    if args.suite in ('all', 'corpus', 'options', 'behavior', 'modes', 'portfolios', 'arithmetic'):
        from option_cases import catalogue
        try:
            discovered = catalogue(binary, args.output / 'discovery')
        except (ValueError, OSError) as error:
            discovery_errors.append(str(error))
            print(f'[FAIL] Option discovery: {error}; continuing independent suites', flush=True)
        cases.append(Case('discovery/options', [str(binary), '--show_options', 'on',
            '--show_experimental_options', 'on', '--show_options_line_wrap', 'off'], str(ROOT), 'contains', '--mode'))
    if args.suite in ('all', 'units'): cases += unit_cases(args.build)
    if args.suite in ('all', 'corpus'):
        corpus, skipped = corpus_cases(binary)
        cases += corpus
    if args.suite in ('all', 'generated'): cases += generated_cases(binary, args.output / 'inputs', args.seed)
    if args.suite in ('all', 'features'): cases += feature_cases(binary, args.output / 'feature-inputs')
    if args.suite in ('all', 'edges'):
        from edge_cases import edge_cases
        cases += edge_cases(binary, args.output / 'edge-inputs', args.seed, Case, ROOT, corpus_cases, write_input)
    if args.suite in ('all', 'options') and discovered is not None:
        from option_cases import option_cases
        cases += option_cases(binary, args.output / 'option-inputs', Case, ROOT, write_input, discovered)
    if args.suite in ('all', 'behavior'):
        from behavior_cases import behavior_cases
        cases += behavior_cases(binary, args.output / 'behavior-inputs', Case, ROOT, write_input, discovered[0] if discovered else [])
    if args.suite in ('all', 'parsers'):
        from parser_cases import parser_cases
        cases += parser_cases(binary, args.output / 'parser-inputs', Case, ROOT, write_input)
    if args.suite in ('all', 'modes'):
        from mode_cases import mode_cases
        cases += mode_cases(binary, args.output / 'mode-inputs', Case, ROOT, write_input, discovered[0] if discovered else [])
    if args.suite in ('all', 'arithmetic'):
        from arithmetic_cases import arithmetic_cases
        cases += arithmetic_cases(binary, args.output / 'arithmetic-inputs', Case, ROOT, write_input, options=discovered[0] if discovered else [])
    if args.suite in ('all', 'portfolios'):
        from portfolio_cases import portfolio_cases
        cases += portfolio_cases(binary, args.output / 'portfolio-inputs', Case, ROOT, write_input, discovered[0] if discovered else [])
    if args.suite in ('all', 'datatypes'):
        from datatype_cases import datatype_cases
        cases += datatype_cases(binary, args.output / 'datatype-inputs', Case, ROOT, write_input)
    if args.suite == 'sanity':
        if args.memcheck:
            parser.error('use --suite corpus with --memcheck; sanity includes tight release timing checks')
        cases = [Case('sanity', ['sh', 'checks/sanity', os.path.relpath(binary, ROOT)], str(ROOT))]
    capability_rejections = []
    if discovered is not None:
        names = {entry['name'] for entry in discovered[0]}
        sat = next((entry for entry in discovered[0] if entry['short'] == 'sas'), None)
        fmb = next((entry for entry in discovered[0] if entry['name'] == 'fmb_enumeration_strategy'), None)
        for case in cases:
            if not case.name.startswith('corpus/') or case.check != 'szs': continue
            command = case.command
            diagnostic = None
            if sat and 'z3' not in sat['values']:
                if '-sas' in command and command[command.index('-sas') + 1] == 'z3':
                    diagnostic = 'z3 is an invalid value for sas'
                elif any('sas=z3' in arg for arg in command):
                    diagnostic = 'value z3 for option sas not known'
            if diagnostic is None and fmb and 'smt' not in fmb['values']:
                for flag in ('--fmb_enumeration_strategy', '-fmbes'):
                    if flag in command and command[command.index(flag) + 1] == 'smt':
                        diagnostic = 'smt is an invalid value for fmb_enumeration_strategy'
            if diagnostic is None and 'theory_instantiation' not in names:
                if '-thi' in command: diagnostic = 'thi is not a valid short option'
                elif any('thi=' in arg for arg in command): diagnostic = 'option thi not known'
            if diagnostic and any('thi=' in arg for arg in command) and 'theory_instantiation' not in names:
                case.check, case.expected, case.allow_error_exit = 'reject-regex', '(?:' + re.escape(diagnostic) + '|' + re.escape('option thi not known') + ')', True
                capability_rejections.append(case.name)
                continue
            if diagnostic:
                case.check, case.expected, case.allow_error_exit = 'reject', diagnostic, True
                capability_rejections.append(case.name)
    if args.filter: cases = [c for c in cases if re.search(args.filter, c.name)]
    if args.limit is not None: cases = cases[:args.limit]
    if not cases: parser.error('no tests selected')
    solver_timeout = args.solver_timeout if args.solver_timeout is not None else (0 if args.memcheck else None)
    if solver_timeout is not None:
        for case in cases:
            if case.name.startswith(('corpus/', 'generated/', 'features/', 'edge/', 'behavior/', 'parser/', 'mode/', 'portfolio/', 'datatype/', 'arithmetic/')):
                case.command += ['-t', str(solver_timeout)]
    if args.asan:
        for case in cases:
            if case.command[0] == str(binary) and not any(flag in case.command for flag in ('-m', '--memory_limit')):
                case.command += ['-m', '0']
    metadata = {'commit': checked_output(['git', 'rev-parse', 'HEAD']),
                'dirty': checked_output(['git', 'status', '--porcelain']),
                'started': datetime.now(timezone.utc).isoformat(), 'seed': args.seed,
                'arguments': {k: str(v) if isinstance(v, Path) else v for k, v in vars(args).items()},
                'selected': len(cases), 'artifact_naming': 'readable-prefix-sha256-16', 'skipped_shell_assertions': skipped,
                'discovery_errors': discovery_errors, 'capability_rejections': capability_rejections,
                'environment': {key: os.environ.get(key) for key in ('ASAN_OPTIONS', 'UBSAN_OPTIONS', 'LSAN_OPTIONS', 'LD_LIBRARY_PATH', 'LD_PRELOAD', 'GCOV_PREFIX', 'GCOV_PREFIX_STRIP', 'GCOV_ERROR_FILE', 'GCOV_EXIT_AT_ERROR')},
                'harness_sha256': harness_hashes(), 'source_sha256': source_fingerprint()}
    snapshot = args.output / ('harness-snapshot-' + str(time.time_ns()))
    snapshot.mkdir()
    for name in metadata['harness_sha256']:
        destination = snapshot / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes((ROOT / 'checks/testing' / name).read_bytes())
    metadata['harness_snapshot'] = str(snapshot)
    metadata['binary_sha256'] = binary_hashes([binary, args.build / 'vtest'])
    all_cases = [asdict(case) for case in cases]
    # Reject collisions before scheduling any workers.
    recover_results(args.output, cases)
    atomic_json(args.output / 'cases.json', all_cases)
    metadata['cases_sha256'] = file_hash(args.output / 'cases.json')
    metadata['input_sha256'] = input_hashes(cases, args.output)
    (args.output / 'source.diff').write_text(checked_output(['git', 'diff', 'HEAD']))
    atomic_json(args.output / 'run.json', metadata)
    return execute_cases(args, metadata, cases, [])

if __name__ == '__main__':
    sys.exit(main())
