#!/usr/bin/env python3
"""Check logical answers and runtime-option activation on bounded fixtures."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import subprocess

import diagnostics
import finite_model_validation
import run as harness
from runtime_options_cases import arguments, cases, record

ROOT = Path(__file__).resolve().parents[2]
PROFILES = ('release', 'debug', 'asan', 'ubsan', 'no-z3', 'valgrind', 'coverage')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def assess(case, stdout, stderr, code, timeout, checker=finite_model_validation):
    statuses = harness.SZS.findall(stdout)
    status = statuses[-1] if statuses else None
    if timeout:
        semantic, reason = 'inconclusive', 'external wall timeout'
    elif diagnostics.ASSERTION.search(stdout + stderr) or code is not None and code < 0:
        semantic, reason = 'fail', 'assertion or signal'
    elif any(s in ('Satisfiable', 'Unsatisfiable', 'Theorem', 'CounterSatisfiable', 'ContradictoryAxioms')
             and s != case.expected for s in statuses):
        semantic, reason = 'fail', 'logical status disagrees with the independent oracle'
    elif status == case.expected and code in (0, 1):
        semantic, reason = 'pass', ''
    else:
        semantic, reason = 'inconclusive', 'no conclusive answer; inspect raw diagnostics before attributing a defect'
    model_report = None
    if semantic == 'pass' and case.model is not None:
        try:
            model_report = checker.check_model(stdout, case.model)
        except (ValueError, KeyError, TypeError) as error:
            semantic, reason = 'fail', 'independent model validation: ' + str(error)
    matches = re.findall(case.marker, stdout, re.IGNORECASE) if case.marker else []
    if case.model is not None:
        matches = [int(x) for x in re.findall(r'^% TRYING \[(\d+)\]\s*$', stdout, re.MULTILINE)]
        if matches == list(range(int(case.value), case.model['size'] + 1)):
            activation = 'observed'
            activation_reason = 'Enumeration trace starts at the requested size and reaches the expected model size.'
        else:
            activation = 'inconclusive'
            activation_reason = 'Enumeration trace does not establish the requested start size.'
    elif case.marker is None:
        activation, activation_reason = 'control', 'Disabled-setting control.'
    elif matches:
        activation, activation_reason = 'observed', 'Positive inference or transformation counter.'
    else:
        activation = 'inconclusive'
        activation_reason = 'No matching positive counter; command presence is insufficient.'
    if (case.option == 'equality_resolution_with_deletion' and case.value == 'on'
            and activation == 'observed' and 'equality resolution with deletion' not in stdout):
        activation = 'inconclusive'
        activation_reason = 'Shared equality-resolution counter lacks its preprocessing phase marker.'
    return {'semantic_outcome': semantic, 'semantic_reason': reason, 'status': status,
            'activation': activation, 'activation_reason': activation_reason,
            'activation_matches': matches, 'activation_required': case.activation_required,
            'model_validation': model_report}


def evaluate_result(case, base, stdout, stderr, profile):
    # The process runner separates solver answers from instrumentation exit codes.
    interrupted = base.get('sanitizer_error_deadline', False)
    checked = assess(case, stdout, stderr,
                     0 if base['semantic_outcome'] == 'pass' else base['exit'], base['wall_timeout'] or interrupted)
    if interrupted:
        checked['semantic_outcome'] = 'inconclusive'
        checked['semantic_reason'] = base['semantic_reason'] or 'terminated after sanitizer error grace expired'
    if checked['semantic_outcome'] == 'pass' and base['semantic_outcome'] != 'pass':
        checked['semantic_outcome'] = base['semantic_outcome']
        checked['semantic_reason'] = base['semantic_reason']
    outcome, reason, memory = diagnostics.combine(
        checked['semantic_outcome'], checked['semantic_reason'], base['sanitizer_messages'],
        base['valgrind_errors'], base['wall_timeout'], base['sanitizer_warnings'])
    if profile in ('release', 'debug', 'no-z3', 'coverage') and not base['sanitizer_messages'] and not base['sanitizer_warnings']:
        memory = 'not-instrumented'
    if outcome == 'pass' and case.activation_required and checked['activation'] != 'observed':
        outcome, reason = 'inconclusive', 'required runtime-option activation was not observed'
    if interrupted:
        reason += '; terminated after sanitizer error grace expired'
    return {**base, **checked, 'option': case.option, 'value': case.value,
            'outcome': outcome, 'reason': reason, 'memory_outcome': memory}


def git_output(root, *arguments):
    result = subprocess.run(['git', '-C', str(root), *arguments], text=True, capture_output=True)
    return result.stdout.strip() if result.returncode == 0 else None


def build_metadata(binary):
    cache_path = binary.parent / 'CMakeCache.txt'
    cache = {}
    if cache_path.is_file():
        for line in cache_path.read_text(errors='replace').splitlines():
            if line and not line.startswith(('#', '//')) and ':' in line and '=' in line:
                key, value = line.split('=', 1)
                cache[key.split(':', 1)[0]] = value
    source = Path(cache['CMAKE_HOME_DIRECTORY']) if 'CMAKE_HOME_DIRECTORY' in cache else None
    tracked = git_output(source, 'ls-files') if source else None
    source_files = {}
    for name in (tracked or '').splitlines():
        path = source / name
        if path.is_file() and (path.suffix in ('.c', '.cc', '.cpp', '.cxx', '.h', '.hpp', '.cmake')
                               or path.name == 'CMakeLists.txt'):
            source_files[name] = digest(path)
    return {'directory': str(binary.parent), 'cmake_cache_sha256': digest(cache_path) if cache_path.is_file() else None,
            'cmake_build_type': cache.get('CMAKE_BUILD_TYPE'), 'source_directory': str(source) if source else None,
            'source_revision': git_output(source, 'rev-parse', 'HEAD') if source else None,
            'source_status': git_output(source, 'status', '--porcelain', '--untracked-files=no') if source else None,
            'source_files_sha256': source_files,
            'source_tree_sha256': hashlib.sha256(json.dumps(source_files, sort_keys=True).encode()).hexdigest()
                                  if source_files else None}


def run_suite(build, profile, output, *, jobs=2, timeout=120, pattern='', sanitizer_error_grace=None):
    """Run selected cases; return the persisted summary, including its exit_code."""
    if profile not in PROFILES:
        raise ValueError('unknown runtime-option profile: ' + profile)
    if (jobs < 1 or not math.isfinite(timeout) or timeout <= 0 or
            (sanitizer_error_grace is not None and (not math.isfinite(sanitizer_error_grace) or sanitizer_error_grace <= 0))):
        raise ValueError('jobs must be positive; timeout and sanitizer error grace must be finite and positive')
    binary = Path(build).resolve()
    if binary.is_dir():
        binary /= 'vampire'
    if not binary.is_file():
        raise ValueError('Vampire binary does not exist: ' + str(binary))
    selected = [case for case in cases() if re.search(pattern, case.name)]
    if not selected:
        raise ValueError('filter selects no runtime-option cases')
    if profile == 'valgrind' and shutil.which('valgrind') is None:
        raise ValueError('Valgrind is not available on PATH')
    if profile == 'asan':
        os.environ.setdefault('ASAN_OPTIONS', 'detect_leaks=1:halt_on_error=1:abort_on_error=0:exitcode=98')
    if profile == 'ubsan':
        os.environ.setdefault('UBSAN_OPTIONS', 'halt_on_error=1:print_stacktrace=1')
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    inputs = output / 'inputs'
    inputs.mkdir()
    snapshots = output / 'harness'
    snapshots.mkdir()
    # These copies record the sources used by this invocation. Imports stay local.
    for path in Path(__file__).parent.glob('*.py'):
        shutil.copyfile(path, snapshots / path.name)
    version = subprocess.run([str(binary), '--version'], text=True, capture_output=True, timeout=timeout)
    metadata = {
        'started_utc': datetime.now(timezone.utc).isoformat(),
        'harness_revision': git_output(ROOT, 'rev-parse', 'HEAD'),
        'harness_status': git_output(ROOT, 'status', '--porcelain', '--', 'checks/testing'),
        'harness_sha256': {path.name: digest(path) for path in sorted(snapshots.glob('*.py'))},
        'build': build_metadata(binary), 'binary': str(binary), 'binary_sha256': digest(binary),
        'binary_version': version.stdout, 'binary_version_stderr': version.stderr,
        'binary_version_exit': version.returncode, 'jobs': jobs, 'profile': profile,
        'timeout': timeout, 'filter': pattern, 'sanitizer_error_grace': sanitizer_error_grace,
        'environment': {key: os.environ.get(key) for key in ('ASAN_OPTIONS', 'UBSAN_OPTIONS', 'LSAN_OPTIONS')},
        'cases': [record(case) for case in selected],
    }
    (output / 'metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')

    def execute(case):
        path = inputs / (case.name + '.p')
        path.write_text(case.text)
        command = [str(binary), *arguments(case), str(path)]
        if profile == 'valgrind':
            command += ['-t', '0']
        if profile == 'asan':
            command += ['-m', '0']
        kwargs = {'asan': profile == 'asan'}
        if sanitizer_error_grace is not None:
            kwargs['sanitizer_error_grace'] = sanitizer_error_grace
        base = harness.run_case(harness.Case(case.name, command, str(inputs), 'szs', case.expected, str(path)),
                                output, timeout, profile == 'valgrind', **kwargs)
        folder = Path(base['artifacts'])
        row = evaluate_result(case, base, (folder / 'stdout.log').read_text(errors='replace'),
                              (folder / 'stderr.log').read_text(errors='replace'), profile)
        row['input_sha256'] = digest(path)
        (folder / 'result.json').write_text(json.dumps(row, indent=2) + '\n')
        print(f'{row["outcome"].upper():12} {case.name}: logic {row["semantic_outcome"]}; '
              f'memory {row["memory_outcome"]}; activation {row["activation"]}', flush=True)
        if row['outcome'] != 'pass':
            print(f'  Reason: {row["reason"]}\n  Logs: {row["artifacts"]}', flush=True)
        return row

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        results = list(pool.map(execute, selected))
    data = {'metadata': str(output / 'metadata.json'), 'results': results,
            'binary_sha256_after': digest(binary), 'finished_utc': datetime.now(timezone.utc).isoformat()}
    for prefix, states, field in (
        ('semantic', ('pass', 'fail', 'inconclusive'), 'semantic_outcome'),
        ('outcome', ('pass', 'fail', 'inconclusive'), 'outcome'),
        ('memory', ('pass', 'fail', 'inconclusive', 'not-instrumented'), 'memory_outcome'),
        ('activation', ('observed', 'control', 'inconclusive'), 'activation'),
    ):
        data[prefix + '_counts'] = {state: sum(row[field] == state for row in results) for state in states}
    data['exit_code'] = int(data['binary_sha256_after'] != metadata['binary_sha256']
                            or any(row['outcome'] != 'pass' for row in results))
    (output / 'summary.json').write_text(json.dumps(data, indent=2) + '\n')
    return data


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build', type=Path, required=True, help='build directory or Vampire executable')
    parser.add_argument('--profile', choices=PROFILES, default='release')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--jobs', type=int, default=2)
    parser.add_argument('--timeout', type=float, default=120)
    parser.add_argument('--filter', default='')
    parser.add_argument('--sanitizer-error-grace', type=float)
    args = parser.parse_args(argv)
    try:
        data = run_suite(args.build, args.profile, args.output, jobs=args.jobs, timeout=args.timeout,
                         pattern=args.filter, sanitizer_error_grace=args.sanitizer_error_grace)
    except (ValueError, FileExistsError, re.error) as error:
        parser.error(str(error))
    print(json.dumps({key: value for key, value in data.items() if key != 'results'}, indent=2))
    return data['exit_code']


if __name__ == '__main__':
    raise SystemExit(main())
