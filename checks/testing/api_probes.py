#!/usr/bin/env python3
"""Run optional API-only probes beside an existing Debug Unix Makefiles build."""
import argparse
from contextlib import contextmanager
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess

import run as harness

HERE = Path(__file__).resolve().parent
FIXTURES = (('api_destruction.cpp', 'ApiDestruction'), ('api_unit_count.cpp', 'ApiUnitCount'))
PROBES = (
    ('F08', 'ApiDestruction', 'destroy_sat_inference', 'F08_END inference.destroy'),
    ('F12', 'ApiDestruction', 'destroy_long_label_boolean_term_formula', 'F12_END formula.destroy'),
    ('F13', 'ApiUnitCount', 'only_incoming_units_count_once',
     'F13_COUNT before=1 cached_after=2 actual_units=2 expected_after=2'),
)


def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for data in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(data)
    return digest.hexdigest()


def compiler(command):
    if not command or Path(command[0]).name not in ('c++', 'g++', 'clang++'):
        raise ValueError('only direct c++, g++, and clang++ commands are supported')
    return [command[0]]


def compile_command(original, source, output, unit):
    command = compiler(original)
    if not source.is_absolute() or not output.is_absolute():
        raise ValueError('probe source and object paths must be absolute')
    if re.fullmatch(r'[A-Za-z_]\w*', unit) is None:
        raise ValueError('unit name must be a C++ identifier')
    index, seen = 1, set()
    while index < len(original):
        token = original[index]
        if token in ('-o', '-c', '-MF', '-MT', '-MQ'):
            if index + 1 == len(original) or token in seen:
                raise ValueError('invalid or repeated compiler output/source flag: ' + token)
            seen.add(token)
            value = source if token == '-c' else str(output) + '.d' if token == '-MF' else output
            command += [token, str(value)]
            index += 2
            continue
        if token.startswith(('-DUNIT_ID=', '-DUNIT_ID_STR=')):
            pass
        elif (token in ('-g', '-g0', '-g1', '-g2', '-g3', '-O0', '-Wall', '-Wextra', '-Wpedantic',
                        '-fno-threadsafe-statics', '-fno-rtti', '-fPIC', '-fPIE', '-pthread', '-MD', '-MMD', '-MP')
              or re.fullmatch(r'-D[A-Za-z_]\w*(?:=[^\r\n\x00]*)?', token)
              or re.fullmatch(r'-U[A-Za-z_]\w*', token)
              or re.fullmatch(r'-I[^\r\n\x00]+', token)
              or re.fullmatch(r'-std=(?:gnu\+\+|c\+\+)(?:98|03|0x|11|1y|14|1z|17|2a|20|2b|23|2c|26)', token)):
            command.append(token)
        else:
            raise ValueError('unsupported compiler flag: ' + token)
        index += 1
    if not {'-c', '-o'} <= seen:
        raise ValueError('compiler command requires -c and -o')
    if any(flag in original for flag in ('-MD', '-MMD')) and '-MF' not in seen:
        command += ['-MF', str(output) + '.d']
    return command + ['-DUNIT_ID=' + unit, '-DUNIT_ID_STR="' + unit + '"']


def link_command(original, build, binary, added_objects):
    command, inputs, search, libraries = compiler(original), [], [], []
    if not binary.is_absolute() or any(not path.is_absolute() for path in added_objects):
        raise ValueError('probe binary and added object paths must be absolute')
    index, output_seen = 1, False
    while index < len(original):
        token = original[index]
        if token == '-o':
            if output_seen or index + 1 == len(original):
                raise ValueError('invalid or repeated link output')
            output_seen = True
            command += ['-o', str(binary)]
            index += 2
            continue
        if token.startswith('-Wl,--dependency-file='):
            command.append('-Wl,--dependency-file=' + str(binary.with_suffix('.link.d')))
        elif token in ('-g', '-pthread', '-rdynamic', '-Wl,--as-needed', '-Wl,--no-as-needed'):
            command.append(token)
        elif token.startswith('-Wl,-rpath,') and ',' not in token[len('-Wl,-rpath,'):]:
            command.append(token)
        elif token.startswith('-L') and len(token) > 2:
            folder = (build / token[2:]).resolve()
            search.append(folder)
            command.append('-L' + str(folder))
        elif re.fullmatch(r'-l[A-Za-z0-9_+.-]+', token):
            libraries.append(token[2:])
            command.append(token)
        elif not token.startswith('-') and (token.endswith(('.o', '.a')) or '.so' in Path(token).name):
            path = (build / token).resolve()
            if not path.is_file():
                raise ValueError('missing link input: ' + str(path))
            inputs.append(path)
            command.append(str(path))
        else:
            raise ValueError('unsupported linker token: ' + token)
        index += 1
    if not output_seen or not any(path.suffix == '.o' for path in inputs):
        raise ValueError('link command requires -o and existing object files')
    for name in libraries:
        found = next((folder / ('lib' + name + suffix) for folder in search
                      for suffix in ('.so', '.a') if (folder / ('lib' + name + suffix)).is_file()), None)
        if found is None:
            raise ValueError('library must resolve through an explicit -L directory: ' + name)
        inputs.append(found.resolve())
    command[1:1] = [str(path) for path in added_objects]
    return command, inputs


def snapshot(paths):
    return {str(path): sha(path) for path in sorted(set(path.resolve() for path in paths))}


def resolve_driver(name, cwd):
    compiler([name])
    path = Path(name)
    if not path.is_absolute():
        if '/' in name:
            path = Path(cwd) / path
        else:
            search = os.pathsep.join(str(Path(item) if Path(item).is_absolute() else Path(cwd) / item)
                                     for item in os.environ.get('PATH', os.defpath).split(os.pathsep))
            resolved = shutil.which(name, path=search)
            if resolved is None: raise ValueError('compiler executable is missing: ' + name)
            path = Path(resolved)
    path = path.absolute()
    if not path.is_file(): raise ValueError('compiler executable is missing: ' + str(path))
    return path


def counter_snapshot(build):
    return snapshot([*build.rglob('*.gcda'), *build.rglob('*.profraw')])


def changed_inputs(expected):
    return [name for name, digest in expected.items()
            if not Path(name).is_file() or sha(Path(name)) != digest]


def environment_policy():
    # GCC's dependency-output environment can otherwise bypass command-line
    # output rewriting. Profiling-instrumented objects are rejected separately.
    return {'DEPENDENCIES_OUTPUT': None, 'SUNPRO_DEPENDENCIES': None,
            'GCC_COMPARE_DEBUG': None, 'GCC_COMPARE_DEBUG_OUTFILE': None}


def reject_instrumented_objects(inputs):
    objects = [path for path in inputs if path.suffix in ('.o', '.a') or '.so' in path.name]
    inspector = shutil.which('nm')
    if inspector is None: raise ValueError('nm is required to check baseline objects for instrumentation')
    command = [inspector, '-u', '--', *map(str, objects)]
    result = subprocess.run(command, capture_output=True, text=True, timeout=60)
    if result.returncode: raise ValueError('cannot inspect baseline objects: ' + result.stderr.strip())
    hooks = re.findall(r'(?:__gcov_|llvm_gcda_|llvm_gcov_|__llvm_profile_|__llvm_prf|__asan_|__ubsan_|__tsan_|__msan_|__cyg_profile_)\w*|\b_?mcount\b|\b__fentry__\b', result.stdout)
    if hooks:
        raise ValueError('API probes require noninstrumented Debug objects; found ' + ', '.join(sorted(set(hooks))))
    return {'command': command, 'tool_sha256': sha(Path(inspector)),
            'undefined_symbols_sha256': hashlib.sha256(result.stdout.encode()).hexdigest()}


def show_result(result):
    api = f'; API {result["api_outcome"]}' if 'api_outcome' in result else ''
    print(f'[{result["outcome"].upper()}] {result["name"]}{api}; memory {result.get("memory_outcome", "unknown")}', flush=True)
    print(f'  Reason: {result.get("api_reason") or result.get("reason") or "completed"}', flush=True)
    print(f'  Artifacts: {result["artifacts"]}', flush=True)


@contextmanager
def execution_environment(policy):
    previous = {name: os.environ.get(name) for name in policy}
    try:
        for name, value in policy.items():
            if value is None: os.environ.pop(name, None)
            else: os.environ[name] = value
        yield
    finally:
        for name, value in previous.items():
            if value is None: os.environ.pop(name, None)
            else: os.environ[name] = value


def classify_api(result):
    access = [error for error in result.get('valgrind_errors', []) if not error['kind'].startswith('Leak_')
              and error['kind'] not in ('invalid-xml', 'missing-xml')]
    result = {**result, 'scope': 'API-only', 'access_errors': access}
    result['api_outcome'] = ('inconclusive' if result.get('wall_timeout') and not access
                             and not result.get('sanitizer_messages') else result['outcome'])
    result['api_reason'] = ('API call did not finish; timeout alone is not an access-error finding'
                            if result['api_outcome'] == 'inconclusive' and result.get('wall_timeout')
                            else result['reason'])
    return result


def prepare(build, output):
    cache = (build / 'CMakeCache.txt').read_text()
    if 'CMAKE_BUILD_TYPE:STRING=Debug\n' not in cache or 'CMAKE_GENERATOR:INTERNAL=Unix Makefiles\n' not in cache:
        raise ValueError('a completed Debug Unix Makefiles build is required')
    source_match = re.search(r'^CMAKE_HOME_DIRECTORY:INTERNAL=(.+)$', cache, re.MULTILINE)
    if not source_match:
        raise ValueError('CMake source directory is missing')
    source = Path(source_match[1]).resolve()
    if output.is_relative_to(source) or output.is_relative_to(build) or build.is_relative_to(output):
        raise ValueError('probe output must be outside the baseline source and build directories')
    database = build / 'compile_commands.json'
    link = build / 'CMakeFiles/vtest.dir/link.txt'
    entries = json.loads(database.read_text())
    entry = next((item for item in entries if '/UnitTests/' in item['file']
                  and 'vtest.dir' in (item.get('command') or ' '.join(item.get('arguments', [])))), None)
    if entry is None:
        raise ValueError('no vtest UnitTests command in compile_commands.json')
    original = list(entry.get('arguments') or shlex.split(entry['command']))
    compile_driver = resolve_driver(original[0], entry['directory'])
    original[0] = str(compile_driver)
    commands = []
    for name, unit in FIXTURES:
        commands.append({'name': 'compile-' + unit,
                         'command': compile_command(original, output / name, output / (unit + '.o'), unit),
                         'cwd': entry['directory']})
    link_original = shlex.split(link.read_text())
    link_driver = resolve_driver(link_original[0], build)
    link_original[0] = str(link_driver)
    linked, inputs = link_command(link_original, build, output / 'vtest-api-probes',
                                 [output / (unit + '.o') for _, unit in FIXTURES])
    instrumentation_check = reject_instrumented_objects(inputs)
    commands.append({'name': 'link', 'command': linked, 'cwd': str(build)})
    tracked = subprocess.check_output(['git', '-C', str(source), 'ls-files', '-z']).decode().split('\0')
    paths = inputs + [database, link, build / 'CMakeCache.txt', build / 'vampire', build / 'vtest']
    dependency = build / 'CMakeFiles/vtest.dir/link.d'
    if dependency.is_file():
        paths.append(dependency)
    paths += [source / name for name in tracked if name and (source / name).is_file()]
    # Include the compiler executable and the exact fixtures used for new objects.
    drivers_and_binaries = [compile_driver, link_driver, build / 'vampire', build / 'vtest']
    dependencies = harness.binary_hashes(drivers_and_binaries)
    counters = counter_snapshot(build)
    paths += [*(Path(name) for name in dependencies), *(Path(name) for name in counters),
              *(HERE / 'fixtures/api' / name for name, _ in FIXTURES)]
    return {'source_directory': str(source), 'source_revision': subprocess.check_output(
                ['git', '-C', str(source), 'rev-parse', 'HEAD'], text=True).strip(),
            'source_status': subprocess.check_output(['git', '-C', str(source), 'status', '--porcelain',
                                                       '--untracked-files=no'], text=True).strip(),
            'compile_template': entry, 'link_template': link.read_text(), 'commands': commands,
            'immutable_inputs': snapshot(paths),
            'source_sha256': harness.source_fingerprint(source),
            'drivers_and_binaries': [str(path) for path in drivers_and_binaries],
            'binary_dependency_sha256': dependencies, 'counter_inputs': counters,
            'instrumentation_check': instrumentation_check,
            'scope': 'API-only probes; no claim that a CLI solver path reaches these operations.'}


def run_probes(build, output, *, memcheck=False, timeout=30, plan_only=False):
    build, output = Path(build).resolve(), Path(output).resolve()
    if output.exists():
        raise ValueError('output already exists; choose a new directory')
    if not math.isfinite(timeout) or timeout <= 0:
        raise ValueError('timeout must be finite and positive')
    if memcheck and shutil.which('valgrind') is None:
        raise ValueError('Valgrind is not available on PATH')
    metadata = prepare(build, output)
    output.mkdir(parents=True)
    for name, _ in FIXTURES:
        shutil.copyfile(HERE / 'fixtures/api' / name, output / name)
    metadata.update(build=str(build), output=str(output), memcheck=memcheck, timeout=timeout,
                    plan_only=plan_only, runner_sha256=sha(Path(__file__)),
                    harness_sha256=snapshot([HERE / name for name in
                        ('api_probes.py', 'run.py', 'diagnostics.py', 'report.py')]))
    metadata['immutable_inputs'].update(metadata['harness_sha256'])
    metadata['execution_environment'] = environment_policy()
    metadata['library_environment'] = {name: os.environ.get(name) for name in ('LD_LIBRARY_PATH', 'LD_PRELOAD')}
    harness.atomic_json(output / 'metadata.json', metadata)
    results = []
    with execution_environment(metadata['execution_environment']):
        if not plan_only:
            for item in metadata['commands']:
                result = harness.run_case(harness.Case(item['name'], item['command'], item['cwd']), output, 300, False)
                results.append(result)
                show_result(result)
                if result['outcome'] != 'pass':
                    break
            if all(row['outcome'] == 'pass' for row in results):
                for finding, unit, test, expected in PROBES:
                    command = [str(output / 'vtest-api-probes'), 'run', unit, test]
                    result = harness.run_case(harness.Case(finding, command, str(output), 'contains', expected),
                                              output, timeout, memcheck)
                    result = classify_api(result)
                    harness.atomic_json(Path(result['artifacts']) / 'result.json', result)
                    results.append(result)
                    show_result(result)
    changed = changed_inputs(metadata['immutable_inputs'])
    counters_after = counter_snapshot(build)
    changed_counters = sorted(name for name in set(counters_after) | set(metadata['counter_inputs'])
                              if counters_after.get(name) != metadata['counter_inputs'].get(name))
    source_unchanged = (harness.source_fingerprint(Path(metadata['source_directory'])) == metadata['source_sha256']
                        and subprocess.check_output(['git', '-C', metadata['source_directory'], 'rev-parse', 'HEAD'],
                                                    text=True).strip() == metadata['source_revision'])
    dependencies_unchanged = harness.binary_hashes(metadata['drivers_and_binaries']) == metadata['binary_dependency_sha256']
    unchanged = not changed and not changed_counters and source_unchanged and dependencies_unchanged
    summary = {'metadata': str(output / 'metadata.json'), 'results': results, 'plan_only': plan_only,
               'immutable_inputs_unchanged': unchanged, 'changed_inputs': changed,
               'changed_counters': changed_counters, 'source_identity_unchanged': source_unchanged,
               'binary_dependencies_unchanged': dependencies_unchanged,
               'probe_binary_sha256': sha(output / 'vtest-api-probes')
                                      if (output / 'vtest-api-probes').is_file() else None,
               'exit_code': int(not unchanged or any(row['outcome'] != 'pass' for row in results))}
    harness.atomic_json(output / 'summary.json', summary)
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--memcheck', action='store_true')
    parser.add_argument('--timeout', type=float, default=30)
    parser.add_argument('--plan-only', action='store_true', help='record commands and provenance without compiling or running')
    args = parser.parse_args()
    try:
        result = run_probes(args.build, args.output, memcheck=args.memcheck, timeout=args.timeout, plan_only=args.plan_only)
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        parser.error(str(error))
    print(json.dumps({key: value for key, value in result.items() if key != 'results'}, indent=2))
    return result['exit_code']


if __name__ == '__main__':
    raise SystemExit(main())
