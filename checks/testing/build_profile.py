#!/usr/bin/env python3
"""Check that CMake configured the requested testing profile before building."""
import argparse
import hashlib
import json
from pathlib import Path
import shlex
import subprocess

PROFILES = ('release', 'debug', 'memcheck', 'asan', 'ubsan', 'no-z3', 'coverage')


def read_cache(path):
    values = {}
    for line in path.read_text().splitlines():
        if line.startswith(('#', '//')) or '=' not in line or ':' not in line.split('=', 1)[0]:
            continue
        key, value = line.split('=', 1)
        values[key.split(':', 1)[0]] = value
    return values


def validate(profile, cache, arguments):
    errors = []
    definitions = {}
    tokens = iter(arguments)
    for item in tokens:
        if item in ('-D', '-U'):
            item += next(tokens, '')
        if item.startswith('-D'):
            name, _, value = item[2:].partition('=')
            definitions[name] = value or '1'
        elif item.startswith('-U'):
            definitions.pop(item[2:], None)
    # Upstream COVERAGE removes existing .gcda files during CMake configuration.
    # These profiles use explicit flags and preserve/reset counters separately.
    legacy_coverage = cache.get('COVERAGE', 'OFF').upper()
    if legacy_coverage not in ('', '0', 'OFF', 'FALSE', 'NO', 'N', 'IGNORE', 'NOTFOUND') and not legacy_coverage.endswith('-NOTFOUND'):
        errors.append('COVERAGE must be OFF; its CMake configure step deletes coverage counters')
    debug = profile != 'release'
    expected_type = 'Debug' if debug else 'Release'
    if cache.get('CMAKE_BUILD_TYPE') != expected_type:
        errors.append(f'expected CMAKE_BUILD_TYPE={expected_type}')
    for name, expected in (('VDEBUG', str(int(debug))), ('CHECK_LEAKS', str(int(debug))),
                           ('VZ3', str(int(profile != 'no-z3')))):
        if definitions.get(name) != expected:
            errors.append(f'expected -D{name}={expected}, got {definitions.get(name)!r}')
    switches = set(arguments)
    required = {'asan': {'-fsanitize=address', '-fno-omit-frame-pointer'},
                'ubsan': {'-fsanitize=undefined', '-fno-sanitize-recover=undefined'},
                'coverage': {'--coverage', '-fprofile-update=atomic'}}.get(profile, set())
    for flag in sorted(required - switches):
        errors.append(f'missing compiler flag {flag}')
    sanitizers = {name for flag in arguments if flag.startswith('-fsanitize=')
                  for name in flag.partition('=')[2].split(',')}
    expected_sanitizers = {'asan': {'address'}, 'ubsan': {'undefined'}}.get(profile, set())
    for sanitizer in sorted(sanitizers - expected_sanitizers):
        errors.append(f'unexpected sanitizer instrumentation: {sanitizer}')
    if profile in ('asan', 'ubsan'):
        for flag in arguments:
            if flag.startswith('-fno-sanitize='):
                errors.append(f'sanitizer-disabling flag conflicts with {profile}: {flag}')
        if profile == 'asan' and '-fomit-frame-pointer' in switches:
            errors.append('frame-pointer omission conflicts with the ASan profile')
        if profile == 'ubsan' and any(flag.startswith('-fsanitize-recover') for flag in arguments):
            errors.append('sanitizer recovery conflicts with the UBSan profile')
    coverage_flags = {'--coverage', '-fprofile-arcs', '-ftest-coverage'}
    if profile != 'coverage' and switches & coverage_flags:
        errors.append('unexpected coverage instrumentation')
    if profile == 'coverage':
        for flag in arguments:
            if flag in ('-fno-profile-arcs', '-fno-test-coverage') or (flag.startswith('-fprofile-update=') and flag != '-fprofile-update=atomic'):
                errors.append(f'coverage-disabling or conflicting flag: {flag}')
    linker = shlex.split(cache.get('CMAKE_EXE_LINKER_FLAGS', ''))
    linker += shlex.split(cache.get('CMAKE_EXE_LINKER_FLAGS_' + expected_type.upper(), ''))
    for flag in linker:
        if flag.startswith('-fsanitize='):
            for sanitizer in sorted(set(flag.partition('=')[2].split(',')) - expected_sanitizers):
                errors.append(f'unexpected executable linker sanitizer: {sanitizer}')
        if profile in ('asan', 'ubsan') and flag.startswith('-fno-sanitize='):
            errors.append(f'executable linker disables sanitizer: {flag}')
        if profile != 'coverage' and flag in coverage_flags:
            errors.append('unexpected executable linker coverage instrumentation')
    link_flag = {'asan': '-fsanitize=address', 'coverage': '--coverage'}.get(profile)
    if link_flag and link_flag not in linker:
        errors.append(f'missing executable linker flag {link_flag}')
    if definitions.get('VZ3') != '1' and profile != 'no-z3':
        errors.append('set Z3_DIR to the pinned Z3 build containing its CMake package')
    return errors


def inspect(build, profile):
    cache_path = build / 'CMakeCache.txt'
    commands_path = build / 'compile_commands.json'
    cache = read_cache(cache_path)
    commands = json.loads(commands_path.read_text())
    entries = [entry for entry in commands if Path(entry['file']).name == 'vampire.cpp']
    if len(entries) != 1:
        raise ValueError(f'expected one vampire.cpp compiler command, found {len(entries)}')
    arguments = entries[0].get('arguments') or shlex.split(entries[0]['command'])
    errors = validate(profile, cache, arguments)
    compiler = cache.get('CMAKE_CXX_COMPILER', '')
    version = subprocess.run([compiler, '--version'], text=True, capture_output=True, timeout=15)
    if version.returncode:
        errors.append('compiler version command failed')
    return {'profile': profile, 'status': 'fail' if errors else 'pass', 'errors': errors,
            'build': str(build), 'compiler': compiler, 'compiler_version': version.stdout.strip(),
            'settings': {key: cache.get(key) for key in (
                'CMAKE_BUILD_TYPE', 'CMAKE_CXX_FLAGS', 'CMAKE_EXE_LINKER_FLAGS',
                'CHECK_LEAKS', 'UBSAN', 'COVERAGE', 'Z3_DIR', 'CMAKE_DISABLE_FIND_PACKAGE_Z3',
                'CMAKE_EXE_LINKER_FLAGS_DEBUG', 'CMAKE_EXE_LINKER_FLAGS_RELEASE')},
            'compiler_arguments': arguments,
            'inputs_sha256': {path.name: hashlib.sha256(path.read_bytes()).hexdigest()
                              for path in (cache_path, commands_path)}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build', type=Path, required=True)
    parser.add_argument('--profile', choices=PROFILES, required=True)
    args = parser.parse_args()
    build = args.build.resolve()
    try:
        result = inspect(build, args.profile)
    except (OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        result = {'profile': args.profile, 'status': 'fail', 'errors': [str(error)]}
    (build / 'testing-profile.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'[{result["status"].upper()}] build profile {args.profile}')
    for error in result['errors']:
        print(f'  {error}')
    print(f'Profile report: {build / "testing-profile.json"}')
    return int(result['status'] != 'pass')


if __name__ == '__main__':
    raise SystemExit(main())
