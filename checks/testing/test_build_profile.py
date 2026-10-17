import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import build_profile


class BuildProfileTests(unittest.TestCase):
    def config(self, profile):
        debug = profile != 'release'
        cache = {'CMAKE_BUILD_TYPE': 'Debug' if debug else 'Release',
                 'CMAKE_EXE_LINKER_FLAGS': {'asan': '-fsanitize=address',
                                           'coverage': '--coverage'}.get(profile, '')}
        args = [f'-DVDEBUG={int(debug)}', f'-DCHECK_LEAKS={int(debug)}',
                f'-DVZ3={int(profile != "no-z3")}']
        args += {'asan': ['-fsanitize=address', '-fno-omit-frame-pointer'],
                 'ubsan': ['-fsanitize=undefined', '-fno-sanitize-recover=undefined'],
                 'coverage': ['--coverage', '-fprofile-update=atomic']}.get(profile, [])
        return cache, args

    def test_each_requested_profile(self):
        for profile in build_profile.PROFILES:
            with self.subTest(profile=profile):
                self.assertEqual(build_profile.validate(profile, *self.config(profile)), [])

    def test_z3_cannot_silently_disappear(self):
        cache, args = self.config('release')
        args[2] = '-DVZ3=0'
        errors = build_profile.validate('release', cache, args)
        self.assertTrue(any('VZ3' in e for e in errors))
        self.assertTrue(any('Z3_DIR' in e for e in errors))

    def test_no_z3_rejects_enabled_dependency(self):
        cache, args = self.config('no-z3')
        args[2] = '-DVZ3=1'
        self.assertTrue(build_profile.validate('no-z3', cache, args))

    def test_debug_requires_assertions_and_cleanup(self):
        for index in (0, 1):
            cache, args = self.config('debug')
            args[index] = args[index].replace('=1', '=0')
            self.assertTrue(build_profile.validate('debug', cache, args))

    def test_missing_instrumentation_and_link_flags(self):
        for profile in ('asan', 'ubsan', 'coverage'):
            cache, args = self.config(profile)
            for flag in args[3:]:
                with self.subTest(profile=profile, flag=flag):
                    self.assertTrue(build_profile.validate(profile, cache, [a for a in args if a != flag]))
            if profile != 'ubsan':
                cache['CMAKE_EXE_LINKER_FLAGS'] = ''
                self.assertTrue(build_profile.validate(profile, cache, args))

    def test_stale_profile_flags(self):
        cache, args = self.config('release')
        for flag in ('-fsanitize=address', '-fsanitize=undefined', '--coverage'):
            self.assertTrue(build_profile.validate('release', cache, args + [flag]))

    def test_legacy_coverage_option_is_rejected_before_profile_acceptance(self):
        for profile in build_profile.PROFILES:
            cache, args = self.config(profile)
            cache['COVERAGE'] = 'ON'
            self.assertTrue(any('deletes coverage counters' in e for e in build_profile.validate(profile, cache, args)))

    def test_combined_and_other_sanitizers_cannot_hide_in_noninstrumented_profile(self):
        cache, args = self.config('release')
        for flag in ('-fsanitize=address,undefined', '-fsanitize=thread', '-fsanitize=leak'):
            with self.subTest(flag=flag):
                self.assertTrue(build_profile.validate('release', cache, args + [flag]))

    def test_later_flags_cannot_disable_requested_instrumentation(self):
        flags = {'asan': ['-fno-sanitize=address', '-fno-sanitize=all', '-fomit-frame-pointer'],
                 'ubsan': ['-fno-sanitize=undefined', '-fno-sanitize=alignment', '-fsanitize-recover=undefined'],
                 'coverage': ['-fno-profile-arcs', '-fno-test-coverage', '-fprofile-update=single']}
        for profile, disabled in flags.items():
            cache, args = self.config(profile)
            for flag in disabled:
                with self.subTest(profile=profile, flag=flag):
                    self.assertTrue(build_profile.validate(profile, cache, args + [flag]))

    def test_split_definitions_and_later_undefinition(self):
        cache, args = self.config('debug')
        split = [part for arg in args for part in ('-D', arg[2:])]
        self.assertEqual(build_profile.validate('debug', cache, split), [])
        self.assertTrue(build_profile.validate('debug', cache, args + ['-U', 'CHECK_LEAKS']))

    def test_configuration_specific_linker_flags_are_checked(self):
        cache, args = self.config('release')
        cache['CMAKE_EXE_LINKER_FLAGS_RELEASE'] = '-fsanitize=address'
        self.assertTrue(build_profile.validate('release', cache, args))
        cache, args = self.config('asan')
        cache['CMAKE_EXE_LINKER_FLAGS_DEBUG'] = '-fno-sanitize=address'
        self.assertTrue(build_profile.validate('asan', cache, args))

    def test_wrong_build_type(self):
        cache, args = self.config('debug')
        cache['CMAKE_BUILD_TYPE'] = 'Release'
        self.assertTrue(build_profile.validate('debug', cache, args))

    def test_reads_cmake_cache_and_arguments(self):
        with tempfile.TemporaryDirectory() as temporary:
            build = Path(temporary)
            cache, args = self.config('release')
            (build / 'CMakeCache.txt').write_text('// comment\n# comment\n' + '\n'.join(
                f'{k}:STRING={v}' for k, v in {**cache, 'CMAKE_CXX_COMPILER': '/usr/bin/c++'}.items()))
            (build / 'compile_commands.json').write_text(json.dumps([
                {'file': '/src/vampire.cpp', 'arguments': ['/usr/bin/c++', *args]}]))
            with patch('build_profile.subprocess.run') as run:
                run.return_value.returncode = 0
                run.return_value.stdout = 'compiler version\n'
                result = build_profile.inspect(build, 'release')
            self.assertEqual(result['status'], 'pass')
            self.assertEqual(len(result['inputs_sha256']), 2)
            self.assertEqual(result['compiler_version'], 'compiler version')


if __name__ == '__main__':
    unittest.main()
