import tempfile
import unittest
import os
import shutil
import subprocess
from types import SimpleNamespace
from pathlib import Path
from unittest.mock import patch

from api_probes import (changed_inputs, classify_api, compile_command, counter_snapshot,
                        environment_policy, execution_environment, link_command, reject_instrumented_objects, resolve_driver)


class ApiProbeCommandsTests(unittest.TestCase):
    def test_compile_redirects_source_object_and_dependency_outputs(self):
        command = compile_command(['c++', '-g', '-DUNIT_ID=Old', '-DUNIT_ID_STR="Old"', '-MD',
                                   '-MF', 'old.d', '-MT', 'old.o', '-o', 'old.o', '-c', 'old.cpp'],
                                  Path('/output/probe.cpp'), Path('/output/probe.o'), 'Probe')
        self.assertEqual(command[command.index('-c') + 1], '/output/probe.cpp')
        self.assertEqual(command[command.index('-o') + 1], '/output/probe.o')
        self.assertEqual(command[command.index('-MF') + 1], '/output/probe.o.d')
        self.assertEqual(command[command.index('-MT') + 1], '/output/probe.o')
        self.assertNotIn('-DUNIT_ID=Old', command)
        self.assertIn('-DUNIT_ID=Probe', command)

    def test_implicit_dependency_output_gets_an_explicit_destination(self):
        command = compile_command(['c++', '-MMD', '-o', 'old.o', '-c', 'old.cpp'],
                                  Path('/output/probe.cpp'), Path('/output/probe.o'), 'Probe')
        self.assertEqual(command[command.index('-MF') + 1], '/output/probe.o.d')

    def test_compile_rejects_response_files_and_extra_output_flags(self):
        for flag in ('@compile.rsp', '--coverage', '-fprofile-arcs', '-save-temps', '-flto', '-ftime-trace'):
            with self.subTest(flag=flag), self.assertRaises(ValueError):
                compile_command(['c++', flag, '-o', 'old.o', '-c', 'old.cpp'],
                                Path('/output/probe.cpp'), Path('/output/probe.o'), 'Probe')

    def test_compile_rejects_compiler_wrappers(self):
        with self.assertRaises(ValueError):
            compile_command(['ccache', 'c++', '-o', 'old.o', '-c', 'old.cpp'],
                            Path('/output/probe.cpp'), Path('/output/probe.o'), 'Probe')

    def test_compile_flags_cannot_consume_redirected_output_options(self):
        for flag in ('-I', '-D', '-U', '-D-o', '-U=NAME', '-std=', '-I\npath', '-DNAME=x\n#pragma once'):
            with self.subTest(flag=flag), self.assertRaises(ValueError):
                compile_command(['c++', flag, '-o', 'old.o', '-c', 'old.cpp'],
                                Path('/output/probe.cpp'), Path('/output/probe.o'), 'Probe')

    def test_attached_macro_values_and_include_paths_stay_single_arguments(self):
        command = compile_command(['c++', '-DNOTE=-o', '-UOLD', '-I/path with spaces', '-std=gnu++17',
                                   '-o', 'old.o', '-c', 'old.cpp'],
                                  Path('/output/probe.cpp'), Path('/output/probe.o'), 'Probe')
        self.assertIn('-DNOTE=-o', command)
        self.assertIn('-I/path with spaces', command)

    def test_compile_rejects_relative_probe_output(self):
        with self.assertRaisesRegex(ValueError, 'absolute'):
            compile_command(['c++', '-o', 'old.o', '-c', 'old.cpp'],
                            Path('/output/probe.cpp'), Path('-o'), 'Probe')

    def test_link_redirects_dependency_file_as_well_as_binary(self):
        with tempfile.TemporaryDirectory() as temporary:
            build = Path(temporary)
            (build / 'one.o').write_bytes(b'object')
            output = build / 'separate' / 'vtest-api-probes'
            command, inputs = link_command(['c++', '-g', '-Wl,--dependency-file=CMakeFiles/vtest.dir/link.d',
                                             'one.o', '-o', 'vtest'], build, output, [output.with_suffix('.o')])
            self.assertIn('-Wl,--dependency-file=' + str(output.with_suffix('.link.d')), command)
            self.assertEqual(command[command.index('-o') + 1], str(output))
            self.assertEqual(inputs, [build / 'one.o'])

    def test_link_rejects_unclassified_output_flags(self):
        for flag in ('-Wl,-Map=baseline.map', '@objects.rsp', '-flto', '-Wl,--out-implib=baseline.a'):
            with self.subTest(flag=flag), self.assertRaises(ValueError):
                link_command(['c++', flag, '-o', 'vtest'], Path('/build'), Path('/output/probe'), [])

    def test_link_hashes_explicit_library_input(self):
        with tempfile.TemporaryDirectory() as temporary:
            build = Path(temporary)
            (build / 'one.o').write_bytes(b'object')
            (build / 'libz3.so').write_bytes(b'library')
            _, inputs = link_command(['c++', 'one.o', '-o', 'vtest', '-L' + str(build), '-lz3'],
                                     build, Path('/output/probe'), [])
            self.assertIn(build / 'libz3.so', inputs)

    def test_link_uses_static_library_in_earlier_search_directory(self):
        with tempfile.TemporaryDirectory() as temporary:
            build = Path(temporary)
            early, late = build / 'early', build / 'late'
            early.mkdir()
            late.mkdir()
            (build / 'one.o').write_bytes(b'object')
            (early / 'libprobe.a').write_bytes(b'archive')
            (late / 'libprobe.so').write_bytes(b'library')
            _, inputs = link_command(['c++', 'one.o', '-o', 'vtest', '-L' + str(early), '-L' + str(late), '-lprobe'],
                                     build, Path('/output/probe'), [])
            self.assertIn(early / 'libprobe.a', inputs)
            self.assertNotIn(late / 'libprobe.so', inputs)

    def test_relative_driver_is_resolved_from_recorded_compile_directory(self):
        with tempfile.TemporaryDirectory() as temporary:
            cwd = Path(temporary)
            (cwd / 'tools').mkdir()
            (cwd / 'tools/g++').write_text('compiler')
            self.assertEqual(resolve_driver('tools/g++', cwd), cwd / 'tools/g++')

    def test_environment_is_restored_even_when_execution_fails(self):
        with patch.dict(os.environ, {'DEPENDENCIES_OUTPUT': '/baseline/dependencies', 'GCOV_PREFIX': '/old/counters'}):
            with self.assertRaisesRegex(ValueError, 'stop'):
                with execution_environment(environment_policy()):
                    self.assertNotIn('DEPENDENCIES_OUTPUT', os.environ)
                    self.assertEqual(os.environ['GCOV_PREFIX'], '/old/counters')
                    raise ValueError('stop')
            self.assertEqual(os.environ['DEPENDENCIES_OUTPUT'], '/baseline/dependencies')
            self.assertEqual(os.environ['GCOV_PREFIX'], '/old/counters')

    @unittest.skipUnless(shutil.which('c++'), 'C++ compiler unavailable')
    def test_actual_compile_leaves_baseline_directory_untouched(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            baseline, output = root / 'baseline', root / 'output'
            baseline.mkdir()
            output.mkdir()
            source = output / 'probe.cpp'
            source.write_text('int probe() { return 7; }\n')
            command = compile_command(['c++', '-g', '-MD', '-o', 'old.o', '-c', 'old.cpp'], source, output / 'probe.o', 'Probe')
            with patch.dict(os.environ, {'DEPENDENCIES_OUTPUT': str(baseline / 'unexpected.d')}):
                with execution_environment(environment_policy()):
                    subprocess.run(command, cwd=baseline, check=True, capture_output=True)
            self.assertEqual(list(baseline.iterdir()), [])
            self.assertTrue((output / 'probe.o').is_file())
            self.assertTrue((output / 'probe.o.d').is_file())

    def test_counter_inventory_detects_new_modified_and_removed_counters(self):
        with tempfile.TemporaryDirectory() as temporary:
            build = Path(temporary)
            old = build / 'old.gcda'
            old.write_bytes(b'old')
            before = counter_snapshot(build)
            old.write_bytes(b'changed')
            (build / 'new.gcda').write_bytes(b'new')
            after = counter_snapshot(build)
            self.assertNotEqual(before, after)
            self.assertEqual(changed_inputs(before), [str(old)])
            old.unlink()
            self.assertEqual(changed_inputs(before), [str(old)])

    def test_mixed_instrumented_objects_are_rejected_before_probe_execution(self):
        for hook in ('__gcov_init', '__llvm_profile_runtime', '__asan_init', '__ubsan_handle_type_mismatch_v1', 'mcount'):
            result = SimpleNamespace(returncode=0, stdout=' U ' + hook + '\n', stderr='')
            with self.subTest(hook=hook), patch('api_probes.shutil.which', return_value='/usr/bin/nm'), patch('api_probes.subprocess.run', return_value=result):
                with self.assertRaisesRegex(ValueError, 'noninstrumented Debug objects'):
                    reject_instrumented_objects([Path('/build/mixed.o')])


class ApiProbeClassificationTests(unittest.TestCase):
    def result(self, **changes):
        return {'outcome': 'fail', 'reason': 'memory error', 'wall_timeout': True,
                'valgrind_errors': [], 'sanitizer_messages': [], **changes}

    def test_timeout_alone_is_api_inconclusive(self):
        result = classify_api(self.result(outcome='inconclusive', reason='wall timeout'))
        self.assertEqual(result['api_outcome'], 'inconclusive')
        self.assertEqual(result['outcome'], 'inconclusive')

    def test_timeout_with_only_leaks_does_not_claim_an_access_error(self):
        result = classify_api(self.result(valgrind_errors=[{'kind': 'Leak_DefinitelyLost'}]))
        self.assertEqual(result['api_outcome'], 'inconclusive')
        self.assertEqual(result['outcome'], 'fail')
        self.assertEqual(result['access_errors'], [])

    def test_timeout_cannot_hide_actual_access_or_sanitizer_errors(self):
        access = classify_api(self.result(valgrind_errors=[{'kind': 'InvalidRead'}]))
        sanitizer = classify_api(self.result(sanitizer_messages=['ERROR: AddressSanitizer: heap-use-after-free']))
        self.assertEqual(access['api_outcome'], 'fail')
        self.assertEqual(sanitizer['api_outcome'], 'fail')

    def test_wrong_api_count_remains_failure(self):
        result = classify_api(self.result(wall_timeout=False, reason='missing expected count'))
        self.assertEqual(result['api_outcome'], 'fail')
        self.assertEqual(result['api_reason'], 'missing expected count')


if __name__ == '__main__':
    unittest.main()
