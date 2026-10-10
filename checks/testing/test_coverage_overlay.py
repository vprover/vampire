import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

from coverage_overlay import (capture, compare_metrics, inventory, prepare, run_overlay,
                              sha256, trace_metrics, verify_original, verify_overlay_notes)


def trace(source, *, line=3, hit=0, alias='f', branch='0', grouped=True):
    functions = f'FNL:0,2,5\nFNA:0,{hit},{alias}\n' if grouped else f'FN:2,5,{alias}\nFNDA:{hit},{alias}\n'
    return (f'TN:\nSF:{source}\n{functions}FNF:1\nFNH:{int(hit > 0)}\n'
            f'DA:{line},{hit}\nLF:1\nLH:{int(hit > 0)}\n'
            f'BRDA:{line},f0,{branch},{hit}\nBRF:1\nBRH:{int(hit > 0)}\nend_of_record\n')


class CoverageOverlayTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.source = self.root / 'source'
        self.source.mkdir()
        self.code = self.source / 'sample.cpp'
        self.code.write_text('int f() { return 0; }\n')
        self.build = self.root / 'build'
        self.build.mkdir()
        (self.build / 'sample.gcno').write_bytes(b'notes')
        (self.build / 'sample.gcda').write_bytes(b'old counters')
        self.baseline = self.root / 'baseline.info'
        self.baseline.write_text(trace(self.code))
        self.output = self.root / 'overlay'

    def prepared(self):
        return prepare(self.build, self.source, self.output, self.baseline)

    def metrics(self, **kwargs):
        path = self.root / 'other.info'
        path.write_text(trace(self.code, **kwargs))
        return trace_metrics(path)

    def test_gains_preserve_exact_denominator(self):
        before = trace_metrics(self.baseline)
        delta = compare_metrics(before, self.metrics(hit=5))
        self.assertEqual({key: value['new_hit'] for key, value in delta.items()},
                         {'lines': 1, 'functions': 1, 'function_groups': 1, 'branches': 1})

    def test_equal_totals_do_not_hide_changed_line_function_or_branch(self):
        for changed in ({'line': 4}, {'alias': 'different'}, {'branch': '1'}):
            with self.subTest(changed=changed), self.assertRaisesRegex(ValueError, 'denominator'):
                compare_metrics(trace_metrics(self.baseline), self.metrics(**changed))

    def test_hit_regression_rejected(self):
        with self.assertRaisesRegex(ValueError, 'lost'):
            compare_metrics(self.metrics(hit=1), trace_metrics(self.baseline))

    def test_repeated_branch_labels_preserve_each_occurrence(self):
        data = self.baseline.read_text().replace('BRF:1', 'BRDA:3,f0,0,2\nBRF:2').replace('BRH:0', 'BRH:1')
        self.baseline.write_text(data)
        branches = trace_metrics(self.baseline)['branches']
        self.assertEqual(len(branches), 2)
        self.assertEqual(sum(branches.values()), 1)
        self.assertEqual({key[-1] for key in branches}, {0, 1})

    def test_legacy_and_grouped_function_formats_agree(self):
        self.assertEqual(trace_metrics(self.baseline), self.metrics(grouped=False))

    def test_malformed_trace_and_inconsistent_totals_rejected(self):
        for content in (self.baseline.read_text().replace('end_of_record\n', ''),
                        self.baseline.read_text().replace('LF:1', 'LF:2'),
                        self.baseline.read_text().replace('FNA:0,', 'FNA:9,')):
            self.baseline.write_text(content)
            with self.assertRaises(ValueError):
                trace_metrics(self.baseline)

    def test_prepare_copies_notes_without_old_counters_or_links(self):
        metadata = self.prepared()
        notes = Path(metadata['note_root']) / 'sample.gcno'
        self.assertEqual(notes.read_bytes(), b'notes')
        self.assertNotEqual(notes.stat().st_ino, (self.build / 'sample.gcno').stat().st_ino)
        self.assertFalse(list(self.output.rglob('*.gcda')))
        self.assertEqual((self.build / 'sample.gcda').read_bytes(), b'old counters')
        self.assertEqual(metadata['environment']['GCOV_PREFIX_STRIP'], '0')

    def test_existing_and_nested_output_rejected(self):
        for output in (self.build / 'overlay', self.root, self.baseline):
            with self.subTest(output=output), self.assertRaises(ValueError):
                prepare(self.build, self.source, output, self.baseline)

    def test_counter_changes_and_additions_rejected(self):
        metadata = self.prepared()
        (self.build / 'new.gcda').write_bytes(b'new')
        with self.assertRaisesRegex(ValueError, 'gcda'):
            verify_original(metadata)
        (self.build / 'new.gcda').unlink()
        (self.build / 'sample.gcda').write_bytes(b'changed')
        with self.assertRaisesRegex(ValueError, 'gcda'):
            verify_original(metadata)

    def test_source_changes_rejected(self):
        metadata = self.prepared()
        self.code.write_text('changed source')
        with self.assertRaisesRegex(ValueError, 'immutable input'):
            verify_original(metadata)

    def test_symlink_into_original_build_rejected_before_execution(self):
        metadata = self.prepared()
        note_root = Path(metadata['note_root'])
        shutil.rmtree(note_root)
        note_root.symlink_to(self.build, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'symbolic links'):
            run_overlay(self.output, [sys.executable, '-c', 'raise SystemExit(90)'])

    def test_orphan_counter_rejected(self):
        metadata = self.prepared()
        (Path(metadata['note_root']) / 'orphan.gcda').write_bytes(b'counter')
        with self.assertRaisesRegex(ValueError, 'matching copied note'):
            verify_overlay_notes(metadata)

    def test_command_inherits_redirection_and_preserves_nonzero_exit(self):
        metadata = self.prepared()
        command = [sys.executable, '-c', 'import os; print(os.environ["GCOV_PREFIX"]); raise SystemExit(7)']
        result = run_overlay(self.output, command)
        self.assertEqual(result['exit'], 7)
        self.assertTrue(result['original_inputs_unchanged'])
        self.assertEqual((Path(result['artifacts']) / 'stdout.log').read_text().strip(), metadata['environment']['GCOV_PREFIX'])

    def test_original_mutation_by_command_is_reported_and_preserved(self):
        self.prepared()
        command = [sys.executable, '-c', 'from pathlib import Path; import sys; Path(sys.argv[1]).write_bytes(b"changed")', str(self.build / 'sample.gcda')]
        with self.assertRaisesRegex(ValueError, 'original .gcda'):
            run_overlay(self.output, command)
        saved = json.loads((self.output / 'overlay.json').read_text())
        self.assertFalse(saved['runs'][0]['original_inputs_unchanged'])
        self.assertEqual((self.build / 'sample.gcda').read_bytes(), b'changed')

    def test_capture_refuses_empty_execution(self):
        self.prepared()
        with self.assertRaisesRegex(ValueError, 'no recorded execution counters'):
            capture(self.output)

    def detached_launcher(self, *, exit_normally):
        marker = self.root / 'detached-child-marker'
        child = ('from pathlib import Path; import time; time.sleep(0.8); '
                 f'Path({str(marker)!r}).write_text("survived"); time.sleep(0.1)')
        launcher = ('import subprocess,sys,time; '
                    f'p=subprocess.Popen([sys.executable,"-c",{child!r}],start_new_session=True); '
                    'print(p.pid,flush=True); ' +
                    ('time.sleep(0.05)' if exit_normally else 'time.sleep(5)'))
        return marker, [sys.executable, '-c', launcher]

    def test_timeout_detached_child_blocks_later_run_and_capture(self):
        self.prepared()
        marker, command = self.detached_launcher(exit_normally=False)
        try:
            result = run_overlay(self.output, command, timeout=0.2)
            self.assertEqual(result['status'], 'timeout')
            self.assertFalse(result['counter_processes_quiescent'])
            self.assertTrue(result['remaining_counter_processes'])
            self.assertFalse(marker.exists())
            with self.assertRaisesRegex(ValueError, 'interrupted or abnormal'):
                capture(self.output)
            with self.assertRaisesRegex(ValueError, 'interrupted or abnormal'):
                run_overlay(self.output, [sys.executable, '-c', 'pass'])
        finally:
            # The child owns no external resources and exits within one second.
            time.sleep(1)
        self.assertTrue(marker.exists())
        # Quiescence later does not silently erase the interrupted-run history.
        with self.assertRaisesRegex(ValueError, 'interrupted or abnormal'):
            capture(self.output)

    def test_normal_launcher_exit_with_detached_child_is_not_finalized(self):
        self.prepared()
        marker, command = self.detached_launcher(exit_normally=True)
        try:
            with self.assertRaisesRegex(ValueError, 'live overlay descendants'):
                run_overlay(self.output, command, timeout=2)
            saved = json.loads((self.output / 'overlay.json').read_text())
            self.assertEqual(saved['runs'][0]['status'], 'error')
            self.assertFalse(saved['runs'][0]['counter_processes_quiescent'])
            with self.assertRaisesRegex(ValueError, 'interrupted or abnormal'):
                capture(self.output)
        finally:
            time.sleep(1)
        self.assertTrue(marker.exists())

    def test_interrupted_record_blocks_execution_before_any_new_artifact(self):
        metadata = self.prepared()
        for status in ('running', 'timeout', 'error'):
            metadata['runs'] = [{'status': status}]
            (self.output / 'overlay.json').write_text(json.dumps(metadata))
            with self.subTest(status=status):
                with self.assertRaisesRegex(ValueError, 'interrupted or abnormal'):
                    run_overlay(self.output, [sys.executable, '-c', 'pass'])
                with self.assertRaisesRegex(ValueError, 'interrupted or abnormal'):
                    capture(self.output)
                self.assertFalse((self.output / 'runs').exists())
                self.assertFalse((self.output / 'capture').exists())

    def test_live_inherited_environment_blocks_an_otherwise_idle_overlay(self):
        metadata = self.prepared()
        child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(0.8)'],
                                 env={**os.environ, **metadata['environment']}, start_new_session=True)
        try:
            with self.assertRaisesRegex(ValueError, 'counter processes are still alive'):
                capture(self.output)
            with self.assertRaisesRegex(ValueError, 'counter processes are still alive'):
                run_overlay(self.output, [sys.executable, '-c', 'pass'])
        finally:
            child.wait(timeout=3)

    def test_wall_clock_shift_cannot_hide_a_counter_writer(self):
        from coverage_overlay import counter_writers
        metadata = self.prepared()
        metadata['created_utc'] = '2099-01-01T00:00:00+00:00'
        process = self.root / '424242'
        process.mkdir()
        fields = ['S', '1'] + ['0'] * 17 + ['100']
        (process / 'stat').write_text('424242 (fixture) ' + ' '.join(fields))
        (process / 'environ').write_bytes(('GCOV_PREFIX=' + metadata['environment']['GCOV_PREFIX']).encode() + b'\0')
        with patch.object(Path, 'iterdir', return_value=iter([process])):
            self.assertEqual(counter_writers(metadata), [{'pid': 424242, 'start_ticks': '100'}])

    def test_proc_exit_permission_race_does_not_block(self):
        from coverage_overlay import counter_writers
        metadata = self.prepared()
        metadata['created_utc'] = '1970-01-01T00:00:00+00:00'
        process = self.root / '424242'
        process.mkdir()
        fields = ['S', '1'] + ['0'] * 17 + ['100']
        (process / 'stat').write_text('424242 (fixture) ' + ' '.join(fields))
        original_read_bytes = Path.read_bytes
        def disappear(path):
            if path == process / 'environ':
                (process / 'stat').unlink()
                raise PermissionError('exiting')
            return original_read_bytes(path)
        with patch.object(Path, 'iterdir', return_value=iter([process])), patch.object(Path, 'read_bytes', disappear):
            self.assertEqual(counter_writers(metadata), [])

    def test_live_unreadable_process_still_fails_closed(self):
        from coverage_overlay import counter_writers
        metadata = self.prepared()
        metadata['created_utc'] = '1970-01-01T00:00:00+00:00'
        process = self.root / '424242'
        process.mkdir()
        fields = ['S', '1'] + ['0'] * 17 + ['100']
        (process / 'stat').write_text('424242 (fixture) ' + ' '.join(fields))
        original_read_bytes = Path.read_bytes
        def unreadable(path):
            if path == process / 'environ':
                raise PermissionError('still alive')
            return original_read_bytes(path)
        with patch.object(Path, 'iterdir', return_value=iter([process])), patch.object(Path, 'read_bytes', unreadable):
            with self.assertRaisesRegex(ValueError, 'cannot verify counter-process quiescence'):
                counter_writers(metadata)

    def test_transient_environment_permissions_are_retried_without_hiding_writer(self):
        from coverage_overlay import counter_writers
        metadata = self.prepared()
        process = self.root / '424242'
        process.mkdir()
        fields = ['S', '1'] + ['0'] * 17 + ['100']
        (process / 'stat').write_text('424242 (fixture) ' + ' '.join(fields))
        original = Path.read_bytes
        for has_prefix in (False, True):
            attempts = []
            def transient(path):
                if path != process / 'environ': return original(path)
                attempts.append(1)
                if len(attempts) <= 2: raise PermissionError('exec transition')
                return (('GCOV_PREFIX=' + metadata['environment']['GCOV_PREFIX']).encode() + b'\0') if has_prefix else b'OTHER=1\0'
            with self.subTest(has_prefix=has_prefix), patch.object(Path, 'iterdir', return_value=iter([process])), patch.object(Path, 'read_bytes', transient):
                writers = counter_writers(metadata)
            self.assertEqual(len(attempts), 3)
            self.assertEqual(writers, [{'pid': 424242, 'start_ticks': '100'}] if has_prefix else [])

    def test_environment_retry_has_a_bound_and_never_accepts_an_opaque_process(self):
        from coverage_overlay import counter_writers
        metadata = self.prepared()
        process = self.root / '424242'
        process.mkdir()
        fields = ['S', '1'] + ['0'] * 17 + ['100']
        (process / 'stat').write_text('424242 (fixture) ' + ' '.join(fields))
        attempts = []
        original = Path.read_bytes
        def opaque(path):
            if path != process / 'environ': return original(path)
            attempts.append(1)
            raise PermissionError('persistent')
        with patch.object(Path, 'iterdir', return_value=iter([process])), patch.object(Path, 'read_bytes', opaque):
            with self.assertRaisesRegex(ValueError, 'cannot verify counter-process quiescence'):
                counter_writers(metadata)
        self.assertEqual(len(attempts), 4)

    def test_environment_retry_rechecks_identity_before_reading_again(self):
        from coverage_overlay import process_environment
        process = self.root / '424242'
        process.mkdir()
        fields = ['S', '1'] + ['0'] * 17 + ['100']
        (process / 'stat').write_text('424242 (fixture) ' + ' '.join(fields))
        attempts = []
        original = Path.read_bytes
        def replaced(path):
            if path != process / 'environ': return original(path)
            attempts.append(1)
            fields[-1] = '101'
            (process / 'stat').write_text('424242 (replacement) ' + ' '.join(fields))
            raise PermissionError('identity changed')
        with patch.object(Path, 'read_bytes', replaced):
            self.assertIsNone(process_environment(process, '100'))
        self.assertEqual(len(attempts), 1)

    def login_helper_fixture(self):
        proc = self.root / 'proc-fixture'
        child, parent = proc / '111', proc / '110'
        child.mkdir(parents=True, exist_ok=True)
        parent.mkdir(exist_ok=True)
        uid = os.geteuid()
        group = f'/user.slice/user-{uid}.slice/user@{uid}.service'
        def stat(path, comm, parent_pid, started):
            fields = ['S', str(parent_pid)] + ['0'] * 17 + [str(started)]
            (path / 'stat').write_text(f'{path.name} ({comm}) ' + ' '.join(fields))
        stat(child, '(sd-pam)', 110, 101)
        stat(parent, 'systemd', 1, 100)
        (child / 'cmdline').write_bytes(b'(sd-pam)\0')
        (parent / 'cmdline').write_bytes(b'/usr/lib/systemd/systemd\0--user\0')
        for path in (child, parent):
            (path / 'cgroup').write_text('0::' + group + '/init.scope\n')
        properties = ('ActiveState=active\nSubState=running\nMainPID=110\n'
                      'ExecStart={ path=/usr/lib/systemd/systemd ; argv[]=/usr/lib/systemd/systemd --user ; pid=110 ; }\n'
                      'ControlGroup=' + group + '\n')
        return child, parent, properties

    @unittest.skipUnless(Path('/usr/lib/systemd/systemd').is_file(), 'systemd executable is required')
    def test_login_helper_requires_service_manager_attestation(self):
        from coverage_overlay import login_helper_attestation
        child, _, properties = self.login_helper_fixture()
        with patch('coverage_overlay.subprocess.run', return_value=subprocess.CompletedProcess([], 0, properties, '')):
            result = login_helper_attestation(child, '101')
        self.assertIsNotNone(result)
        self.assertEqual(result['process']['pid'], 111)
        self.assertEqual(result['parent']['pid'], 110)
        self.assertTrue(result['configured_executable_sha256'])

    @unittest.skipUnless(Path('/usr/lib/systemd/systemd').is_file(), 'systemd executable is required')
    def test_user_manager_requires_its_own_attested_main_pid(self):
        from coverage_overlay import login_helper_attestation
        _, parent, properties = self.login_helper_fixture()
        with patch('coverage_overlay.subprocess.run', return_value=subprocess.CompletedProcess([], 0, properties, '')):
            result = login_helper_attestation(parent, '100')
        self.assertEqual(result['kind'], 'systemd-user-manager')
        with patch('coverage_overlay.subprocess.run', return_value=subprocess.CompletedProcess([], 0,
                properties.replace('MainPID=110', 'MainPID=999'), '')):
            self.assertIsNone(login_helper_attestation(parent, '100'))

    def test_spoofed_login_helper_argv_is_not_exempt(self):
        from coverage_overlay import login_helper_attestation
        child, parent, _ = self.login_helper_fixture()
        (parent / 'cmdline').write_bytes(b'/usr/lib/systemd/systemd\0--user\0--spoof\0')
        with patch('coverage_overlay.subprocess.run') as manager:
            self.assertIsNone(login_helper_attestation(child, '101'))
            manager.assert_not_called()

    @unittest.skipUnless(Path('/usr/lib/systemd/systemd').is_file(), 'systemd executable is required')
    def test_service_pid_and_cgroup_mismatch_are_not_exempt(self):
        from coverage_overlay import login_helper_attestation
        for change in ('manager-pid', 'cgroup'):
            child, _, properties = self.login_helper_fixture()
            if change == 'manager-pid':
                properties = properties.replace('MainPID=110', 'MainPID=999')
            else:
                (child / 'cgroup').write_text('0::/unrelated\n')
            with self.subTest(change=change), patch('coverage_overlay.subprocess.run',
                    return_value=subprocess.CompletedProcess([], 0, properties, '')):
                self.assertIsNone(login_helper_attestation(child, '101'))

    @unittest.skipUnless(Path('/usr/lib/systemd/systemd').is_file(), 'systemd executable is required')
    def test_service_attestation_rechecks_pid_start_after_manager_query(self):
        from coverage_overlay import login_helper_attestation
        child, _, properties = self.login_helper_fixture()
        def replace_pid(*args, **kwargs):
            (child / 'stat').write_text((child / 'stat').read_text().rsplit(' ', 1)[0] + ' 999')
            return subprocess.CompletedProcess([], 0, properties, '')
        with patch('coverage_overlay.subprocess.run', side_effect=replace_pid):
            self.assertIsNone(login_helper_attestation(child, '101'))

    @unittest.skipUnless(shutil.which('gcc'), 'GCC is needed for real counter relocation')
    def test_real_gcc_runtime_uses_new_counter_tree(self):
        (self.build / 'sample.gcno').unlink()
        (self.build / 'sample.gcda').unlink()
        code = self.source / 'counter.c'
        code.write_text('int main(int argc, char **argv) { return argc > 1 ? 0 : 1; }\n')
        binary = self.build / 'counter'
        subprocess.run(['gcc', '--coverage', str(code), '-o', str(binary)], check=True)
        subprocess.run([str(binary), 'baseline'], check=True)
        before = inventory(self.build, '.gcda')
        self.assertTrue(before)
        metadata = self.prepared()
        result = run_overlay(self.output, [str(binary), 'overlay'])
        self.assertEqual(result['exit'], 0)
        self.assertEqual(inventory(self.build, '.gcda'), before)
        self.assertEqual(inventory(Path(metadata['note_root']), '.gcda').keys(), before.keys())
        verify_overlay_notes(metadata)


    def raw_document(self, count=1):
        return {'current_working_directory': str(self.source), 'files': [{
            'file': str(self.code),
            'functions': [{'name': 'f', 'start_line': 1, 'end_line': 2, 'execution_count': count}],
            'lines': [{'line_number': 1, 'function_name': 'f', 'count': count,
                       'branches': [{'source_block_id': 2, 'destination_block_id': 3,
                                     'throw': False, 'fallthrough': True, 'count': count}]}]}]}

    def test_invalid_raw_counts_identify_the_kind_source_and_edge(self):
        from coverage_overlay import raw_object_metrics
        for kind in ('lines', 'functions', 'branches'):
            for count in (-1, 1.5, True, None, '1'):
                doc = self.raw_document()
                record = doc['files'][0]
                if kind == 'functions':
                    record['functions'][0]['execution_count'] = count
                elif kind == 'lines':
                    record['lines'][0]['count'] = count
                else:
                    record['lines'][0]['branches'][0]['count'] = count
                with self.subTest(kind=kind, count=count):
                    with self.assertRaises(ValueError) as raised:
                        raw_object_metrics(doc, self.source)
                    message = str(raised.exception)
                    self.assertIn('invalid raw gcov ' + kind + ' count ' + repr(count), message)
                    self.assertIn(str(self.code), message)
                    self.assertIn("'f'", message)
                    if kind == 'branches':
                        self.assertIn(', 1, 2, 3, False, True, 0)', message)
        metrics = raw_object_metrics(self.raw_document(0), self.source)
        self.assertTrue(all(count == 0 for rows in metrics.values() for count in rows.values()))

    def test_raw_merge_requires_exact_sum_not_only_no_lost_hits(self):
        from coverage_overlay import raw_object_metrics, compare_raw_object
        def metrics(count): return raw_object_metrics(self.raw_document(count), self.source)
        result = compare_raw_object(metrics(2), metrics(3), metrics(5))
        self.assertEqual(result['branches']['new_hit'], 0)
        for incorrect in (2, 4, 6):
            with self.subTest(incorrect=incorrect), self.assertRaisesRegex(ValueError, 'exact counter sum'):
                compare_raw_object(metrics(2), metrics(3), metrics(incorrect))

    def test_raw_merge_rejects_changed_function_or_block_identity(self):
        from coverage_overlay import raw_object_metrics, compare_raw_object
        before = raw_object_metrics(self.raw_document(), self.source)
        for mode in ('function', 'block'):
            doc = self.raw_document()
            if mode == 'function': doc['files'][0]['functions'][0]['name'] = 'g'
            else: doc['files'][0]['lines'][0]['branches'][0]['destination_block_id'] = 4
            with self.subTest(mode=mode), self.assertRaisesRegex(ValueError, 'identities changed'):
                compare_raw_object(before, raw_object_metrics(doc, self.source), raw_object_metrics(self.raw_document(2), self.source))

    def test_raw_parallel_arcs_keep_pinned_note_ordinals(self):
        from coverage_overlay import raw_object_metrics
        doc = self.raw_document()
        branches = doc['files'][0]['lines'][0]['branches']
        branches.append(dict(branches[0], count=2))
        result = raw_object_metrics(doc, self.source)['branches']
        self.assertEqual(sorted(result.values()), [1, 2])
        self.assertEqual({key[-1] for key in result}, {0, 1})

    @unittest.skipUnless(shutil.which('gcc') and shutil.which('gcov-tool'), 'GCC merge tools are needed')
    def test_real_gcov_merge_preserves_old_tree_and_matches_every_raw_counter(self):
        from coverage_overlay import verify_raw_union
        (self.build / 'sample.gcno').unlink()
        (self.build / 'sample.gcda').unlink()
        code = self.source / 'counter.c'
        code.write_text('int main(int argc, char **argv) {\n if (argc > 1) return 0;\n return 1;\n}\n')
        binary = self.build / 'counter'
        subprocess.run(['gcc', '--coverage', str(code), '-o', str(binary)], check=True)
        subprocess.run([str(binary), 'baseline'], check=True)
        metadata = self.prepared()
        run_overlay(self.output, [str(binary)])
        baseline = self.root / 'copied-baseline'
        baseline.mkdir()
        for suffix in ('.gcno', '.gcda'):
            for filename in self.build.glob('*' + suffix): shutil.copyfile(filename, baseline / filename.name)
        merged = self.root / 'merged'
        subprocess.run(['gcov-tool', 'merge', str(baseline), metadata['note_root'], '-o', str(merged)], check=True)
        for filename in baseline.glob('*.gcno'): shutil.copyfile(filename, merged / filename.name)
        target = self.root / 'verified'
        target.mkdir()
        result = verify_raw_union(metadata, target, baseline, Path(metadata['note_root']), merged)
        self.assertTrue(result['exact_raw_counter_sum'])
        self.assertGreater(result['metrics']['branches']['new_hit'], 0)
        verify_original(metadata)
        next(merged.glob('*.gcda')).write_bytes(b'corrupt copied counter')
        failed = self.root / 'failed-verification'
        failed.mkdir()
        with self.assertRaises(ValueError):
            verify_raw_union(metadata, failed, baseline, Path(metadata['note_root']), merged)
        verify_original(metadata)


    def test_prepare_and_run_record_exact_helper_bytes(self):
        metadata = self.prepared()
        saved = metadata['prepare_implementation']
        self.assertEqual(sha256(saved['snapshot']), saved['sha256'])
        result = run_overlay(self.output, [sys.executable, '-c', 'pass'])
        self.assertEqual(result['implementation'], saved)

    def test_hard_link_to_original_counter_rejected_before_execution(self):
        metadata = self.prepared()
        os.link(self.build / 'sample.gcda', Path(metadata['note_root']) / 'sample.gcda')
        with self.assertRaisesRegex(ValueError, 'hard links'):
            run_overlay(self.output, [sys.executable, '-c', 'raise SystemExit(90)'])

    def test_error_output_redirection_changes_rejected(self):
        metadata = self.prepared()
        metadata['environment']['GCOV_ERROR_FILE'] = str(self.root / 'other-errors.log')
        with self.assertRaisesRegex(ValueError, 'relocation metadata'):
            verify_overlay_notes(metadata)


    def test_gcov_diagnostic_cannot_hide_an_existing_unreadable_counter(self):
        from coverage_overlay import validate_gcov_diagnostics
        note = self.build / 'sample.gcno'
        warning = (str(note.with_suffix('.gcda')) + ':cannot open data file, assuming not executed\n').encode()
        with self.assertRaisesRegex(ValueError, 'diagnostics need review'):
            validate_gcov_diagnostics(warning, note, self.raw_document())
        note.with_suffix('.gcda').unlink()
        validate_gcov_diagnostics(warning, note, self.raw_document())
        with self.assertRaisesRegex(ValueError, 'diagnostics need review'):
            validate_gcov_diagnostics(b'profile checksum mismatch\n', note, self.raw_document())


if __name__ == '__main__':
    unittest.main()
