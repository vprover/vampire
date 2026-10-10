"""Recovery preserves completed failures and rejects incompatible evidence."""
import argparse
import contextlib
from dataclasses import asdict
import io
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

import campaign
import run


class CampaignRecovery(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.output = self.root / 'campaign'
        self.identity = {'commit': 'frozen', 'source_sha256': 'source', 'harness_sha256': {'run.py': 'runner'},
                         'options': {'profiles': ['coverage']}}
        self.silence = contextlib.redirect_stdout(io.StringIO())
        self.silence.__enter__()

    def tearDown(self):
        self.silence.__exit__(None, None, None)
        self.temporary.cleanup()

    def create(self, resume=False, identity=None):
        return campaign.Campaign(self.output, identity or self.identity, resume=resume, root=self.root)

    def test_completed_failed_stage_is_never_executed_again(self):
        counter = self.root / 'counter'
        command = [sys.executable, '-c', f"from pathlib import Path; p=Path({str(counter)!r}); p.write_text(p.read_text()+'x' if p.exists() else 'x'); raise SystemExit(7)"]
        first = self.create()
        self.assertFalse(first.stage('reported-failure', command))
        first.finish()
        second = self.create(resume=True)
        self.assertFalse(second.stage('reported-failure', command))
        second.finish()
        self.assertEqual(counter.read_text(), 'x')
        self.assertEqual(len(second.find('reported-failure')['attempts']), 1)

    def test_interrupted_stage_gets_a_new_attempt_and_preserves_partial_output(self):
        first = self.create()
        output = self.output / 'runtime'
        command = [sys.executable, '-c', 'pass']
        with patch.object(campaign.subprocess, 'Popen', side_effect=KeyboardInterrupt):
            with self.assertRaises(KeyboardInterrupt): first.stage('runtime', command, case_output=output)
        output.mkdir()
        (output / 'partial.log').write_text('old evidence')
        first.finish(interrupted=KeyboardInterrupt())
        second = self.create(resume=True)
        self.assertTrue(second.stage('runtime', command, case_output=output))
        self.assertEqual(len(second.find('runtime')['attempts']), 2)
        archived = Path(second.find('runtime')['preserved_partial_outputs'][0])
        self.assertEqual((archived / 'partial.log').read_text(), 'old evidence')
        second.finish()

    def test_interrupted_case_stage_receives_resume_flag(self):
        first = self.create()
        output = self.output / 'cases'
        runner = self.root / 'run.py'
        runner.write_text("import sys; assert '--resume' in sys.argv\n")
        command = [sys.executable, runner, 'run', '--output', output]
        with patch.object(campaign.subprocess, 'Popen', side_effect=KeyboardInterrupt):
            with self.assertRaises(KeyboardInterrupt): first.stage('cases', command, case_output=output)
        output.mkdir()
        (output / 'run.json').write_text('{}')
        self.assertTrue(first.stage('cases', command, case_output=output))
        self.assertIn('--resume', first.find('cases')['attempts'][-1]['command'])
        first.finish()

    def test_changed_source_harness_options_or_commit_refuses_resume(self):
        first = self.create()
        first.finish()
        for key in ('commit', 'source_sha256', 'harness_sha256', 'options'):
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, 'cannot resume'):
                self.create(resume=True, identity={**self.identity, key: 'changed'})

    def test_changed_built_binary_refuses_resume(self):
        binary = self.root / 'binary'
        binary.write_text('original')
        first = self.create()
        first.stage('build', [sys.executable, '-c', 'pass'], binaries=[binary])
        first.finish()
        binary.write_text('changed')
        with self.assertRaisesRegex(ValueError, 'binary changed'): self.create(resume=True)

    def test_interruption_during_evidence_hashing_does_not_mark_stage_complete(self):
        first = self.create()
        with patch.object(campaign, 'evidence_hashes', side_effect=KeyboardInterrupt):
            with self.assertRaises(KeyboardInterrupt): first.stage('cases', [sys.executable, '-c', 'pass'])
        first.finish(interrupted=KeyboardInterrupt())
        saved = json.loads((self.output / 'campaign.json').read_text())
        self.assertEqual(saved['stages'][0]['status'], 'running')
        second = self.create(resume=True)
        self.assertTrue(second.stage('cases', [sys.executable, '-c', 'pass']))
        self.assertEqual(second.find('cases')['attempts'][0]['status'], 'interrupted')
        second.finish()

    def test_missing_build_binary_is_a_saved_failure(self):
        first = self.create()
        self.assertFalse(first.stage('build', [sys.executable, '-c', 'pass'], binaries=[self.root / 'missing']))
        first.finish()
        self.assertEqual(first.find('build')['status'], 'fail')

    def test_changed_completed_results_refuse_resume(self):
        result = self.root / 'result.json'
        first = self.create()
        first.stage('cases', [sys.executable, '-c', f"from pathlib import Path; Path({str(result)!r}).write_text('failure')"], artifacts=[result])
        first.finish()
        result.write_text('{"outcome":"pass"}')
        with self.assertRaisesRegex(ValueError, 'evidence or binary changed'): self.create(resume=True)

    def test_live_campaign_identity_refuses_resume(self):
        first = self.create()
        with self.assertRaisesRegex(ValueError, 'still alive'): self.create(resume=True)
        first.finish()

    def test_changed_raw_diagnostics_refuse_resume(self):
        output = self.output / 'cases'
        first = self.create()
        command = [sys.executable, '-c', f"from pathlib import Path; p=Path({str(output)!r}); p.mkdir(); (p/'stderr.log').write_text('sanitizer report')"]
        first.stage('cases', command, case_output=output)
        first.finish()
        (output / 'stderr.log').write_text('changed')
        with self.assertRaisesRegex(ValueError, 'evidence or binary changed'): self.create(resume=True)

    def test_unrecorded_output_collision_is_rejected(self):
        first = self.create()
        output = self.output / 'cases'
        output.mkdir()
        with self.assertRaisesRegex(ValueError, 'unrecorded stage output'):
            first.stage('cases', [sys.executable, '-c', 'pass'], case_output=output)
        first.finish()

    def test_reset_is_refused_if_coverage_tests_already_started(self):
        first = self.create()
        first.data['stages'].append({'name': 'coverage-all', 'status': 'running'})
        with self.assertRaisesRegex(ValueError, 'coverage tests have started'):
            first.stage('coverage-reset', [sys.executable, '-c', 'pass'])
        first.finish(interrupted=KeyboardInterrupt())

    def test_resume_preserves_coverage_counters_and_does_not_repeat_reset(self):
        build = self.root / 'coverage'
        build.mkdir()
        counters = build / 'solver.gcda'
        counters.write_bytes(b'old counters')
        first = self.create()
        campaign.archive_coverage_counters(first, build)
        reset = [sys.executable, '-c', f"from pathlib import Path; Path({str(counters)!r}).write_bytes(b'')"]
        first.stage('coverage-reset', reset)
        counters.write_bytes(b'new coverage')
        first.finish(interrupted=KeyboardInterrupt())
        archive_hash = run.file_hash(self.output / 'previous-counters.tar.gz')
        second = self.create(resume=True)
        campaign.archive_coverage_counters(second, build)
        second.stage('coverage-reset', reset)
        second.finish()
        self.assertEqual(counters.read_bytes(), b'new coverage')
        self.assertEqual(run.file_hash(self.output / 'previous-counters.tar.gz'), archive_hash)

    def test_empty_or_malformed_coverage_is_rejected(self):
        trace = self.root / 'coverage.info'
        for content in ('', 'SF:source.cpp\n', 'SF:source.cpp\nLF:1\nLH:2\nFNF:0\nFNH:0\nBRF:0\nBRH:0\nend_of_record\n'):
            trace.write_text(content)
            with self.assertRaises(ValueError): campaign.coverage_gaps(trace)


class CaseRecovery(unittest.TestCase):
    def setUp(self):
        run.CANCELLED.clear()
        self.temporary = tempfile.TemporaryDirectory()
        self.output = Path(self.temporary.name)
        self.case = run.Case('case/failed', [sys.executable, '-c', 'raise SystemExit(2)'], str(self.output))
        self.folder = self.output / run.artifact_name(self.case.name)
        self.folder.mkdir(exist_ok=True)
        (self.folder / 'stdout.log').write_text('failed output')
        (self.folder / 'stderr.log').write_text('original diagnostic')
        self.result = {**asdict(self.case), 'outcome': 'fail', 'reason': 'exit 2',
                       'artifacts': str(self.folder), 'evidence_sha256': run.case_evidence_hashes(self.folder)}

    def tearDown(self):
        run.CANCELLED.clear()
        self.temporary.cleanup()

    def disk(self, result=None):
        folder = self.output / run.artifact_name(self.case.name)
        folder.mkdir(exist_ok=True)
        run.atomic_json(folder / 'result.json', self.result if result is None else result)

    def journal(self, raw=None):
        (self.output / 'results.jsonl').write_bytes(raw if raw is not None else (json.dumps(self.result) + '\n').encode())

    def test_journal_and_disk_count_once_and_orphan_result_is_recovered(self):
        self.disk()
        self.assertEqual(run.recover_results(self.output, [self.case])[0], [self.result])
        self.journal()
        self.assertEqual(run.recover_results(self.output, [self.case])[0], [self.result])

    def test_incomplete_tail_is_preserved_but_complete_bad_record_is_rejected(self):
        raw = (json.dumps(self.result) + '\n{"name":').encode()
        self.journal(raw)
        rows, preserved = run.recover_results(self.output, [self.case])
        self.assertEqual(rows, [self.result])
        self.assertEqual(preserved, raw)
        self.journal(b'{broken}\n')
        with self.assertRaises(ValueError): run.recover_results(self.output, [self.case])

    def test_conflict_duplicate_and_changed_case_are_rejected(self):
        self.journal()
        self.disk({**self.result, 'outcome': 'pass'})
        with self.assertRaisesRegex(ValueError, 'disagreement'): run.recover_results(self.output, [self.case])
        self.disk()
        self.journal(((json.dumps(self.result) + '\n') * 2).encode())
        with self.assertRaisesRegex(ValueError, 'duplicate'): run.recover_results(self.output, [self.case])
        self.journal()
        changed = run.Case(**{**asdict(self.case), 'expected': 'changed'})
        with self.assertRaisesRegex(ValueError, 'definition changed'): run.recover_results(self.output, [changed])

    def test_failed_case_is_not_reexecuted_when_pending_case_runs(self):
        marker = self.output / 'executions'
        self.case.command = [sys.executable, '-c', f"from pathlib import Path; Path({str(marker)!r}).write_text('reran'); raise SystemExit(2)"]
        self.result = {**self.result, **asdict(self.case)}
        self.disk()
        self.journal()
        pending = run.Case('case/pending', [sys.executable, '-c', 'pass'], str(self.output))
        rows, _ = run.recover_results(self.output, [self.case, pending])
        args = argparse.Namespace(output=self.output, jobs=1, timeout=2, memcheck=False, z3='z3', asan=False, sanitizer_error_grace=None)
        with contextlib.redirect_stdout(io.StringIO()):
            code = run.execute_cases(args, {'discovery_errors': []}, [self.case, pending], rows)
        self.assertEqual(code, 1)
        self.assertFalse(marker.exists())
        summary = json.loads((self.output / 'summary.json').read_text())
        self.assertEqual(summary['totals'], {'fail': 1, 'pass': 1})
        self.assertTrue(summary['exactly_once_verified'])
        self.assertEqual(len((self.output / 'results.jsonl').read_text().splitlines()), 2)

    def test_old_unhashed_completed_row_is_not_trusted(self):
        legacy = {key: value for key, value in self.result.items() if key != 'evidence_sha256'}
        self.disk(legacy)
        with self.assertRaisesRegex(ValueError, 'lacks raw evidence hashes'):
            run.recover_results(self.output, [self.case])

    def test_raw_log_xml_and_nested_validator_tampering_is_rejected(self):
        for name in ('stdout.log', 'stderr.log', 'valgrind.123.xml',
                     'mode-validation.json', 'validator/result.json'):
            path = self.folder / name
            path.parent.mkdir(exist_ok=True)
            path.write_text('original evidence')
        self.result['evidence_sha256'] = run.case_evidence_hashes(self.folder)
        self.disk()
        self.journal()
        for name in self.result['evidence_sha256']:
            path = self.folder / name
            original = path.read_bytes()
            path.write_bytes(original + b'changed')
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, 'raw evidence changed'):
                run.recover_results(self.output, [self.case])
            path.write_bytes(original)
        self.assertEqual(run.recover_results(self.output, [self.case])[0], [self.result])

    def test_missing_or_added_raw_artifacts_are_rejected(self):
        self.disk()
        stdout = self.folder / 'stdout.log'
        original = stdout.read_bytes()
        stdout.unlink()
        with self.assertRaisesRegex(ValueError, 'raw evidence changed'):
            run.recover_results(self.output, [self.case])
        stdout.write_bytes(original)
        (self.folder / 'extra.log').write_text('unrecorded')
        with self.assertRaisesRegex(ValueError, 'raw evidence changed'):
            run.recover_results(self.output, [self.case])

    def test_evidence_symlink_is_rejected(self):
        self.disk()
        (self.folder / 'linked.log').symlink_to(self.folder / 'stdout.log')
        with self.assertRaisesRegex(ValueError, 'symbolic link'):
            run.recover_results(self.output, [self.case])

    def test_real_case_saves_raw_hashes_and_rejects_later_log_change(self):
        case = run.Case('case/actual', [sys.executable, '-c', "print('proof')"],
                        str(self.output), 'contains', 'proof')
        row = run.run_case(case, self.output, 2, False)
        self.assertEqual(row['outcome'], 'pass')
        self.assertIn('stdout.log', row['evidence_sha256'])
        self.assertIn('stderr.log', row['evidence_sha256'])
        self.assertIn('command.json', row['evidence_sha256'])
        self.assertEqual(run.recover_results(self.output, [case])[0], [row])
        (Path(row['artifacts']) / 'stdout.log').write_text('changed')
        with self.assertRaisesRegex(ValueError, 'raw evidence changed'):
            run.recover_results(self.output, [case])

    def test_saved_input_mutation_refuses_resume_before_recovery(self):
        input_path = self.output / 'input.p'
        input_path.write_text('original')
        args = argparse.Namespace(output=self.output, resume=True)
        metadata = {'arguments': {'output': str(self.output), 'resume': False}, 'commit': 'commit',
                    'source_sha256': 'source', 'harness_sha256': {},
                    'environment': {name: os.environ.get(name) for name in ('ASAN_OPTIONS', 'UBSAN_OPTIONS', 'LSAN_OPTIONS', 'LD_LIBRARY_PATH', 'LD_PRELOAD', 'GCOV_PREFIX', 'GCOV_PREFIX_STRIP', 'GCOV_ERROR_FILE', 'GCOV_EXIT_AT_ERROR')},
                    'binary_sha256': {}, 'input_sha256': {str(input_path): run.file_hash(input_path)}}
        run.atomic_json(self.output / 'run.json', metadata)
        input_path.write_text('changed')
        with patch.object(run, 'checked_output', return_value='commit'), patch.object(run, 'source_fingerprint', return_value='source'), patch.object(run, 'harness_hashes', return_value={}):
            with self.assertRaisesRegex(ValueError, 'input_sha256'): run.validate_resume(args)

    def test_separator_variants_have_distinct_artifact_names(self):
        alias = run.Case(**{**asdict(self.case), 'name': 'case_failed'})
        self.assertNotEqual(run.artifact_name(self.case.name).casefold(), run.artifact_name(alias.name).casefold())
        self.assertEqual(run.recover_results(self.output, [self.case, alias])[0], [])

    def test_case_only_variants_run_and_recover_without_casefold_collisions(self):
        cases = [run.Case(name, [sys.executable, '-c', f'print({name!r})'], str(self.output), 'contains', name)
                 for name in ('options/boundary/time_limit-1d', 'options/boundary/time_limit-1D')]
        results = [run.run_case(case, self.output, 2, False) for case in cases]
        self.assertEqual(len({Path(row['artifacts']).name.casefold() for row in results}), 2)
        self.assertTrue(all(row['outcome'] == 'pass' for row in results))
        for case, row in zip(cases, results):
            self.assertEqual((Path(row['artifacts']) / 'stdout.log').read_text().strip(), case.name)
        recovered, _ = run.recover_results(self.output, cases)
        self.assertEqual({row['name'] for row in recovered}, {case.name for case in cases})

    def test_hash_collision_is_still_rejected_before_execution(self):
        alias = run.Case(**{**asdict(self.case), 'name': 'case_failed'})
        with patch.object(run, 'artifact_name', return_value='forced-collision'):
            with self.assertRaisesRegex(ValueError, 'collide'): run.recover_results(self.output, [self.case, alias])

    def test_cli_signal_then_resume_keeps_completed_failure_once(self):
        repo = self.output / 'repo'
        harness = repo / 'checks/testing'
        harness.mkdir(parents=True)
        for name in ('run.py', 'report.py', 'diagnostics.py', 'unit_output.py'):
            shutil.copyfile(Path(run.__file__).parent / name, harness / name)
        for command in (['git', 'init', '-q', str(repo)], ['git', '-C', str(repo), 'add', '.'],
                        ['git', '-C', str(repo), '-c', 'user.name=Pietro Pellegrino',
                         '-c', 'user.email=72952819+shalashaska117@users.noreply.github.com',
                         'commit', '-qm', 'add recovery fixture']):
            subprocess.run(command, check=True, capture_output=True)
        build = self.output / 'build'
        build.mkdir()
        counter = self.output / 'invocations'
        binary = build / 'vampire'
        binary.write_text(f"#!{sys.executable}\nimport time\nfrom pathlib import Path\np=Path({str(counter)!r})\nn=int(p.read_text()) if p.exists() else 0\np.write_text(str(n+1))\nif n == 1: time.sleep(30)\nprint('% SZS status Satisfiable')\nraise SystemExit(2 if n == 0 else 0)\n")
        binary.chmod(0o755)
        output = self.output / 'results'
        command = [sys.executable, '-B', str(harness / 'run.py'), 'run', '--suite', 'generated',
                   '--limit', '2', '--jobs', '1', '--timeout', '10', '--build', str(build), '--output', str(output)]
        with (self.output / 'initial.log').open('w') as log:
            process = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT)
            try:
                deadline = time.monotonic() + 10
                while time.monotonic() < deadline:
                    if counter.exists() and counter.read_text() == '2': break
                    if process.poll() is not None:
                        self.fail('runner exited before interruption:\n' + (self.output / 'initial.log').read_text(errors='replace'))
                    time.sleep(.05)
                else: self.fail('runner did not reach its second case')
                process.terminate()
                process.wait(timeout=5)
            finally:
                if process.poll() is None:
                    process.kill()
                    process.wait()
        state = json.loads((output / 'run-state.json').read_text())
        self.assertEqual(state['status'], 'interrupted')
        for path in output.rglob('process.json'):
            self.assertFalse(run.process_alive(json.loads(path.read_text())))
        resumed = subprocess.run([*command, '--resume'], capture_output=True, text=True, timeout=10)
        self.assertEqual(resumed.returncode, 1, resumed.stdout + resumed.stderr)
        summary = json.loads((output / 'summary.json').read_text())
        self.assertEqual(summary['totals'], {'fail': 1, 'pass': 1})
        self.assertEqual(counter.read_text(), '3')
        self.assertEqual(len((output / 'results.jsonl').read_text().splitlines()), 2)

    def test_initialized_submodule_tracked_bytes_affect_source_fingerprint(self):
        repo = self.output / 'repo'
        child = repo / 'nested'
        child.mkdir(parents=True)
        (child / 'source.cpp').write_text('original')
        commands = [
            ['git', 'init', '-q', str(repo)], ['git', 'init', '-q', str(child)],
            ['git', '-C', str(child), 'add', 'source.cpp'],
            ['git', '-C', str(child), '-c', 'user.name=Pietro Pellegrino',
             '-c', 'user.email=72952819+shalashaska117@users.noreply.github.com', 'commit', '-qm', 'add source fixture']]
        for command in commands: subprocess.run(command, check=True, capture_output=True)
        head = subprocess.check_output(['git', '-C', str(child), 'rev-parse', 'HEAD'], text=True).strip()
        subprocess.run(['git', '-C', str(repo), 'update-index', '--add', '--cacheinfo', f'160000,{head},nested'], check=True)
        before = run.source_fingerprint(repo)
        (child / 'source.cpp').write_text('changed')
        self.assertNotEqual(before, run.source_fingerprint(repo))

    def test_resolved_shared_library_bytes_are_hashed(self):
        binary = self.output / 'elf'
        library = self.output / 'libz3.so'
        binary.write_bytes(b'\x7fELFfixture')
        library.write_bytes(b'original')
        answer = argparse.Namespace(returncode=0, stdout=f'libz3.so => {library} (0x1234)\n', stderr='')
        with patch.object(run.subprocess, 'run', return_value=answer):
            before = run.binary_hashes([binary])
            library.write_bytes(b'changed')
            after = run.binary_hashes([binary])
        self.assertIn(str(library.resolve()), before)
        self.assertNotEqual(before, after)

    def test_nested_api_fixtures_are_included_in_harness_snapshot_hashes(self):
        fixture = self.output / 'checks/testing/fixtures/api/probe.cpp'
        fixture.parent.mkdir(parents=True)
        fixture.write_text('int main() {}')
        hashes = run.harness_hashes(self.output)
        self.assertEqual(hashes['fixtures/api/probe.cpp'], run.file_hash(fixture))


if __name__ == '__main__': unittest.main()
