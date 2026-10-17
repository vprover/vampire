#!/usr/bin/env python3
import contextlib
import io
import fcntl
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from report import TerminalReporter, failure_detail, section, table, read_results, main


class TerminalOutput(unittest.TestCase):
    def test_parser_is_a_separate_section(self):
        self.assertEqual(section({'name': 'corpus/001-test', 'source': 'parse/test.p'}), 'Parser')

    def test_inconclusive_does_not_count_as_pass(self):
        cases = [{'name': f'generated/cnf-{i}'} for i in range(3)]
        results = [{**cases[0], 'outcome': 'pass'}, {**cases[1], 'outcome': 'inconclusive'}]
        output = table(cases, results)
        self.assertRegex(output, r'Generated CNF\s+2/3\s+1\s+0\s+1')
        self.assertRegex(output, r'TOTAL\s+2/3\s+1\s+0\s+1')

    def test_failure_has_test_input_answer_and_logs(self):
        result = {'name': 'generated/cnf-7', 'source': 'inputs/cnf-7.p', 'outcome': 'fail',
                  'reason': 'wrong answer', 'check': 'szs', 'expected': 'Unsatisfiable',
                  'statuses': ['Satisfiable'], 'artifacts': '/tmp/case-7'}
        output = failure_detail(result)
        for value in ('generated/cnf-7', 'inputs/cnf-7.p', 'expected Unsatisfiable',
                      'observed Satisfiable', '/tmp/case-7/'):
            self.assertIn(value, output)

    def test_memory_report_points_to_stack_location(self):
        with tempfile.TemporaryDirectory() as temporary:
            xml = Path(temporary) / 'valgrind.xml'
            xml.write_text('<valgrindoutput><error><kind>InvalidRead</kind><stack><frame>'
                           '<dir>/src/Kernel</dir><file>Term.cpp</file><line>123</line>'
                           '</frame></stack></error></valgrindoutput>')
            result = {'name': 'unit/Term', 'outcome': 'fail', 'reason': 'memory error',
                      'valgrind_errors': [{'kind': 'InvalidRead', 'file': str(xml)}]}
            output = failure_detail(result)
            self.assertIn('/src/Kernel/Term.cpp:123', output)
            self.assertIn('InvalidRead=1', output)

    def test_resumed_results_are_not_double_counted(self):
        cases = [{'name': 'unit/A'}, {'name': 'unit/B'}]
        previous = [{**cases[0], 'outcome': 'pass'}]
        failed = {**cases[1], 'outcome': 'fail', 'reason': 'exit 2'}
        with tempfile.TemporaryDirectory() as temporary, contextlib.redirect_stdout(io.StringIO()) as stream:
            reporter = TerminalReporter(cases, previous, Path(temporary))
            reporter.record(failed)
            reporter.finish()
            self.assertRegex(stream.getvalue(), r'TOTAL\s+2/2\s+1\s+1\s+0')
            self.assertIn('unit/B', (Path(temporary) / 'failures.txt').read_text())


class SavedJournalIntegrity(unittest.TestCase):
    def record(self, name='unit/A', outcome='pass'):
        return {'name': name, 'outcome': outcome}

    def test_only_an_active_unterminated_tail_is_tolerated(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)
            (output / 'results.jsonl').write_text(json.dumps(self.record()) + '\n{"name":')
            with (output / '.run.lock').open('a') as lock:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                self.assertEqual(read_results(output), [self.record()])
            with self.assertRaisesRegex(ValueError, 'invalid result journal record'):
                read_results(output)

    def test_complete_malformed_row_is_rejected_even_with_active_writer(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)
            (output / 'results.jsonl').write_text(json.dumps(self.record()) + '\n{"name":\n')
            with (output / '.run.lock').open('a') as lock:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                with self.assertRaisesRegex(ValueError, 'invalid result journal record'):
                    read_results(output)

    def test_duplicate_unknown_case_and_unknown_outcome_are_rejected(self):
        cases = [{'name': 'unit/A'}]
        examples = [([self.record(), self.record()], 'duplicate result'),
                    ([self.record('unit/B')], 'unknown case'),
                    ([self.record(outcome='skipped')], 'unknown outcome')]
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)
            for records, message in examples:
                with self.subTest(message=message):
                    (output / 'results.jsonl').write_text(''.join(json.dumps(row) + '\n' for row in records))
                    with self.assertRaisesRegex(ValueError, message):
                        read_results(output, cases)

    def test_completed_summary_must_match_journal_failures(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)
            row = self.record(outcome='fail')
            (output / 'results.jsonl').write_text(json.dumps(row) + '\n')
            summary = {'results': [row], 'totals': {'fail': 1}}
            (output / 'summary.json').write_text(json.dumps(summary))
            self.assertEqual(read_results(output, [{'name': 'unit/A'}]), [row])
            summary['totals'] = {'pass': 1}
            (output / 'summary.json').write_text(json.dumps(summary))
            with self.assertRaisesRegex(ValueError, 'summary totals'):
                read_results(output)
            summary = {'results': [self.record()], 'totals': {'pass': 1}}
            (output / 'summary.json').write_text(json.dumps(summary))
            with self.assertRaisesRegex(ValueError, 'summary and result journal differ'):
                read_results(output)

    def test_completed_summary_prevents_live_tail_exception(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)
            (output / 'results.jsonl').write_text('{"name":')
            (output / 'summary.json').write_text('{}')
            with (output / '.run.lock').open('a') as lock:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                with self.assertRaisesRegex(ValueError, 'invalid result journal record'):
                    read_results(output)

    def test_concurrent_completion_is_reread_before_summary_comparison(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)
            journal = output / 'results.jsonl'
            first, second = self.record(), self.record('unit/B', 'fail')
            old_bytes = (json.dumps(first) + '\n').encode()
            journal.write_bytes(old_bytes)
            original_read = Path.read_bytes
            advanced = False
            def read(path):
                nonlocal advanced
                if path == journal and not advanced:
                    advanced = True
                    journal.write_text(json.dumps(first) + '\n' + json.dumps(second) + '\n')
                    (output / 'summary.json').write_text(json.dumps({'results': [first, second], 'totals': {'pass': 1, 'fail': 1}}))
                    return old_bytes
                return original_read(path)
            with patch.object(Path, 'read_bytes', read):
                self.assertEqual(read_results(output), [first, second])

    def test_cli_corruption_is_an_error_with_no_success_table(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)
            (output / 'results.jsonl').write_text('bad record\n')
            stdout, stderr = io.StringIO(), io.StringIO()
            with patch('sys.argv', ['report.py', str(output)]), contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                with self.assertRaises(SystemExit) as raised:
                    main()
            self.assertNotEqual(raised.exception.code, 0)
            self.assertIn('invalid result journal record', stderr.getvalue())
            self.assertNotIn('TOTAL', stdout.getvalue())


if __name__ == '__main__': unittest.main()
