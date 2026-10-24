#!/usr/bin/env python3
"""Native subtest reporting must retain failures without inventing completion."""
import contextlib
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import run
from report import TerminalReporter, failure_detail, table
from unit_output import parse_unit_output


OUTPUT = ('Running good... \r\r[  OK  ] good          \n'
          'Running bad... \rCondition at location /source with spaces/tUnit.cpp:42 violated:\n'
          'value == expected\n\r[ FAIL ] bad          \n\n'
          'Tests run: 2\n  - ok   1\t(50.0) %\n  - fail 1\t(50.0) %\n')


class NativeOutputParsing(unittest.TestCase):
    def test_full_suite_with_exit_255_retains_name_and_bound_assertion(self):
        summary = parse_unit_output(OUTPUT, exit_code=255)
        self.assertTrue(summary['complete'], summary)
        self.assertEqual(summary['counts'], {'total': 2, 'passed': 1, 'failed': 1})
        self.assertEqual(summary['passed_names'], ['good'])
        self.assertEqual(summary['failed_names'], ['bad'])
        self.assertEqual(summary['observations'][1]['assertions'][0]['location'], '/source with spaces/tUnit.cpp:42')

    def test_truncated_output_retains_observed_fail_but_no_final_counts(self):
        summary = parse_unit_output(OUTPUT.split('Tests run:')[0], exit_code=255)
        self.assertFalse(summary['complete'])
        self.assertEqual(summary['observed_failed_names'], ['bad'])
        self.assertNotIn('counts', summary)
        self.assertNotIn('failed_names', summary)

    def test_signal_and_timeout_refuse_even_a_complete_printed_trailer(self):
        for code, interrupted in [(-9, False), (255, True)]:
            with self.subTest(code=code, interrupted=interrupted):
                summary = parse_unit_output(OUTPUT, exit_code=code, interrupted=interrupted)
                self.assertFalse(summary['complete'])
                self.assertNotIn('counts', summary)

    def test_duplicate_names_and_repeated_trailers_refuse_completion(self):
        for text in [OUTPUT.replace('bad', 'good'), OUTPUT + 'Tests run: 0\n  - ok 0 (nan) %\n  - fail 0 (nan) %\n']:
            with self.subTest(text=text):
                self.assertFalse(parse_unit_output(text, exit_code=255)['complete'])

    def test_missing_or_mismatched_footer_counts_refuse_completion(self):
        variants = [OUTPUT.replace('Tests run: 2', 'Tests run: 3'),
                    OUTPUT.replace('- fail 1', '- fail 0'), OUTPUT.split('  - fail')[0],
                    OUTPUT.replace('  - ok   1', '  - ok   bad')]
        for text in variants:
            with self.subTest(text=text):
                self.assertFalse(parse_unit_output(text, exit_code=255)['complete'])

    def test_marker_after_footer_and_unfinished_test_refuse_completion(self):
        for tail in ['[ FAIL ] late\n', 'Running unfinished... \n']:
            self.assertFalse(parse_unit_output(OUTPUT + tail, exit_code=255)['complete'])

    def test_zero_exit_with_fail_marker_and_instrumentation_exit_are_not_complete(self):
        for code in (0, 97, 98, None):
            with self.subTest(code=code):
                self.assertFalse(parse_unit_output(OUTPUT, exit_code=code)['complete'])

    def test_stderr_assertion_is_never_bound_by_cross_stream_order(self):
        summary = parse_unit_output(OUTPUT, '/other/t.cpp:93: void f(): Assertion x failed.\n', 255)
        self.assertEqual(len(summary['observations'][1]['assertions']), 1)
        self.assertEqual(summary['unassigned_assertions'][0]['location'], '/other/t.cpp:93')

    def test_mismatched_running_name_does_not_misattribute_assertion(self):
        summary = parse_unit_output(OUTPUT.replace('Running bad', 'Running someone_else'), exit_code=255)
        self.assertFalse(summary['complete'])
        self.assertEqual([row['name'] for row in summary['observations']], ['good'])
        self.assertEqual(summary['nested_observations'][0]['name'], 'bad')
        self.assertEqual(summary['nested_observations'][0]['parent'], 'someone_else')
        self.assertEqual(summary['unassigned_assertions'][0]['location'], '/source with spaces/tUnit.cpp:42')

    def test_nested_ok_names_are_diagnostics_until_exact_outer_result(self):
        text = ('Running viras_internal_Real...\n'
                '[ OK ] breaks_lra_case_01\n[ OK ] breaks_lra_case_01\n'
                '[ OK ] viras_internal_Real\n'
                'Running typed_terms...\n'
                '[ OK ] p($sum(b,2/1))\n[ OK ] p($sum(b,2/1))\n'
                '[ OK ] typed_terms\n'
                'Tests run: 2\n - ok 2 (100.0) %\n - fail 0 (0.0) %\n')
        for newline in ('\n', '\r\n', '\r'):
            summary = parse_unit_output(text.replace('\n', newline), exit_code=0)
            self.assertTrue(summary['complete'], summary)
            self.assertEqual(summary['passed_names'], ['viras_internal_Real', 'typed_terms'])
            self.assertEqual(len(summary['nested_observations']), 4)
            self.assertEqual(summary['nested_observations'][0]['stdout_line'], 2)
            self.assertEqual(summary['nested_observations'][2]['parent'], 'typed_terms')

    def test_nested_fail_is_preserved_and_prevents_clean_outer_pass(self):
        text = ('Running outer...\n[ FAIL ] child\n[ OK ] outer\n'
                'Tests run: 1\n - ok 1 (100.0) %\n - fail 0 (0.0) %\n')
        summary = parse_unit_output(text, exit_code=0)
        self.assertFalse(summary['complete'])
        self.assertEqual(summary['nested_observations'][0]['outcome'], 'fail')
        self.assertTrue(any('nested FAIL marker for child inside outer' in p for p in summary['problems']))

    def test_multiword_and_bare_nested_fail_are_never_ignored(self):
        for payload in ('f(X0): $rat', ''):
            text = ('Running outer...\n[ FAIL ] ' + payload + '\n[ OK ] outer\n'
                    'Tests run: 1\n - ok 1 (100.0) %\n - fail 0 (0.0) %\n')
            summary = parse_unit_output(text, exit_code=0)
            self.assertFalse(summary['complete'])
            self.assertEqual(summary['nested_observations'][0]['name'], payload)
            self.assertEqual(summary['nested_observations'][0]['outcome'], 'fail')

    def test_multiword_nested_ok_payload_is_preserved(self):
        text = ('Running outer...\n[ OK ] f(X0): $rat\n[ OK ] outer\n'
                'Tests run: 1\n - ok 1 (100.0) %\n - fail 0 (0.0) %\n')
        summary = parse_unit_output(text, exit_code=0)
        self.assertTrue(summary['complete'], summary)
        self.assertEqual(summary['nested_observations'][0]['name'], 'f(X0): $rat')

    def test_nested_ok_cannot_replace_the_outer_result(self):
        text = ('Running outer...\n[ OK ] child\n'
                'Tests run: 1\n - ok 1 (100.0) %\n - fail 0 (0.0) %\n')
        summary = parse_unit_output(text, exit_code=0)
        self.assertFalse(summary['complete'])
        self.assertEqual(summary['observations'], [])
        self.assertIn('a started test has no result marker', summary['problems'])

    def test_assertion_before_or_after_outer_ok_prevents_clean_pass(self):
        diagnostic = 'Condition at location /source/t.cpp:42 violated:\n'
        variants = [('Running outer...\n' + diagnostic + '[ OK ] outer\n', ''),
                    ('Running outer...\n[ OK ] outer\n' + diagnostic, ''),
                    ('Running outer...\n[ OK ] outer\n', diagnostic)]
        trailer = 'Tests run: 1\n - ok 1 (100.0) %\n - fail 0 (0.0) %\n'
        for stdout, stderr in variants:
            summary = parse_unit_output(stdout + trailer, stderr, 0)
            self.assertFalse(summary['complete'], summary)
            self.assertTrue(summary['observations'][0]['assertions'] or summary['unassigned_assertions'])

    def test_unframed_marker_and_nested_marker_after_trailer_refuse_completion(self):
        trailer = 'Tests run: 1\n - ok 1 (100.0) %\n - fail 0 (0.0) %\n'
        for text in ['[ OK ] outer\n' + trailer,
                     'Running outer...\n' + trailer + '[ OK ] child\n[ OK ] outer\n']:
            self.assertFalse(parse_unit_output(text, exit_code=0)['complete'])

    def test_empty_direct_test_output_has_no_invented_test(self):
        summary = parse_unit_output('', exit_code=0)
        self.assertFalse(summary['complete'])
        self.assertEqual(summary['observations'], [])


class NativeOutputIntegration(unittest.TestCase):
    def test_nested_failure_details_are_visible_with_parent_and_log_position(self):
        for payload in ('f(X0): $rat', ''):
            stdout = ('Running outer...\n[ FAIL ] ' + payload + '\n[ OK ] outer\n'
                      'Tests run: 1\n - ok 1 (100.0) %\n - fail 0 (0.0) %\n')
            result = {'name': 'unit/Example', 'outcome': 'pass', 'exit': 0,
                      'unit_test_summary': parse_unit_output(stdout, exit_code=0)}
            with tempfile.TemporaryDirectory() as temporary, contextlib.redirect_stdout(io.StringIO()) as stream:
                reporter = TerminalReporter([{'name': result['name']}], [], Path(temporary))
                reporter.record(result)
                reporter.finish()
                for text in (stream.getvalue(), (Path(temporary) / 'failures.txt').read_text()):
                    self.assertIn('[UNIT OUTPUT WARNING]', text)
                    self.assertIn('Nested [FAIL] ' + (payload or '(no payload)') + ' inside outer', text)
                    self.assertIn('stdout.log, normalized line 2', text)
                    self.assertIn('Diagnostic: [ FAIL ]', text)

    def test_passed_marker_assertion_remains_visible_in_report(self):
        stdout = ('Running outer...\nCondition at location /source/t.cpp:42 violated:\n'
                  '[ OK ] outer\nTests run: 1\n - ok 1 (100.0) %\n - fail 0 (0.0) %\n')
        result = {'name': 'unit/Example', 'outcome': 'pass', 'exit': 0,
                  'unit_test_summary': parse_unit_output(stdout, exit_code=0)}
        text = failure_detail(result)
        self.assertIn('[OK WITH ASSERTION] outer', text)
        self.assertIn('Where: /source/t.cpp:42', text)

    def test_runner_records_subtests_and_report_keeps_one_suite(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            case = run.Case('unit/Example', [sys.executable, '-c', f'print({OUTPUT!r}, end=""); raise SystemExit(255)'], temporary)
            result = run.run_case(case, root, 5, False)
            self.assertEqual(result['outcome'], 'fail')
            self.assertEqual(result['exit'], 255)
            self.assertEqual(result['unit_test_summary']['failed_names'], ['bad'])
            self.assertEqual(json.loads((Path(result['artifacts']) / 'result.json').read_text()), result)
            self.assertIn('stdout.log', result['evidence_sha256'])
            self.assertRegex(table([{'name': case.name}], [result]), r'TOTAL\s+1/1\s+0\s+1\s+0')
            with contextlib.redirect_stdout(io.StringIO()) as stream:
                reporter = TerminalReporter([{'name': case.name}], [], root)
                reporter.record(result)
                reporter.finish()
            for text in (stream.getvalue(), (root / 'failures.txt').read_text()):
                self.assertIn('[FAIL] bad', text)
                self.assertIn('/source with spaces/tUnit.cpp:42', text)
                self.assertIn('1 passed, 1 failed, 2 total', text)

    def test_runner_timeout_does_not_promote_printed_counts(self):
        with tempfile.TemporaryDirectory() as temporary:
            case = run.Case('unit/Timeout', [sys.executable, '-c', f'import time; print({OUTPUT!r}, flush=True); time.sleep(10)'], temporary)
            result = run.run_case(case, Path(temporary), 0.3, False)
            self.assertEqual(result['outcome'], 'inconclusive')
            self.assertFalse(result['unit_test_summary']['complete'])
            text = failure_detail(result)
            self.assertIn('not final counts', text)
            self.assertIn('[FAIL] bad', text)

    def test_old_result_logs_are_read_without_rewriting_history(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / 'stdout.log').write_text(OUTPUT)
            (root / 'stderr.log').write_text('')
            before = {p.name: p.read_bytes() for p in root.iterdir()}
            result = {'name': 'unit/Example', 'outcome': 'fail', 'exit': 255, 'artifacts': temporary}
            text = failure_detail(result)
            self.assertIn('[FAIL] bad', text)
            self.assertNotIn('unit_test_summary', result)
            self.assertEqual(before, {p.name: p.read_bytes() for p in root.iterdir()})

    def test_zero_exit_contradiction_is_visible_without_changing_suite_count(self):
        result = {'name': 'unit/Example', 'outcome': 'pass', 'exit': 0,
                  'unit_test_summary': parse_unit_output(OUTPUT, exit_code=0)}
        with tempfile.TemporaryDirectory() as temporary, contextlib.redirect_stdout(io.StringIO()) as stream:
            reporter = TerminalReporter([{'name': result['name']}], [], Path(temporary))
            reporter.record(result)
            reporter.finish()
            self.assertIn('[UNIT OUTPUT WARNING]', stream.getvalue())
            self.assertIn('[FAIL] bad', stream.getvalue())
            self.assertRegex(stream.getvalue(), r'TOTAL\s+1/1\s+1\s+0\s+0')

    def test_discovery_keeps_suite_count_and_names(self):
        data = {'tests': [{'name': f'Suite{i}', 'command': ['vtest', 'run', f'Suite{i}']} for i in range(104)]}
        with patch.object(run, 'checked_output', return_value=json.dumps(data)):
            cases = run.unit_cases(Path('/build'))
        self.assertEqual(len(cases), 104)
        self.assertEqual(cases[0].name, 'unit/Suite0')
        self.assertEqual(cases[-1].name, 'unit/Suite103')


if __name__ == '__main__': unittest.main()
