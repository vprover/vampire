"""Keep incomplete leak checks separate from solver and memory failures."""
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from diagnostics import sanitizer_messages, sanitizer_warnings
from report import failure_detail
from run import Case, run_case
from validation import validate_roundtrip

SUSPENSION = '==215188==Running thread 215167 was not suspended. False leaks are possible.'
FATAL = '==215188==LeakSanitizer has encountered a fatal error.'
ERROR = '==215188==ERROR: LeakSanitizer: detected memory leaks'


class LeakCheckWarnings(unittest.TestCase):
    def answer(self, diagnostics, answer='Unsatisfiable', exitcode=0, asan=True):
        source = 'import sys; '
        if answer:
            source += f'print({("% SZS status " + answer + " for input")!r}); '
        source += f'print({diagnostics!r}, file=sys.stderr); raise SystemExit({exitcode})'
        with tempfile.TemporaryDirectory() as directory:
            case = Case('fixture', [sys.executable, '-c', source], directory, 'szs', 'Unsatisfiable')
            return run_case(case, Path(directory), 5, False, asan=asan)

    def test_raw_warning_is_preserved_separately_and_deduplicated(self):
        raw = '% WARNING: debug build, do not use in anger\n' + SUSPENSION + '\n' + FATAL + '\n'
        self.assertEqual(sanitizer_warnings(SUSPENSION, raw), [SUSPENSION, FATAL])
        self.assertEqual(sanitizer_messages('', raw), [])

    def test_correct_answer_with_warning_is_memory_inconclusive(self):
        for asan in (False, True):
            with self.subTest(asan=asan):
                result = self.answer(SUSPENSION, asan=asan)
                self.assertEqual(result['semantic_outcome'], 'pass')
                self.assertEqual(result['memory_outcome'], 'inconclusive')
                self.assertEqual(result['outcome'], 'inconclusive')
                self.assertEqual(result['sanitizer_warnings'], [SUSPENSION])
                self.assertEqual(result['sanitizer_messages'], [])
                self.assertIn('Sanitizer warning: ' + SUSPENSION, failure_detail(result))

    def test_real_error_remains_failure_with_warning(self):
        for diagnostic in (ERROR, 'ERROR: AddressSanitizer: heap-use-after-free'):
            with self.subTest(diagnostic=diagnostic):
                result = self.answer(SUSPENSION + '\n' + diagnostic, exitcode=98)
                self.assertEqual(result['semantic_outcome'], 'pass')
                self.assertEqual(result['memory_outcome'], 'fail')
                self.assertEqual(result['outcome'], 'fail')
                self.assertEqual(result['sanitizer_warnings'], [SUSPENSION])
                self.assertIn('leak check needs confirmation', result['reason'])

    def test_wrong_answer_still_fails_with_warning_or_fatal_check(self):
        for diagnostic, exitcode in ((SUSPENSION, 0), (FATAL, 1), (FATAL, 98),
                                     (SUSPENSION + '\n' + ERROR, 98)):
            with self.subTest(diagnostic=diagnostic, exitcode=exitcode):
                result = self.answer(diagnostic, answer='Satisfiable', exitcode=exitcode)
                self.assertEqual(result['semantic_outcome'], 'fail')
                self.assertEqual(result['outcome'], 'fail')
                self.assertEqual(result['memory_outcome'], 'fail' if ERROR in diagnostic else 'inconclusive')

    def test_fatal_leak_check_after_correct_answer_is_inconclusive(self):
        for exitcode in (1, 98):
            with self.subTest(exitcode=exitcode):
                result = self.answer(FATAL, exitcode=exitcode)
                self.assertEqual(result['semantic_outcome'], 'pass')
                self.assertEqual(result['memory_outcome'], 'inconclusive')
                self.assertEqual(result['outcome'], 'inconclusive')
                self.assertEqual(result['sanitizer_messages'], [])

    def test_fatal_leak_check_without_answer_does_not_prove_a_solver_failure(self):
        result = self.answer(FATAL, answer=None, exitcode=1)
        self.assertEqual(result['semantic_outcome'], 'inconclusive')
        self.assertEqual(result['memory_outcome'], 'inconclusive')
        self.assertEqual(result['outcome'], 'inconclusive')

    def test_unrelated_warning_does_not_prevent_memory_pass(self):
        result = self.answer('% WARNING: debug build, do not use in anger')
        self.assertEqual(result['outcome'], 'pass')
        self.assertEqual(result['memory_outcome'], 'pass')
        self.assertEqual(result['sanitizer_warnings'], [])

    def test_roundtrip_child_propagates_warning_and_keeps_failures(self):
        for answer, diagnostic, exitcode, semantic, memory in (
                ('Unsatisfiable', SUSPENSION, 0, 'pass', 'inconclusive'),
                ('Unsatisfiable', FATAL, 1, 'pass', 'inconclusive'),
                ('Unsatisfiable', SUSPENSION + '\n' + ERROR, 98, 'pass', 'fail'),
                ('Satisfiable', SUSPENSION, 0, 'fail', 'inconclusive')):
            with self.subTest(answer=answer, diagnostic=diagnostic), tempfile.TemporaryDirectory() as directory:
                folder = Path(directory)
                script = folder / 'solver'
                script.write_text('#!/usr/bin/env python3\nimport sys\n'
                    'if "--input_syntax" in sys.argv:\n'
                    f' print({("% SZS status " + answer + " for input")!r})\n'
                    f' print({diagnostic!r}, file=sys.stderr)\n'
                    f' sys.exit({exitcode})\n'
                    'print("cnf(a,axiom,$false).")\n')
                script.chmod(0o755)
                result = run_case(Case('transform', [str(script)], directory, 'roundtrip', 'Unsatisfiable'),
                                  folder, 5, False, asan=True)
                self.assertEqual(result['semantic_outcome'], semantic)
                self.assertEqual(result['memory_outcome'], memory)
                self.assertEqual(result['outcome'], 'fail' if 'fail' in (semantic, memory) else 'inconclusive')
                self.assertEqual(result['sanitizer_warnings'], result['validator_result']['sanitizer_warnings'])
                self.assertTrue(result['sanitizer_warnings'])

    def test_standalone_roundtrip_warning_does_not_hide_wrong_answer(self):
        for answer, outcome in (('Unsatisfiable', 'inconclusive'), ('Satisfiable', 'fail')):
            with self.subTest(answer=answer), tempfile.TemporaryDirectory() as directory:
                completed = SimpleNamespace(stdout=f'% SZS status {answer} for input\n',
                                            stderr=SUSPENSION, returncode=0)
                with patch('validation.subprocess.run', return_value=completed):
                    result = validate_roundtrip('cnf(a,axiom,$false).\n', Path(directory),
                                                'vampire', 'Unsatisfiable', 5)
                self.assertEqual(result[0], outcome)


if __name__ == '__main__': unittest.main()
