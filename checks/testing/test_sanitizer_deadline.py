"""A shutdown hang must not hide the sanitizer error or shorten clean tests."""
from pathlib import Path
import sys
import tempfile
import unittest

import run


class SanitizerDeadline(unittest.TestCase):
    def setUp(self): run.CANCELLED.clear()

    def invoke(self, code, *, asan=True, grace=0.15, timeout=2):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            case = run.Case('fixture', [sys.executable, '-c', code], str(root), 'szs', 'Unsatisfiable')
            result = run.run_case(case, root, timeout, False, asan=asan, sanitizer_error_grace=grace)
            stderr = (Path(result['artifacts']) / 'stderr.log').read_text()
            saved = (Path(result['artifacts']) / 'result.json').read_text()
            return result, stderr, saved

    def test_actual_error_then_hang_is_bounded_and_remains_memory_failure(self):
        result, stderr, saved = self.invoke(
            "import sys,time; print('ERROR: AddressSanitizer: heap-use-after-free',file=sys.stderr,flush=True); time.sleep(5)")
        self.assertLess(result['seconds'], 1.5)
        self.assertTrue(result['sanitizer_error_deadline'])
        self.assertFalse(result['wall_timeout'])
        self.assertEqual(result['memory_outcome'], 'fail')
        self.assertEqual(result['semantic_outcome'], 'inconclusive')
        self.assertEqual(result['outcome'], 'fail')
        self.assertIn('heap-use-after-free', stderr)
        self.assertIn('sanitizer_error_grace_seconds', saved)
        self.assertIn('grace expired', result['reason'])

    def test_clean_process_can_run_longer_than_error_grace(self):
        result, _, _ = self.invoke("import time; time.sleep(.4); print('% SZS status Unsatisfiable')")
        self.assertGreater(result['seconds'], .35)
        self.assertEqual(result['outcome'], 'pass')
        self.assertFalse(result['sanitizer_error_deadline'])

    def test_warning_alone_does_not_start_error_grace(self):
        result, _, _ = self.invoke("import sys,time; print('Running thread 3 was not suspended. False leaks are possible.',file=sys.stderr,flush=True); time.sleep(.4); print('% SZS status Unsatisfiable')")
        self.assertGreater(result['seconds'], .35)
        self.assertFalse(result['sanitizer_error_deadline'])
        self.assertEqual(result['outcome'], 'inconclusive')

    def test_default_preserves_original_wall_timeout(self):
        result, _, _ = self.invoke("import sys,time; print('AddressSanitizer:DEADLYSIGNAL',file=sys.stderr,flush=True); time.sleep(5)", grace=None, timeout=.4)
        self.assertTrue(result['wall_timeout'])
        self.assertFalse(result['sanitizer_error_deadline'])
        self.assertGreaterEqual(result['seconds'], .35)
        self.assertEqual(result['memory_outcome'], 'fail')

    def test_non_asan_call_does_not_enable_grace(self):
        result, _, _ = self.invoke("import sys,time; print('AddressSanitizer:DEADLYSIGNAL',file=sys.stderr,flush=True); time.sleep(.4); print('% SZS status Unsatisfiable')", asan=False)
        self.assertFalse(result['sanitizer_error_deadline'])
        self.assertGreater(result['seconds'], .35)

    def test_clean_hang_uses_full_wall_timeout(self):
        result, _, _ = self.invoke('import time; time.sleep(5)', timeout=.45)
        self.assertTrue(result['wall_timeout'])
        self.assertGreaterEqual(result['seconds'], .4)
        self.assertEqual(result['memory_outcome'], 'inconclusive')

    def test_error_that_finishes_keeps_complete_diagnostics(self):
        result, stderr, _ = self.invoke("import sys; print('ERROR: AddressSanitizer: heap-use-after-free\\nSUMMARY: AddressSanitizer: heap-use-after-free',file=sys.stderr)")
        self.assertFalse(result['sanitizer_error_deadline'])
        self.assertIn('SUMMARY:', stderr)
        self.assertEqual(result['memory_outcome'], 'fail')


if __name__ == '__main__': unittest.main()
