"""Nonfinite budgets must fail before any worker starts or output is created."""
import contextlib
import io
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import api_probes
import campaign
import run
import runtime_options


class FiniteBudgets(unittest.TestCase):
    budgets = (float('nan'), float('inf'), float('-inf'))

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.output = self.root / 'output'
        self.build = self.root / 'missing-build'
        run.CANCELLED.clear()

    def tearDown(self):
        self.temporary.cleanup()

    def assert_api_rejected(self, invoke):
        for budget in self.budgets:
            with self.subTest(budget=budget), patch('subprocess.Popen') as process:
                with self.assertRaisesRegex(ValueError, 'finite'):
                    invoke(budget)
                process.assert_not_called()
                self.assertFalse(self.output.exists())

    def assert_cli_rejected(self, module, arguments, flag):
        for budget in self.budgets:
            errors = io.StringIO()
            argv = [module.__name__ + '.py', *arguments, flag + '=' + str(budget)]
            with self.subTest(budget=budget), patch.object(sys, 'argv', argv), patch('subprocess.Popen') as process:
                with contextlib.redirect_stderr(errors), self.assertRaises(SystemExit) as exit:
                    module.main()
                self.assertEqual(exit.exception.code, 2)
                self.assertIn('finite', errors.getvalue())
                process.assert_not_called()
                self.assertFalse(self.output.exists())

    def test_case_api_rejects_nonfinite_wall_budget(self):
        case = run.Case('fixture', [sys.executable, '-c', 'pass'], str(self.root))
        self.assert_api_rejected(lambda budget: run.run_case(case, self.output, budget, False))

    def test_case_api_rejects_nonfinite_error_grace(self):
        case = run.Case('fixture', [sys.executable, '-c', 'pass'], str(self.root))
        self.assert_api_rejected(lambda budget: run.run_case(case, self.output, 1, False, asan=True, sanitizer_error_grace=budget))

    def test_runner_cli_rejects_nonfinite_wall_budget(self):
        self.assert_cli_rejected(run, ['run', '--build', str(self.build), '--output', str(self.output)], '--timeout')

    def test_runner_cli_rejects_nonfinite_error_grace(self):
        self.assert_cli_rejected(run, ['run', '--asan', '--build', str(self.build), '--output', str(self.output)], '--sanitizer-error-grace')

    def test_campaign_cli_rejects_nonfinite_error_grace(self):
        self.assert_cli_rejected(campaign, ['--output', str(self.output)], '--sanitizer-error-grace')

    def test_runtime_api_rejects_nonfinite_wall_budget(self):
        self.assert_api_rejected(lambda budget: runtime_options.run_suite(self.build, 'release', self.output, timeout=budget))

    def test_runtime_api_rejects_nonfinite_error_grace(self):
        self.assert_api_rejected(lambda budget: runtime_options.run_suite(self.build, 'asan', self.output, sanitizer_error_grace=budget))

    def test_runtime_cli_rejects_nonfinite_wall_budget(self):
        self.assert_cli_rejected(runtime_options, ['--build', str(self.build), '--output', str(self.output)], '--timeout')

    def test_runtime_cli_rejects_nonfinite_error_grace(self):
        self.assert_cli_rejected(runtime_options, ['--profile', 'asan', '--build', str(self.build), '--output', str(self.output)], '--sanitizer-error-grace')

    def test_api_probes_function_rejects_nonfinite_wall_budget(self):
        self.assert_api_rejected(lambda budget: api_probes.run_probes(self.build, self.output, timeout=budget))

    def test_api_probes_cli_rejects_nonfinite_wall_budget(self):
        self.assert_cli_rejected(api_probes, ['--build', str(self.build), '--output', str(self.output)], '--timeout')


if __name__ == '__main__': unittest.main()
