"""Coverage reporting does not replace solver outcomes or imply readiness."""
import argparse
import contextlib
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import campaign


TRACE = ('SF:example.cpp\nDA:1,4\nDA:2,0\nFNDA:4,used\nFNDA:0,unused\n'
         'BRDA:1,0,0,4\nBRDA:1,0,1,0\nLF:2\nLH:1\nFNF:2\nFNH:1\n'
         'BRF:2\nBRH:1\nend_of_record\n')


class CampaignCoveragePolicy(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.trace = self.root / 'coverage.info'
        self.trace.write_text(TRACE)

    def tearDown(self):
        self.temporary.cleanup()

    def create(self, required=None, *, resume=False):
        identity = {'commit': 'frozen', 'coverage_policy': campaign.coverage_policy(required),
                    'options': {'require_coverage_percent': required}}
        return campaign.Campaign(self.root / 'campaign', identity, resume=resume, root=self.root)

    def test_partial_coverage_is_informational_by_default(self):
        data = campaign.coverage_gaps(self.trace)
        self.assertEqual(set(data['percentages'].values()), {50})
        self.assertIsNone(data['target_percent'])
        self.assertIsNone(data['threshold_met'])
        self.assertEqual(data['coverage_policy']['mode'], 'informational')
        self.assertEqual(data['files'][0]['lines'], [2])
        self.assertEqual(data['files'][0]['functions'], ['unused'])
        self.assertEqual(len(data['files'][0]['branches']), 1)

    def test_requested_threshold_has_an_inclusive_boundary(self):
        for threshold, passed in ((0, True), (49.9, True), (50, True), (50.01, False), (100, False)):
            with self.subTest(threshold=threshold):
                data = campaign.coverage_gaps(self.trace, threshold)
                self.assertEqual(data['threshold_met'], passed)
                self.assertEqual(data['target_percent'], threshold)
                self.assertEqual(data['coverage_policy']['mode'], 'required-percent')

    def test_function_alias_gap_cannot_be_hidden_by_covered_group(self):
        self.trace.write_text(TRACE.replace('FNDA:4,used\nFNDA:0,unused',
                                           'FNL:0,1,2\nFNA:0,4,used\nFNA:0,0,unused')
                             .replace('FNF:2\nFNH:1', 'FNF:1\nFNH:1'))
        data = campaign.coverage_gaps(self.trace, 75)
        self.assertEqual(data['percentages']['function_groups'], 100)
        self.assertEqual(data['percentages']['functions'], 50)
        self.assertFalse(data['threshold_met'])

    def test_empty_metric_denominator_cannot_satisfy_a_gate(self):
        self.trace.write_text('SF:example.cpp\nDA:1,1\nLF:1\nLH:1\nFNF:0\nFNH:0\nBRF:0\nBRH:0\nend_of_record\n')
        self.assertFalse(campaign.coverage_gaps(self.trace, 0)['threshold_met'])
        self.assertIsNone(campaign.coverage_gaps(self.trace)['threshold_met'])

    def test_missing_branch_metric_is_invalid_even_without_threshold(self):
        self.trace.write_text(''.join(line+'\n' for line in TRACE.splitlines()
                                      if not line.startswith(('BRDA:', 'BRF:', 'BRH:'))))
        with self.assertRaisesRegex(ValueError, 'lacks metric data: BRF'):
            campaign.coverage_gaps(self.trace)
        current = self.create()
        current.record_coverage(self.trace)
        current.finish()
        self.assertEqual(current.data['status'], 'fail')
        self.assertFalse(current.find('coverage-report')['coverage_valid'])

    def test_nonfinite_or_out_of_range_threshold_is_rejected(self):
        for value in ('nan', 'inf', '-inf', '-0.1', '100.1'):
            with self.subTest(value=value), self.assertRaises(argparse.ArgumentTypeError):
                campaign.coverage_percent(value)

    def test_negative_counts_and_unfinished_records_are_rejected(self):
        for original, bad in (('DA:1,4', 'DA:1,-1'), ('FNDA:4,used', 'FNDA:-1,used'),
                              ('BRDA:1,0,0,4', 'BRDA:1,0,0,-1'),
                              ('DA:1,4', 'SF:other.cpp\nDA:1,4')):
            with self.subTest(bad=bad):
                self.trace.write_text(TRACE.replace(original, bad))
                with self.assertRaises(ValueError): campaign.coverage_gaps(self.trace)

    def test_default_report_records_policy_and_keeps_raw_gaps(self):
        current = self.create()
        current.record_coverage(self.trace)
        current.finish()
        row = current.find('coverage-report')
        self.assertEqual(row['status'], 'pass')
        self.assertTrue(row['coverage_valid'])
        self.assertIsNone(row['threshold_met'])
        self.assertTrue(current.data['recorded_stages_complete'])
        self.assertTrue(current.data['all_stages_passed'])
        self.assertEqual(current.data['feature_readiness'], 'not assessed by campaign')
        saved = json.loads((current.output / 'coverage-gaps.json').read_text())
        self.assertEqual(saved['coverage_policy'], current.data['identity']['coverage_policy'])
        self.assertEqual(saved['coverage_policy'], current.data['coverage_policy'])

    def test_missing_or_invalid_coverage_is_a_completed_failure(self):
        for content in (None, '', TRACE.replace('LH:1', 'LH:3')):
            with self.subTest(content=content):
                with tempfile.TemporaryDirectory() as directory:
                    root = Path(directory)
                    trace = root / 'coverage.info'
                    if content is not None: trace.write_text(content)
                    current = campaign.Campaign(root / 'run', {'coverage_policy': campaign.coverage_policy()}, root=root)
                    current.record_coverage(trace)
                    current.finish()
                    self.assertEqual(current.data['status'], 'fail')
                    self.assertTrue(current.data['recorded_stages_complete'])
                    self.assertFalse(current.data['all_stages_passed'])
                    self.assertFalse(current.find('coverage-report')['coverage_valid'])

    def test_valid_report_never_overrides_solver_failure_or_inconclusive_stage(self):
        for outcome in ('fail', 'inconclusive'):
            with self.subTest(outcome=outcome), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                current = campaign.Campaign(root / 'run', {'coverage_policy': campaign.coverage_policy(50)}, root=root)
                output = current.output / 'solver'
                command = [sys.executable, '-c',
                           f"import json; from pathlib import Path; p=Path({str(output)!r}); p.mkdir(); "
                           f"(p/'summary.json').write_text(json.dumps({{'totals': {{{outcome!r}: 1}}}})); raise SystemExit(1)"]
                with contextlib.redirect_stdout(io.StringIO()):
                    self.assertFalse(current.stage('solver', command, case_output=output))
                current.record_coverage(self.trace)
                current.finish()
                self.assertTrue(current.find('coverage-report')['threshold_met'])
                self.assertEqual(current.data['status'], 'fail')
                self.assertTrue(current.data['recorded_stages_complete'])
                self.assertFalse(current.data['all_stages_passed'])
                self.assertEqual(json.loads((output / 'summary.json').read_text())['totals'], {outcome: 1})

    def test_failed_threshold_is_preserved_on_compatible_resume(self):
        current = self.create(80)
        current.record_coverage(self.trace)
        current.finish()
        self.assertEqual(current.data['status'], 'fail')
        resumed = self.create(80, resume=True)
        self.assertFalse(resumed.data['recorded_stages_complete'])
        self.assertIsNone(resumed.data['all_stages_passed'])
        with patch.object(campaign, 'coverage_gaps', side_effect=AssertionError('completed report reran')):
            resumed.record_coverage(self.trace)
        resumed.finish()
        self.assertEqual(resumed.data['status'], 'fail')
        self.assertEqual(len(resumed.data['stages']), 1)

    def test_coverage_policy_change_refuses_resume(self):
        current = self.create()
        current.record_coverage(self.trace)
        current.finish()
        with self.assertRaisesRegex(ValueError, 'cannot resume'):
            self.create(50, resume=True)

    def test_top_level_policy_must_match_pinned_identity_on_resume(self):
        current = self.create()
        current.finish()
        current.data['coverage_policy'] = campaign.coverage_policy(50)
        current.save()
        with self.assertRaisesRegex(ValueError, 'recorded coverage policy'):
            self.create(resume=True)

    def test_failed_prerequisite_completes_only_recorded_stages(self):
        current = self.create()
        with contextlib.redirect_stdout(io.StringIO()):
            current.stage('build-release', [sys.executable, '-c', 'raise SystemExit(1)'])
        current.finish()
        self.assertTrue(current.data['recorded_stages_complete'])
        self.assertFalse(current.data['all_stages_passed'])
        self.assertNotIn('execution_complete', current.data)
        self.assertIn('failed prerequisites can block requested stages', current.data['completion_scope'])

    def test_threshold_without_coverage_profile_is_rejected_before_work(self):
        argv = ['campaign.py', '--output', str(self.root / 'unused'), '--profiles', 'release',
                '--require-coverage-percent', '50']
        with patch.object(sys, 'argv', argv), contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as result:
            campaign.main()
        self.assertEqual(result.exception.code, 2)
        self.assertFalse((self.root / 'unused').exists())


if __name__ == '__main__': unittest.main()
