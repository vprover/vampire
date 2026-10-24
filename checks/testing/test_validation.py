import json
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from diagnostics import combine, sanitizer_messages
from option_cases import catalogue
from run import Case, run_case
from validation import validate_smt_script, validate_roundtrip

PROOF = '% SZS output start Proof for x\n(set-logic ALL)\n(assert false)\n(check-sat)\n% SZS output end Proof for x\n'


class Validation(unittest.TestCase):
    def check_proof(self, proof, stdout='unsat\n', code=0, stderr=''):
        with tempfile.TemporaryDirectory() as directory, patch('validation.subprocess.run',
                return_value=SimpleNamespace(stdout=stdout, stderr=stderr, returncode=code)):
            return validate_smt_script(proof, Path(directory), 'z3', 5)

    def test_untested_function_alias_prevents_full_coverage(self):
        from campaign import coverage_gaps
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'coverage.info'
            path.write_text('SF:example.cpp\nFNL:0,1,2\nFNA:0,5,used<int>\n'
                            'FNA:0,0,unused<long>\nFNF:1\nFNH:1\nLF:1\nLH:1\n'
                            'BRF:1\nBRH:1\nend_of_record\n')
            data = coverage_gaps(path)
            self.assertEqual(data['percentages']['functions'], 50)
            self.assertEqual(data['percentages']['function_groups'], 100)
            self.assertEqual(data['files'][0]['functions'], ['unused<long>'])

    def test_legacy_function_coverage_records(self):
        from campaign import coverage_gaps
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'coverage.info'
            path.write_text('SF:example.cpp\nFNDA:2,used\nFNDA:0,unused\n'
                            'FNF:2\nFNH:1\nLF:0\nLH:0\nBRF:0\nBRH:0\nend_of_record\n')
            data = coverage_gaps(path)
            self.assertEqual(data['totals']['FAF'], 2)
            self.assertEqual(data['percentages']['functions'], 50)

    def instrumented_answer(self, answer):
        with tempfile.TemporaryDirectory() as directory:
            code = 'import sys; print("ERROR: AddressSanitizer: heap-use-after-free", file=sys.stderr); '
            if answer: code += f'print("% SZS status {answer} for x"); '
            code += 'raise SystemExit(98)'
            case = Case('instrumented', [sys.executable, '-c', code], directory, 'szs', 'Unsatisfiable')
            return run_case(case, Path(directory), 5, False, asan=True)

    def test_sanitizer_does_not_hide_a_wrong_answer(self):
        result = self.instrumented_answer('Satisfiable')
        self.assertEqual(result['semantic_outcome'], 'fail')
        self.assertEqual(result['memory_outcome'], 'fail')

    def test_sanitizer_before_answer_is_inconclusive_semantically(self):
        result = self.instrumented_answer(None)
        self.assertEqual(result['semantic_outcome'], 'inconclusive')
        self.assertEqual(result['outcome'], 'fail')

    def test_correct_answer_does_not_hide_memory_error(self):
        result = self.instrumented_answer('Unsatisfiable')
        self.assertEqual(result['semantic_outcome'], 'pass')
        self.assertEqual(result['outcome'], 'fail')

    def test_roundtrip_uses_instrumented_runner_and_unlimited_asan_memory(self):
        with tempfile.TemporaryDirectory() as directory:
            seen = []
            def run_solver(command):
                seen.append(command)
                return {'semantic_outcome': 'fail', 'semantic_reason': 'wrong answer'}
            outcome = validate_roundtrip('cnf(a,axiom,$false).\n', Path(directory), 'vampire',
                                         'Unsatisfiable', 5, run_solver, True)
            self.assertEqual(outcome, ('fail', 'wrong answer'))
            self.assertEqual(seen[0][-2:], ['-m', '0'])

    def test_roundtrip_child_memory_failure_reaches_parent(self):
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            script = folder / 'solver'
            script.write_text('#!/usr/bin/env python3\nimport sys\n'
                'if "--input_syntax" in sys.argv:\n'
                ' print("% SZS status Unsatisfiable for x")\n'
                ' print("ERROR: AddressSanitizer: heap-use-after-free", file=sys.stderr)\n'
                ' sys.exit(98)\n'
                'print("cnf(a,axiom,$false).")\n')
            script.chmod(0o755)
            case = Case('transform', [str(script)], directory, 'roundtrip', 'Unsatisfiable')
            result = run_case(case, folder, 5, False, asan=True)
            self.assertEqual(result['semantic_outcome'], 'pass')
            self.assertEqual(result['memory_outcome'], 'fail')
            self.assertEqual(result['outcome'], 'fail')
            self.assertTrue(result['validator_result']['sanitizer_messages'])

    def test_satisfiable_proof_obligation_fails(self):
        self.assertEqual(self.check_proof(PROOF, 'sat\n')[0], 'fail')

    def test_incomplete_answers_fail(self):
        self.assertEqual(self.check_proof(PROOF.replace('(check-sat)', '(check-sat)\n(check-sat)'))[0], 'fail')

    def test_unsupported_proof_step_never_passes(self):
        proof = PROOF.replace('(assert false)', '(echo "sorry: cnf transformation")\n(assert false)')
        self.assertEqual(self.check_proof(proof, 'sorry: cnf transformation\nunsat\n')[0], 'inconclusive')

    def test_bad_known_obligation_still_fails_with_unsupported_steps(self):
        proof = PROOF.replace('(assert false)', '(echo "sorry: cnf transformation")\n(assert false)')
        self.assertEqual(self.check_proof(proof, 'sorry: cnf transformation\nsat\n')[0], 'fail')

    def test_proof_parser_errors_cannot_be_hidden_by_unsat(self):
        self.assertEqual(self.check_proof(PROOF, 'unsat\n(error "bad input")\n')[0], 'fail')

    def test_absent_proof_boundaries_fail(self):
        self.assertEqual(self.check_proof('(check-sat)\n')[0], 'fail')

    def test_unknown_is_inconclusive(self):
        self.assertEqual(self.check_proof(PROOF, 'unknown\n')[0], 'inconclusive')

    def test_empty_transformation_is_reparsed(self):
        with tempfile.TemporaryDirectory() as directory, patch('validation.subprocess.run',
                return_value=SimpleNamespace(stdout='% SZS status Satisfiable for x\n', stderr='', returncode=0)) as run:
            self.assertEqual(validate_roundtrip('% only comments\n', Path(directory), 'vampire', 'Satisfiable', 5)[0], 'pass')
            run.assert_called_once()

    def test_erased_contradiction_cannot_pass_roundtrip(self):
        with tempfile.TemporaryDirectory() as directory, patch('validation.subprocess.run',
                return_value=SimpleNamespace(stdout='% SZS status Satisfiable for x\n', stderr='', returncode=0)):
            self.assertEqual(validate_roundtrip('', Path(directory), 'vampire', 'Unsatisfiable', 5)[0], 'fail')

    def test_sanitizer_report_survives_timeout(self):
        messages = sanitizer_messages('', '==7==ERROR: AddressSanitizer: heap-use-after-free\n')
        self.assertEqual(combine('inconclusive', 'wall timeout', messages, [], True),
                         ('fail', 'sanitizer reported errors', 'fail'))

    def test_bad_answer_is_retained_separately_from_memory_failure(self):
        self.assertEqual(combine('fail', 'wrong answer', [], [{'kind': 'InvalidRead'}], False)[0], 'fail')
        self.assertEqual(combine('pass', '', [], [{'kind': 'invalid-xml'}], False)[0], 'inconclusive')

    def test_discovery_timeout_saves_diagnostics(self):
        with tempfile.TemporaryDirectory() as directory, patch('option_cases.subprocess.run',
                side_effect=subprocess.TimeoutExpired(['vampire'], 1, output=b'partial catalogue', stderr=b'asan detail')):
            folder = Path(directory)
            with self.assertRaises(ValueError): catalogue('vampire', folder, timeout=1)
            self.assertTrue(json.loads((folder / 'discovery.json').read_text())['timeout'])
            self.assertEqual((folder / 'stderr.log').read_text(), 'asan detail')

    def test_catalogue_can_be_read_when_sanitizer_fails_at_exit(self):
        with tempfile.TemporaryDirectory() as directory, patch('option_cases.subprocess.run',
                return_value=SimpleNamespace(stdout='--mode\n\tdefault: vampire\n\tvalues: vampire,output\n',
                    stderr='ERROR: LeakSanitizer: detected memory leaks', returncode=98)):
            entries, _ = catalogue('vampire', Path(directory))
            self.assertEqual(entries[0]['values'], ['vampire', 'output'])
            self.assertEqual(json.loads((Path(directory) / 'discovery.json').read_text())['exit'], 98)

    def test_standard_input_is_saved_and_delivered(self):
        with tempfile.TemporaryDirectory() as directory:
            case = Case('stdin', [sys.executable, '-c', 'import sys; print(sys.stdin.read(), end="")'],
                        directory, 'exact', 'hello\n', stdin_text='hello\n')
            result = run_case(case, Path(directory), 5, False)
            self.assertEqual(result['outcome'], 'pass')
            self.assertEqual((Path(result['artifacts']) / 'stdin.txt').read_text(), 'hello\n')

    def test_timed_out_asan_failure_is_not_lost(self):
        with tempfile.TemporaryDirectory() as directory:
            case = Case('asan', [sys.executable, '-c',
                'import sys,time; print("ERROR: AddressSanitizer: heap-use-after-free", file=sys.stderr, flush=True); time.sleep(10)'], directory)
            result = run_case(case, Path(directory), 0.1, False)
            self.assertEqual(result['outcome'], 'fail')
            self.assertEqual(result['semantic_outcome'], 'inconclusive')
            self.assertEqual(result['memory_outcome'], 'fail')


if __name__ == '__main__': unittest.main()
