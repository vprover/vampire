import unittest
from runtime_options_cases import cases, truth_table, arguments
from runtime_options import assess, evaluate_result, run_suite
from runtime_options_audit import solver_command

class RuntimeOptionsTests(unittest.TestCase):
    def test_truth_table_distinguishes_empty_clause_and_empty_set(self):
        self.assertEqual(truth_table([]),{})
        self.assertIsNone(truth_table([[]]))

    def test_truth_table_needs_every_clause(self):
        self.assertIsNone(truth_table([['p','q'],['~p','q'],['p','~q'],['~p','~q']]))
        self.assertEqual(truth_table([['p','q'],['~p','q'],['p','~q']]),{'p':True,'q':True})

    def test_counter_does_not_replace_semantic_check(self):
        case=next(c for c in cases() if c.name=='blocked_clause_elimination-unsat-on')
        row=assess(case,'% SZS status Satisfiable\nBlocked clauses: 2\n','',0,False,None)
        self.assertEqual(row['semantic_outcome'],'fail');self.assertEqual(row['activation'],'observed')

    def test_zero_counter_does_not_claim_activation(self):
        case=next(c for c in cases() if c.name=='blocked_clause_elimination-sat-on')
        row=assess(case,'% SZS status Satisfiable\nBlocked clauses: 0\n','',0,False,None)
        self.assertEqual(row['semantic_outcome'],'pass');self.assertEqual(row['activation'],'inconclusive')

    def test_no_status_is_inconclusive(self):
        self.assertEqual(assess(cases()[0],'User error: unavailable\n','',4,False,None)['semantic_outcome'],'inconclusive')

    def test_model_checker_rejection_is_semantic_failure(self):
        class Reject:
            def check_model(self,*_): raise ValueError('wrong table')
        case=next(c for c in cases() if c.model)
        row=assess(case,'% SZS status Satisfiable\n','',0,False,Reject())
        self.assertEqual(row['semantic_outcome'],'fail')

    def test_suite_has_both_answers_for_nine_options(self):
        groups={}
        for case in cases(): groups.setdefault(case.option,set()).add(case.expected)
        self.assertEqual(len(groups),10)
        for option,answers in groups.items():
            self.assertEqual(answers,{'Satisfiable'} if option=='fmb_start_size' else {'Satisfiable','Unsatisfiable'})

    def test_fmb_does_not_set_saturation_only_avatar_option(self):
        for case in cases():
            if case.model: self.assertNotIn('-av',arguments(case))

    def test_fmb_activation_requires_the_requested_start(self):
        class Accept:
            def check_model(self,*_): return {'domain_size':2}
        case=next(c for c in cases() if c.model and c.value=='2')
        bad=assess(case,'% TRYING [1]\n% TRYING [2]\n% SZS status Satisfiable\n','',0,False,Accept())
        good=assess(case,'% TRYING [2]\n% SZS status Satisfiable\n','',0,False,Accept())
        self.assertEqual(bad['activation'],'inconclusive')
        self.assertEqual(good['activation'],'observed')

    def test_audit_excludes_discovery_and_help_commands(self):
        for name,argv in [('discovery/options',['--show_options','on']),('behavior/help',['--help','on'])]:
            self.assertFalse(solver_command({'name':name,'command':['/tmp/vampire',*argv],'check':'szs'})[0])

    def test_audit_keeps_real_solver_with_listing_disabled(self):
        self.assertTrue(solver_command({'name':'behavior/example','command':['/tmp/vampire','--show_options','off','x.p'],'check':'szs'})[0])

    def test_audit_excludes_transformations_and_rejections(self):
        self.assertFalse(solver_command({'name':'behavior/transform','command':['/tmp/vampire','--mode','clausify','x.p'],'check':'szs'})[0])
        self.assertFalse(solver_command({'name':'corpus/reject','command':['/tmp/vampire','x.p'],'check':'reject'})[0])

    def test_audit_counts_exact_unsat_core_solver_output(self):
        self.assertTrue(solver_command({'name':'corpus/core','command':['/tmp/vampire','-om','ucore','x.smt2'],
            'check':'exact','expected':'unsat\n(\none\ntwo\n)\n'})[0])



    def test_fixture_count_and_activation_contract(self):
        suite = cases()
        self.assertEqual(len(suite), 47)
        self.assertEqual(len({case.name for case in suite}), 47)
        self.assertEqual(sum(case.activation_required for case in suite), 27)
        exempt = [case.name for case in suite if not case.activation_required and case.marker]
        self.assertEqual(exempt, ['predicate_elimination-multi-occurrence-on'])

    def test_conflicting_answers_fail_even_when_last_answer_matches(self):
        case = next(case for case in cases() if case.expected == 'Unsatisfiable')
        row = assess(case, '% SZS status Satisfiable\n% SZS status Unsatisfiable\n', '', 0, False)
        self.assertEqual(row['semantic_outcome'], 'fail')

    def test_assertion_is_not_hidden_by_correct_answer(self):
        row = assess(cases()[0], '% SZS status Satisfiable\nAssertion violation\n', '', 0, False)
        self.assertEqual(row['semantic_outcome'], 'fail')

    def test_instrumentation_failure_keeps_correct_logical_answer(self):
        case = next(case for case in cases() if case.name == 'blocked_clause_elimination-sat-on')
        base = {'semantic_outcome': 'pass', 'semantic_reason': '', 'exit': 97, 'wall_timeout': False,
                'sanitizer_messages': [], 'sanitizer_warnings': [],
                'valgrind_errors': [{'kind': 'Leak_DefinitelyLost', 'message': 'lost allocation'}]}
        row = evaluate_result(case, base, '% SZS status Satisfiable\nBlocked clauses: 2\n', '', 'valgrind')
        self.assertEqual(row['semantic_outcome'], 'pass')
        self.assertEqual(row['activation'], 'observed')
        self.assertEqual(row['memory_outcome'], 'fail')
        self.assertEqual(row['outcome'], 'fail')

    def test_required_activation_missing_does_not_pass(self):
        case = next(case for case in cases() if case.name == 'blocked_clause_elimination-sat-on')
        base = {'semantic_outcome': 'pass', 'semantic_reason': '', 'exit': 0, 'wall_timeout': False,
                'sanitizer_messages': [], 'sanitizer_warnings': [], 'valgrind_errors': []}
        row = evaluate_result(case, base, '% SZS status Satisfiable\nBlocked clauses: 0\n', '', 'release')
        self.assertEqual(row['semantic_outcome'], 'pass')
        self.assertEqual(row['outcome'], 'inconclusive')
        self.assertEqual(row['memory_outcome'], 'not-instrumented')

    def test_fatal_leak_checker_warning_keeps_memory_inconclusive(self):
        case = cases()[0]
        base = {'semantic_outcome': 'pass', 'semantic_reason': '', 'exit': 98, 'wall_timeout': False,
                'sanitizer_messages': [], 'sanitizer_warnings': ['LeakSanitizer has encountered a fatal error.'],
                'valgrind_errors': []}
        row = evaluate_result(case, base, '% SZS status Satisfiable\n', '', 'asan')
        self.assertEqual(row['semantic_outcome'], 'pass')
        self.assertEqual(row['memory_outcome'], 'inconclusive')
        self.assertEqual(row['outcome'], 'inconclusive')

    def test_invalid_profile_is_rejected_before_creating_output(self):
        with self.assertRaisesRegex(ValueError, 'unknown runtime-option profile'):
            run_suite('unused', 'typo', 'unused')

    def test_cli_records_wrong_answer_and_returns_failure(self):
        import contextlib
        import io
        import json
        import tempfile
        from pathlib import Path
        from runtime_options import main
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            binary = root / 'vampire'
            binary.write_text('#!/bin/sh\nprintf "%s\\n" "% SZS status Unsatisfiable"\n')
            binary.chmod(0o755)
            output = root / 'results'
            with contextlib.redirect_stdout(io.StringIO()):
                code = main(['--build', str(root), '--profile', 'release', '--output', str(output),
                             '--filter', '^blocked_clause_elimination-sat-off$'])
            self.assertEqual(code, 1)
            summary = json.loads((output / 'summary.json').read_text())
            metadata = json.loads((output / 'metadata.json').read_text())
            self.assertEqual(summary['semantic_counts']['fail'], 1)
            self.assertEqual(metadata['binary_sha256'], summary['binary_sha256_after'])
            self.assertEqual(metadata['cases'][0]['expected'], 'Satisfiable')
            self.assertIn('runtime_options.py', metadata['harness_sha256'])


    def test_sanitizer_grace_termination_is_not_a_solver_signal_failure(self):
        case = cases()[0]
        base = {'semantic_outcome': 'inconclusive',
                'semantic_reason': 'terminated after sanitizer error grace expired',
                'exit': -9, 'wall_timeout': False, 'sanitizer_error_deadline': True,
                'sanitizer_messages': ['ERROR: AddressSanitizer: heap-use-after-free'],
                'sanitizer_warnings': [], 'valgrind_errors': []}
        row = evaluate_result(case, base, '', '', 'asan')
        self.assertEqual(row['semantic_outcome'], 'inconclusive')
        self.assertEqual(row['semantic_reason'], base['semantic_reason'])
        self.assertEqual(row['memory_outcome'], 'fail')
        self.assertEqual(row['outcome'], 'fail')
        self.assertIn('sanitizer error grace expired', row['reason'])


if __name__ == '__main__':
    unittest.main()
