import argparse
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import run
from report import section


class CoverageResume(unittest.TestCase):
    def test_changing_counter_destination_refuses_resume(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp)
            args = argparse.Namespace(output=output, resume=True)
            environment = {name: os.environ.get(name) for name in (
                'ASAN_OPTIONS', 'UBSAN_OPTIONS', 'LSAN_OPTIONS', 'LD_LIBRARY_PATH',
                'LD_PRELOAD', 'GCOV_PREFIX', 'GCOV_PREFIX_STRIP', 'GCOV_ERROR_FILE', 'GCOV_EXIT_AT_ERROR')}
            environment['GCOV_PREFIX'] = '/original-counter-output'
            run.atomic_json(output / 'run.json', {
                'arguments': {'output': str(output), 'resume': False}, 'commit': 'commit',
                'source_sha256': 'source', 'harness_sha256': {}, 'environment': environment})
            with patch.object(run, 'checked_output', return_value='commit'), \
                 patch.object(run, 'source_fingerprint', return_value='source'), \
                 patch.object(run, 'harness_hashes', return_value={}), \
                 patch.dict(os.environ, {'GCOV_PREFIX': '/different-counter-output'}):
                with self.assertRaisesRegex(ValueError, 'instrumentation environment'):
                    run.validate_resume(args)

    def test_mode_contract_is_part_of_saved_input_identity(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp)
            source = output / 'input.p'
            source.write_text('cnf(a,axiom,p).')
            contract = source.with_suffix('.mode.json')
            contract.write_text('{"expected": "p"}')
            case = run.Case('mode/contract', ['/vampire', str(source)], str(output), source=str(source))
            before = run.input_hashes([case], output)
            self.assertIn(str(contract), before)
            contract.write_text('{"expected": "q"}')
            self.assertNotEqual(before, run.input_hashes([case], output))

    def test_new_sections_are_not_hidden_in_other_checks(self):
        for name in ('arithmetic/round/native/sat', 'datatype/tree/rule', 'parser/numeral/positive', 'mode/interpolant', 'portfolio/smt-logic/UF',
                     'portfolio/properties/casc', 'portfolio/induction/mixed'):
            with self.subTest(name=name):
                self.assertNotEqual(section({'name': name}), 'Other corpus checks')


if __name__ == '__main__': unittest.main()
