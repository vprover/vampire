import copy
import gzip
import json
from pathlib import Path
import tempfile
import unittest

from coverage_overlay import sha256
from reachable_coverage import verify_entries, summary, render


class ReachableCoverageTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.build = self.root / 'build'
        self.build.mkdir()
        self.source = self.root / 'source'
        self.source.mkdir()
        self.source_file = self.source / 'sample.cpp'
        self.source_file.write_text('int f() { return 0; }')
        self.note = self.build / 'sample.cpp.gcno'
        self.note.write_bytes(b'notes')
        self.object = self.build / 'sample.cpp.o'
        self.object.write_bytes(b'object')
        self.binary = self.build / 'vampire'
        self.binary.write_bytes(b'binary')
        self.cache = self.build / 'CMakeCache.txt'
        self.cache.write_bytes(b'build options')
        self.proof = self.root / 'proof.md'
        self.proof.write_text('This fixture edge follows a constant false condition.')
        self.ledger_path = self.root / 'ledger.json'
        self.branches = [dict(count=0, source_block_id=4, destination_block_id=5, throw=False, fallthrough=True),
                         dict(count=9, source_block_id=4, destination_block_id=6, throw=False, fallthrough=False)]
        self.expected_note = self.root / 'overlay/capture/raw-merged/sample.cpp.gcno'
        self.document = {'gcc_version': '15.2.0', 'format_version': '2', 'current_working_directory': str(self.source),
                         'data_file': str(self.expected_note),
                         'files': [{'file': str(self.source_file), 'lines': [
                             {'function_name': '_Z1fv', 'line_number': 1, 'branches': self.branches}]}]}
        self.artifact = self.root / 'overlay/capture/gcov-json/merged/sample.cpp.gcno.json.gz'
        self.artifact.parent.mkdir(parents=True)
        self.write_artifact()
        self.metadata = {'build': str(self.build), 'source': str(self.source), 'output': str(self.root / 'overlay'), 'gcov_tool': 'gcov',
                         'original_gcno': {'sample.cpp.gcno': sha256(self.note)},
                         'immutable_files': {str(self.binary): sha256(self.binary)}}
        self.raw = {'exact_raw_counter_sum': True, 'objects': 1, 'per_object': [
            {'object': 'sample.cpp.gcno', 'gcc_version': '15.2.0', 'artifacts': {
                'merged': {'path': str(self.artifact), 'sha256': sha256(self.artifact),
                           'command': ['gcov', '--branch-probabilities', '--json-format', '--stdout', str(self.expected_note)]}}}]}
        self.ledger = {'schema_version': 1, 'build': {
            'source': str(self.source), 'path': str(self.build), 'gcc_version': '15.2.0',
            'gcno_sha256': dict(self.metadata['original_gcno']),
            'binary_sha256': dict(self.metadata['immutable_files']), 'cmake_cache_sha256': sha256(self.cache),
            'compiler_inputs_sha256': {str(self.cache): sha256(self.cache)}},
            'entries': [{'id': 'constant-condition', 'classification': 'proved-unreachable',
                'rationale': 'Constant false condition.', 'scope': 'This exact fixture binary.',
                'source': 'sample.cpp', 'source_sha256': sha256(self.source_file),
                'proof': {'path': 'proof.md', 'sha256': sha256(self.proof), 'supporting_sha256': {}},
                'mapping': 'unique-object-function-source-line',
                'lcov': {'line': 1, 'block': 'f0', 'branch': '4 -> 5', 'occurrence': 0},
                'contributors': [{'object': 'sample.cpp.gcno', 'gcno_sha256': sha256(self.note),
                    'object_sha256': sha256(self.object), 'function': '_Z1fv', 'ordinal': 0,
                    'source_block_id': 4, 'destination_block_id': 5, 'throw': False, 'fallthrough': True}]}]}
        self.metrics = {'lines': {(str(self.source_file), 1): True}, 'functions': {}, 'function_groups': {},
                        'branches': {(str(self.source_file), 1, 'f0', '4 -> 5', 0): False,
                                     (str(self.source_file), 1, '0', '4 -> 6', 0): True}}

    def write_artifact(self):
        self.artifact.write_bytes(gzip.compress(json.dumps(self.document).encode(), mtime=0))

    def verify(self):
        return verify_entries(self.ledger, self.ledger_path, self.metadata, self.raw, self.metrics)

    def test_one_proof_keeps_the_reachable_sibling_and_raw_metrics(self):
        before = copy.deepcopy(self.metrics)
        self.assertEqual(len(self.verify()), 1)
        self.assertEqual(self.metrics, before)
        self.assertEqual(summary(self.metrics)['branches'], {'hit': 1, 'found': 2, 'percent': 50})

    def test_stale_pinned_inputs_are_rejected(self):
        for path in (self.proof, self.source_file, self.object, self.note, self.binary, self.cache, self.artifact):
            with self.subTest(path=path):
                previous = path.read_bytes()
                path.write_bytes(previous + b'changed')
                with self.assertRaises(ValueError): self.verify()
                path.write_bytes(previous)

    def test_unlisted_note_is_rejected(self):
        (self.build / 'other.gcno').write_bytes(b'other object')
        with self.assertRaisesRegex(ValueError, 'inventory'): self.verify()

    def test_missing_object_inventory_is_rejected(self):
        self.raw['per_object'] = []
        with self.assertRaisesRegex(ValueError, 'inventory'): self.verify()

    def test_duplicate_object_inventory_is_rejected(self):
        self.raw['per_object'].append(copy.deepcopy(self.raw['per_object'][0]))
        with self.assertRaisesRegex(ValueError, 'inventory'): self.verify()

    def test_duplicate_exclusions_are_rejected(self):
        self.ledger['entries'].append(copy.deepcopy(self.ledger['entries'][0]))
        with self.assertRaisesRegex(ValueError, 'duplicate ledger'): self.verify()
        self.ledger['entries'][1]['id'] = 'other-id-same-branch'
        with self.assertRaisesRegex(ValueError, 'duplicate excluded'): self.verify()

    def test_hit_edge_cannot_be_excluded_even_if_proof_claims_it_is_dead(self):
        self.metrics['branches'][(str(self.source_file), 1, 'f0', '4 -> 5', 0)] = True
        with self.assertRaisesRegex(ValueError, 'was executed'): self.verify()

    def test_raw_hit_edge_cannot_be_excluded_even_with_zero_lcov_hit(self):
        self.branches[0]['count'] = 1
        self.write_artifact()
        self.raw['per_object'][0]['artifacts']['merged']['sha256'] = sha256(self.artifact)
        with self.assertRaisesRegex(ValueError, 'raw branch was executed'): self.verify()

    def test_another_template_instance_cannot_be_hidden_by_one_proof(self):
        instance = copy.deepcopy(self.document['files'][0]['lines'][0])
        instance['function_name'] = '_Z1fIiEv'
        self.document['files'][0]['lines'].append(instance)
        self.write_artifact()
        self.raw['per_object'][0]['artifacts']['merged']['sha256'] = sha256(self.artifact)
        with self.assertRaisesRegex(ValueError, 'ambiguous'): self.verify()

    def test_renumbered_lcov_mapping_is_rejected(self):
        old = (str(self.source_file), 1, '0', '4 -> 6', 0)
        self.metrics['branches'][(str(self.source_file), 1, '0', '9 -> 12', 0)] = self.metrics['branches'].pop(old)
        with self.assertRaisesRegex(ValueError, 'one-to-one'): self.verify()

    def test_ordinal_cannot_point_to_reachable_sibling(self):
        self.ledger['entries'][0]['contributors'][0]['ordinal'] = 1
        with self.assertRaisesRegex(ValueError, 'identity'): self.verify()

    def test_unproved_bug_blocked_classification_is_rejected(self):
        for classification in ('bug-blocked', 'unsupported', 'unknown', 'exception'):
            with self.subTest(classification=classification):
                self.ledger['entries'][0]['classification'] = classification
                with self.assertRaisesRegex(ValueError, 'only proved'): self.verify()

    def test_wrong_compiler_is_rejected(self):
        self.ledger['build']['gcc_version'] = 'different'
        with self.assertRaisesRegex(ValueError, 'compiler'): self.verify()

    def test_lcov_type_must_match_the_raw_edge(self):
        old = (str(self.source_file), 1, '0', '4 -> 6', 0)
        self.metrics['branches'][(str(self.source_file), 1, 'e0', '4 -> 6', 0)] = self.metrics['branches'].pop(old)
        with self.assertRaisesRegex(ValueError, 'type differs'): self.verify()

    def test_reassigned_raw_artifact_is_rejected(self):
        self.document['data_file'] = str(self.expected_note.parent / 'different.gcno')
        self.write_artifact()
        self.raw['per_object'][0]['artifacts']['merged']['sha256'] = sha256(self.artifact)
        with self.assertRaisesRegex(ValueError, 'data_file differs'): self.verify()

    def test_raw_command_must_reference_the_object(self):
        self.raw['per_object'][0]['artifacts']['merged']['command'][-1] = 'different.gcno'
        with self.assertRaisesRegex(ValueError, 'bound to its captured object'): self.verify()

    def test_proof_cannot_escape_ledger_bundle(self):
        self.ledger['entries'][0]['proof']['path'] = '../outside.md'
        with self.assertRaisesRegex(ValueError, 'escapes'): self.verify()

    def test_report_shows_raw_and_adjusted_denominators(self):
        report = {'target_percent': 100, 'target_met': True, 'raw': summary(self.metrics),
                  'reachable_branches': {'hit': 1, 'found': 1, 'percent': 100, 'remaining': 0},
                  'excluded_branch_count': 1, 'verified_exclusions': self.verify(),
                  'policy': 'Raw LCOV is unchanged.', 'limitation': 'Finite branch measurement.'}
        output = render(report)
        self.assertIn('| Raw branches | 1 | 2 | 50.000000% |', output)
        self.assertIn('| Reachable branches | 1 | 1 | 100.000000% |', output)
        self.assertIn('constant-condition', output)


if __name__ == '__main__': unittest.main()
