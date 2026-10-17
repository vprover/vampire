import copy
from pathlib import Path
import tempfile
import unittest

from finite_model_validation import check_model, InvalidModel, validate_model

ORACLE = {'size': 2, 'names': {'constants': ['a0', 'a1'], 'function': 'f', 'relation': 'r'},
          'function': [1, 0], 'relation': [[True, False], [False, True]]}
MODEL = """% SZS output start FiniteModel for test
tff(d0,type,'fmb_$i_1':$i).
tff(d1,type,'fmb_$i_2':$i).
tff(domain,axiom,![X:$i]:(X='fmb_$i_1'|X='fmb_$i_2')).
tff(distinct,axiom,'fmb_$i_1'!='fmb_$i_2').
tff(a0t,type,a0:$i).
tff(a1t,type,a1:$i).
tff(a0d,axiom,a0='fmb_$i_1').
tff(a1d,axiom,a1='fmb_$i_2').
tff(ft,type,f:($i)>$i).
tff(fd,axiom,f('fmb_$i_1')='fmb_$i_2' & f('fmb_$i_2')='fmb_$i_1').
tff(rt,type,r:($i*$i)>$o).
tff(rd,axiom,r('fmb_$i_1','fmb_$i_1') & ~r('fmb_$i_1','fmb_$i_2') & ~r('fmb_$i_2','fmb_$i_1') & r('fmb_$i_2','fmb_$i_2')).
% SZS output end FiniteModel for test
"""


class FiniteModelValidation(unittest.TestCase):
    def rejected(self, text, oracle=None):
        with self.assertRaises(InvalidModel): check_model(text, ORACLE if oracle is None else oracle)

    def test_complete_model_is_checked(self):
        report = check_model(MODEL, ORACLE)
        self.assertEqual(report['function_equations'], 2)
        self.assertEqual(report['relation_literals'], 4)

    def test_domain_numbering_need_not_match_input_names(self):
        text = MODEL.replace("a0='fmb_$i_1'", "a0='fmb_$i_2'").replace("a1='fmb_$i_2'", "a1='fmb_$i_1'")
        self.assertEqual(check_model(text, ORACLE)['domain_size'], 2)

    def test_wrong_function_table_rejected(self):
        self.rejected(MODEL.replace("f('fmb_$i_1')='fmb_$i_2'", "f('fmb_$i_1')='fmb_$i_1'"))

    def test_wrong_relation_table_rejected(self):
        self.rejected(MODEL.replace("~r('fmb_$i_1','fmb_$i_2')", "r('fmb_$i_1','fmb_$i_2')"))

    def test_missing_function_entry_rejected(self):
        self.rejected(MODEL.replace(" & f('fmb_$i_2')='fmb_$i_1'", ''))

    def test_missing_negative_relation_entry_rejected(self):
        self.rejected(MODEL.replace(" & ~r('fmb_$i_1','fmb_$i_2')", ''))

    def test_collapsed_input_constants_rejected(self):
        self.rejected(MODEL.replace("a1='fmb_$i_2'", "a1='fmb_$i_1'"))

    def test_conflicting_definition_rejected(self):
        self.rejected(MODEL.replace('tff(rt,type', "tff(bad,axiom,f('fmb_$i_1')='fmb_$i_1').\ntff(rt,type"))

    def test_false_output_axiom_rejected(self):
        self.rejected(MODEL.replace('tff(rt,type', "tff(bad,axiom,a0!=a0).\ntff(rt,type"))

    def test_extra_missing_declaration_table_rejected(self):
        self.rejected(MODEL.replace('tff(rt,type', 'tff(g,type,g:($i)>$i).\ntff(rt,type'))

    def test_undeclared_symbol_rejected(self):
        self.rejected(MODEL.replace('tff(rt,type', 'tff(bad,axiom,rogue(a0)).\ntff(rt,type'))

    def test_unknown_atom_cannot_hide_behind_a_true_disjunct(self):
        self.rejected(MODEL.replace('tff(rt,type', 'tff(bad,axiom,(a0=a0|rogue)).\ntff(rt,type'))

    def test_wrong_domain_size_rejected(self):
        oracle = copy.deepcopy(ORACLE); oracle['size'] = 3
        self.rejected(MODEL, oracle)

    def test_missing_or_reversed_or_repeated_boundaries_rejected(self):
        self.rejected(MODEL.replace('% SZS output end FiniteModel for test', ''))
        self.rejected(MODEL + MODEL)
        self.rejected('% SZS output end FiniteModel for test\n' + MODEL.split('% SZS output end')[0])

    def test_unsupported_sort_rejected(self):
        self.rejected(MODEL.replace('tff(a0t,type,a0:$i)', 'tff(a0t,type,a0:s)'))

    def test_malformed_declaration_rejected(self):
        self.rejected(MODEL.replace('f:($i)>$i', 'f:($i*)>$i'))

    def test_quantified_predicate_definition_is_evaluated(self):
        text = MODEL[:MODEL.index('tff(rd,axiom')]
        text += "tff(rd,axiom,![X:$i,Y:$i]:(r(X,Y)<=>(X=Y))).\n% SZS output end FiniteModel for test\n"
        self.assertEqual(check_model(text, ORACLE)['relation_literals'], 4)

    def test_validation_failure_is_saved(self):
        import json
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory); oracle = folder / 'oracle.json'
            oracle.write_text(json.dumps(ORACLE))
            outcome, reason = validate_model('no model', folder, oracle)
            self.assertEqual(outcome, 'fail')
            self.assertIn('boundaries', reason)
            self.assertIn('error', json.loads((folder / 'model-validation.json').read_text()))


if __name__ == '__main__': unittest.main()
