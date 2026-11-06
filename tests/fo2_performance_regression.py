"""Run with python3 tests/fo2_performance_regression.py after building Vampire."""

from pathlib import Path
import re
import os
import random
import subprocess
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]


class FO2PerformanceRegression(unittest.TestCase):
    def test_subsumption_keeps_factors_needed_for_refutation(self):
        # On the diagonal the first clause requires p(X,X), the second its
        # negation. A parent must not delete its shorter factor by collapsing
        # two occurrences onto one target literal.
        self.solve('cnf(a,axiom,p(X,Y) | p(Y,X)).\n'
                   'cnf(b,axiom,~p(X,Y) | ~p(Y,X)).\n', 'Unsatisfiable')

    def solve(self, source, expected, structural=False):
        with tempfile.TemporaryDirectory(prefix="fo2-regression-") as directory:
            problem = Path(directory) / "problem.p"
            problem.write_text(source)
            result = subprocess.run(
                [str(ROOT / "build/vampire"), "--mode", "fo2", "-t", "5",
                 "-m", "128", str(problem)],
                capture_output=True, text=True, timeout=10,
                env=dict(os.environ, FO2_STRUCTURAL_NAMING="1") if structural else None,
            )
        output = result.stdout + result.stderr
        self.assertEqual(result.returncode, 0, output)
        self.assertEqual(re.findall(r"SZS status (\w+)", output), [expected], output)
        return output

    def test_phase_profile_is_opt_in_and_global(self):
        # Both split alternatives contradict a ground fact. The aggregate must
        # survive branch changes and exclusive phase times must not double count.
        source = ("cnf(a,axiom,p(X) | q(Y)).\ncnf(b,axiom,~p(a) | r).\n"
                  "cnf(c,axiom,~p(a) | ~r).\ncnf(d,axiom,~q(b) | s).\n"
                  "cnf(e,axiom,~q(b) | ~s).")
        with patch.dict(os.environ):
            os.environ.pop("FO2_PHASE_PROFILE", None)
            baseline = self.solve(source, "Unsatisfiable")
        self.assertNotIn("FO2_PHASE ", baseline)
        with patch.dict(os.environ, {"FO2_PHASE_PROFILE": "1"}):
            output = self.solve(source, "Unsatisfiable")
        self.assertIn("FO2_PREPROCESS_TIME seconds=", output)
        reports = [line for line in output.splitlines() if line.startswith("FO2_PHASE ")]
        final = reports[-1]
        self.assertIn("scope=whole_search final=1", final)
        values = {key: float(value) for key, value in
                  re.findall(r"(\w+)=([\d.]+(?:e[+-]?\d+)?)", final)}
        self.assertEqual(values["branches_examined"], 3)
        self.assertEqual(values["splits"], 1)
        self.assertEqual(values["branches_closed_by_propagation"], 2)
        elapsed = values["elapsed_seconds"]
        exclusive = sum(value for key, value in values.items()
                        if key.endswith("_seconds") and key != "elapsed_seconds")
        self.assertLessEqual(exclusive, elapsed * 1.01 + 0.00001)

    def test_pending_subsumption_index_against_full_scan(self):
        # Same signature at different lengths, variables/constants, and live
        # deletion on selection exercise forward and backward retrieval.
        sources = [
            "cnf(a,axiom,p(X)|q(X)|r(X)).\ncnf(b,axiom,p(X)|q(X)).\n"
            "cnf(c,axiom,p(a)|q(a)|s(a)).\ncnf(d,axiom,p(a)|q(a)).",
            "cnf(a,axiom,p(X)|q(X)).\ncnf(b,axiom,p(a)|q(a)|r(a)).\n"
            "cnf(c,axiom,p(a)|q(a)|s(a)).\ncnf(d,axiom,p(X)|q(X)|r(X)).",
        ]
        for source in sources:
            with patch.dict(os.environ, {"FO2_VERIFY_PENDING_INDEX": "1", "FO2_VERIFY_INDEX": "1"}):
                self.solve(source, "Satisfiable")

    def test_structural_resolution_index(self):
        # Input functions would bypass the FO2 classifier. Generate rigid
        # function roots through Skolemization of accepted relational formulas.
        source = ""
        for i in range(2):
            for tag, matrix in (("a", f"p(Y) | q{i}(X)"), ("b", f"p(Y) | ~q{i}(X)"),
                                ("c", f"~p(Y) | r{i}(X)"), ("d", f"~p(Y) | ~r{i}(X)")):
                source += f"fof({tag}{i},axiom, ! [X] : ? [Y] : ({matrix})).\n"
        # A two-object model assigns positive and negative witnesses separately.
        with patch.dict(os.environ, {"FO2_SEARCH_METRICS": "1", "FO2_VERIFY_INDEX": "1"}):
            output = self.solve(source, "Satisfiable")
        self.assertIn("[FO2]", output)
        self.assertRegex(output, r"resolution_filtered=[1-9]\d*")
        self.solve(source + "fof(e,axiom, ! [Y] : p(Y)).", "Unsatisfiable")
        self.solve("cnf(a,axiom,p(a) | q).\ncnf(b,axiom,p(a) | ~q).\n"
                   "cnf(c,axiom,~p(b) | r).\ncnf(d,axiom,~p(b) | ~r).", "Satisfiable")

    def test_structural_quantifier_naming(self):
        witness = "fof(a,axiom, ! [X,Y] : (s(X,Y) | ? [X] : r(X,Y))).\n"
        for source, expected in (
            (witness, "Satisfiable"),
            (witness + "fof(b,axiom, ! [X,Y] : ~s(X,Y)).\n"
             "fof(c,axiom, ! [X,Y] : ~r(X,Y)).", "Unsatisfiable"),
            ("fof(a,axiom, ! [X] : ? [Y] : (r(X,Y) & ! [X] : ? [Y] : s(X,Y))).", "Satisfiable"),
            ("fof(a,axiom, ! [X] : ? [Y] : (r(X,Y) & ~r(X,X))).", "Satisfiable"),
            ("fof(a,axiom, ! [X] : (p(X) <=> ? [Y] : r(X,Y))).\n"
             "fof(b,axiom, ! [X] : p(X)).\nfof(c,axiom, ! [X,Y] : ~r(X,Y)).", "Unsatisfiable"),
            ("fof(a,axiom, ! [X] : (p(X) <~> ! [Y] : r(X,Y))).\n"
             "fof(b,axiom, ! [X] : p(X)).\nfof(c,axiom, ! [X,Y] : ~r(X,Y)).", "Satisfiable"),
        ):
            with self.subTest(source=source):
                self.solve(source, expected, structural=True)

    def test_pending_subsumption_preserves_answers(self):
        base = "cnf(a,axiom,p(X) | q(X)).\ncnf(b,axiom,p(X) | ~q(X)).\n"
        redundant = "".join(f"cnf(r{i},axiom,p(X) | q(X) | s{i}(X)).\n" for i in range(20))
        for source in (base + redundant, redundant + base):
            self.solve(source, "Satisfiable")
            self.solve(source + "cnf(c,axiom,~p(X) | q(X)).\n"
                       "cnf(d,axiom,~p(X) | ~q(X)).", "Unsatisfiable")
        # Shared predicate/sign signatures do not imply subsumption; argument
        # relationships must still be checked by one consistent substitution.
        self.solve("cnf(a,axiom,p(X) | q(X)).\n"
                   "cnf(b,axiom,p(a) | q(b)).\n"
                   "cnf(c,axiom,~p(a)).\ncnf(d,axiom,~q(b)).", "Unsatisfiable")

    def test_exact_tautologies_and_variable_scope(self):
        self.solve("cnf(a,axiom,p(X) | ~p(X)).", "Satisfiable")
        # Removing a clause whose complements only unify would miss this contradiction.
        self.solve("cnf(a,axiom,p(X) | ~p(Y)).\n"
                   "cnf(b,axiom,p(a)).\ncnf(c,axiom,~p(b)).", "Unsatisfiable")
        self.solve("cnf(a,axiom,p(X) | p(Y) | ~p(X)).\n"
                   "cnf(b,axiom,q(X) | r(X)).", "Satisfiable")

    def test_nested_equivalences(self):
        # A linear-size input that full NNF expands exponentially. Positive
        # units force the whole equivalence chain true, providing known answers.
        atoms = [f"p{i}(X)" for i in range(21)]
        chain = atoms[0]
        for atom in atoms[1:]:
            chain = f"({chain} <=> {atom})"
        units = "\n".join(
            f"fof(a{i},axiom, ! [X] : {atom})."
            for i, atom in enumerate(atoms)
        )
        for negated, expected in ((False, "Satisfiable"), (True, "Unsatisfiable")):
            with self.subTest(expected=expected):
                formula = f"~({chain})" if negated else chain
                self.solve(units + f"\nfof(chain,axiom, ! [X] : ({formula})).", expected)

    def test_resolution_and_splitting(self):
        for source, expected in (
            ("cnf(a,axiom,p(X) | q(Y)).\ncnf(b,axiom,~p(X)).", "Satisfiable"),
            ("cnf(a,axiom,p(X) | q(Y)).\ncnf(b,axiom,~p(X)).\n"
             "cnf(c,axiom,~q(Y)).", "Unsatisfiable"),
            ("cnf(a,axiom,p(X) | p(Y)).\ncnf(b,axiom,~p(X)).", "Unsatisfiable"),
            ("fof(a,axiom, ! [X] : ? [Y] : r(X,Y)).\n"
             "fof(b,axiom, ! [X,Y] : ~r(X,Y)).", "Unsatisfiable"),
        ):
            with self.subTest(source=source):
                self.solve(source, expected)

    def test_equivalence_polarities_and_equality(self):
        for source, expected in (
            ("fof(a,axiom, ! [X,Y] : (r(X,Y) <=> ~s(Y,X))).\n"
             "fof(b,axiom, ! [X,Y] : r(X,Y)).\n"
             "fof(c,axiom, ! [X,Y] : s(X,Y)).", "Unsatisfiable"),
            ("fof(a,axiom, ! [X] : (p(X) <~> q(X))).\n"
             "fof(b,axiom, ! [X] : p(X)).\n"
             "fof(c,axiom, ! [X] : ~q(X)).", "Satisfiable"),
            ("fof(a,axiom, ! [X] : (p(X) <~> q(X))).\n"
             "fof(b,axiom, ! [X] : p(X)).\n"
             "fof(c,axiom, ! [X] : q(X)).", "Unsatisfiable"),
            # Equality elimination currently rejects these inputs before the
            # preprocessor. Preserve its conservative Unknown boundary.
            ("fof(a,axiom, ! [X] : X = X).", "Unknown"),
            ("fof(a,axiom, ? [X] : X != X).", "Unknown"),
        ):
            with self.subTest(source=source):
                self.solve(source, expected)

    def test_ground_units_before_splitting(self):
        # Without propagation each mixed clause creates another branch, even
        # though its ground alternative is contradicted by an existing unit.
        clauses = "\n".join(
            f"cnf(c{i},axiom,g{i} | p{i}(X)).\ncnf(u{i},axiom,~g{i})."
            for i in range(20)
        )
        self.solve(clauses, "Satisfiable")
        self.solve(clauses + "\ncnf(contradiction,axiom,~p19(X)).", "Unsatisfiable")

    def test_ground_propagation_chain_and_scope(self):
        for source, expected in (
            ("cnf(a,axiom,g0).\ncnf(b,axiom,~g0 | g1).\n"
             "cnf(c,axiom,~g1 | p(X)).\ncnf(d,axiom,~p(X)).", "Unsatisfiable"),
            ("cnf(a,axiom,p(a)).\ncnf(b,axiom,~p(b)).", "Satisfiable"),
            ("cnf(a,axiom,p(a)).\ncnf(b,axiom,~p(X)).", "Unsatisfiable"),
            ("cnf(a,axiom,g).\ncnf(b,axiom,~g).", "Unsatisfiable"),
        ):
            with self.subTest(source=source):
                self.solve(source, expected)

    def test_small_universal_problems_against_boolean_oracle(self):
        # Every satisfiable universal, function-free problem here has a
        # singleton model. Exhaustive Boolean assignments therefore give an
        # independent oracle, including mixed ground/variable splitting.
        rng = random.Random(20261010)
        for case in range(60):
            clauses = [
                [(rng.randrange(5), bool(rng.randrange(2)), rng.choice(("X", "Y")))
                 for _ in range(rng.randint(1, 3))]
                for _ in range(10)
            ]
            satisfiable = any(
                all(any(bool(assignment & (1 << atom)) == positive
                        for atom, positive, _ in clause) for clause in clauses)
                for assignment in range(1 << 5)
            )
            lines = []
            for i, clause in enumerate(clauses):
                literals = []
                for atom, positive, variable in clause:
                    predicate = f"g{atom}" if atom < 2 else f"p{atom}({variable})"
                    if atom == 4:
                        other = "Y" if variable == "X" else "X"
                        predicate = f"r4({variable},{other})"
                    literals.append(predicate if positive else "~" + predicate)
                lines.append(f"cnf(c{i},axiom,({' | '.join(literals)})).")
            with self.subTest(case=case):
                self.solve("\n".join(lines), "Satisfiable" if satisfiable else "Unsatisfiable")

    def test_unit_matching_preserves_variable_scope(self):
        for source, expected in (
            ("cnf(a,axiom,p(X)).\ncnf(b,axiom,~p(X) | q(X)).\n"
             "cnf(c,axiom,~q(X)).", "Unsatisfiable"),
            ("cnf(a,axiom,p(a)).\ncnf(b,axiom,~p(X) | q(X)).\n"
             "cnf(c,axiom,p(b)).\ncnf(d,axiom,~q(b)).", "Unsatisfiable"),
            ("cnf(a,axiom,p(a)).\ncnf(b,axiom,~p(X) | q(X)).\n"
             "cnf(c,axiom,~q(b)).", "Satisfiable"),
            ("cnf(a,axiom,p(f(X))).\ncnf(b,axiom,~p(Y) | q(Y)).\n"
             "cnf(c,axiom,p(a)).\ncnf(d,axiom,~q(a)).", "Unsatisfiable"),
            ("cnf(a,axiom,p(X)).\ncnf(b,axiom,~p(f(Y)) | q(Y)).\n"
             "cnf(c,axiom,~q(Y)).", "Unsatisfiable"),
        ):
            with self.subTest(source=source):
                self.solve(source, expected)

    def test_units_generated_during_saturation(self):
        source = ("cnf(a,axiom,p(X) | q(X)).\n"
                  "cnf(b,axiom,p(X) | ~q(X)).\n"
                  "cnf(c,axiom,~p(X) | r(X)).\n")
        self.solve(source + "cnf(d,axiom,~p(X) | ~r(X)).", "Unsatisfiable")
        self.solve(source + "cnf(d,axiom,~p(X) | s(X)).", "Satisfiable")

    def test_unit_preprocessing_before_indexing(self):
        self.solve("cnf(a,axiom,p(X)).\n"
                   "cnf(b,axiom,~p(X) | r(X,Y)).\n"
                   "cnf(c,axiom,~r(X,Y)).", "Unsatisfiable")

    def test_wide_clause_with_short_generated_consequences(self):
        wide = " | ".join(f"p{i}(X)" for i in range(12))
        source = f"cnf(wide,axiom,({wide})).\n"
        for i in range(12):
            source += f"cnf(a{i},axiom,~p{i}(X) | r{i}(X)).\n"
            source += f"cnf(b{i},axiom,~p{i}(X) | ~r{i}(X)).\n"
        self.solve(source, "Unsatisfiable")


if __name__ == "__main__":
    unittest.main()
