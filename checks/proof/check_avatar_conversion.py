#!/usr/bin/env python3
"""Run with: python3 checks/proof/check_avatar_conversion.py [build/vampire]."""

from pathlib import Path
from itertools import product
import re
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
VAMPIRE = Path(sys.argv.pop(1)).resolve() if len(sys.argv) > 1 else ROOT / "build/vampire"


class AvatarConversionTests(unittest.TestCase):
    def proof(self, mode, fixture="theory-sat-conversion.p"):
        result = subprocess.run(
            [str(VAMPIRE), "--proof", mode, "--proof_extra", "replay", "--avatar_congruence_closure", "on",
             "--function_definition_elimination", "none", "--time_limit", "5",
             str(ROOT / "checks/proof" / fixture)],
            cwd=ROOT, text=True, capture_output=True, timeout=10, check=True)
        self.assertIn("% SZS status Unsatisfiable", result.stdout)
        start = result.stdout.index("% SZS output start")
        return result.stdout[start:result.stdout.index("% SZS output end", start)]

    def test_ac_mapping_and_definition_parents(self):
        for mode, fixture in product(
                ("tstp-ac", "tptp-ac", "tptp_ac"),
                ("theory-sat-conversion.p", "theory-sat-predicate-conversion.p")):
            with self.subTest(mode=mode, fixture=fixture):
                text = self.proof(mode, fixture)
                theory = re.search(
                    r"fof\((f\d+),axiom,\(\s*([^\n]*?)\),\s*"
                    r"introduced\(theory,\[theory_tautology_sat_conflict\],\[\]\)\)",
                    text, re.S)
                self.assertIsNotNone(theory)
                origin, formula = theory.groups()
                source = [literal.strip() for literal in formula.split("|")]
                conversion = re.search(
                    r"cnf\((s\d+), plain, (.*?), inference\(sat_conversion,"
                    r"\[avatar_map\(\[(.*?)\]\)\],\[" + origin + r",([^]]+)\]\)\)",
                    text)
                self.assertIsNotNone(conversion)
                _, sat_formula, mapping, parents = conversion.groups()
                definitions = parents.split(",")
                entries = re.findall(
                    r"map\(literal\(" + origin + r",(\d+)\),"
                    r"(positive|negative)\((\w+)\),(f\d+)\)", mapping)
                self.assertEqual(len(entries), len(source))
                self.assertEqual([int(e[0]) for e in entries], list(range(len(source))))
                self.assertEqual(len(set(definitions)), len(definitions))
                named_literals = []
                for index, polarity, name, definition in entries:
                    self.assertIn(definition, definitions)
                    defined = re.search(
                        r"fof\(" + definition + r",definition,\(\s*" + name +
                        r" <=> (.*?)\),\s*introduced", text, re.S)
                    self.assertIsNotNone(defined)
                    self.assertLess(defined.start(), conversion.start())
                    positive = defined.group(1).strip()
                    literal = source[int(index)]
                    if polarity == "negative":
                        if literal.startswith("~"):
                            self.assertEqual(literal[1:], positive)
                        else:
                            self.assertEqual(literal.replace("!=", "="), positive)
                            self.assertIn("!=", literal)
                    else:
                        self.assertEqual(literal, positive)
                    named_literals.append(("~" if polarity == "negative" else "") + name)
                self.assertCountEqual(sat_formula.split(" | "), named_literals)
                # The other conversions already have propositional FO origins.
                self.assertEqual(text.count("avatar_map("), 1)
                parsed = subprocess.run(
                    [str(VAMPIRE), "--mode", "output", "--proof_extra", "replay", "--input_syntax", "tptp"],
                    input=text, cwd=ROOT, text=True, capture_output=True, timeout=10)
                self.assertEqual(parsed.returncode, 0, parsed.stdout + parsed.stderr)

    def test_plain_tptp_unchanged(self):
        text = self.proof("tptp")
        self.assertIn("theory_tautology_sat_conflict", text)
        self.assertIn("inference(sat_conversion,[],[", text)
        self.assertNotIn("avatar_map(", text)


if __name__ == "__main__":
    unittest.main()
