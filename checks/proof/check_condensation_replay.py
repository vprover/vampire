#!/usr/bin/env python3
"""Run with: python3 checks/proof/check_condensation_replay.py [build/vampire]."""

from pathlib import Path
import re
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
VAMPIRE = Path(sys.argv.pop(1)).resolve() if len(sys.argv) > 1 else ROOT / "build/vampire"


class CondensationReplayTests(unittest.TestCase):
    def check_proof(self, fixture, mode):
        result = subprocess.run(
            [str(VAMPIRE), "--proof", "tstp-ac", "--proof_extra", "replay", "--condensation", mode,
             "--avatar", "off", "--forward_subsumption_resolution", "off",
             "--backward_subsumption_resolution", "off", "--time_limit", "5",
             str(ROOT / "checks/proof" / fixture)],
            cwd=ROOT, text=True, capture_output=True, timeout=10, check=True)
        self.assertIn("% SZS status Unsatisfiable", result.stdout)
        start = result.stdout.index("% SZS output start")
        text = result.stdout[start:result.stdout.index("% SZS output end", start)]
        self.assertRegex(text,
            r"inference\(condensation,\[unifier\(\[subs\(f\d+,\[b\(X\d+,a\)\]\)\]\),"
            r"removed_literals\(literal\(f\d+,\d+\)\)\],\[f\d+\]\)")
        self.assertEqual(len(re.findall(r"inference\(condensation,", text)), 1)
        parsed = subprocess.run(
            [str(VAMPIRE), "--mode", "output", "--proof_extra", "replay", "--input_syntax", "tptp"],
            input=text, cwd=ROOT, text=True, capture_output=True, timeout=10)
        self.assertEqual(parsed.returncode, 0, parsed.stdout + parsed.stderr)

    def test_general_condensation(self):
        self.check_proof("condensation.p", "on")

    def test_fast_condensation(self):
        self.check_proof("condensation-fast.p", "fast")

    def test_unit_resulting_resolution(self):
        result = subprocess.run(
            [str(VAMPIRE), "--proof", "tstp-ac", "--proof_extra", "replay", "--avatar", "off",
             "--unit_resulting_resolution", "on",
             "--forward_subsumption_resolution", "off",
             "--backward_subsumption_resolution", "off", "--time_limit", "5",
             str(ROOT / "checks/proof/replay-extended.p")],
            cwd=ROOT, text=True, capture_output=True, timeout=10, check=True)
        start = result.stdout.index("% SZS output start")
        text = result.stdout[start:result.stdout.index("% SZS output end", start)]
        self.assertIn("inference(unit_resulting_resolution,[unifier([subs(", text)
        self.assertIn("resolved_literals([literal(", text)
        parsed = subprocess.run(
            [str(VAMPIRE), "--mode", "output", "--proof_extra", "replay", "--input_syntax", "tptp"],
            input=text, cwd=ROOT, text=True, capture_output=True, timeout=10)
        self.assertEqual(parsed.returncode, 0, parsed.stdout + parsed.stderr)


if __name__ == "__main__":
    unittest.main()
