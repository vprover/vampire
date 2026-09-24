#!/usr/bin/env python3
"""
Find (pragmatically) subset-minimal sets of input units vampire can prove a problem from, using
-drcl (drop_clauses).

  scripts/drop_inputs.py [-j N] [--timeout S] [--max-runs N] [--max-time S] \
      ./vampire <vampire options including problem> -p on

A run is identified by what it drops (LHS) and, if proven, yields the input units of its proof
(RHS): the proof lines tagged [input(...)], i.e. axioms/assumptions and the conjecture, or the
negated conjecture in cnf -- exactly the units the TPTP parser can drop. Every run is logged as

  [dropped units] -> [input units of the proof]

Phase 1 (greedy descent): at a node (LHS, RHS), the units F of the RHS are tried one by one
(axioms before the conjecture, units already dropped successfully elsewhere first); the first
LHS + {F} still proven becomes the next node. A node none of whose drops is proven is MINIMAL.
The child's RHS is either a subset of the parent's (the parent's proof used F needlessly) or brings
in units the parent did not use (a different proof).

Phase 2 (further minimal sets): every new minimal set has to miss a unit of each one found so far,
so the next descent starts from dropping a (smallest first) hitting set of the minimal sets found.

Failure memo: once dropping a set X was not proven, dropping any superset of X is predicted not to
be proven either, and is not run (fewer axioms cannot prove more -- exact logically, though only an
approximation of what vampire manages within its limits). A MINIMAL verdict relying on such a
prediction is labelled "(memo)". "Not proven" only ever means not proven within the given limits.

Runs are cached by their LHS. The search stops when --max-runs real runs or --max-time seconds
are used up, or when no hitting set is left to try.

A -drcl/--drop_clauses already in the vampire command is kept in every run (and shown in LHS).
Only the TPTP parser drops input units, so SMT-LIB input is not supported.
"""

import argparse
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

PROVEN = {"Theorem", "Unsatisfiable", "ContradictoryAxioms"}
CONJECTURE_ROLES = {"conjecture", "negated conjecture"}

STATUS_RE = re.compile(r"^% SZS status (\w+)")
# "14. killed(agatha,agatha) [input(conjecture)]", optionally "[input(axiom) name]"
INPUT_RE = re.compile(r"^(\d+)\. .* \[input\(([^)]*)\)(?: [^\]]*)?\]$")


def split_drops(command):
    """Separate a -drcl/--drop_clauses already present in command from the rest of it."""
    rest, drops = [], []
    i = 0
    while i < len(command):
        if command[i] in ("-drcl", "--drop_clauses") and i + 1 < len(command):
            drops += [int(n) for n in command[i + 1].split(",") if n]
            i += 2
        else:
            rest.append(command[i])
            i += 1
    return rest, drops


class Result:
    def __init__(self, status, inputs, roles):
        self.status = status  # SZS status, or a description of what went wrong
        self.inputs = inputs  # number -> proof line, for the input units of the proof
        self.roles = roles    # number -> input role ("axiom", "negated conjecture", ...)

    @property
    def proven(self):
        return self.status in PROVEN

    @property
    def rhs(self):
        return frozenset(self.inputs)


def run(command, drops, timeout):
    cmd = list(command)
    if drops:
        cmd += ["-drcl", ",".join(map(str, sorted(drops)))]
    try:
        proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              text=True, errors="replace", timeout=timeout)
    except subprocess.TimeoutExpired:
        return Result("outer timeout", {}, {})

    status = None
    reason = None  # a time limit, e.g., comes without an SZS status
    inputs = {}
    roles = {}
    in_proof = False
    for line in proc.stdout.splitlines():
        m = STATUS_RE.match(line)
        if m and status is None:
            status = m.group(1)
        if line.startswith("% Termination reason: ") and reason is None:
            reason = line[len("% Termination reason: "):].strip()
        if line.startswith("% SZS output start"):
            in_proof = True
        elif line.startswith("% SZS output end"):
            in_proof = False
        elif in_proof:
            m = INPUT_RE.match(line)
            if m:
                inputs[int(m.group(1))] = line
                roles[int(m.group(1))] = m.group(2)
    if status is None:
        status = reason or f"no SZS status (exit code {proc.returncode})"
    return Result(status, inputs, roles)


def show(ns):
    return str(sorted(ns))


def size_order(s):
    return (len(s), sorted(s))


class OutOfBudget(Exception):
    pass


class Search:
    def __init__(self, command, root, args, pool):
        self.command = command
        self.root = root
        self.args = args
        self.pool = pool
        self.start = time.monotonic()
        self.cache = {}         # LHS -> Result
        self.failed = []        # LHSs not proven, for the failure memo
        self.predicted = 0      # runs skipped because the memo predicted failure
        self.good_drops = set() # units whose drop was proven somewhere
        self.texts = {}         # unit number -> its proof line
        self.minimal = []       # (rhs, lhs, relies on memo), in the order found
        self.visited = set()    # LHSs descended through

    def predicted_to_fail(self, lhs):
        return any(f <= lhs for f in self.failed)

    def run_batch(self, lhss, notes):
        """Run the given uncached LHSs in parallel and log them; notes: LHS -> suffix of its log line."""
        if len(self.cache) >= self.args.max_runs or \
                (self.args.max_time is not None and time.monotonic() - self.start >= self.args.max_time):
            raise OutOfBudget()
        lhss = lhss[:self.args.max_runs - len(self.cache)]
        results = self.pool.map(lambda lhs: run(self.command, lhs, self.args.timeout), lhss)
        for lhs, res in zip(lhss, results):
            self.cache[lhs] = res
            if not res.proven:
                self.failed.append(lhs)
                print(f"{show(lhs)} -> not proven ({res.status})", flush=True)
                continue
            self.texts.update(res.inputs)
            print(f"{show(lhs)} -> {show(res.rhs)}{notes(lhs, res)}", flush=True)

    def descend(self, lhs):
        """Greedily drop units from the proven node lhs until no drop is proven; record the minimal set."""
        while True:
            self.visited.add(lhs)
            res = self.cache[lhs]
            # axioms before the conjecture, units already dropped successfully first
            cands = sorted(res.rhs, key=lambda f: (res.roles.get(f) in CONJECTURE_ROLES, f not in self.good_drops, f))
            memo_used = False
            nxt = None
            i = 0
            while nxt is None and i < len(cands):
                # the next stretch of candidates holding up to -j of them that need a real run
                j, torun = i, []
                while j < len(cands) and len(torun) < self.args.jobs:
                    child = lhs | {cands[j]}
                    if child not in self.cache and not self.predicted_to_fail(child):
                        torun.append(child)
                    j += 1

                def note(child, cres):
                    introduced = cres.rhs - res.rhs
                    return f"   (different proof: +{show(introduced)})" if introduced else "   (subset)"
                if torun:
                    self.run_batch(torun, note)
                for f in cands[i:j]:  # the first proven one in candidate order wins
                    child = lhs | {f}
                    if child not in self.cache:
                        if not self.predicted_to_fail(child):
                            raise OutOfBudget()  # the batch got cut short
                        memo_used = True
                        self.predicted += 1
                    elif self.cache[child].proven:
                        self.good_drops.add(f)
                        nxt = child
                        break
                i = j
            if nxt is None:
                break
            lhs = nxt

        rhs = self.cache[lhs].rhs
        if all(m[0] != rhs for m in self.minimal):
            self.minimal.append((rhs, lhs, memo_used))
            print(f"MINIMAL {show(rhs)}{' (memo)' if memo_used else ''}   (reached by dropping {show(lhs)})", flush=True)

    def hitting_sets(self):
        """The subset-minimal sets containing a unit of every minimal set found, smallest first."""
        hs = [frozenset()]
        for rhs, _, _ in self.minimal:
            ext = set()
            for h in hs:
                if h & rhs:
                    ext.add(h)
                else:
                    ext.update(h | {f} for f in rhs)
            hs = [h for h in ext if not any(g < h for g in ext)]
        return sorted(hs, key=size_order)

    def explore(self):
        self.run_batch([self.root], lambda lhs, res: "")
        root_res = self.cache[self.root]
        if not root_res.proven:
            return False
        print("the proof uses these input units:")
        for n in sorted(root_res.rhs):
            print("  " + root_res.inputs[n])
        print(flush=True)

        self.descend(self.root)
        while True:
            seeds = []
            for h in self.hitting_sets():
                s = self.root | h
                if s in self.visited or (s in self.cache and not self.cache[s].proven):
                    continue
                if s not in self.cache and self.predicted_to_fail(s):
                    self.predicted += 1
                    continue
                seeds.append(s)
            if not seeds:
                print("no further hitting set to try", flush=True)
                return True
            batch = seeds[:self.args.jobs]
            self.run_batch([s for s in batch if s not in self.cache], lambda lhs, res: "   (seed)")
            for s in batch:  # the first proven seed in order wins
                if s not in self.cache:
                    raise OutOfBudget()  # the batch got cut short
                if self.cache[s].proven:
                    self.descend(s)
                    break

    def summary(self):
        print()
        elapsed = time.monotonic() - self.start
        print(f"{len(self.cache)} runs ({self.predicted} predicted failures not run), {elapsed:.0f} s")
        found = {res.rhs for res in self.cache.values() if res.proven}
        print(f"{len(self.minimal)} minimal premise sets:")
        for rhs, lhs, memo in self.minimal:
            # the memo can be wrong: a later run may prove from a proper subset after all
            smaller = [r for r in found if r < rhs]
            refuted = f"   REFUTED, contains {show(min(smaller, key=size_order))}" if smaller else ""
            print(f"  MINIMAL {show(rhs)}{' (memo)' if memo else ''}   (reached by dropping {show(lhs)}){refuted}")

        others = sorted(found - {m[0] for m in self.minimal}, key=size_order)
        if others:
            print("other premise sets seen:")
            for rhs in others:
                smaller = [r for r in found if r < rhs]
                mark = f"not minimal, contains {show(min(smaller, key=size_order))}" if smaller else "not examined"
                print(f"  {show(rhs)}  {mark}")

        new = sorted(set(self.texts) - self.cache[self.root].rhs)
        if new:
            print()
            print("input units not in the original proof:")
            for n in new:
                print("  " + self.texts[n])


def main():
    parser = argparse.ArgumentParser(
        description="Find subset-minimal sets of input units a problem can be proven from, by dropping proof premises.",
        usage="%(prog)s [-j N] [--timeout S] [--max-runs N] [--max-time S] ./vampire <vampire options including problem> -p on")
    parser.add_argument("-j", "--jobs", type=int, default=1,
                        help="number of vampire runs to do in parallel (default: 1)")
    parser.add_argument("--timeout", type=float, default=None,
                        help="outer wall-clock limit per run in seconds (default: none, rely on vampire's -t)")
    parser.add_argument("--max-runs", type=int, default=1000,
                        help="stop after this many vampire runs (default: 200)")
    parser.add_argument("--max-time", type=float, default=None,
                        help="stop starting new runs after this many seconds (default: none)")
    parser.add_argument("command", nargs=argparse.REMAINDER,
                        help="the vampire invocation")
    args = parser.parse_args()
    if not args.command:
        parser.error("missing the vampire invocation")
    if args.max_runs < 1:
        parser.error("--max-runs must be at least 1")

    command, base_drops = split_drops(args.command)

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        search = Search(command, frozenset(base_drops), args, pool)
        try:
            if not search.explore():
                return 1
        except OutOfBudget:
            print("budget used up", flush=True)
    search.summary()
    return 0


if __name__ == "__main__":
    sys.exit(main())
