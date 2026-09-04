"""Shared helpers for the tstat analysis scripts.

Parsing of Vampire `-tstat on` logs plus the TPTP problem headers.
See ingest.py for the schema that comes out of this.
"""

import os
import re
import sqlite3

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
DB = os.path.join(HERE, "tstat.db")
OUT = os.path.join(HERE, "out")
LOGDIR = os.path.join(ROOT, "problemsALLlocal_tstat11156_tstat-on_i100K")
PROBLEMS = os.path.join(ROOT, "Problems")

# The printer uses U+03BC (GREEK SMALL LETTER MU); accept U+00B5 too, just in case.
UNIT_NS = {"ns": 1, "μs": 1000, "µs": 1000, "ms": 10**6, "s": 10**9}
_U = "ns|μs|µs|ms|s"
# `instr:` was added alongside `cnt:` when TIME_TRACE gained hardware instruction
# counters; it is optional here so that older sweeps still parse. A value of "-"
# means the counter was unavailable for that run (no perf, or not Linux).
INSTR_UNIT = {"": 1, "k": 1000, "M": 10**6, "G": 10**9}

FLAT_BEGIN = "===== start of flattened time profile ====="
FLAT_END = "===== end of flattened time profile ====="
TREE_BEGIN = "===== start of time trace ====="
TREE_END = "===== end of time trace ====="

_INSTR = r"(?:,\s*instr:\s*(?P<i>-|\d+)\s*(?P<iu>[GMk]?)\s*)?"

RE_ROOT = re.compile(
    r"^\[root\]\s*\(total:\s*(?P<t>\d+)\s*(?P<tu>" + _U + r"),"
    r"\s*avg:\s*(?P<a>\d+)\s*(?P<au>" + _U + r"),"
    r"\s*cnt:\s*(?P<c>\d+)\s*" + _INSTR + r"\)\s*$"
)
RE_NODE = re.compile(
    r"^(?P<ind>[ │├└─]*)\[\s*(?P<pct>\d+)%\]\s"
    r"(?P<name>.*?)\s*"
    r"\(total:\s*(?P<t>\d+)\s*(?P<tu>" + _U + r"),"
    r"\s*avg:\s*(?P<a>\d+)\s*(?P<au>" + _U + r"),"
    r"\s*cnt:\s*(?P<c>\d+)\s*" + _INSTR + r"\)\s*$"
)

# Node names are a closed vocabulary (Debug/TimeProfiling.hpp plus ad-hoc TIME_TRACE
# literals).  Anything else in a trace line is interleaved garbage, so we reject it.
KNOWN_NODES = frozenset(
    """
    SAT solver
    activation
    add clause
    backward simplification
    backward superposition index maintenance
    binary resolution index maintenance
    clause generation
    clause selection
    codetree subsumption index maintenance
    consequence finding
    fmb definition introduction
    forward demodulation
    forward demodulation index maintenance
    forward simplification
    forward superposition index maintenance
    hvci compute hash
    hvci insert
    hvci retrieve
    hyper superposition
    immediate simplification
    init
    interpreted evaluation
    literal order aftercheck
    literal selection
    LRS limit maintenance
    main loop
    minimizing solver time
    naming
    parsing
    passive container maintenance
    perform superposition
    preprocessing
    property evaluation
    redundancy check
    resolution
    run
    shuffling things
    sine selection
    sort sharing
    splitting
    splitting component index maintenance
    splitting component index usage
    splitting model update
    superposition
    term sharing
    unification with abstraction
    uwa fixed point
    """.strip().splitlines()
)
KNOWN_NODES = frozenset(n.strip() for n in KNOWN_NODES)


def _dur(val, unit):
    return int(val) * UNIT_NS[unit]


def _instr(m):
    """Instruction count from a matched line: None when absent or reported as '-'."""
    v = m.groupdict().get("i")
    if v is None or v == "-":
        return None
    return int(v) * INSTR_UNIT[m.group("iu") or ""]


def _consistent(total_ns, avg_ns, cnt):
    """total == avg*cnt up to the printer's aggressive unit rounding.

    The printer drops to whole units at 10x the unit boundary, so `avg` can be off
    by up to 10% and `total` by up to 10%; be generous but not vacuous.
    """
    if cnt <= 0:
        return False
    return abs(total_ns - avg_ns * cnt) <= 0.25 * total_ns + 2 * avg_ns + 1000


def _indent_depth(ind):
    """Depth of a trace-tree line from its box-drawing prefix.

    Root children are printed with a 2-space lead then `|--`; each further level adds
    5 columns.  We only need a monotone, self-consistent measure, so count columns.
    """
    return (len(ind) - 2) // 5 + 1 if len(ind) >= 2 else 0


def parse_flat(text):
    """Parse the flattened profile.

    Returns ((root_ns, root_instr), [(name, total_ns, avg_ns, cnt, instr)]) or
    (None, reason).
    `instr` is None when the run had no hardware instruction counter.
    Strict: the section must appear exactly once, be fully parsable, use only known
    node names, respect total<=root and pct<=100, satisfy total~=avg*cnt, and be
    sorted by total descending (which is how the printer emits it).
    """
    if text.count(FLAT_BEGIN) != 1 or text.count(FLAT_END) != 1:
        return None, "flat-section-missing-or-duplicated"
    seg = text.split(FLAT_BEGIN, 1)[1].split(FLAT_END, 1)[0]
    lines = [l for l in seg.split("\n") if l.strip()]
    if not lines:
        return None, "flat-section-empty"
    m = RE_ROOT.match(lines[0])
    if not m:
        return None, "flat-bad-root"
    root, root_instr = _dur(m.group("t"), m.group("tu")), _instr(m)
    rows = []
    for ln in lines[1:]:
        mm = RE_NODE.match(ln)
        if not mm:
            return None, "flat-bad-line"
        name = mm.group("name").strip()
        if name not in KNOWN_NODES:
            return None, "flat-unknown-node"
        t = _dur(mm.group("t"), mm.group("tu"))
        a = _dur(mm.group("a"), mm.group("au"))
        c = int(mm.group("c"))
        if int(mm.group("pct")) > 100 or t > root * 1.02 or not _consistent(t, a, c):
            return None, "flat-inconsistent"
        rows.append((name, t, a, c, _instr(mm)))
    if len(rows) != len(set(r[0] for r in rows)):
        return None, "flat-duplicate-node"
    for i in range(len(rows) - 1):
        if rows[i][1] < rows[i + 1][1]:
            return None, "flat-not-sorted"
    return (root, root_instr), rows


def parse_tree(text):
    """Parse the nesting trace tree.

    Returns ((root_ns, root_instr), [(path, name, depth, total_ns, avg_ns, cnt,
    instr)]) or (None, reason).
    `path` is the dotted ancestry including the node itself, e.g.
    "main loop.run.forward simplification.forward demodulation".
    """
    if text.count(TREE_BEGIN) != 1 or text.count(TREE_END) != 1:
        return None, "tree-section-missing-or-duplicated"
    seg = text.split(TREE_BEGIN, 1)[1].split(TREE_END, 1)[0]
    lines = [l for l in seg.split("\n") if l.strip()]
    if not lines:
        return None, "tree-section-empty"
    m = RE_ROOT.match(lines[0])
    if not m:
        return None, "tree-bad-root"
    root, root_instr = _dur(m.group("t"), m.group("tu")), _instr(m)
    rows = []
    stack = []  # (depth, name) of the ancestors
    for ln in lines[1:]:
        mm = RE_NODE.match(ln)
        if not mm:
            return None, "tree-bad-line"
        name = mm.group("name").strip()
        if name not in KNOWN_NODES:
            return None, "tree-unknown-node"
        t = _dur(mm.group("t"), mm.group("tu"))
        a = _dur(mm.group("a"), mm.group("au"))
        c = int(mm.group("c"))
        if int(mm.group("pct")) > 100 or t > root * 1.02 or not _consistent(t, a, c):
            return None, "tree-inconsistent"
        d = _indent_depth(mm.group("ind"))
        if d < 1 or d > len(stack) + 1:
            return None, "tree-bad-indent"
        del stack[d - 1:]
        stack.append(name)
        rows.append((".".join(stack), name, d, t, a, c, _instr(mm)))
    return (root, root_instr), rows


def add_self_times(tree_rows):
    """Annotate tree rows with exclusive (self) time and instructions."""
    child_t, child_i = {}, {}
    for path, _name, _d, t, _a, _c, i in tree_rows:
        parent = path.rsplit(".", 1)[0] if "." in path else ""
        child_t[parent] = child_t.get(parent, 0) + t
        if i is not None:
            child_i[parent] = child_i.get(parent, 0) + i
    out = []
    for path, name, d, t, a, c, i in tree_rows:
        self_i = None if i is None else i - child_i.get(path, 0)
        out.append((path, name, d, t, a, c, i, t - child_t.get(path, 0), self_i))
    return out


# ---------------------------------------------------------------- scalar outputs

RE_SZS = re.compile(r"^% SZS status (\S+)", re.M)
# The hyphen matters: "Refutation not found, non-redundant clauses discarded" is the
# reason LRS gives when its limits threw away something it later needed, so it is
# exactly the category to watch when changing LRS. Without it the line failed to match
# at all and 95 runs of the 11156 sweep recorded an empty termination.
RE_TERM = re.compile(r"^% Termination reason: ([A-Za-z][A-Za-z ,-]*)\s*$", re.M)
RE_TIME = re.compile(r"^% Time elapsed: ([0-9.]+) s\s*$", re.M)
RE_MEM = re.compile(r"^% Peak memory usage: (\d+) MB\s*$", re.M)
RE_INSTR = re.compile(r"^% Instructions burned: (\d+) \(million\)\s*$", re.M)
RE_SIGNAL = re.compile(r"Aborted by signal\s*(\S*)")
# e.g. "User error: Vampire higher-order is currently not compatible with theory
# reasoning" -- the problem was never attempted, so it is not a measurement failure.
RE_USERERR = re.compile(r"^(?:% )?User error: (.*)$", re.M)
# statistics rows: "% Label | proof | total"  or  "% Label | total"
RE_STAT = re.compile(r"^% ([^|]*[^|\s])\s*\|\s*(\d+)\s*(?:\|\s*(\d+))?\s*$", re.M)
RE_SECTION = re.compile(r"^% ([A-Z][A-Z/ ]*[A-Z])\s+\|", re.M)


def parse_scalars(text):
    d = {}
    m = RE_SZS.search(text)
    d["szs"] = m.group(1) if m else None
    m = RE_TERM.search(text)
    d["termination"] = m.group(1).strip() if m else None
    m = RE_TIME.search(text)
    d["time_s"] = float(m.group(1)) if m else None
    m = RE_MEM.search(text)
    d["peak_mb"] = int(m.group(1)) if m else None
    m = RE_INSTR.search(text)
    d["instr_M"] = int(m.group(1)) if m else None
    m = RE_SIGNAL.search(text)
    d["signal"] = (m.group(1) or "UNKNOWN") if m else None
    m = RE_USERERR.search(text)
    d["user_error"] = m.group(1).strip()[:120] if m else None
    return d


def parse_stats(text):
    """The `% Label | proof | total` statistics block, as (section, label, proof, total)."""
    section = None
    out = []
    for ln in text.split("\n"):
        ms = RE_SECTION.match(ln)
        if ms and ms.group(1).isupper():
            section = ms.group(1).strip()
            continue
        mm = RE_STAT.match(ln)
        if not mm:
            continue
        label = mm.group(1).strip()
        if label != label.strip("-") or not label:
            continue
        a, b = mm.group(2), mm.group(3)
        if b is None:
            out.append((section, label, None, int(a)))
        else:
            out.append((section, label, int(a), int(b)))
    return out


# ------------------------------------------------------------------ TPTP headers

RE_SPC = re.compile(r"^% SPC\s+:\s+(\S+)", re.M)
RE_STATUS = re.compile(r"^% Status\s+:\s+(\S+)", re.M)
RE_RATING = re.compile(r"^% Rating\s+:\s+([0-9.]+)", re.M)
# The first metric sits on the same line as `% Syntax   :`, the rest are continuation
# lines -- hence the optional prefix.  THF/TFF headers report `Number of symbols`
# where FOF/CNF report `predicates` and `functors`, and omit `Maximal term depth`.
_PFX = r"^%\s+(?:Syntax\s+:\s+)?"
_SYN = {
    "formulae": _PFX + r"Number of formulae\s+:\s+(\d+)",
    "atoms": _PFX + r"Number of atoms\s+:\s+(\d+)",
    "equ_atoms": _PFX + r"Number of atoms\s+:\s+\d+\s+\(\s*(\d+) equ\)",
    "max_formula_atoms": _PFX + r"Maximal formula atoms\s+:\s+(\d+)",
    "connectives": _PFX + r"Number of connectives\s+:\s+(\d+)",
    "max_formula_depth": _PFX + r"Maximal formula depth\s+:\s+(\d+)",
    "max_term_depth": _PFX + r"Maximal term depth\s+:\s+(\d+)",
    "predicates": _PFX + r"Number of predicates\s+:\s+(\d+)",
    "functors": _PFX + r"Number of functors\s+:\s+(\d+)",
    "symbols": _PFX + r"Number of symbols\s+:\s+(\d+)",
    "variables": _PFX + r"Number of variables\s+:\s+(\d+)",
    "types": _PFX + r"Number of types\s+:\s+(\d+)",
    "type_conns": _PFX + r"Number of type conns\s+:\s+(\d+)",
}
_SYN = {k: re.compile(v, re.M) for k, v in _SYN.items()}

# CNF headers count different things: "Number of clauses" and "Number of literals"
# where the others say "formulae" and "atoms", and they have no connectives line at
# all. Without these, every CNF problem got size = NULL and dropped out of each
# size-based report -- 8 474 problems, a third of the corpus, and the dialect with by
# far the most parse-dominated runs. Mapped onto the same fields so that `size` means
# the same kind of thing (a count of syntactic units) in every dialect.
_SYN_CNF = {
    "formulae": _PFX + r"Number of clauses\s+:\s+(\d+)",
    "atoms": _PFX + r"Number of literals\s+:\s+(\d+)",
    "equ_atoms": _PFX + r"Number of literals\s+:\s+\d+\s+\(\s*(\d+) equ\)",
    "max_formula_atoms": _PFX + r"Maximal clause size\s+:\s+(\d+)",
}
_SYN_CNF = {k: re.compile(v, re.M) for k, v in _SYN_CNF.items()}


def problem_path(problem):
    """`AGT001+1.p` -> <repo>/Problems/AGT/AGT001+1.p"""
    return os.path.join(PROBLEMS, problem[:3], problem)


def parse_tptp_header(path):
    """Read only the header comment block; that is all we need and it keeps I/O small."""
    buf = []
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            for ln in fh:
                if not ln.strip():
                    continue  # the header block is broken up by blank lines
                if not ln.startswith("%"):
                    break  # first real formula: the header is over
                buf.append(ln)
                if len(buf) > 200:
                    break
    except OSError:
        return None
    head = "".join(buf)
    d = {}
    m = RE_SPC.search(head)
    d["spc"] = m.group(1) if m else None
    d["dialect"] = d["spc"].split("_")[0] if d["spc"] else None
    m = RE_STATUS.search(head)
    d["tptp_status"] = m.group(1) if m else None
    m = RE_RATING.search(head)
    d["rating"] = float(m.group(1)) if m else None
    for k, rx in _SYN.items():
        mm = rx.search(head)
        d[k] = int(mm.group(1)) if mm else None
    # CNF spells four of these differently; fill only what the FOF-shaped patterns
    # missed, so a header carrying both wordings keeps the primary reading.
    for k, rx in _SYN_CNF.items():
        if d.get(k) is None:
            mm = rx.search(head)
            if mm:
                d[k] = int(mm.group(1))
    # A CNF header has no connectives line, and clause structure is what would be
    # counted there; 0 keeps `size` = atoms + connectives + variables well-defined
    # rather than dropping the problem entirely.
    if d.get("connectives") is None and d.get("atoms") is not None:
        d["connectives"] = 0
    return d


RE_FAMILY = re.compile(r"^([A-Z]{3}\d{3})")


def log_to_problem(logname):
    """`Problems_AGT_AGT001+1.p.log` -> `AGT001+1.p`

    The sweep runner names each log after the problem's path with `/` turned into `_`,
    so the name depends on how the problem was reached. The 11131 sweep used a relative
    path and the 11142 one an absolute path into the local TPTP copy
    (`_home_sudamar2_TPTP-v9.3.1_Problems_AGT_AGT001+1.p.log`), so anchor on the
    `Problems_` segment wherever it occurs rather than at the start.
    """
    assert logname.endswith(".log")
    i = logname.find("Problems_")
    assert i >= 0, logname
    return logname[i + len("Problems_"):-len(".log")].split("_", 1)[1]


def family_of(problem):
    """Peer key: the TPTP problem number without its version/variant suffix.

    `CSR115+1.p`, `CSR115+2.p`, ... -> `CSR115`; `SWV422-1.001.p` -> `SWV422`.
    """
    m = RE_FAMILY.match(problem)
    return m.group(1) if m else problem[:3]


def connect(readonly=True):
    if readonly:
        con = sqlite3.connect("file:%s?mode=ro" % DB, uri=True)
    else:
        con = sqlite3.connect(DB)
    con.row_factory = sqlite3.Row
    return con


def ensure_out():
    os.makedirs(OUT, exist_ok=True)
    return OUT


# ------------------------------------------------------------------ presentation

def fmt_ns(ns):
    if ns is None:
        return "-"
    a = abs(ns)
    if a >= 10**9:
        return f"{ns/10**9:.1f}s"
    if a >= 10**6:
        return f"{ns/10**6:.0f}ms"
    if a >= 10**3:
        return f"{ns/10**3:.0f}us"
    return f"{ns:.0f}ns"


def fmt_n(n):
    if n is None:
        return "-"
    for div, suf in ((10**9, "G"), (10**6, "M"), (10**3, "k")):
        if abs(n) >= div:
            return f"{n/div:.1f}{suf}"
    return f"{n:.0f}"


class Table:
    """Print a ranked ASCII table and write the same rows to tstat/out/<name>.csv."""

    def __init__(self, name, cols, title=None):
        self.name = name
        self.cols = list(cols)          # (header, key, format) with format a callable
        self.rows = []
        self.title = title

    def add(self, d):
        self.rows.append(d)

    def _cells(self, d):
        return [("" if d.get(k) is None else f(d[k])) for _, k, f in self.cols]

    def render(self, limit=None):
        rows = self.rows[:limit] if limit else self.rows
        cells = [[h for h, _, _ in self.cols]] + [self._cells(d) for d in rows]
        w = [max(len(str(c[i])) for c in cells) for i in range(len(self.cols))]
        out = []
        if self.title:
            out.append("")
            out.append(self.title)
            out.append("-" * min(len(self.title), 100))
        for i, c in enumerate(cells):
            out.append("  ".join(str(x).ljust(w[j]) if j == 0 else str(x).rjust(w[j])
                                 for j, x in enumerate(c)))
            if i == 0:
                out.append("  ".join("-" * w[j] for j in range(len(self.cols))))
        return "\n".join(out)

    def write_csv(self):
        import csv
        p = os.path.join(ensure_out(), self.name + ".csv")
        with open(p, "w", newline="") as fh:
            wr = csv.writer(fh)
            wr.writerow([k for _, k, _ in self.cols])
            for d in self.rows:
                wr.writerow([d.get(k) for _, k, _ in self.cols])
        return p

    def emit(self, limit=40):
        print(self.render(limit))
        p = self.write_csv()
        extra = f" (showing {limit} of {len(self.rows)})" if len(self.rows) > (limit or 0) else ""
        print(f"\n-> {os.path.relpath(p, ROOT)}{extra}")
