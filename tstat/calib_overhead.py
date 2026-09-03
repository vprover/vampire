#!/opt/local/bin/python3.14
"""Measure what one TIME_TRACE scope costs, so we know which nodes measure themselves.

TimeTrace::ScopedTimer takes one `steady_clock::now()` on entry and one on exit, plus a
linear scan of the current node's children to find the one with a matching name pointer
(Debug/TimeProfiling.cpp, ScopedTimer::ScopedTimer).  A node whose reported average is
within a small multiple of that is reporting instrumentation, not work.

Compiles and runs a small benchmark; nothing is written into the repo.

    ./calib_overhead.py
    ./rpt_hotspots.py --overhead <the number this prints>
"""

import os
import shutil
import subprocess
import sys
import tempfile

SRC = r"""
#include <chrono>
#include <cstdio>
#include <vector>
#include <cstring>

using Clock = std::chrono::steady_clock;

// mimics TimeTrace::ScopedTimer: two clock reads plus a short scan over sibling
// nodes comparing `const char*` identities.
struct Node { const char* name; long long sum; unsigned cnt; };

static std::vector<Node> children;

static const char* NAMES[8] = {"a","b","c","d","e","f","g","h"};

struct Scoped {
  Node* n; Clock::time_point start;
  Scoped(const char* name) {
    n = nullptr;
    for (auto& c : children) if (c.name == name) { n = &c; break; }
    if (!n) { children.push_back({name,0,0}); n = &children.back(); }
    start = Clock::now();
  }
  ~Scoped() { auto e = Clock::now(); n->sum += (e-start).count(); n->cnt++; }
};

int main() {
  const int N = 20000000;
  for (int i = 0; i < 8; i++) children.push_back({NAMES[i],0,0});

  // 1. bare clock read
  auto t0 = Clock::now();
  volatile long long acc = 0;
  for (int i = 0; i < N; i++) acc += Clock::now().time_since_epoch().count();
  auto t1 = Clock::now();
  double one = std::chrono::duration_cast<std::chrono::nanoseconds>(t1-t0).count() / double(N);

  // 2. a whole scoped timer, hitting the 4th sibling (a typical short scan)
  t0 = Clock::now();
  for (int i = 0; i < N; i++) { Scoped s(NAMES[3]); }
  t1 = Clock::now();
  double scope = std::chrono::duration_cast<std::chrono::nanoseconds>(t1-t0).count() / double(N);

  // 3. empty loop, to subtract loop overhead
  t0 = Clock::now();
  for (int i = 0; i < N; i++) acc += i;
  t1 = Clock::now();
  double empty = std::chrono::duration_cast<std::chrono::nanoseconds>(t1-t0).count() / double(N);

  printf("%.2f %.2f %.2f\n", one - empty, scope - empty, empty);
  return 0;
}
"""


def main():
    cxx = os.environ.get("CXX") or shutil.which("c++") or shutil.which("g++")
    if not cxx:
        sys.exit("no C++ compiler found; set CXX")
    with tempfile.TemporaryDirectory() as d:
        src = os.path.join(d, "calib.cpp")
        exe = os.path.join(d, "calib")
        open(src, "w").write(SRC)
        subprocess.run([cxx, "-O2", "-std=c++17", src, "-o", exe], check=True)
        out = subprocess.run([exe], check=True, capture_output=True, text=True).stdout
    one, scope, empty = (float(x) for x in out.split())
    print(f"  steady_clock::now()      {one:6.1f} ns")
    print(f"  one full TIME_TRACE scope{scope:6.1f} ns   <-- use this as --overhead")
    print(f"  (empty loop baseline     {empty:6.1f} ns)")
    print()
    print("A node whose reported average is below ~3x the scope cost is measuring mostly")
    print("itself.  In the reference sweep that is `term sharing` (146ns), `clause")
    print("generation` (142ns) and `literal order aftercheck` (295ns).")
    print()
    print("NB: this is *this* machine.  The sweep ran on the server, where the number")
    print("may differ; the shape of the conclusion does not.")


if __name__ == "__main__":
    main()
