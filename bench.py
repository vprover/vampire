#!/usr/bin/env python3

import time
from subprocess import run, DEVNULL
from sys import argv
from pathlib import Path

VAMPIRE = argv[1]
PROB = argv[2]

def vamp(*args):
    global VAMPIRE, PROB
    start = time.time()
    result = run([VAMPIRE, PROB, '-p', 'off', '-t', '10', *args], stdout=DEVNULL, stderr=DEVNULL)
    end = time.time()
    return result.returncode, end - start

base_ok, base_time = vamp()
new_ok, new_time = vamp('-fc', 'on')
base = Path(PROB).stem
print(f"{base}\t{base_ok}\t{base_time:.3f}\t{new_ok}\t{new_time:.3f}")