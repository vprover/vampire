#!/usr/bin/env python3
"""Confronto sequenziale FO2 con/senza validateClause su un campione MIX."""
import argparse
import csv
import os
from pathlib import Path
import re
import statistics
import subprocess
import time
from collections import Counter

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=float, default=5)
    parser.add_argument('--repeats', type=int, default=2)
    parser.add_argument('--output', type=Path, default=ROOT / 'TEST_grafici/validate_clause_comparison.csv')
    args = parser.parse_args()
    if args.timeout <= 0 or args.repeats < 1:
        parser.error('timeout e repeats devono essere positivi')
    cases = []
    for family in ('equalityscaling', 'depthscaling', 'denseequality'):
        source = ROOT / f'TEST_grafici/GENERATED/MIX/{family}/{family}_3mode_benchmark_results.csv'
        with source.open() as stream:
            rows = list(csv.DictReader(stream))
        solved = sorted((r for r in rows if r['FO2_Status'] in ('Satisfiable', 'Unsatisfiable')),
                        key=lambda r: float(r['FO2_Time']))
        selected = ([solved[0], solved[-1]] if solved else [])
        for status in ('Unknown', 'Timeout'):
            candidates = [r for r in rows if r['FO2_Status'] == status]
            if candidates:
                selected.append(candidates[len(candidates)//2])
        if not selected:
            selected = rows[:2]
        for name in dict.fromkeys(r['FileName'] for r in selected):
            cases.append((family, name))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    results = []
    with args.output.open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=['family', 'FileName', 'repeat', 'validation', 'status', 'seconds', 'returncode'])
        writer.writeheader()
        for family, name in cases:
            path = ROOT / f'tests/generated/test2mix/fo2_datasets/{family}/{name}'
            for repeat in range(args.repeats):
                # Alternate order to reduce systematic warm-cache bias.
                for enabled in ((1, 0) if repeat % 2 == 0 else (0, 1)):
                    env = os.environ.copy()
                    for key in ('FO2_PREPROCESS_AUDIT', 'FO2_SEARCH_METRICS'):
                        env.pop(key, None)
                    env['FO2_VALIDATE_CLAUSES'] = str(enabled)
                    start = time.perf_counter()
                    try:
                        proc = subprocess.run([str(ROOT / 'build/vampire'), '--mode', 'fo2', '-t', str(args.timeout),
                                               '-m', '1024', str(path)], env=env, capture_output=True, text=True,
                                              timeout=args.timeout + 2)
                        output = proc.stdout + proc.stderr
                        statuses = re.findall(r'SZS status (\w+)', output)
                        status = statuses[-1] if statuses else ('Timeout' if 'Time limit' in output else 'Error')
                        code = proc.returncode
                        if code < 0:
                            status = 'Error'
                    except subprocess.TimeoutExpired:
                        status, code = 'Timeout', ''
                    row = dict(family=family, FileName=name, repeat=repeat + 1, validation=enabled,
                               status=status, seconds=f'{time.perf_counter()-start:.6f}', returncode=code)
                    results.append(row)
                    writer.writerow(row)
                    stream.flush()
            print(f'{family}/{name}: completato', flush=True)
    for enabled in (1, 0):
        runs = [r for r in results if r['validation'] == enabled]
        print(f'validation={enabled}: {dict(Counter(r["status"] for r in runs))}; '
              f'tempo totale={sum(float(r["seconds"]) for r in runs):.3f}s')
    differences = []
    ratios = []
    for family, name in cases:
        on = [r for r in results if r['family'] == family and r['FileName'] == name and r['validation'] == 1]
        off = [r for r in results if r['family'] == family and r['FileName'] == name and r['validation'] == 0]
        if [r['status'] for r in on] != [r['status'] for r in off]:
            differences.append((family, name))
        if all(r['status'] in ('Satisfiable', 'Unsatisfiable', 'Unknown') for r in on + off):
            ratios.append(statistics.median(float(r['seconds']) for r in off) /
                          statistics.median(float(r['seconds']) for r in on))
    print(f'Casi con differenze di esito: {differences}')
    if ratios:
        print(f'Rapporto mediano tempi OFF/ON (casi senza timeout): {statistics.median(ratios):.3f}')
    print(f'CSV: {args.output}')


if __name__ == '__main__':
    main()
