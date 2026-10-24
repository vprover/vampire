#!/usr/bin/env python3
"""Cross-check generated SMT expectations with a separate Z3 executable."""
import argparse
import json
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('summary', type=Path)
    parser.add_argument('--z3', default='z3')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): parser.error('output already exists')
    cases = json.loads(args.summary.read_text())['results']
    seen, answers = set(), []
    for case in cases:
        path = case.get('source', '')
        if not path.endswith('.smt2') or not case['name'].startswith(('generated/', 'edge/theory/')) or path in seen:
            continue
        seen.add(path)
        result = subprocess.run([args.z3, path], text=True, capture_output=True, timeout=10)
        expected = 'sat' if case['expected'] == 'Satisfiable' else 'unsat'
        passed = result.returncode == 0 and result.stdout.strip() == expected and not result.stderr
        answers.append({'path': path, 'expected': expected, 'z3': result.stdout.strip(),
                        'stderr': result.stderr, 'exit': result.returncode, 'pass': passed})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(answers, indent=2))
    passed = sum(a['pass'] for a in answers)
    print(f'{passed}/{len(answers)} generated SMT expectations agree with Z3')
    return int(not answers or passed != len(answers))


if __name__ == '__main__': raise SystemExit(main())
