#!/usr/bin/env python3
"""Inject pthread creation failures and require a diagnostic without an abort."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cc', default='cc')
    args = parser.parse_args()
    if args.output.exists(): parser.error('choose a new output directory')
    out, binary = args.output.resolve(), args.binary.resolve()
    out.mkdir(parents=True)
    helper = Path(__file__).parent / 'fixtures/fail_pthread_create.c'
    library = out / 'fail-pthread.so'
    command = [args.cc, '-shared', '-fPIC', str(helper), '-o', str(library)]
    (out / 'compile-command.json').write_text(json.dumps(command, indent=2))
    result = subprocess.run(command, capture_output=True, text=True)
    (out / 'compile.log').write_text(result.stdout + result.stderr)
    if result.returncode: return 1
    problem = out / 'false.p'
    problem.write_text('cnf(a,axiom,$false).\n')
    rows = []
    for error in ('EAGAIN', 'ENOMEM', 'EPERM'):
        folder = out / error
        folder.mkdir()
        env = {**os.environ, 'LD_PRELOAD': str(library), 'VAMPIRE_TEST_PTHREAD_ERROR': error}
        command = [str(binary), '-t', '1', '-m', '0', '-p', 'off', str(problem)]
        (folder / 'command.json').write_text(json.dumps({
            'argv': command, 'env': {k: env[k] for k in ('LD_PRELOAD', 'VAMPIRE_TEST_PTHREAD_ERROR')}}, indent=2))
        try:
            result = subprocess.run(command, env=env, capture_output=True, text=True, timeout=10)
            stdout, stderr, code = result.stdout, result.stderr, result.returncode
        except subprocess.TimeoutExpired as expired:
            stdout, stderr, code = (expired.stdout or b'').decode(errors='replace'), (expired.stderr or b'').decode(errors='replace'), None
        (folder / 'stdout.log').write_text(stdout)
        (folder / 'stderr.log').write_text(stderr)
        resource_status = '% SZS status ResourceOut' in stdout
        passed = (code == 4 and 'System error:' in stdout and
                  resource_status == (error != 'EPERM') and
                  'Aborted by signal' not in stdout and 'terminate called' not in stderr)
        rows.append({'error': error, 'exit': code, 'outcome': 'pass' if passed else 'fail', 'artifacts': str(folder)})
        print(f'{"PASS" if passed else "FAIL"} thread creation {error}: exit {code}; logs: {folder}', flush=True)
    (out / 'summary.json').write_text(json.dumps({
        'binary': str(binary), 'binary_sha256': hashlib.sha256(binary.read_bytes()).hexdigest(),
        'results': rows}, indent=2))
    return int(any(row['outcome'] != 'pass' for row in rows))


if __name__ == '__main__': raise SystemExit(main())
