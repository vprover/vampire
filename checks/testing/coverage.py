#!/usr/bin/env python3
"""Capture line, function, and branch coverage, including unexecuted objects."""
import argparse
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build', type=Path, default=ROOT / 'build/testing/coverage')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--gcov-tool', default='gcov')
    parser.add_argument('--tool-dir', type=Path, help='directory containing matching lcov and genhtml executables')
    parser.add_argument('--jobs', type=int, default=4)
    parser.add_argument('--allow-overlapping-functions', action='store_true',
                        help='preserve gcov counters without cross-metric consistency checks for overlapping C++ functions')
    args = parser.parse_args()
    build, output = args.build.resolve(), args.output.resolve()
    if output.exists(): parser.error('output already exists; choose a new directory')
    if not list(build.rglob('*.gcno')): parser.error('build has no GCC coverage notes')
    output.mkdir(parents=True)
    def run(name, command):
        (output / (name + '.command.json')).write_text(json.dumps(command, indent=2))
        with (output / (name + '.log')).open('w') as log:
            subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)
    lcov = str(args.tool_dir.resolve() / 'lcov') if args.tool_dir else 'lcov'
    genhtml = str(args.tool_dir.resolve() / 'genhtml') if args.tool_dir else 'genhtml'
    run('version', [lcov, '--version'])
    # An exclusion may match only the initial capture, or an optional dependency.
    # Keep data errors fatal; only unused source-filter patterns are warnings.
    common = [lcov, '--parallel', str(args.jobs), '--branch-coverage',
              '--ignore-errors', 'unused', '--rc', 'geninfo_unexecuted_blocks=1',
              '--gcov-tool', args.gcov_tool]
    consistency = ['--rc', 'check_data_consistency=0'] if args.allow_overlapping_functions else []
    common += consistency
    (output / 'settings.json').write_text(json.dumps({
        'build': str(build), 'gcov': args.gcov_tool, 'lcov': lcov,
        'cross_metric_consistency_checks': not args.allow_overlapping_functions,
        'unexecuted_blocks_count_as_missed': True}, indent=2))
    scope = ['--include', str(ROOT / '*')]
    for folder in ('UnitTests', 'Test', 'cadical', 'viras', 'z3', 'mini-gmp-6.3.0', 'build'):
        if folder == 'z3' and not (ROOT / folder / 'README.md').exists():
            continue
        scope += ['--exclude', str(ROOT / folder / '*')]
    run('initial', common + ['--capture', '--initial', '--directory', str(build), *scope,
                            '--output-file', str(output / 'initial.info')])
    run('capture', common + ['--capture', '--directory', str(build), *scope,
                            '--output-file', str(output / 'executed.info')])
    run('merge', common + ['--add-tracefile', str(output / 'initial.info'),
                          '--add-tracefile', str(output / 'executed.info'),
                          '--output-file', str(output / 'coverage.info')])
    run('html', [genhtml, *consistency, '--branch-coverage', str(output / 'coverage.info'),
                 '--output-directory', str(output / 'html'), '--prefix', str(ROOT)])
    run('summary', common + ['--summary', str(output / 'coverage.info')])
    from campaign import coverage_gaps
    (output / 'summary.json').write_text(json.dumps(coverage_gaps(output / 'coverage.info'), indent=2))
    print((output / 'summary.log').read_text())
    print(f'HTML: {output / "html/index.html"}')


if __name__ == '__main__': main()
