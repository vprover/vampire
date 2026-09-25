#!/usr/bin/env python3
"""Build and run the master test matrix, retaining failures and coverage gaps."""
import argparse
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import math
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tarfile
import time

from run import atomic_json, binary_hashes, file_hash, harness_hashes, process_alive, process_identity, source_fingerprint

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT / 'checks/testing'
COVERAGE_METRICS = (('lines', 'LH', 'LF'), ('functions', 'FAH', 'FAF'),
                    ('function_groups', 'FNH', 'FNF'), ('branches', 'BRH', 'BRF'))


def coverage_percent(value):
    value = float(value)
    if not math.isfinite(value) or not 0 <= value <= 100:
        raise argparse.ArgumentTypeError('coverage percent must be finite and between 0 and 100')
    return value


def coverage_policy(required_percent=None):
    return {'mode': 'informational' if required_percent is None else 'required-percent',
            'required_percent': None if required_percent is None else coverage_percent(required_percent),
            'metrics': [name for name, _, _ in COVERAGE_METRICS],
            'denominator': 'raw', 'feature_readiness': 'not assessed by campaign'}


def coverage_gaps(trace, required_percent=None):
    policy = coverage_policy(required_percent)
    files, current = [], None
    for line in trace.read_text().splitlines():
        if line.startswith('SF:'):
            if current is not None: raise ValueError('coverage record is unfinished')
            current = {'path': line[3:], 'lines': [], 'functions': [], 'branches': [], 'totals': {'FAF': 0, 'FAH': 0}}
        elif current is not None:
            key, _, value = line.partition(':')
            if key in ('LF', 'LH', 'FNF', 'FNH', 'BRF', 'BRH'):
                current['totals'][key] = int(value)
            elif key == 'DA':
                location, count, *_ = value.split(',')
                if int(location) < 1 or int(count) < 0: raise ValueError('invalid coverage line count')
                if int(count) == 0: current['lines'].append(int(location))
            elif key in ('FNDA', 'FNA'):
                # lcov 2.x groups template instances at one source location in
                # FNF/FNH. Count every named alias as lcov's summary does.
                count, name = value.split(',', 2)[1:] if key == 'FNA' else value.split(',', 1)
                if int(count) < 0: raise ValueError('invalid coverage function count')
                current['totals']['FAF'] += 1
                current['totals']['FAH'] += int(int(count) > 0)
                if int(count) == 0: current['functions'].append(name)
            elif key == 'BRDA':
                location, block, branch, count = value.split(',')
                if int(location) < 1 or (count != '-' and int(count) < 0):
                    raise ValueError('invalid coverage branch count')
                if count in ('-', '0'):
                    current['branches'].append({'line': int(location), 'block': block, 'branch': branch})
            elif line == 'end_of_record':
                if not current['path'] or not any(key in current['totals'] for key in ('LF', 'FNF', 'BRF')):
                    raise ValueError('coverage record lacks a source path or totals')
                for found, hit in [('LF', 'LH'), ('FNF', 'FNH'), ('BRF', 'BRH'), ('FAF', 'FAH')]:
                    if (found in current['totals']) != (hit in current['totals']):
                        raise ValueError('coverage record has an incomplete totals pair')
                    if not 0 <= current['totals'].get(hit, 0) <= current['totals'].get(found, 0):
                        raise ValueError('coverage hit count is outside its total')
                files.append(current)
                current = None
    if current is not None or not files:
        raise ValueError('coverage trace is empty or has an unfinished record')
    for found in ('LF', 'FNF', 'BRF'):
        if not any(found in record['totals'] for record in files):
            raise ValueError('coverage trace lacks metric data: ' + found)
    totals = {key: sum(f['totals'].get(key, 0) for f in files)
              for key in ('LF', 'LH', 'FNF', 'FNH', 'FAF', 'FAH', 'BRF', 'BRH')}
    percentages = {label: 100 * totals[hit] / totals[found] if totals[found] else 0
                   for label, hit, found in COVERAGE_METRICS}
    threshold_met = None if required_percent is None else all(
        totals[found] > 0 and percentages[label] >= policy['required_percent']
        for label, _, found in COVERAGE_METRICS)
    return {'target_percent': policy['required_percent'], 'coverage_policy': policy,
            'threshold_met': threshold_met, 'percentages': percentages, 'totals': totals,
            'files': sorted(files, key=lambda f: len(f['branches']), reverse=True)}


def option_audit(run_folder):
    """Keep the old import entry point with the current solver-command rules."""
    from runtime_options_audit import build
    return build(run_folder, [])

def evidence_hashes(paths):
    files = set()
    for path in paths:
        if path.is_file(): files.add(path)
        elif path.is_dir():
            files.update(p for p in path.rglob('*') if p.is_file() and not p.name.endswith('.lock'))
    return {str(path): file_hash(path) for path in sorted(files)}


def stop_tree(process):
    """Stop only this live child's descendants, checking PID reuse before each signal."""
    if process.poll() is not None: return
    identities = {}
    parents = {}
    boot = Path('/proc/sys/kernel/random/boot_id').read_text().strip()
    for path in Path('/proc').iterdir():
        if not path.name.isdigit(): continue
        try:
            stat = (path / 'stat').read_text().rsplit(')', 1)[1].split()
            pid = int(path.name)
            parents[pid] = int(stat[1])
            if stat[0] != 'Z': identities[pid] = {'pid': pid, 'start_ticks': stat[19], 'boot_id': boot}
        except (OSError, ValueError, IndexError): continue
    selected = {process.pid}
    while True:
        children = {pid for pid, parent in parents.items() if parent in selected}
        if children <= selected: break
        selected |= children
    identities = {pid: identity for pid, identity in identities.items() if pid in selected}
    for sig in (signal.SIGTERM, signal.SIGKILL):
        for pid, identity in identities.items():
            if process_alive(identity):
                try: os.kill(pid, sig)
                except ProcessLookupError: pass
        if sig == signal.SIGTERM:
            try: process.wait(timeout=3)
            except subprocess.TimeoutExpired: pass
    process.wait()


class Campaign:
    """An atomic stage journal. A completed failure is still completed work."""
    def __init__(self, output, identity, *, resume=False, root=ROOT, environment=None):
        self.output, self.root = output, root
        self.environment = environment
        self.path = output / 'campaign.json'
        if resume:
            self.data = json.loads(self.path.read_text())
            if self.data.get('schema_version') != 2:
                raise ValueError('this campaign predates durable resume; use a new output directory')
            if self.data['identity'] != identity:
                raise ValueError('cannot resume after changing the commit, source, harness, tools, environment, or options')
            if self.data.get('coverage_policy') != identity.get('coverage_policy', coverage_policy()):
                raise ValueError('cannot resume after changing the recorded coverage policy')
            if process_alive(self.data.get('active_process')):
                raise ValueError('the recorded campaign process is still alive')
            names = [stage['name'] for stage in self.data['stages']]
            if len(names) != len(set(names)): raise ValueError('duplicate campaign stage names')
            for stage in self.data['stages']:
                if process_alive(stage.get('active_process')):
                    raise ValueError(f'a stage process is still alive: {stage["name"]}')
                for name, digest in {**stage.get('artifacts_sha256', {}), **stage.get('binary_sha256', {})}.items():
                    path = Path(name)
                    if not path.is_file() or file_hash(path) != digest:
                        raise ValueError(f'completed stage evidence or binary changed: {name}')
                if stage['status'] in ('pass', 'fail') and 'artifact_roots' in stage and evidence_hashes([Path(path) for path in stage['artifact_roots']]) != stage.get('artifacts_sha256'):
                    raise ValueError(f'completed stage result inventory changed: {stage["name"]}')
                if stage.get('binaries') and binary_hashes(stage['binaries']) != stage['binary_sha256']:
                    raise ValueError(f'shared-library resolution changed: {stage["name"]}')
        else:
            if output.exists(): raise ValueError('choose a new output directory or use --resume')
            output.mkdir(parents=True)
            self.data = {'schema_version': 2, 'identity': identity, 'commit': identity.get('commit'),
                         'started': datetime.now(timezone.utc).isoformat(),
                         'coverage_policy': identity.get('coverage_policy', coverage_policy()),
                         'stages': []}
        self.data.update(status='running', active_process=process_identity(),
                         recorded_stages_complete=False, all_stages_passed=None,
                         completion_scope='recorded stages only; failed prerequisites can block requested stages')
        self.save()

    def save(self): atomic_json(self.path, self.data)

    def find(self, name):
        return next((stage for stage in self.data['stages'] if stage['name'] == name), None)

    def stage(self, name, command, verbose=True, *, case_output=None, artifacts=(), binaries=()):
        command = [str(arg) for arg in command]
        record = self.find(name)
        if record and record['command'] != command:
            raise ValueError(f'stage command changed: {name}')
        if record and record['status'] in ('pass', 'fail'):
            print(f'[PRESERVED {record["status"].upper()}] {name}', flush=True)
            return record['exit'] == 0
        if name == 'coverage-reset' and any(self.find(stage) for stage in ('coverage-all', 'runtime-options-coverage', 'coverage-capture')):
            raise ValueError('refusing to reset counters after coverage tests have started')
        if record is None:
            collisions = [path for path in [*artifacts, *([case_output] if case_output else [])] if path.exists()]
            if collisions: raise ValueError(f'unrecorded stage output already exists: {collisions}')
            record = {'name': name, 'command': command, 'attempts': []}
            self.data['stages'].append(record)
        else:
            if record['attempts'] and record['attempts'][-1]['status'] == 'running':
                record['attempts'][-1].update(status='interrupted', interruption='recorded process stopped before completion was saved', active_process=None)
            for path in artifacts:
                if path.exists():
                    archived = path.with_name(path.name + f'.interrupted-{time.time_ns()}')
                    path.rename(archived)
                    record.setdefault('preserved_partial_outputs', []).append(str(archived))
        actual = list(command)
        if case_output is not None and case_output.exists():
            runner = any(Path(arg).name == 'run.py' for arg in command) and 'run' in command
            if runner and (case_output / 'run.json').exists():
                actual.append('--resume')
            else:
                archived = case_output.with_name(case_output.name + f'.interrupted-{time.time_ns()}')
                case_output.rename(archived)
                record.setdefault('preserved_partial_outputs', []).append(str(archived))
        attempt = {'command': actual, 'started': datetime.now(timezone.utc).isoformat(),
                   'log': str(self.output / f'{name}.attempt-{len(record["attempts"]) + 1}.log'), 'status': 'running'}
        record['attempts'].append(attempt)
        record.update(status='running', log=attempt['log'], active_process=None)
        self.save()
        print(f'\n===== {name} =====\nLog: {attempt["log"]}', flush=True)
        start, last, process = time.monotonic(), 0, None
        try:
            with Path(attempt['log']).open('x') as log:
                process = subprocess.Popen(actual, cwd=self.root, env=self.environment, start_new_session=True,
                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, bufsize=1)
                record['active_process'] = process_identity(process.pid)
                attempt['active_process'] = record['active_process']
                self.save()
                for line in process.stdout:
                    log.write(line)
                    log.flush()
                    if verbose or time.monotonic() - last > 10:
                        print(line, end='', flush=True)
                        last = time.monotonic()
                code = process.wait()
            record.update(exit=code, active_process=None)
        except OSError as error:
            if process is not None and process.poll() is None: stop_tree(process)
            record.update(exit=127, error=str(error), active_process=None)
        except BaseException as error:
            if process is not None: stop_tree(process)
            record.update(status='interrupted', interruption=repr(error), active_process=None)
            attempt.update(status='interrupted', active_process=None)
            self.save()
            raise
        finally:
            if process is not None and process.stdout is not None: process.stdout.close()
        record['seconds'] = round(time.monotonic() - start, 2)
        roots = [*artifacts, *([case_output] if case_output else [])]
        record['artifact_roots'] = [str(path) for path in roots]
        record['artifacts_sha256'] = evidence_hashes(roots)
        if record['exit'] == 0 and binaries:
            missing = [str(path) for path in binaries if not path.is_file()]
            if missing:
                record.update(exit=127, error=f'build succeeded without expected binaries: {missing}')
            else:
                record['binary_sha256'] = binary_hashes(binaries)
                record['binaries'] = [str(path) for path in binaries]
        record['status'] = 'pass' if record['exit'] == 0 else 'fail'
        attempt.update(status=record['status'], exit=record['exit'], seconds=record['seconds'], active_process=None)
        self.save()
        print(f'[{record["status"].upper()}] {name}: exit {record["exit"]}; {record["seconds"]}s', flush=True)
        return record['exit'] == 0

    def record_coverage(self, trace):
        """A valid raw report is required; a numeric threshold is optional."""
        if self.find('coverage-report') is not None: return
        policy = self.data['coverage_policy']
        report = self.output / 'coverage-gaps.json'
        record = {'name': 'coverage-report', 'command': [], 'attempts': [],
                  'coverage_policy': policy, 'target_percent': policy['required_percent']}
        try:
            gaps = coverage_gaps(trace, policy['required_percent'])
            atomic_json(report, gaps)
            passed = gaps['threshold_met'] is not False
            record.update(coverage_valid=True, threshold_met=gaps['threshold_met'],
                          percentages=gaps['percentages'], status='pass' if passed else 'fail',
                          exit=0 if passed else 1, artifact_roots=[str(report)],
                          artifacts_sha256=evidence_hashes([report]))
        except (OSError, ValueError) as error:
            record.update(coverage_valid=False, threshold_met=None, status='fail', exit=1,
                          error=str(error), artifact_roots=[], artifacts_sha256={})
        self.data['stages'].append(record)
        self.save()

    def finish(self, interrupted=None):
        all_stages_passed = not interrupted and all(stage['status'] == 'pass' for stage in self.data['stages'])
        self.data.update(active_process=None, finished=datetime.now(timezone.utc).isoformat(),
                         recorded_stages_complete=not interrupted and all(stage['status'] in ('pass', 'fail') for stage in self.data['stages']),
                         all_stages_passed=all_stages_passed,
                         feature_readiness='not assessed by campaign',
                         status='interrupted' if interrupted else
                         'pass' if all_stages_passed else 'fail')
        if interrupted: self.data['interruption'] = repr(interrupted)
        self.save()


def archive_coverage_counters(campaign, build):
    if campaign.find('coverage-reset') is not None: return
    if 'coverage_backup' in campaign.data: return
    archive_path = campaign.output / 'previous-counters.tar.gz'
    previous = list(build.rglob('*.gcda'))
    if previous and not archive_path.exists():
        temporary = archive_path.with_suffix('.tmp')
        with tarfile.open(temporary, 'w:gz') as archive:
            for path in previous: archive.add(path, arcname=str(path.relative_to(build)))
        os.replace(temporary, archive_path)
    campaign.data['coverage_backup'] = {'files': len(previous), 'archive': str(archive_path) if archive_path.exists() else None}
    campaign.save()


def main():
    settings_path = ROOT / 'build/testing/local-tools.json'
    settings = json.loads(settings_path.read_text()) if settings_path.exists() else {}
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--resume', action='store_true', help='preserve completed stages and resume interrupted case runs')
    parser.add_argument('--jobs', type=int, default=8)
    parser.add_argument('--memcheck-jobs', type=int, default=8)
    parser.add_argument('--sanitizer-error-grace', type=float, default=10,
                        help='ASan only: seconds allowed after the first actual sanitizer error (default: 10)')
    parser.add_argument('--lcov-tool-dir', type=Path, default=settings.get('lcov_tool_dir'))
    parser.add_argument('--z3', default=settings.get('z3', 'z3'))
    parser.add_argument('--require-coverage-percent', type=coverage_percent,
                        help='require this percent for every raw coverage metric; default: report coverage and gaps without a numeric gate')
    parser.add_argument('--profiles', nargs='+', default=['release', 'memcheck', 'ubsan', 'asan', 'no-z3', 'coverage'],
                        choices=['release', 'memcheck', 'ubsan', 'asan', 'no-z3', 'coverage'])
    args = parser.parse_args()
    if args.jobs < 1 or args.memcheck_jobs < 1 or not math.isfinite(args.sanitizer_error_grace) or args.sanitizer_error_grace <= 0:
        parser.error('worker counts must be positive; sanitizer error grace must be finite and positive')
    if len(args.profiles) != len(set(args.profiles)): parser.error('profiles must be unique')
    if args.require_coverage_percent is not None and 'coverage' not in args.profiles:
        parser.error('--require-coverage-percent requires the coverage profile')
    args.output = args.output.resolve()
    if args.lcov_tool_dir: args.lcov_tool_dir = args.lcov_tool_dir.resolve()
    out = args.output
    if args.resume and not (out / 'campaign.json').is_file(): parser.error('--resume requires campaign.json')
    if out.exists() and not args.resume: parser.error('choose a new output directory or use --resume')
    lock_path = ROOT / 'build/testing/campaign.lock'
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    lock = lock_path.open('a')
    try: fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError: parser.error('a campaign is already running in this checkout')
    env = {**os.environ, 'JOBS': str(args.jobs), 'PYTHONUNBUFFERED': '1',
           'UBSAN_OPTIONS': 'halt_on_error=1:print_stacktrace=1',
           'ASAN_OPTIONS': 'detect_leaks=1:halt_on_error=1:abort_on_error=0:exitcode=98'}
    tool_paths = [Path(path) for tool in (args.z3, 'cmake', 'c++', 'valgrind')
                  if (path := shutil.which(tool))]
    if args.lcov_tool_dir:
        tool_paths += [args.lcov_tool_dir / tool for tool in ('lcov', 'genhtml') if (args.lcov_tool_dir / tool).is_file()]
    identity = {'commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                'coverage_policy': coverage_policy(args.require_coverage_percent),
                'source_sha256': source_fingerprint(), 'harness_sha256': harness_hashes(),
                'tools_sha256': {str(path.resolve()): file_hash(path) for path in tool_paths},
                'environment': {name: env.get(name) for name in ('ASAN_OPTIONS', 'UBSAN_OPTIONS', 'LSAN_OPTIONS',
                                                               'Z3_DIR', 'CC', 'CXX', 'CFLAGS', 'CXXFLAGS', 'LDFLAGS',
                                                               'LD_LIBRARY_PATH', 'LD_PRELOAD')},
                'options': {key: str(value) if isinstance(value, Path) else value
                            for key, value in vars(args).items() if key != 'resume'}}
    try: campaign = Campaign(out, identity, resume=args.resume, environment=env)
    except (ValueError, OSError, KeyError) as error: parser.error(str(error))
    stage, python = campaign.stage, sys.executable
    def interrupt(signum, frame): raise KeyboardInterrupt(f'interrupted by signal {signum}')
    handlers = {sig: signal.signal(sig, interrupt) for sig in (signal.SIGTERM, signal.SIGINT)}
    try:
        stage('harness-tests', [python, '-B', '-m', 'unittest', 'discover', '-s', HERE, '-p', 'test_*.py', '-v'])
        built = set()
        for profile in args.profiles:
            build = ROOT / 'build/testing' / profile
            if profile == 'coverage': archive_coverage_counters(campaign, build)
            binaries = [build / 'vampire', *([] if profile == 'release' else [build / 'vtest'])]
            if not stage('build-' + profile, ['bash', HERE / 'build.sh', profile], verbose=False, binaries=binaries):
                print(f'[BLOCKED] Tests for {profile}: build failed; see log above.', flush=True)
                continue
            built.add(profile)
            if profile == 'release':
                stage('release-sanity', [python, HERE / 'run.py', 'run', '--suite', 'sanity', '--build', build,
                      '--jobs', '1', '--timeout', '180', '--output', out / 'release-sanity'], case_output=out / 'release-sanity')
                stage('thread-resource-errors', [python, HERE / 'resource_failure.py', '--binary', build / 'vampire',
                      '--output', out / 'thread-resource-errors'], case_output=out / 'thread-resource-errors')
            if profile == 'coverage':
                lcov = args.lcov_tool_dir / 'lcov' if args.lcov_tool_dir else 'lcov'
                if not stage('coverage-reset', [lcov, '--zerocounters', '--directory', build]):
                    print('[BLOCKED] Coverage run: counter reset failed.', flush=True)
                    continue
            run_folder = out / (profile + '-all')
            asan_flags = ['--asan', '--sanitizer-error-grace', str(args.sanitizer_error_grace)] if profile == 'asan' else []
            stage(profile + '-all', [python, HERE / 'run.py', 'run', '--suite', 'all', '--build', build,
                  '--jobs', str(args.jobs), '--timeout', '180', '--output', run_folder, '--z3', args.z3,
                  *asan_flags], case_output=run_folder)
            runtime_output = out / ('runtime-options-' + profile)
            runtime_command = [python, HERE / 'runtime_options.py', '--build', build,
                               '--profile', 'debug' if profile == 'memcheck' else profile,
                               '--output', runtime_output, '--jobs', str(args.jobs), '--timeout', '180']
            if profile == 'asan': runtime_command += ['--sanitizer-error-grace', str(args.sanitizer_error_grace)]
            stage('runtime-options-' + profile, runtime_command, case_output=runtime_output)
            if profile == 'release' and (run_folder / 'summary.json').exists():
                stage('option-audit', [python, HERE / 'runtime_options_audit.py', '--run', run_folder,
                      '--extension', runtime_output, '--output', out / 'option-audit.json'], artifacts=[out / 'option-audit.json'])
                stage('independent-smt-oracles', [python, HERE / 'check_oracles.py', run_folder / 'summary.json',
                      '--z3', args.z3, '--output', out / 'oracle-results.json'], artifacts=[out / 'oracle-results.json'])
                stage('inventory', [python, HERE / 'run.py', 'inventory', '--build', build,
                      '--output', out / 'inventory.json'], artifacts=[out / 'inventory.json'])
            if profile == 'coverage':
                command = [python, HERE / 'coverage.py', '--build', build, '--output', out / 'lcov',
                           '--jobs', str(args.jobs), '--allow-overlapping-functions']
                if args.lcov_tool_dir: command += ['--tool-dir', args.lcov_tool_dir]
                if stage('coverage-capture', command, case_output=out / 'lcov'):
                    campaign.record_coverage(out / 'lcov/coverage.info')
                    print(f'Uncovered locations: {out / "coverage-gaps.json"}', flush=True)
        if 'memcheck' in built:
            build = ROOT / 'build/testing/memcheck'
            run_folder = out / 'valgrind-all'
            stage('valgrind-all', [python, HERE / 'run.py', 'run', '--suite', 'all', '--build', build,
                  '--memcheck', '--jobs', str(args.memcheck_jobs), '--timeout', '120', '--output', run_folder,
                  '--z3', args.z3], case_output=run_folder)
            stage('runtime-options-valgrind', [python, HERE / 'runtime_options.py', '--build', build,
                  '--profile', 'valgrind', '--output', out / 'runtime-options-valgrind',
                  '--jobs', str(args.memcheck_jobs), '--timeout', '120'], case_output=out / 'runtime-options-valgrind')
            if (run_folder / 'summary.json').exists():
                stage('memory-triage', [python, HERE / 'triage.py', run_folder,
                      '--output', out / 'memcheck-groups.json'], artifacts=[out / 'memcheck-groups.json'])
    except BaseException as error:
        campaign.finish(interrupted=error)
        raise
    finally:
        for sig, handler in handlers.items(): signal.signal(sig, handler)
    campaign.finish()
    print('\n===== Campaign summary =====', flush=True)
    for result in campaign.data['stages']:
        print(f'{result["status"].upper():12} {result["name"]}  {result.get("log", "")}')
    print(f'Results: {out}', flush=True)
    return int(campaign.data['status'] != 'pass')


if __name__ == '__main__': raise SystemExit(main())
