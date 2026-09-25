#!/usr/bin/env python3
"""Accumulate GCC coverage in a fresh tree without resetting an existing build."""
import argparse
from contextlib import contextmanager
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
import time

METRICS = ('lines', 'functions', 'function_groups', 'branches')
EXCLUDED = ('UnitTests', 'Test', 'cadical', 'viras', 'z3', 'mini-gmp-6.3.0', 'build')


def sha256(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def save(path, value):
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    os.replace(temporary, path)


def inventory(build, suffix):
    result = {}
    for path in sorted(build.rglob('*' + suffix)):
        if path.is_symlink() or not path.is_file():
            raise ValueError(f'coverage input is not a regular file: {path}')
        result[str(path.relative_to(build))] = sha256(path)
    return result


def contains(parent, child):
    return child == parent or parent in child.parents


def trace_metrics(path):
    """Read LCOV identities, including each named alias in grouped-function data."""
    result = {metric: {} for metric in METRICS}
    source, record, seen_sources = None, {}, set()
    declared = {key: 0 for key in ('LF', 'LH', 'FNF', 'FNH', 'BRF', 'BRH')}

    def finish():
        if source is None or source in seen_sources:
            raise ValueError('missing or duplicate LCOV source record')
        seen_sources.add(source)
        groups, names = record['groups'], record['names']
        group_hits = {key: False for key in groups}
        for name, (group, count) in names.items():
            if group not in groups:
                raise ValueError(f'function alias references an unknown group: {source}: {name}')
            result['functions'][(source, *groups[group], name)] = count > 0
            group_hits[group] |= count > 0
        for group, location in groups.items():
            # Names disambiguate two groups sharing a source range.
            aliases = tuple(sorted(name for name, (g, _) in names.items() if g == group))
            result['function_groups'][(source, *location, aliases)] = group_hits[group]
        for line, count in record['lines'].items():
            result['lines'][(source, line)] = count > 0
        for key, count in record['branches'].items():
            result['branches'][(source, *key)] = count > 0
        actual = {'LF': len(record['lines']), 'LH': sum(n > 0 for n in record['lines'].values()),
                  'FNF': len(groups), 'FNH': sum(group_hits.values()),
                  'BRF': len(record['branches']), 'BRH': sum(n > 0 for n in record['branches'].values())}
        for key, value in actual.items():
            if record['totals'].get(key, 0) != value:
                raise ValueError(f'LCOV {key} differs from its records: {source}')
            declared[key] += value

    for line in Path(path).read_text().splitlines():
        key, _, value = line.partition(':')
        if key == 'SF':
            if source is not None or not value:
                raise ValueError('unfinished LCOV source record')
            source = value
            record = {'groups': {}, 'names': {}, 'lines': {}, 'branches': {}, 'branch_occurrences': {}, 'totals': {}}
        elif line == 'end_of_record':
            finish()
            source = None
        elif source is None:
            if key not in ('TN', ''):
                raise ValueError(f'LCOV field outside a source record: {key}')
        elif key == 'FNL':
            group, start, *end = value.split(',')
            if group in record['groups']:
                raise ValueError('duplicate LCOV function group')
            record['groups'][group] = (int(start), int(end[0]) if end else None)
        elif key == 'FNA':
            group, count, name = value.split(',', 2)
            if name in record['names']:
                raise ValueError('duplicate LCOV function alias')
            record['names'][name] = (group, int(count))
        elif key == 'FN':
            start, tail = value.split(',', 1)
            end, separator, name = tail.partition(',')
            if not separator or not end.isdigit():
                name, end = tail, None
            if name in record['groups']:
                raise ValueError('duplicate legacy LCOV function')
            record['groups'][name] = (int(start), int(end) if end else None)
        elif key == 'FNDA':
            count, name = value.split(',', 1)
            if name in record['names']:
                raise ValueError('duplicate legacy LCOV function count')
            record['names'][name] = (name, int(count))
        elif key == 'DA':
            location, count, *_ = value.split(',')
            location, count = int(location), int(count)
            if location in record['lines'] or count < 0:
                raise ValueError('duplicate or negative LCOV line count')
            record['lines'][location] = count
        elif key == 'BRDA':
            location, block, branch, count = value.split(',')
            identity = (int(location), block, branch)
            # LCOV can emit repeated labels for template instantiations. Keep
            # their multiplicity and serialized order; do not collapse them.
            occurrence = record['branch_occurrences'].get(identity, 0)
            record['branch_occurrences'][identity] = occurrence + 1
            identity = (*identity, occurrence)
            record['branches'][identity] = 0 if count == '-' else int(count)
            if record['branches'][identity] < 0:
                raise ValueError('negative LCOV branch count')
        elif key in declared:
            if key in record['totals']:
                raise ValueError('duplicate LCOV totals field')
            record['totals'][key] = int(value)
    if source is not None or not seen_sources:
        raise ValueError('empty or unfinished LCOV trace')
    return result


def compare_metrics(before, after):
    deltas = {}
    for metric in METRICS:
        old, new = before[metric], after[metric]
        if old.keys() != new.keys():
            added = sorted(new.keys() - old.keys(), key=repr)
            removed = sorted(old.keys() - new.keys(), key=repr)
            raise ValueError(f'{metric} denominator identities changed: +{len(added)} / -{len(removed)}; '
                             f'added={added[:2]!r}; removed={removed[:2]!r}')
        lost = [key for key in old if old[key] and not new[key]]
        if lost:
            raise ValueError(f'merged trace lost {len(lost)} previously hit {metric}')
        gained = sorted((key for key in old if new[key] and not old[key]), key=repr)
        deltas[metric] = {'found': len(old), 'before_hit': sum(old.values()), 'after_hit': sum(new.values()),
                         'new_hit': len(gained), 'new_identities': gained}
    return deltas


def verify_original(metadata):
    build = Path(metadata['build'])
    for suffix, key in (('.gcda', 'original_gcda'), ('.gcno', 'original_gcno')):
        if inventory(build, suffix) != metadata[key]:
            raise ValueError(f'original {suffix} inventory or content changed; preserve and inspect both trees')
    for filename, expected in metadata['immutable_files'].items():
        if not Path(filename).is_file() or sha256(filename) != expected:
            raise ValueError(f'immutable input changed: {filename}')


def implementation_snapshot(output):
    source = Path(__file__).resolve()
    digest = sha256(source)
    target = output / 'provenance' / (digest + '.py')
    target.parent.mkdir(exist_ok=True)
    if target.exists():
        if sha256(target) != digest:
            raise ValueError('saved helper implementation changed')
    else:
        shutil.copyfile(source, target)
    return {'source': str(source), 'snapshot': str(target), 'sha256': digest}


def executable_identity(command):
    resolved = shutil.which(command)
    if not resolved:
        raise ValueError(f'coverage tool is unavailable: {command}')
    path = Path(resolved).resolve()
    return {'command': command, 'resolved': str(path), 'sha256': sha256(path)}


def prepare(build, source, output, baseline_trace, *, gcov_tool='gcov', gcov_merge_tool='gcov-tool', tool_dir=None,
            jobs=4, allow_overlapping_functions=False):
    build, source, output = Path(build).resolve(), Path(source).resolve(), Path(output).resolve()
    baseline_trace = Path(baseline_trace).resolve()
    if not build.is_dir() or not source.is_dir() or jobs < 1:
        raise ValueError('source/build directories and a positive worker count are required')
    if output.exists() or contains(build, output) or contains(output, build) or contains(output, baseline_trace):
        raise ValueError('choose a fresh output outside the instrumented build and immutable inputs')
    notes, counters = inventory(build, '.gcno'), inventory(build, '.gcda')
    if not notes:
        raise ValueError('build has no GCC coverage notes')
    baseline_metrics = trace_metrics(baseline_trace)
    binaries = [build / name for name in ('vampire', 'vtest') if (build / name).is_file()]
    source_files = {Path(identity[0]) for identity in baseline_metrics['lines']}
    if any(not contains(source, p.resolve()) for p in source_files):
        raise ValueError('baseline trace contains source files outside the original source root')
    immutable = {str(p): sha256(p) for p in [baseline_trace, *binaries, *sorted(source_files)]}
    # Strip zero keeps every embedded absolute path under the new prefix, even
    # if a linked object was built outside this build directory.
    data = output / 'data'
    note_root = data / build.relative_to(build.anchor)
    metadata = {'schema_version': 1, 'created_utc': datetime.now(timezone.utc).isoformat(),
                'build': str(build), 'source': str(source), 'output': str(output), 'note_root': str(note_root),
                'baseline_trace': str(baseline_trace), 'baseline_found': {k: len(v) for k, v in baseline_metrics.items()},
                'original_gcno': notes, 'original_gcda': counters, 'immutable_files': immutable,
                'environment': {'GCOV_PREFIX': str(data), 'GCOV_PREFIX_STRIP': '0',
                                'GCOV_ERROR_FILE': str(output / 'gcov-errors.log'), 'GCOV_EXIT_AT_ERROR': '1'},
                'gcov_tool': gcov_tool, 'gcov_merge_tool': gcov_merge_tool, 'lcov': str(Path(tool_dir).resolve() / 'lcov') if tool_dir else 'lcov',
                'jobs': jobs, 'allow_overlapping_functions': allow_overlapping_functions,
                'runs': [], 'status': 'prepared'}
    output.mkdir(parents=True)
    metadata['prepare_implementation'] = implementation_snapshot(output)
    save(output / 'overlay.json', metadata)
    for filename, expected in notes.items():
        target = note_root / filename
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(build / filename, target)
        if sha256(target) != expected:
            raise ValueError('coverage note copy differs')
    verify_original(metadata)
    save(output / 'environment.json', metadata['environment'])
    return metadata


@contextmanager
def locked(output):
    output = Path(output).resolve()
    if not (output / 'overlay.json').is_file():
        raise ValueError('prepare an overlay first')
    with (output / '.overlay.lock').open('a') as stream:
        try:
            fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise ValueError('another overlay operation is active') from exc
        metadata = json.loads((output / 'overlay.json').read_text())
        if metadata.get('schema_version') != 1 or metadata.get('output') != str(output):
            raise ValueError('overlay metadata does not match this directory')
        yield metadata


def verify_overlay_notes(metadata):
    note_root = Path(metadata['note_root'])
    output, data = Path(metadata['output']), Path(metadata['output']) / 'data'
    if (metadata['environment']['GCOV_PREFIX'] != str(data) or
            metadata['environment']['GCOV_PREFIX_STRIP'] != '0' or
            note_root != data / Path(metadata['build']).relative_to(Path(metadata['build']).anchor) or
            metadata['environment'].get('GCOV_ERROR_FILE') != str(output / 'gcov-errors.log') or
            metadata['environment'].get('GCOV_EXIT_AT_ERROR') != '1'):
        raise ValueError('coverage relocation metadata changed')
    if data.is_symlink() or any(p.is_symlink() for p in data.rglob('*')):
        raise ValueError('overlay coverage tree must not contain symbolic links')
    if any(p.is_file() and p.stat().st_nlink > 1 for p in data.rglob('*')):
        raise ValueError('overlay coverage tree must not contain hard links')
    if inventory(note_root, '.gcno') != metadata['original_gcno']:
        raise ValueError('overlay notes changed or are incomplete')
    for counter in (Path(metadata['output']) / 'data').rglob('*.gcda'):
        if counter.is_symlink() or not counter.with_suffix('.gcno').is_file():
            raise ValueError(f'counter lacks a matching copied note: {counter}')




def login_helper_attestation(process, started):
    """Verify a protected user manager or sd-pam helper through root systemd."""
    try:
        boot_file = Path('/proc/sys/kernel/random/boot_id')
        boot = boot_file.read_text().strip()
        uid = os.geteuid()
        def snapshot(path):
            raw = (path / 'stat').read_text()
            fields = raw.rsplit(')', 1)[1].split()
            return {'pid': int(path.name), 'comm': raw.split('(', 1)[1].rsplit(')', 1)[0],
                    'state': fields[0], 'parent': int(fields[1]), 'start_ticks': fields[19],
                    'uid': path.stat().st_uid}
        def argv(path):
            return [os.fsdecode(value) for value in (path / 'cmdline').read_bytes().split(b'\0') if value]
        def cgroup(path):
            entries = (path / 'cgroup').read_text().splitlines()
            return next(line[3:] for line in entries if line.startswith('0::'))
        child = snapshot(process)
        manager_process = child['comm'] == 'systemd' and child['parent'] == 1
        if (child['comm'] not in ('(sd-pam)', 'systemd') or child['state'] == 'Z' or
                child['start_ticks'] != started or child['uid'] != uid):
            return None
        parent_path = process if manager_process else process.parent / str(child['parent'])
        parent = snapshot(parent_path)
        if parent['comm'] != 'systemd' or parent['parent'] != 1 or parent['state'] == 'Z' or parent['uid'] != uid:
            return None
        child_argv, parent_argv = argv(process), argv(parent_path)
        executable = Path('/usr/lib/systemd/systemd')
        expected_child_argv = [str(executable), '--user'] if manager_process else ['(sd-pam)']
        if child_argv != expected_child_argv or parent_argv != [str(executable), '--user']:
            return None
        if executable.stat().st_uid != 0 or executable.stat().st_mode & 0o022:
            return None
        service = f'user@{uid}.service'
        command = ['/usr/bin/systemctl', 'show', service, '--property=MainPID',
                   '--property=ExecStart', '--property=ActiveState',
                   '--property=SubState', '--property=ControlGroup']
        response = subprocess.run(command, text=True, capture_output=True, timeout=5, check=True)
        properties = dict(line.split('=', 1) for line in response.stdout.splitlines() if '=' in line)
        expected_group = f'/user.slice/user-{uid}.slice/{service}'
        expected_exec = '{ path=' + str(executable) + ' ; argv[]=' + str(executable) + ' --user ;'
        if (properties.get('MainPID') != str(parent['pid']) or
                properties.get('ActiveState') != 'active' or properties.get('SubState') != 'running' or
                properties.get('ControlGroup') != expected_group or
                not properties.get('ExecStart', '').startswith(expected_exec) or
                f' ; pid={parent["pid"]} ;' not in properties['ExecStart']):
            return None
        child_group, parent_group = cgroup(process), cgroup(parent_path)
        if any(value != expected_group and not value.startswith(expected_group + '/')
               for value in (child_group, parent_group)):
            return None
        # Scheduling state can change; PID, start, parent, command and UID cannot.
        def same_identity(path, expected):
            current = snapshot(path)
            return current['state'] != 'Z' and all(current[key] == value
                        for key, value in expected.items() if key != 'state')
        # Bind the service-manager response to the exact live identities.
        if (boot_file.read_text().strip() != boot or not same_identity(process, child) or
                not same_identity(parent_path, parent) or argv(process) != child_argv or
                argv(parent_path) != parent_argv or cgroup(process) != child_group or
                cgroup(parent_path) != parent_group):
            return None
        return {'kind': 'systemd-user-manager' if manager_process else 'systemd-user-session-helper', 'boot_id': boot,
                'process': child, 'parent': parent, 'argv': child_argv, 'parent_argv': parent_argv,
                'cgroup': child_group, 'parent_cgroup': parent_group,
                'service': service, 'manager_command': command, 'manager_properties': properties,
                'configured_executable': str(executable), 'configured_executable_sha256': sha256(executable),
                'executable_evidence': 'Root systemd manager MainPID/ExecStart and root-owned executable; protected proc exe links are not read.'}
    except (OSError, ValueError, KeyError, IndexError, StopIteration, subprocess.SubprocessError):
        return None


def process_environment(process, started):
    """Retry transient exec/exit permission races for the same live identity.

    Four attempts take at most 60 ms of deliberate waiting. A persistent
    unreadable environment still reaches the caller's fail-closed policy.
    """
    for attempt in range(4):
        if attempt: time.sleep(0.01 * attempt)
        current = (process / 'stat').read_text().rsplit(')', 1)[1].split()
        if current[0] == 'Z' or current[19] != started: return None
        try:
            environment = (process / 'environ').read_bytes().split(b'\0')
        except PermissionError:
            if attempt == 3: raise
            continue
        current = (process / 'stat').read_text().rsplit(')', 1)[1].split()
        if current[0] == 'Z' or current[19] != started: return None
        return environment


def counter_writers(metadata):
    """Find live processes that inherited this overlay's counter destination.

    The wrapper is not a filesystem sandbox. This guard covers its inherited
    environment, including solver children that create separate sessions.
    """
    prefix = str(Path(metadata['environment']['GCOV_PREFIX']).resolve())
    writers = []
    for process in Path('/proc').iterdir():
        if not process.name.isdigit() or int(process.name) == os.getpid():
            continue
        started = None
        try:
            if process.stat().st_uid != os.geteuid():
                continue
            fields = (process / 'stat').read_text().rsplit(')', 1)[1].split()
            if fields[0] == 'Z':
                continue
            started = fields[19]
            # Scan every same-user process. Wall time can move relative to boot
            # ticks, so a UTC creation time cannot safely exclude an old PID.
            environment = process_environment(process, started)
            if environment is None:
                continue
            matches = any(item.startswith(b'GCOV_PREFIX=') and
                          os.fsdecode(item.partition(b'=')[2]).rstrip('/') == prefix
                          for item in environment)
            current = (process / 'stat').read_text().rsplit(')', 1)[1].split()
            if current[19] != started or current[0] == 'Z':
                continue
            if matches:
                writers.append({'pid': int(process.name), 'start_ticks': started})
        except (FileNotFoundError, ProcessLookupError):
            continue
        except PermissionError as exc:
            # proc entries can become unreadable during exit or PID replacement.
            try:
                current = (process / 'stat').read_text().rsplit(')', 1)[1].split()
                if current[0] == 'Z' or (started is not None and current[19] != started):
                    continue
            except (FileNotFoundError, ProcessLookupError):
                continue
            except (OSError, IndexError):
                pass
            attestation = login_helper_attestation(process, started)
            if attestation is not None:
                attestations = metadata.setdefault('quiescence_service_attestations', [])
                if attestation not in attestations:
                    attestations.append(attestation)
                continue
            raise ValueError(f'cannot verify counter-process quiescence: {process}: {exc}') from exc
        except (OSError, IndexError) as exc:
            raise ValueError(f'cannot verify counter-process quiescence: {process}: {exc}') from exc
    return writers


def require_quiescent(metadata):
    incomplete = [index for index, run in enumerate(metadata['runs'])
                  if run.get('status') != 'finished']
    if incomplete:
        raise ValueError(f'interrupted or abnormal overlay runs {incomplete}; preserve this tree '
                         'for review and prepare a fresh overlay')
    writers = counter_writers(metadata)
    if writers:
        raise ValueError(f'overlay counter processes are still alive: {writers}')


def run_overlay(output, command, *, cwd=None, timeout=120):
    if not command or not math.isfinite(timeout) or timeout <= 0:
        raise ValueError('a command and positive timeout are required')
    output = Path(output).resolve()
    with locked(output) as metadata:
        if metadata['status'] == 'captured':
            raise ValueError('capture is final; prepare another overlay for more execution')
        require_quiescent(metadata)
        verify_original(metadata)
        verify_overlay_notes(metadata)
        folder = output / 'runs' / f'{len(metadata["runs"]):04d}'
        folder.mkdir(parents=True, exist_ok=False)
        entry = {'implementation': implementation_snapshot(output), 'command': list(command), 'cwd': str(Path(cwd or output).resolve()), 'timeout': timeout,
                 'started_utc': datetime.now(timezone.utc).isoformat(), 'artifacts': str(folder), 'status': 'running'}
        metadata['runs'].append(entry)
        save(output / 'overlay.json', metadata)
        process = None
        try:
            with (folder / 'stdout.log').open('w') as stdout, (folder / 'stderr.log').open('w') as stderr:
                process = subprocess.Popen(command, cwd=entry['cwd'], env={**os.environ, **metadata['environment']},
                                           stdout=stdout, stderr=stderr, start_new_session=True)
                try:
                    entry['exit'] = process.wait(timeout=timeout)
                    entry['status'] = 'finished'
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                    entry.update(exit=process.returncode, status='timeout')
            writers = counter_writers(metadata)
            entry['remaining_counter_processes'] = writers
            entry['counter_processes_quiescent'] = not writers
            if writers and entry['status'] == 'finished':
                raise ValueError(f'launcher exited with live overlay descendants: {writers}')
        except BaseException as exc:
            if process is not None and process.poll() is None:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            entry.update(status='error', error=str(exc))
            raise
        finally:
            entry['finished_utc'] = datetime.now(timezone.utc).isoformat()
            try:
                verify_original(metadata)
                verify_overlay_notes(metadata)
                entry['original_inputs_unchanged'] = True
            except Exception as exc:
                entry.update(original_inputs_unchanged=False, integrity_error=str(exc))
                raise
            finally:
                save(output / 'overlay.json', metadata)
                save(folder / 'command.json', entry)
        return entry


def raw_object_metrics(document, source):
    """Keep object-local function/block identity, before LCOV template folding."""
    result = {kind: {} for kind in ('lines', 'functions', 'branches')}
    for item in document['files']:
        path = Path(item['file'])
        if not path.is_absolute():
            path = Path(document['current_working_directory']) / path
        path = path.resolve()
        if not contains(source, path) or any(contains(source / folder, path) for folder in EXCLUDED):
            continue
        for function in item['functions']:
            key = (str(path), function['name'], function['start_line'], function['end_line'])
            if key in result['functions']:
                raise ValueError('duplicate object-local gcov function identity')
            result['functions'][key] = function['execution_count']
        for line in item['lines']:
            prefix = (str(path), line.get('function_name'), line['line_number'])
            if prefix in result['lines']:
                raise ValueError('duplicate object-local gcov line identity')
            result['lines'][prefix] = line['count']
            for ordinal, branch in enumerate(line['branches']):
                key = (*prefix, branch['source_block_id'], branch['destination_block_id'],
                       branch['throw'], branch['fallthrough'], ordinal)
                if key in result['branches']:
                    raise ValueError('duplicate object-local gcov branch identity')
                result['branches'][key] = branch['count']
    for kind, counts in result.items():
        for identity, count in counts.items():
            if type(count) is not int or count < 0:
                raise ValueError(f'invalid raw gcov {kind} count {count!r} at {identity!r}')
    return result


def compare_raw_object(baseline, overlay, merged):
    result = {}
    for kind, old in baseline.items():
        extra, combined = overlay[kind], merged[kind]
        if old.keys() != extra.keys() or old.keys() != combined.keys():
            raise ValueError(f'raw object {kind} identities changed')
        wrong = [key for key, count in combined.items() if count != old[key] + extra[key]]
        if wrong:
            raise ValueError(f'raw object {kind} merge is not the exact counter sum: {wrong[:2]!r}')
        new = [key for key in old if old[key] == 0 and combined[key] > 0]
        result[kind] = {'found': len(old), 'before_hit': sum(n > 0 for n in old.values()),
                        'after_hit': sum(n > 0 for n in combined.values()), 'new_hit': len(new),
                        'new_identities': new}
    return result


def validate_gcov_diagnostics(stderr, note, document):
    permitted = set()
    if not note.with_suffix('.gcda').exists():
        permitted.add(str(note.with_suffix('.gcda')) + ':cannot open data file, assuming not executed')
    if not any(item['functions'] for item in document['files']):
        permitted.add(str(note) + ':no functions found')
    unexpected = [line for line in stderr.decode(errors='replace').splitlines() if line not in permitted]
    if unexpected:
        raise ValueError(f'gcov diagnostics need review: {unexpected[:2]!r}')


def verify_raw_union(metadata, target, baseline, overlay, merged):
    import gzip
    from concurrent.futures import ThreadPoolExecutor
    source = Path(metadata['source'])
    roots = {'baseline': baseline, 'overlay': overlay, 'merged': merged}
    artifact_root = target / 'gcov-json'
    artifact_root.mkdir()

    def check(relative):
        observations, artifacts, versions = {}, {}, set()
        for name, root in roots.items():
            command = [metadata['gcov_tool'], '--branch-probabilities', '--json-format', '--stdout', str(root / relative)]
            result = subprocess.run(command, cwd=source, capture_output=True)
            folder = artifact_root / name / Path(relative).parent
            folder.mkdir(parents=True, exist_ok=True)
            artifact = folder / (Path(relative).name + '.json.gz')
            artifact.write_bytes(gzip.compress(result.stdout, mtime=0))
            artifact.with_suffix('.stderr.log').write_bytes(result.stderr)
            save(artifact.with_suffix('.command.json'), command)
            if result.returncode:
                raise ValueError(f'gcov failed for {root / relative}: exit {result.returncode}')
            document = json.loads(result.stdout)
            if document.get('format_version') != '2':
                raise ValueError('gcov JSON format 2 is required for basic-block identities')
            versions.add(document['gcc_version'])
            validate_gcov_diagnostics(result.stderr, root / relative, document)
            artifacts[name] = {'path': str(artifact), 'sha256': sha256(artifact), 'command': command}
            observations[name] = raw_object_metrics(document, source)
        if len(versions) != 1:
            raise ValueError('gcov compiler version changed during capture')
        return {'object': relative, 'gcc_version': versions.pop(), 'artifacts': artifacts,
                'metrics': compare_raw_object(observations['baseline'], observations['overlay'], observations['merged'])}

    with ThreadPoolExecutor(max_workers=metadata['jobs']) as executor:
        rows = list(executor.map(check, sorted(metadata['original_gcno'])))
    summary = {'exact_raw_counter_sum': True, 'objects': len(rows),
               'identity': 'copied note path, source, function, source line, source/destination basic block, exception/fallthrough flags, pinned-note branch ordinal',
               'metrics': {kind: {key: sum(row['metrics'][kind][key] for row in rows)
                                  for key in ('found', 'before_hit', 'after_hit', 'new_hit')}
                           for kind in ('lines', 'functions', 'branches')},
               'per_object': rows,
               'scope_note': 'Object-local counts retain template instances and are separate from the LCOV source-level denominator.'}
    save(target / 'raw-union.json', summary)
    return summary


def capture(output):
    output = Path(output).resolve()
    with locked(output) as metadata:
        require_quiescent(metadata)
        verify_original(metadata)
        verify_overlay_notes(metadata)
        if metadata['status'] == 'captured' or (output / 'capture').exists():
            raise ValueError('capture output already exists; preserve it and choose a new overlay')
        counters = inventory(Path(metadata['note_root']), '.gcda')
        if not counters:
            raise ValueError('overlay has no recorded execution counters')
        errors = output / 'gcov-errors.log'
        if errors.exists() and errors.stat().st_size:
            raise ValueError('libgcov reported errors; inspect gcov-errors.log')
        target = output / 'capture'
        target.mkdir()
        metadata['capture_implementation'] = implementation_snapshot(output)
        tool_identities = {name: executable_identity(command) for name, command in
                           (('lcov', metadata['lcov']), ('gcov', metadata['gcov_tool']),
                            ('gcov-tool', metadata.get('gcov_merge_tool', 'gcov-tool')))}
        save(target / 'tools.json', tool_identities)
        common = [metadata['lcov'], '--parallel', str(metadata['jobs']), '--branch-coverage',
                  '--ignore-errors', 'unused', '--rc', 'geninfo_unexecuted_blocks=1', '--gcov-tool', metadata['gcov_tool']]
        if metadata['allow_overlapping_functions']:
            common += ['--rc', 'check_data_consistency=0']
        source, build = Path(metadata['source']), Path(metadata['build'])
        scope = ['--include', str(source / '*')]
        for folder in EXCLUDED:
            scope += ['--exclude', str(source / folder / '*')]

        def invoke(name, command):
            save(target / (name + '.command.json'), command)
            with (target / (name + '.log')).open('w') as log:
                subprocess.run(command, cwd=source, stdout=log, stderr=subprocess.STDOUT, check=True)

        def stable_inputs():
            verify_original(metadata)
            verify_overlay_notes(metadata)
            if inventory(Path(metadata['note_root']), '.gcda') != counters:
                raise ValueError('overlay counters changed during capture')

        try:
            baseline, merged = target / 'raw-baseline', target / 'raw-merged'
            baseline.mkdir()
            for suffix, key in (('.gcno', 'original_gcno'), ('.gcda', 'original_gcda')):
                for relative in metadata[key]:
                    destination = baseline / relative
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(build / relative, destination)
                if inventory(baseline, suffix) != metadata[key]:
                    raise ValueError(f'copied baseline {suffix} differs')
            stable_inputs()
            gcov_merge_tool = metadata.get('gcov_merge_tool', 'gcov-tool')
            invoke('gcov-tool-version', [gcov_merge_tool, '--version'])
            invoke('raw-merge', [gcov_merge_tool, 'merge', str(baseline), metadata['note_root'], '-o', str(merged)])
            for relative in metadata['original_gcno']:
                destination = merged / relative
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(build / relative, destination)
            raw = verify_raw_union(metadata, target, baseline, Path(metadata['note_root']), merged)
            invoke('version', [metadata['lcov'], '--version'])
            for name, root in (('baseline', baseline), ('merged', merged)):
                for phase, flags in (('initial', ['--initial']), ('executed', [])):
                    invoke(name + '-' + phase, common + ['--capture', *flags, '--directory', str(root),
                                                         *scope, '--output-file', str(target / (name + '-' + phase + '.info'))])
                invoke(name + '-total', common + ['--add-tracefile', str(target / (name + '-initial.info')),
                                                '--add-tracefile', str(target / (name + '-executed.info')),
                                                '--output-file', str(target / (name + '.info'))])
            historical = trace_metrics(metadata['baseline_trace'])
            before, after = trace_metrics(target / 'baseline.info'), trace_metrics(target / 'merged.info')
            # Historical LCOV can choose a different template representative even
            # for unchanged counters. Require exact source maps for other metrics,
            # branch multiplicity per line/type, and all saved totals. The object-
            # local raw check above proves the actual merge before LCOV folding.
            from collections import Counter
            def branch_scope(rows):
                return Counter((key[0], key[1], key[2][:1] if key[2][:1] in ('e', 'f') else '') for key in rows)
            for kind in METRICS:
                if len(historical[kind]) != len(before[kind]) or sum(historical[kind].values()) != sum(before[kind].values()):
                    raise ValueError(f'raw baseline does not reproduce saved {kind} totals')
                if kind != 'branches' and historical[kind] != before[kind]:
                    raise ValueError(f'raw baseline does not reproduce saved {kind} identities and hits')
            if branch_scope(historical['branches']) != branch_scope(before['branches']):
                raise ValueError('raw baseline does not reproduce saved branch scope')
            deltas = compare_metrics(before, after)
            stable_inputs()
            for suffix, key in (('.gcno', 'original_gcno'), ('.gcda', 'original_gcda')):
                if inventory(baseline, suffix) != metadata[key]:
                    raise ValueError('copied baseline changed during capture')
            shutil.copyfile(target / 'merged.info', target / 'coverage.info')
            report = {'created_utc': datetime.now(timezone.utc).isoformat(), 'same_denominator': True,
                      'original_inputs_unchanged': True, 'baseline_trace': metadata['baseline_trace'],
                      'baseline_trace_sha256': sha256(metadata['baseline_trace']), 'merged_trace_sha256': sha256(target / 'coverage.info'),
                      'baseline_recapture_sha256': sha256(target / 'baseline.info'),
                      'implementation': metadata['capture_implementation'], 'tools': tool_identities,
                      'historical_branch_identity_symmetric_difference': len(historical['branches'].keys() ^ before['branches'].keys()),
                      'overlay_counter_count': len(counters), 'overlay_counter_sha256': counters, 'metrics': deltas,
                      'raw_union': {key: value for key, value in raw.items() if key != 'per_object'},
                      'raw_union_report_sha256': sha256(target / 'raw-union.json'),
                      'merge_method': 'gcov-tool adds copied baseline and overlay counters before capture; historical LCOV is retained, not added again',
                      'policy': 'No exception, compiler-generated, defensive, or uncovered branch exclusions added. Original source filters are retained.'}
            save(target / 'delta.json', report)
            metadata.update(status='captured', capture_summary=str(target / 'delta.json'))
            return report
        finally:
            stable_inputs()
            save(output / 'overlay.json', metadata)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    prep = sub.add_parser('prepare')
    for name in ('build', 'source', 'output', 'baseline-trace'):
        prep.add_argument('--' + name, type=Path, required=True)
    prep.add_argument('--gcov-tool', default='gcov')
    prep.add_argument('--gcov-merge-tool', default='gcov-tool')
    prep.add_argument('--tool-dir', type=Path)
    prep.add_argument('--jobs', type=int, default=4)
    prep.add_argument('--allow-overlapping-functions', action='store_true')
    runner = sub.add_parser('run')
    runner.add_argument('--output', type=Path, required=True)
    runner.add_argument('--cwd', type=Path)
    runner.add_argument('--timeout', type=float, default=120)
    runner.add_argument('command', nargs=argparse.REMAINDER)
    capturer = sub.add_parser('capture')
    capturer.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    try:
        if args.action == 'prepare':
            result = prepare(args.build, args.source, args.output, args.baseline_trace, gcov_tool=args.gcov_tool, gcov_merge_tool=args.gcov_merge_tool,
                             tool_dir=args.tool_dir, jobs=args.jobs, allow_overlapping_functions=args.allow_overlapping_functions)
            print(json.dumps({'output': result['output'], 'environment': result['environment'], 'copied_notes': len(result['original_gcno']), 'preserved_counters': len(result['original_gcda'])}, indent=2))
        elif args.action == 'run':
            command = args.command[1:] if args.command[:1] == ['--'] else args.command
            result = run_overlay(args.output, command, cwd=args.cwd, timeout=args.timeout)
            print(json.dumps(result, indent=2))
            return result.get('exit', 1) if result.get('exit', 1) >= 0 else 1
        else:
            result = capture(args.output)
            print(json.dumps({k: v for k, v in result.items() if k != 'metrics'} | {'metrics': {k: {f: v for f, v in data.items() if f != 'new_identities'} for k, data in result['metrics'].items()}}, indent=2))
    except (ValueError, OSError, subprocess.SubprocessError) as exc:
        parser.exit(1, f'coverage overlay: {exc}\n')
    return 0


if __name__ == '__main__':
    sys.exit(main())
