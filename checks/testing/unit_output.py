"""Read vtest's explicit per-test markers without changing suite outcomes."""
import re


RESULT = re.compile(r'^\[\s*(OK|FAIL)\s*\](?:\s+(.*?))?\s*$')
RUNNING = re.compile(r'^Running (\S+)\.\.\.\s*$')
TOTAL = re.compile(r'^Tests run:\s*(\d+)\s*$')
COUNT = re.compile(r'^\s*- (ok|fail)\s+(\d+)\s+\([^()]*\)\s*%\s*$')
LOCATION = re.compile(r'\bat location (.+?:\d+)\s+(?:was )?violated')
C_ASSERT = re.compile(r'^(.+?\.(?:cpp|hpp|cc|c|h):\d+):.*\b[Aa]ssertion\b')


def assertion(line, number, stream):
    match = LOCATION.search(line) or C_ASSERT.search(line)
    if match:
        return {'location': match.group(1), 'text': line,
                'stream': stream, 'line': number}
    return None


def parse_unit_output(stdout, stderr='', exit_code=None, interrupted=False):
    """Keep observations on partial output; expose final counts only if validated.

    stderr has no reliable order relative to stdout, so its assertions remain
    unassigned. Running/result pairs bind stdout assertions to that test.
    Some tests print their own result markers. Preserve those as nested output
    until the active test's exact name closes its Running/result pair.
    """
    lines = stdout.splitlines()
    observations, nested, unassigned, problems = [], [], [], []
    active, pending = None, []
    totals = []
    for index, line in enumerate(lines):
        running = RUNNING.fullmatch(line)
        marker = RESULT.fullmatch(line)
        total = TOTAL.fullmatch(line)
        if running:
            if active is not None:
                problems.append('a started test has no result marker')
                unassigned.extend(pending)
            active, pending = running.group(1), []
        elif marker:
            name = marker.group(2) or ''
            outcome = 'pass' if marker.group(1) == 'OK' else 'fail'
            if active is not None and active != name:
                nested.append({'name': name, 'outcome': outcome, 'parent': active,
                               'stdout_line': index + 1, 'text': line})
                if outcome == 'fail':
                    problems.append(f'nested FAIL marker for {name} inside {active}')
                continue
            bound = pending if active == name else []
            if active is None:
                problems.append('a result marker has no running test')
            if outcome == 'pass' and bound:
                problems.append(f'passed test {name} contains an assertion diagnostic')
            observations.append({'name': name, 'outcome': outcome,
                                 'stdout_line': index + 1, 'assertions': bound})
            active, pending = None, []
        elif total:
            totals.append((index, int(total.group(1))))
        else:
            found = assertion(line, index + 1, 'stdout')
            if found:
                (pending if active is not None else unassigned).append(found)
    if active is not None:
        problems.append('a started test has no result marker')
        unassigned.extend(pending)
    for index, line in enumerate(stderr.splitlines(), 1):
        found = assertion(line, index, 'stderr')
        if found: unassigned.append(found)

    passed = [row['name'] for row in observations if row['outcome'] == 'pass']
    failed = [row['name'] for row in observations if row['outcome'] == 'fail']
    names = [row['name'] for row in observations]
    if len(names) != len(set(names)): problems.append('duplicate test result names')
    if any(row['stream'] == 'stdout' for row in unassigned):
        problems.append('unassigned stdout assertion diagnostics')
    if unassigned and not failed:
        problems.append('assertion diagnostics without a failed test')
    reported = None
    if len(totals) != 1:
        problems.append('missing or repeated native summary trailer')
    else:
        index, total = totals[0]
        footer = [line for line in lines[index + 1:] if line.strip()][:2]
        matches = [COUNT.fullmatch(line) for line in footer]
        if len(matches) != 2 or not all(matches) or [m.group(1) for m in matches] != ['ok', 'fail']:
            problems.append('malformed native summary trailer')
        else:
            reported = {'total': total, 'passed': int(matches[0].group(2)), 'failed': int(matches[1].group(2))}
            if (reported['passed'] + reported['failed'] != total or
                    reported['passed'] != len(passed) or reported['failed'] != len(failed)):
                problems.append('native summary counts disagree with result markers')
        if any(row['stdout_line'] > index + 1 for row in observations + nested):
            problems.append('test result markers follow the native summary trailer')
    if interrupted or (isinstance(exit_code, int) and exit_code < 0):
        problems.append('process was interrupted or killed')
    elif exit_code not in (0, 255):
        problems.append('native exit status is unavailable or was replaced')
    elif reported is not None and ((exit_code == 0) != (reported['failed'] == 0)):
        problems.append('native exit status disagrees with the failure count')
    summary = {'complete': not problems, 'observed_passed_names': passed,
               'observed_failed_names': failed, 'observations': observations,
               'nested_observations': nested,
               'unassigned_assertions': unassigned,
               'reported_counts': reported, 'problems': list(dict.fromkeys(problems))}
    if summary['complete']:
        summary.update(counts=reported, passed_names=passed, failed_names=failed)
    return summary


def result_unit_summary(result):
    """Read older result logs in memory; never rewrite historical records."""
    if not result.get('name', '').startswith('unit/'): return None
    if isinstance(result.get('unit_test_summary'), dict): return result['unit_test_summary']
    if not result.get('artifacts'): return None
    from pathlib import Path
    folder = Path(result['artifacts'])
    try:
        stdout = (folder / 'stdout.log').read_text(errors='replace')
        stderr = (folder / 'stderr.log').read_text(errors='replace')
    except OSError:
        return None
    return parse_unit_output(stdout, stderr, result.get('exit'),
                             result.get('wall_timeout', False) or result.get('sanitizer_error_deadline', False))
