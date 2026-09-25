#!/usr/bin/env python3
"""Readable live and saved reports for a Vampire test campaign."""
import argparse
from collections import Counter, defaultdict
import fcntl
import json
from pathlib import Path
import shlex
import sys
import time
import xml.etree.ElementTree as ET

from unit_output import result_unit_summary


def section(case):
    name = case['name']
    if name.startswith('discovery/'): return 'Option discovery'
    if name.startswith('arithmetic/'): return 'Exact arithmetic and arrays'
    if name.startswith('datatype/'): return 'Datatype graph oracle'
    if name.startswith('parser/'): return 'Parser contracts'
    if name.startswith('mode/'): return 'Mode output contracts'
    if name.startswith('portfolio/'):
        return {'smt-logic': 'SMT schedule dispatch', 'properties': 'Portfolio input categories',
                'induction': 'Induction schedules'}.get(name.split('/')[1], 'Portfolio contracts')
    if name.startswith('behavior/'):
        return {'shutdown': 'Shutdown memory paths', 'fmb-memory': 'FMB memory regressions',
                'model': 'Independent model checks', 'fmb-options': 'Finite-model options', 'roundtrip': 'TPTP output round trips',
                'stdin': 'Standard input', 'resources': 'Resource option behavior',
                'proof': 'Independent proof checks', 'portfolio': 'Portfolio schedules'}[name.split('/')[1]]
    if name.startswith('options/'):
        return {'values': 'Option documented values', 'aliases': 'Option short names',
                'rejection': 'Invalid option values', 'boundary': 'Numeric option boundaries'}[name.split('/')[1]]
    if name.startswith('edge/'):
        return {'finite': 'Quantifier model oracle', 'functions': 'Function model oracle',
                'metamorphic': 'Input transformations', 'equality': 'Equality and selection',
                'theory': 'Theory identities', 'parser': 'Parser boundaries',
                'rejection': 'Malformed inputs', 'interactions': 'Option interactions', 'hol': 'HOL option variants'}[name.split('/')[1]]
    if name.startswith('unit/'): return 'Unit tests'
    if name.startswith('generated/cnf-'): return 'Generated CNF'
    if name.startswith('generated/bool-'): return 'Boolean expressions'
    if name.startswith('generated/int-'): return 'Integer boundaries'
    if name.startswith('features/finite-'): return 'Finite models'
    if name.startswith('features/portfolio-'): return 'Portfolio workers'
    if name.startswith('features/proof-'): return 'Proof output'
    if name == 'sanity': return 'Release sanity'
    source = case.get('source', '')
    for prefix, label in [('parse/', 'Parser'), ('Problems/', 'TPTP regressions'),
                          ('theory/', 'Theories and FOOL'), ('hol/', 'Higher-order logic'),
                          ('induction/', 'Induction'), ('term-algebra/', 'Datatypes'),
                          ('synthesis/', 'Synthesis'), ('ucore/', 'Unsat cores'), ('fmb/', 'Finite models')]:
        if source.startswith(prefix): return label
    return 'Other corpus checks'


def location(result):
    errors = result.get('valgrind_errors', [])
    # Allocation/read stack locations help navigation; they do not prove a root cause.
    for error in errors[:1]:
        if not error.get('file'): continue
        try:
            tree = ET.parse(error['file'])
            for item in tree.findall('error'):
                if item.findtext('kind') != error['kind']: continue
                for frame in item.findall('stack/frame'):
                    filename = frame.findtext('file', '')
                    if filename.endswith(('.cpp', '.hpp')):
                        directory = frame.findtext('dir', '')
                        return f'{Path(directory) / filename}:{frame.findtext("line", "?")}'
        except (OSError, ET.ParseError):
            pass
    if result.get('source'): return result['source']
    if result['name'].startswith('unit/'):
        unit = result['name'].removeprefix('unit/')
        matches = list((Path(__file__).resolve().parents[2] / 'UnitTests').rglob('t' + unit + '.cpp'))
        if matches: return str(matches[0])
    return result['name']


def native_unit_detail(result):
    summary = result_unit_summary(result)
    if summary is None: return []
    lines = []
    if summary['complete']:
        counts = summary['counts']
        lines.append(f'  Native tests: {counts["passed"]} passed, {counts["failed"]} failed, {counts["total"]} total (complete output)')
    else:
        lines.append('  Native tests: incomplete output; ' + '; '.join(summary['problems']))
        lines.append(f'  Observed markers: {len(summary["observed_passed_names"])} OK, {len(summary["observed_failed_names"])} FAIL (not final counts)')
    for row in summary['observations']:
        if row['outcome'] != 'fail' and not row['assertions']: continue
        marker = 'FAIL' if row['outcome'] == 'fail' else 'OK WITH ASSERTION'
        lines.append(f'    [{marker}] {row["name"]} (stdout.log, normalized line {row["stdout_line"]})')
        for assertion in row['assertions']:
            lines.append(f'      Where: {assertion["location"]}')
            lines.append(f'      Assertion: {assertion["text"]}')
    for row in summary.get('nested_observations', []):
        if row['outcome'] != 'fail': continue
        lines.append(f'    Nested [FAIL] {row["name"] or "(no payload)"} inside {row["parent"]} (stdout.log, normalized line {row["stdout_line"]})')
        lines.append(f'      Diagnostic: {row["text"]}')
    for assertion in summary['unassigned_assertions']:
        lines.append(f'    Unassigned assertion: {assertion["location"]} ({assertion["stream"]}.log, normalized line {assertion["line"]})')
    return lines


def unit_output_warning(result):
    # Surface inconsistent/partial native logs without changing legacy suite counts.
    summary = result_unit_summary(result)
    return bool(summary and (not summary['complete'] or summary['observed_failed_names']))


def failure_detail(result, commands=False):
    tag = {'fail': 'FAIL', 'inconclusive': 'INCONCLUSIVE', 'pass': 'UNIT OUTPUT WARNING'}[result['outcome']]
    lines = [f'[{tag}] {result["name"]} ({result.get("seconds", 0):.2f}s)',
             f'  Reason: {result.get("reason", "unknown")}',
             f'  Where:  {location(result)}']
    if result.get('check') in ('szs', 'smt-proof', 'roundtrip', 'finite-model'):
        lines.append(f'  Answer: expected {result["expected"]}; observed {", ".join(result.get("statuses", [])) or "no SZS status"}')
    if result.get('semantic_outcome'):
        lines.append(f'  Logical check: {result["semantic_outcome"]}; memory: {result.get("memory_outcome", "unknown")}')
    for diagnostic in result.get('sanitizer_messages', [])[:2]: lines.append('  Sanitizer: ' + diagnostic)
    for warning in result.get('sanitizer_warnings', [])[:2]: lines.append('  Sanitizer warning: ' + warning)
    errors = Counter(e['kind'] for e in result.get('valgrind_errors', []))
    if errors:
        lines.append('  Memory: ' + ', '.join(f'{kind}={count}' for kind, count in sorted(errors.items())))
    lines.extend(native_unit_detail(result))
    artifacts = result.get('artifacts')
    if artifacts:
        lines.append(f'  Logs:   {artifacts}/')
        command_file = Path(artifacts) / 'command.json'
        if commands and command_file.exists():
            command = json.loads(command_file.read_text())
            lines.append(f'  Cwd:    {command["cwd"]}')
            lines.append(f'  Run:    {shlex.join(command["argv"])}')
    return '\n'.join(lines)


def table(cases, results):
    planned = Counter(section(case) for case in cases)
    counts = defaultdict(Counter)
    for result in results: counts[section(result)][result['outcome']] += 1
    labels = list(dict.fromkeys([*planned, *counts]))
    lines = [f'{"Section":<25} {"Done/total":>12} {"Pass":>6} {"Fail":>6} {"Inconcl.":>9}']
    for label in labels:
        row = counts[label]
        done = sum(row.values())
        total = planned.get(label, '?')
        lines.append(f'{label:<25} {str(done) + "/" + str(total):>12} {row["pass"]:>6} {row["fail"]:>6} {row["inconclusive"]:>9}')
    total = Counter(result['outcome'] for result in results)
    lines.append(f'{"TOTAL":<25} {str(len(results)) + "/" + str(len(cases) or "?"):>12} {total["pass"]:>6} {total["fail"]:>6} {total["inconclusive"]:>9}')
    return '\n'.join(lines)


class TerminalReporter:
    def __init__(self, cases, previous, output, metadata=None):
        self.cases = cases
        self.results = list(previous)
        self.output = output
        self.started = set()
        self.last_progress = time.monotonic()
        info = (metadata or {}).get('arguments', {})
        self.verbose = info.get('verbose', False)
        mode = 'Valgrind Memcheck' if info.get('memcheck') else 'Correctness'
        print(f'Vampire test campaign | {mode}\nBuild: {info.get("build", "unknown")}\nWorkers: {info.get("jobs", "?")} | Wall timeout: {info.get("timeout", "?")}s\nResults: {output}\n', flush=True)
        print(table(cases, previous), flush=True)
        self.transcript = (output / 'terminal.log').open('a')
        self.transcript.write(table(cases, previous) + '\n')

    def record(self, result):
        self.results.append(result)
        label = section(result)
        lines = []
        if label not in self.started:
            self.started.add(label)
            lines.append(f'\n=== {label} ===')
        if result['outcome'] != 'pass' or unit_output_warning(result):
            lines.append(f'[{label}] ' + failure_detail(result))
        elif self.verbose or len(self.results) % 100 == 0 or time.monotonic() - self.last_progress >= 10:
            lines.append(f'[PASS] [{label}] {result["name"]} ({len(self.results)}/{len(self.cases)} completed)')
            self.last_progress = time.monotonic()
        if lines:
            text = '\n'.join(lines)
            print(text, flush=True)
            self.transcript.write(text + '\n')
            self.transcript.flush()

    def finish(self):
        failures = [r for r in self.results if r['outcome'] != 'pass' or unit_output_warning(r)]
        groups = defaultdict(list)
        for result in failures: groups[section(result)].append(result)
        with (self.output / 'failures.txt').open('w') as out:
            for label, rows in groups.items():
                out.write(f'=== {label}: {len(rows)} suite failures or output warnings ===\n\n')
                for result in sorted(rows, key=lambda r: r['name']):
                    out.write(failure_detail(result, commands=True) + '\n\n')
        text = '\n=== Final section summary ===\n' + table(self.cases, self.results)
        text += f'\nFailure details and commands: {self.output / "failures.txt"}'
        text += f'\nMachine-readable results: {self.output / "summary.json"}'
        print(text, flush=True)
        self.transcript.write(text + '\n')
        self.transcript.close()


def journal_active(output):
    """A held run lock identifies a current writer; stale state files do not."""
    if (output / 'summary.json').exists(): return False
    try:
        with (output / '.run.lock').open('rb') as lock:
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                return True
            # The context closes only this descriptor and releases our lock.
    except FileNotFoundError:
        pass
    return False


def read_results(output, cases=None):
    summary_path = output / 'summary.json'
    summary_present = summary_path.exists()
    summary = json.loads(summary_path.read_text()) if summary_present else None
    results = []
    seen = set()
    selected = None if cases is None else {case['name'] for case in cases}
    journal = output / 'results.jsonl'
    if journal.exists():
        lines = journal.read_bytes().splitlines(keepends=True)
        for number, line in enumerate(lines, 1):
            try:
                row = json.loads(line)
            except (ValueError, UnicodeDecodeError) as error:
                if number == len(lines) and not line.endswith(b'\n') and journal_active(output):
                    break
                if not summary_present and summary_path.exists():
                    return read_results(output, cases)  # Re-read after a concurrent final write.
                raise ValueError(f'invalid result journal record at {journal}:{number}: {error}') from error
            if not isinstance(row, dict) or not isinstance(row.get('name'), str):
                raise ValueError(f'invalid result record at {journal}:{number}: expected a named object')
            name = row['name']
            if name in seen:
                raise ValueError(f'duplicate result for {name} at {journal}:{number}')
            if selected is not None and name not in selected:
                raise ValueError(f'unknown case {name} at {journal}:{number}')
            if row.get('outcome') not in ('pass', 'fail', 'inconclusive'):
                raise ValueError(f'unknown outcome {row.get("outcome")!r} for {name} at {journal}:{number}')
            seen.add(name)
            results.append(row)
    if not summary_present and summary_path.exists():
        return read_results(output, cases)  # The final journal preceded this summary.
    if summary_present:
        if not isinstance(summary, dict) or not isinstance(summary.get('totals'), dict):
            raise ValueError(f'invalid completed summary: {summary_path}')
        saved = summary.get('results')
        if not isinstance(saved, list) or len(saved) != len(results) or any(not isinstance(row, dict) or 'name' not in row for row in saved):
            raise ValueError(f'completed summary and result journal differ: {summary_path}')
        if len({row['name'] for row in saved}) != len(saved) or {row['name']: row for row in saved} != {row['name']: row for row in results}:
            raise ValueError(f'completed summary and result journal differ: {summary_path}')
        if Counter(summary.get('totals', {})) != Counter(row['outcome'] for row in results):
            raise ValueError(f'completed summary totals and result journal differ: {summary_path}')
        if selected is not None and seen != selected:
            raise ValueError(f'completed journal does not contain the selected cases: {summary_path}')
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('--watch', action='store_true')
    parser.add_argument('--interval', type=float, default=5)
    parser.add_argument('--failures', action='store_true', help='show every non-passing test with log paths')
    parser.add_argument('--commands', action='store_true', help='include saved reproduction commands')
    parser.add_argument('--tail', type=int, help='show only the most recent N non-passing tests (watch default: 5)')
    args = parser.parse_args()
    if args.interval <= 0 or (args.tail is not None and args.tail < 0): parser.error('interval must be positive and tail nonnegative')
    manifest = args.output / 'cases.json'
    cases = json.loads(manifest.read_text()) if manifest.exists() else None
    while True:
        finished = (args.output / 'summary.json').exists()
        if manifest.exists(): cases = json.loads(manifest.read_text())
        try:
            results = read_results(args.output, cases)
        except (OSError, ValueError) as error:
            parser.error(str(error))
        if args.watch and sys.stdout.isatty(): print('\033[2J\033[H', end='')
        print(f'Vampire campaign: {args.output}\n{table(cases or [], results)}', flush=True)
        failures = [r for r in results if r['outcome'] != 'pass' or unit_output_warning(r)]
        if args.failures or args.watch:
            limit = args.tail if args.tail is not None else (5 if args.watch else None)
            shown = failures if limit is None else failures[-limit:] if limit else []
            for result in shown: print('\n' + failure_detail(result, commands=args.commands), flush=True)
        if not args.watch or finished: break
        time.sleep(args.interval)


if __name__ == '__main__':
    try: main()
    except KeyboardInterrupt: pass
