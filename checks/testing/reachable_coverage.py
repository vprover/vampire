#!/usr/bin/env python3
"""Report raw coverage and apply build-specific, proved branch exclusions."""
import argparse
import gzip
import json
from pathlib import Path

from coverage_overlay import EXCLUDED, inventory, sha256, trace_metrics, verify_original


def pinned_file(path, expected):
    path = Path(path)
    if not isinstance(expected, str) or len(expected) != 64 or sha256(path) != expected:
        raise ValueError(f'changed or invalid pinned file: {path}')
    return path


def under(root, relative):
    relative = Path(relative)
    root = Path(root).resolve()
    path = (root / relative).resolve()
    if relative.is_absolute() or not path.is_relative_to(root):
        raise ValueError(f'path escapes its pinned root: {relative}')
    return path


def summary(metrics):
    return {kind: {'hit': sum(rows.values()), 'found': len(rows),
                   'percent': 100 * sum(rows.values()) / len(rows) if rows else None}
            for kind, rows in metrics.items()}


def verify_entries(ledger, ledger_path, metadata, raw_union, metrics):
    """Accept only source lines with a single object/function contributor.

    Multiple template or object contributors require a separate, reviewed
    mapping implementation. An ambiguous mapping cannot grant an exclusion.
    """
    if ledger.get('schema_version') != 1:
        raise ValueError('unsupported reachability ledger schema')
    build, source = Path(metadata['build']), Path(metadata['source'])
    pins = ledger['build']
    if pins['source'] != str(source) or pins['path'] != str(build):
        raise ValueError('ledger belongs to a different build/source root')
    if pins['gcno_sha256'] != metadata['original_gcno']:
        raise ValueError('ledger coverage note inventory differs from capture')
    if inventory(build, '.gcno') != pins['gcno_sha256']:
        raise ValueError('coverage note inventory changed')
    expected_binaries = {str(build / name): metadata['immutable_files'][str(build / name)]
                         for name in ('vampire', 'vtest')
                         if str(build / name) in metadata['immutable_files']}
    if not expected_binaries or pins['binary_sha256'] != expected_binaries:
        raise ValueError('ledger does not pin every captured binary')
    for path, digest in pins['binary_sha256'].items():
        pinned_file(path, digest)
    pinned_file(build / 'CMakeCache.txt', pins['cmake_cache_sha256'])
    if not pins['compiler_inputs_sha256']:
        raise ValueError('ledger must pin compiler inputs')
    for path, digest in pins['compiler_inputs_sha256'].items():
        pinned_file(path, digest)
    if raw_union.get('exact_raw_counter_sum') is not True:
        raise ValueError('raw counters were not verified as an exact sum')
    objects = raw_union['per_object']
    names = [row['object'] for row in objects]
    if len(names) != len(set(names)) or set(names) != set(pins['gcno_sha256']):
        raise ValueError('raw contributor inventory is incomplete or duplicated')
    if raw_union['objects'] != len(names):
        raise ValueError('raw contributor count differs from its inventory')

    targets = set()
    entries = ledger['entries']
    seen_ids, seen_keys = set(), set()
    for entry in entries:
        if entry['classification'] != 'proved-unreachable':
            raise ValueError('only proved-unreachable edges can be excluded')
        if not entry['id'] or entry['id'] in seen_ids:
            raise ValueError('empty or duplicate ledger ID')
        seen_ids.add(entry['id'])
        if not entry['rationale'].strip() or not entry['scope'].strip():
            raise ValueError('exclusion needs a rationale and proof scope')
        source_file = under(source, entry['source'])
        pinned_file(source_file, entry['source_sha256'])
        pinned_file(under(Path(ledger_path).parent, entry['proof']['path']), entry['proof']['sha256'])
        for path, digest in entry['proof']['supporting_sha256'].items():
            pinned_file(under(Path(ledger_path).parent, path), digest)
        if entry['mapping'] != 'unique-object-function-source-line':
            raise ValueError('unsupported or ambiguous contributor mapping')
        key = (str(source_file), entry['lcov']['line'], entry['lcov']['block'],
               entry['lcov']['branch'], entry['lcov']['occurrence'])
        if key in seen_keys:
            raise ValueError('duplicate excluded LCOV edge')
        seen_keys.add(key)
        if key not in metrics['branches']:
            raise ValueError(f'excluded edge is absent from this capture: {key}')
        if metrics['branches'][key]:
            raise ValueError(f'excluded edge was executed: {key}')
        targets.add(key[:2])

    # Read the entire pinned object inventory, including zero-count objects.
    # Looking only in the proposed contributor would miss template instances.
    contributors = {key: [] for key in targets}
    seen_artifacts, seen_digests = set(), set()
    for row in objects:
        if row['gcc_version'] != pins['gcc_version']:
            raise ValueError('compiler version differs from ledger')
        artifact = row['artifacts']['merged']
        path = pinned_file(artifact['path'], artifact['sha256'])
        expected_note = under(Path(metadata['output']) / 'capture/raw-merged', row['object'])
        expected_artifact = under(Path(metadata['output']) / 'capture/gcov-json/merged', row['object'] + '.json.gz')
        expected_command = [metadata['gcov_tool'], '--branch-probabilities', '--json-format', '--stdout', str(expected_note)]
        if path.resolve() != expected_artifact or artifact['command'] != expected_command:
            raise ValueError('raw artifact is not bound to its captured object')
        if path.resolve() in seen_artifacts or artifact['sha256'] in seen_digests:
            raise ValueError('duplicate raw artifact')
        seen_artifacts.add(path.resolve())
        seen_digests.add(artifact['sha256'])
        document = json.loads(gzip.decompress(path.read_bytes()))
        if document.get('data_file') != str(expected_note):
            raise ValueError('raw gcov data_file differs from its captured object')
        if document.get('format_version') != '2' or document.get('gcc_version') != pins['gcc_version']:
            raise ValueError('raw gcov format/compiler differs from ledger')
        for item in document['files']:
            filename = Path(item['file'])
            if not filename.is_absolute():
                filename = Path(document['current_working_directory']) / filename
            filename = str(filename.resolve())
            for line in item['lines']:
                key = (filename, line['line_number'])
                if key in targets and line['branches']:
                    contributors[key].append((row['object'], line))

    verified = []
    for entry in entries:
        location = (str(under(source, entry['source'])), entry['lcov']['line'])
        matching = contributors[location]
        if len(matching) != 1 or len(entry['contributors']) != 1:
            raise ValueError(f'contributor mapping is ambiguous or incomplete: {location}')
        relative, line = matching[0]
        pin = entry['contributors'][0]
        if pin['object'] != relative or pin['function'] != line.get('function_name'):
            raise ValueError('raw contributor identity differs from proof')
        if pin['gcno_sha256'] != pins['gcno_sha256'][relative]:
            raise ValueError('contributor coverage note differs from proof')
        pinned_file(under(build, relative).with_suffix('.o'), pin['object_sha256'])
        ordinal = pin['ordinal']
        if type(ordinal) is not int or not 0 <= ordinal < len(line['branches']):
            raise ValueError('unknown raw branch ordinal')
        branch = line['branches'][ordinal]
        fields = ('source_block_id', 'destination_block_id', 'throw', 'fallthrough')
        if any(branch[field] != pin[field] for field in fields):
            raise ValueError('raw branch identity differs from proof')
        if branch['count'] != 0:
            raise ValueError('proved-unreachable raw branch was executed')
        # Require one-to-one labels for every branch on the source line.
        # Order is immaterial because source/destination labels are unique.
        # Repeated labels or a folded source line cannot be mapped here.
        raw_labels = [f"{b['source_block_id']} -> {b['destination_block_id']}" for b in line['branches']]
        lcov_rows = {key: hit for key, hit in metrics['branches'].items() if key[:2] == location}
        labels = [key[3] for key in lcov_rows]
        if len(set(raw_labels)) != len(raw_labels) or len(set(labels)) != len(labels) or sorted(raw_labels) != sorted(labels):
            raise ValueError('LCOV line does not map one-to-one to raw branches')
        for key, hit in lcov_rows.items():
            raw_branch = line['branches'][raw_labels.index(key[3])]
            raw_count = raw_branch['count']
            # LCOV gives exception precedence when both flags are true.
            prefix = 'e' if raw_branch['throw'] else 'f' if raw_branch['fallthrough'] else ''
            block = key[2]
            if not block.startswith(prefix) or not block[len(prefix):].isdigit():
                raise ValueError('LCOV branch type differs from raw data')
            if type(raw_count) is not int or raw_count < 0 or hit != (raw_count > 0):
                raise ValueError('LCOV branch hit state differs from raw data')
        if entry['lcov']['branch'] != raw_labels[ordinal] or entry['lcov']['occurrence'] != 0:
            raise ValueError('excluded LCOV edge maps to a different raw edge')
        verified.append({'id': entry['id'], 'source': entry['source'], 'lcov': entry['lcov'],
                         'rationale': entry['rationale'], 'scope': entry['scope'], 'proof': entry['proof'],
                         'contributors': entry['contributors']})
    return verified


def evaluate(overlay, ledger_path, target=100):
    if not 0 <= target <= 100:
        raise ValueError('target must be between 0 and 100 percent')
    overlay, ledger_path = Path(overlay).resolve(), Path(ledger_path).resolve()
    metadata_path = overlay / 'overlay.json'
    metadata = json.loads(metadata_path.read_text())
    if metadata['status'] != 'captured':
        raise ValueError('reachable coverage requires a completed, verified capture')
    verify_original(metadata)
    capture = overlay / 'capture'
    delta_path = capture / 'delta.json'
    delta = json.loads(delta_path.read_text())
    if delta.get('same_denominator') is not True or delta.get('original_inputs_unchanged') is not True:
        raise ValueError('capture did not preserve the original measurement')
    trace = pinned_file(capture / 'coverage.info', delta['merged_trace_sha256'])
    union_path = pinned_file(capture / 'raw-union.json', delta['raw_union_report_sha256'])
    metrics = trace_metrics(trace)
    ledger = json.loads(ledger_path.read_text())
    excluded = verify_entries(ledger, ledger_path, metadata, json.loads(union_path.read_text()), metrics)
    raw = summary(metrics)
    reachable = dict(raw['branches'])
    reachable['found'] -= len(excluded)
    # An empty denominator is not evidence of a completed testing target.
    reachable['percent'] = 100 * reachable['hit'] / reachable['found'] if reachable['found'] else None
    reachable['remaining'] = reachable['found'] - reachable['hit']
    passed = bool(reachable['found']) and 100 * reachable['hit'] >= target * reachable['found']
    return {'schema_version': 1, 'target_percent': target, 'target_met': passed,
            'raw': raw, 'reachable_branches': reachable, 'verified_exclusions': excluded,
            'excluded_branch_count': len(excluded),
            'inputs': {str(p): sha256(p) for p in (metadata_path, delta_path, trace, union_path, ledger_path)},
            'implementation_sha256': {str(p): sha256(p) for p in
                                      (Path(__file__).resolve(), Path(__file__).resolve().with_name('coverage_overlay.py'))},
            'source_scope': {'root': metadata['source'], 'excluded_trees': list(EXCLUDED),
                             'note': 'Raw means unadjusted coverage within this compiled project scope. '
                                     'Test sources, build output, vendored dependencies and files outside the source root are outside that scope. '
                                     'Production-header template instances remain counted. Other build configurations need separate measurements.'},
            'policy': 'Only individually proved unreachable branches are removed from the adjusted denominator. '
                      'Unknown, unsupported and bug-blocked branches remain counted. Raw LCOV is unchanged.',
            'limitation': 'Branch coverage does not establish correctness for every input or execution-path combination.'}


def render(report):
    lines = ['# Reachable branch coverage', '', f"Target: {report['target_percent']:g}%.", '',
             '| Measurement | Hit | Counted | Percent |', '| --- | ---: | ---: | ---: |']
    for label, metric in [(f'Raw {k.replace("_", " ")}', v) for k, v in report['raw'].items()] + [('Reachable branches', report['reachable_branches'])]:
        percent = 'n/a' if metric['percent'] is None else f"{metric['percent']:.6f}%"
        lines.append(f"| {label} | {metric['hit']} | {metric['found']} | {percent} |")
    lines += ['', f"Verified exclusions: {report['excluded_branch_count']}.",
              f"Reachable branches still missed: {report['reachable_branches']['remaining']}.",
              f"Target met: {'yes' if report['target_met'] else 'no'}.", '', report['policy'], '', report['limitation']]
    if 'source_scope' in report:
        scope = report['source_scope']
        lines += ['', '## Measurement scope', '', scope['note'], '',
                  f"Source root: `{scope['root']}`.",
                  'Excluded source trees: ' + ', '.join(f'`{item}/`' for item in scope['excluded_trees']) + '.']
    for entry in report['verified_exclusions']:
        lines += ['', f"## {entry['id']}", '', f"{entry['source']}:{entry['lcov']['line']}, edge {entry['lcov']['branch']}.",
                  '', entry['rationale'], '', f"Proof scope: {entry['scope']}", '',
                  f"Proof: `{entry['proof']['path']}` (SHA-256 `{entry['proof']['sha256']}`)."]
    return '\n'.join(lines) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--overlay', required=True, type=Path)
    parser.add_argument('--ledger', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--require-percent', type=float, default=100)
    args = parser.parse_args()
    if args.output.exists():
        parser.error('output already exists; choose a new directory')
    try:
        report = evaluate(args.overlay, args.ledger, args.require_percent)
    except (ValueError, KeyError, TypeError, OSError, EOFError) as error:
        parser.exit(2, f'reachable coverage: {error}\n')
    args.output.mkdir(parents=True)
    (args.output / 'summary.json').write_text(json.dumps(report, indent=2) + '\n')
    (args.output / 'summary.md').write_text(render(report))
    print(render(report))
    return 0 if report['target_met'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
