#!/usr/bin/env python3
"""Group Valgrind reports by error kind and the first project stack frames."""
import argparse
from collections import Counter
import json
from pathlib import Path
import xml.etree.ElementTree as ET


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('results', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): parser.error('output already exists')
    groups, incomplete = {}, []
    for path in sorted(args.results.rglob('valgrind.*.xml')):
        if any('.interrupted-' in part for part in path.parts):
            continue
        try:
            tree = ET.parse(path)
        except ET.ParseError:
            incomplete.append(str(path))
            continue
        for error in tree.findall('error'):
            kind = error.findtext('kind')
            if kind == 'Leak_StillReachable': continue
            frames = []
            for frame in error.findall('stack/frame'):
                filename = frame.findtext('file', '')
                if filename.endswith(('.cpp', '.hpp')):
                    frames.append(f'{filename}:{frame.findtext("line", "?")} {frame.findtext("fn", "?")}')
                if len(frames) == 3: break
            key = (kind, *frames)
            item = groups.setdefault(key, {'kind': kind, 'frames': frames, 'reports': 0,
                                          'cases': set(), 'example_xml': str(path),
                                          'message': error.findtext('what') or error.findtext('xwhat/text')})
            item['reports'] += 1
            item['cases'].add(str(path.parent.relative_to(args.results)))
    rows = sorted(groups.values(), key=lambda row: (-len(row['cases']), row['kind'], row['frames']))
    for row in rows: row['cases'] = sorted(row['cases'])
    data = {'groups': rows, 'incomplete_xml': incomplete,
            'group_kinds': dict(Counter(row['kind'] for row in rows))}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=2))
    print(f'{len(rows)} stack groups; {len(incomplete)} incomplete XML files')
    print(json.dumps(data['group_kinds']))


if __name__ == '__main__': main()
