#!/usr/bin/env python3
"""Bundle unchanged LDRQ/LDRT proofs by their exact closeout consumers.

Canonical board files remain available. Consumers import nested board modules
directly, without aliases or compatibility wrappers. Grouping by exact consumer
membership prevents a consumer from loading unrelated boards. Require scoping
uses the accepted LAP bundler's renderer. Run before gen_closeout_tr.py.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import re

from gen_lap_bundles import REQUIRE, render_bundle as render_lap_bundle

REPO = Path(__file__).resolve().parents[2]
BOARD_DIRECTORY = Path('theories/Machines/LadderTr')
CONSUMER_DIRECTORY = Path('theories/CloseoutTr')
BOARD_NAME = re.compile(r'LDR[QT]_[A-Za-z0-9_]+\Z')
BUNDLE_NAME = re.compile(r'BundleLDR[QT]_[0-9a-f]{12}_[0-9]{3}\Z')
BOARD_REQUIRE = re.compile(
    r'^From BBB4\.Machines\.LadderTr Require (Import )?([\w \t\n]+)\.[ \t]*$', re.M)
ADAPTER = re.compile(
    r'^\(\* LADDER BUNDLE IMPORT: (From BBB4\.Machines\.LadderTr Require [^*]+) \*\)\n'
    r'.*?^\(\* END LADDER BUNDLE IMPORT \*\)', re.M | re.S)


def original_imports(text):
    restored = ADAPTER.sub(lambda match: match[1], text)
    if '(* LADDER BUNDLE IMPORT:' in restored or '(* END LADDER BUNDLE IMPORT *)' in restored:
        raise ValueError('malformed ladder import adapter')
    return restored


def imported_boards(text):
    text = original_imports(text)
    matches = list(BOARD_REQUIRE.finditer(text))
    if any(set(match[2].split()) & {'Export', 'Import'} for match in matches):
        raise ValueError('unsupported LadderTr Require modifier')
    names = {name for match in matches
             for name in match[2].split() if BOARD_NAME.fullmatch(name)}
    # Fail closed for an unsupported LadderTr Require form rather than missing
    # a consumer and changing the intended membership grouping.
    residual = BOARD_REQUIRE.sub('', text)
    if re.search(r'^From BBB4\.Machines\.LadderTr Require\b', residual, re.M):
        raise ValueError('unsupported LadderTr Require form')
    return names


def grouping(repo, chunk=32):
    if type(chunk) is not int or not 1 <= chunk <= 32:
        raise ValueError('ladder bundle size must be an integer between 1 and 32')
    repo = Path(repo)
    boards = {path.stem: path for prefix in ('LDRQ', 'LDRT')
              for path in sorted((repo / BOARD_DIRECTORY).glob(prefix + '_*.v'))}
    if not boards:
        raise ValueError('no LDRQ/LDRT canonical boards')
    if any(not BOARD_NAME.fullmatch(name) for name in boards):
        raise ValueError('invalid canonical board name')
    consumers, uses = {}, defaultdict(set)
    for path in sorted((repo / CONSUMER_DIRECTORY).glob('CBT_*.v')):
        names = imported_boards(path.read_text())
        if names - boards.keys():
            raise ValueError(f'{path}: missing canonical boards: {sorted(names - boards.keys())}')
        if names:
            consumers[path] = names
            for name in names:
                uses[name].add(path.stem)
    if boards.keys() - uses.keys():
        raise ValueError('canonical boards have no supported consumer: ' +
                         ', '.join(sorted(boards.keys() - uses.keys())))
    cohorts = defaultdict(list)
    for name in sorted(boards):
        cohorts[(name.split('_', 1)[0], tuple(sorted(uses[name])))].append(boards[name])
    grouped, cohort_info = {}, []
    for (prefix, members), paths in sorted(cohorts.items()):
        digest = hashlib.sha256(('\n'.join(members) + '\n').encode()).hexdigest()[:12]
        bundles = []
        for start in range(0, len(paths), chunk):
            name = f'Bundle{prefix}_{digest}_{start // chunk:03d}'
            if name in grouped:
                raise ValueError('bundle name collision')
            grouped[name] = paths[start:start + chunk]
            bundles.append(name)
        cohort_info.append({'prefix': prefix, 'consumers': list(members),
                            'boards': [path.stem for path in paths], 'bundles': bundles})
    mapping = {path.stem: name for name, paths in grouped.items() for path in paths}
    if set(mapping) != set(boards):
        raise ValueError('incomplete board mapping')
    for path, expected in consumers.items():
        actual = {board.stem for name in {mapping[board] for board in expected}
                  for board in grouped[name]}
        if actual != expected:
            raise ValueError(f'{path}: bundled board union differs from original')
    return grouped, mapping, consumers, cohort_info


def render_bundle(paths):
    for path in paths:
        raw = path.read_bytes()
        if b'\r' in raw or b'\x00' in raw:
            raise ValueError(f'noncanonical source bytes: {path}')
        source = raw.decode('utf-8')
        if re.search(r'^\s*(Module|End|Global|Set|Unset|Open Scope|Close Scope)\b', source, re.M):
            raise ValueError(f'unreviewed module/scope command: {path}')
    text = render_lap_bundle(paths).replace('tools/censustr/gen_lap_bundles.py',
                                          'tools/censustr/gen_ladder_bundles.py', 1)
    for path in paths:
        expected = REQUIRE.sub(lambda match: f'Import {match[2]}.', path.read_text())
        wrapped = f'Module {path.stem}.\n{expected}\nEnd {path.stem}.\n'
        if text.count(wrapped) != 1:
            raise ValueError(f'proof body preservation failed: {path}')
    return text


def rewrite_imports(text, mapping):
    text = original_imports(text)
    expected = imported_boards(text)
    if expected - mapping.keys():
        raise ValueError('missing bundle mapping for ' + ', '.join(sorted(expected - mapping.keys())))
    seen = set()
    def adapt(match):
        names = match[2].split()
        if not any(name in mapping for name in names):
            return match[0]
        lines = [f'(* LADDER BUNDLE IMPORT: {match[0]} *)']
        for name in names:
            if name not in mapping:
                lines.append(f'From BBB4.Machines.LadderTr Require {match[1] or ""}{name}.')
                continue
            bundle = mapping[name]
            if bundle not in seen:
                lines.append(f'From BBB4.Machines.LadderTr.Bundles Require Import {bundle}.')
                seen.add(bundle)
            if match[1]:
                lines.append(f'Import {name}.')
        lines.append('(* END LADDER BUNDLE IMPORT *)')
        return '\n'.join(lines)
    adapted = BOARD_REQUIRE.sub(adapt, text)
    if original_imports(adapted) != text:
        raise ValueError('consumer changed outside reversible import adapter')
    return adapted


def read_bundle_map(repo=REPO):
    path = Path(repo) / BOARD_DIRECTORY / 'Bundles/boards.tsv'
    if not path.exists():
        return {}
    mapping = {}
    for line in path.read_text().splitlines():
        parts = line.split('\t')
        if len(parts) != 2:
            raise ValueError(f'invalid ladder bundle inventory: {line}')
        board, bundle = parts
        if board in mapping or not BOARD_NAME.fullmatch(board) or not BUNDLE_NAME.fullmatch(bundle):
            raise ValueError(f'invalid ladder bundle inventory: {line}')
        mapping[board] = bundle
    if not mapping:
        raise ValueError('empty ladder bundle inventory')
    return mapping


def generate(repo=REPO, chunk=32, check=False):
    repo = Path(repo)
    grouped, mapping, consumers, cohorts = grouping(repo, chunk)
    directory = repo / BOARD_DIRECTORY / 'Bundles'
    outputs = {directory / f'{name}.v': render_bundle(paths) for name, paths in grouped.items()}
    stale = set(directory.glob('BundleLDR*.v')) - outputs.keys()
    if stale:
        raise ValueError('unexpected old ladder bundles: ' + ', '.join(map(str, sorted(stale))))
    outputs[directory / 'boards.tsv'] = ''.join(f'{board}\t{bundle}\n' for board, bundle in sorted(mapping.items()))
    manifest = {'format': 'ladder-consumer-cohorts-v1', 'maximum_boards_per_bundle': chunk,
        'grouping': 'prefix and exact sorted closeout consumer membership, then sorted chunks',
        'board_count': len(mapping), 'bundle_count': len(grouped), 'consumer_count': len(consumers),
        'consumer_board_union_equal': True, 'cohorts': cohorts,
        'canonical_sha256': {str(path.relative_to(repo)): hashlib.sha256(path.read_bytes()).hexdigest()
                             for paths in grouped.values() for path in paths}}
    outputs[directory / 'cohorts.json'] = json.dumps(manifest, sort_keys=True, indent=2) + '\n'
    for path in consumers:
        outputs[path] = rewrite_imports(path.read_text(), mapping)
    project = repo / '_CoqProject'
    source = project.read_text()
    if source and not source.endswith('\n'):
        raise ValueError('_CoqProject must end with a newline')
    have = set(source.splitlines())
    expected = {str((directory / f'{name}.v').relative_to(repo)) for name in grouped}
    old = {line for line in have if line.startswith(str(BOARD_DIRECTORY / 'Bundles/BundleLDR'))}
    if old - expected:
        raise ValueError('unexpected old ladder bundle entries in _CoqProject')
    outputs[project] = source + ''.join(name + '\n' for name in sorted(expected - have))
    changed = [path for path, text in outputs.items() if not path.exists() or path.read_text() != text]
    if check and changed:
        raise ValueError('stale generated ladder files: ' + ', '.join(map(str, changed)))
    if not check:
        for path in changed:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(outputs[path])
    print(f'{len(mapping)} boards, {len(cohorts)} cohorts, {len(grouped)} bundles, '
          f'{len(consumers)} consumers; exact board unions preserved; '
          f'{"checked" if check else "wrote"} {len(outputs) if check else len(changed)} files')
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=REPO)
    parser.add_argument('--chunk', type=int, default=32)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    try:
        generate(args.repo, args.chunk, args.check)
    except (OSError, ValueError) as error:
        parser.exit(1, str(error) + '\n')


if __name__ == '__main__':
    main()
