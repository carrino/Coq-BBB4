#!/usr/bin/env python3
"""Render advisory TR hints from explicitly inventoried trace_driver check output.

No Coq or external tool is invoked. Every hinted success is still checked by
HintedTr on the actual machine. Provenance documents a prior trace; it is not a
proof or authentication of that execution. Use --check for read-only replay.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import tempfile

INPUT_DIR = 'tools/censustr/hints'
MANIFEST = INPUT_DIR + '/trace-source-manifest.json'
OUTPUT_MANIFEST = INPUT_DIR + '/generated-data.json'
PART_DIR = 'theories/CensusTr/HintParts'
WRAPPER = 'theories/CensusTr/HintsTr_Data.v'
UNITS, FRONTIER_COUNT, MAX_KEY = 96, 1792, 17**8
UNIT_FIELDS = {'format', 'source_digest', 'unit', 'complete', 'frontier_indices', 'row_count', 'rows'}
PAYLOAD_FIELDS = {'source_sha256', 'compiled_sha256', 'toolchain', 'tag_schema', 'policy', 'parameters_coq_source'}
INTERFACES = ['theories/CensusTr/' + name + '.v' for name in
              ('HintTagTr', 'HintedTr', 'RunTr_Hinted', 'RunTr_Compute', 'RunTr')] + [
              'theories/Tests/HintedTr_Regression.v', 'theories/Tests/HintedTr_Data_Regression.v']
PROJECT_ANCHOR = 'theories/CensusTr/RunTr_Compute.v'
MANIFEST_FIELDS = {'format', 'schema_version', 'units', 'frontier_count', 'chunk_size',
    'safety_limits', 'source_digest', 'trace_payload', 'trace_provenance', 'checked_interfaces', 'unit_files'}
MARKER = '(** GENERATED ADVISORY TR HINT DATA.'
HEADER = MARKER + ''' Every successful hint is checked on the actual machine.
    Input provenance and subset coverage: tools/censustr/hints/generated-data.json. *)
'''


def require(condition, message):
    if not condition:
        raise ValueError(message)


def integer(value, low, high):
    return type(value) is int and low <= value <= high


def sha(data):
    return hashlib.sha256(data).hexdigest()


def digest(value):
    return isinstance(value, str) and re.fullmatch('[0-9a-f]{64}', value) is not None


def encoded(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def unique_fields(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f'duplicate JSON field: {key}')
        result[key] = value
    return result


def parse(data):
    def invalid_constant(value):
        raise ValueError(f'nonstandard JSON constant: {value}')
    return json.loads(data, object_pairs_hook=unique_fields, parse_constant=invalid_constant)


def safe_path(root, relative):
    require(isinstance(relative, str) and '\\' not in relative, 'invalid relative path')
    p = PurePosixPath(relative)
    require(not p.is_absolute() and p.parts and all(x not in ('.', '..') for x in p.parts)
            and p.as_posix() == relative, f'noncanonical relative path: {relative}')
    current = root
    for component in p.parts:
        current = current / component
        require(not current.is_symlink(), f'symlink is not an input/output path: {relative}')
    return current


def read_limited(path, limit):
    require(path.is_file(), f'missing regular file: {path}')
    require(path.stat().st_size <= limit, f'input exceeds declared byte budget: {path}')
    with path.open('rb') as stream:
        data = stream.read(limit + 1)
    require(len(data) <= limit, f'input exceeds declared byte budget: {path}')
    return data


def tag_schema():
    entries = []
    for family, count, horizon in [('ngram', 4, None), ('rank', 4, None),
            ('qh_plain', 9, 'short'), ('qh_lex', 3, 'short'), ('qh_rw', 1, 'short'),
            ('qh_plain', 9, 'full'), ('qh_lex', 3, 'full'), ('qh_rw', 1, 'full'), ('rw', 4, None)]:
        for index in range(count):
            item = {'code': len(entries), 'family': family, 'index': index}
            if horizon is not None:
                item['horizon'] = horizon
            entries.append(item)
    return entries


def validate_manifest(manifest):
    require(isinstance(manifest, dict) and set(manifest) == MANIFEST_FIELDS, 'unexpected source manifest fields')
    require(manifest['format'] == 'tr-hint-source-v1' and type(manifest['schema_version']) is int
            and manifest['schema_version'] == 1, 'unsupported manifest/schema version')
    require(type(manifest['units']) is int and manifest['units'] == UNITS
            and type(manifest['frontier_count']) is int and manifest['frontier_count'] == FRONTIER_COUNT,
            'unsupported unit/frontier inventory')
    require(integer(manifest['chunk_size'], 1, 1024), 'chunk_size must be in 1..1024')
    limits = manifest['safety_limits']
    require(isinstance(limits, dict) and set(limits) == {'input_bytes', 'input_rows', 'chunks', 'rationale'},
            'declare input_bytes, input_rows, chunks and rationale safety limits')
    for name in ('input_bytes', 'input_rows', 'chunks'):
        require(integer(limits[name], 1, 2**63-1), f'invalid {name} safety limit')
    require(isinstance(limits['rationale'], str) and limits['rationale'].strip(), 'document safety-limit rationale')
    payload = manifest['trace_payload']
    require(isinstance(payload, dict) and set(payload) == PAYLOAD_FIELDS, 'invalid six-field trace payload')
    require(digest(manifest['source_digest']) and sha(canonical(payload)) == manifest['source_digest'],
            'trace payload/source digest mismatch')
    # Payload map keys are inert historical labels. Never resolve/open them.
    for name in ('source_sha256', 'compiled_sha256'):
        require(isinstance(payload[name], dict) and all(isinstance(k, str) and digest(v)
            for k, v in payload[name].items()), f'invalid documentary {name}')
    require(canonical(payload['tag_schema']) == canonical(tag_schema()), 'unsupported winner tag schema')
    require(isinstance(payload['toolchain'], dict) and isinstance(payload['parameters_coq_source'], str),
            'invalid documentary toolchain/parameters')
    policy = payload['policy']
    require(isinstance(policy, dict) and all(type(policy.get(k)) is int and policy[k] == v
        for k, v in {'units': UNITS, 'frontier_levels': 3, 'pop_exponent': 13, 'rounds': 4096}.items()),
        'unsupported trace exploration policy')
    require(isinstance(manifest['trace_provenance'], dict), 'invalid documentary trace provenance')
    interfaces = manifest['checked_interfaces']
    require(isinstance(interfaces, dict) and set(interfaces) == set(INTERFACES)
            and all(digest(v) for v in interfaces.values()), 'expected checked interface hashes')
    units = manifest['unit_files']
    require(isinstance(units, list) and len(units) <= UNITS, 'invalid unit file inventory')
    previous = -1
    for item in units:
        require(isinstance(item, dict) and set(item) == {'unit', 'path', 'sha256'}, 'invalid unit file entry')
        unit = item['unit']
        require(integer(unit, 0, UNITS-1) and unit > previous, 'unit inventory must be sorted and unique')
        require(item['path'] == f'{INPUT_DIR}/unit{unit:02d}.rows.json' and digest(item['sha256']),
                'noncanonical unit input filename/hash')
        previous = unit
    return manifest


def validate_unit(record, unit, source_digest, row_limit):
    require(isinstance(record, dict) and set(record) == UNIT_FIELDS, 'expected exact trace_driver check-output fields')
    require(record['format'] == 'tr-hint-unit-v1', 'unsupported unit format')
    require(type(record['unit']) is int and record['unit'] == unit, 'unit inventory/record mismatch')
    require(record['source_digest'] == source_digest, 'mixed source/artifact digests')
    require(record['complete'] is True, 'incomplete unit')
    indices = record['frontier_indices']
    require(isinstance(indices, list) and all(type(i) is int for i in indices)
            and indices == list(range(unit, FRONTIER_COUNT, UNITS)), 'incomplete or invalid frontier coverage')
    rows = record['rows']
    require(isinstance(rows, list) and len(rows) <= row_limit, 'input rows exceed declared safety limit')
    require(integer(record['row_count'], 0, row_limit) and record['row_count'] == len(rows), 'row_count mismatch')
    previous = 0
    for row in rows:
        require(isinstance(row, list) and len(row) == 2, 'expected [key, tag] row')
        key, tag = row
        require(integer(key, 1, MAX_KEY), 'invalid eight-slot positive machine key')
        require(integer(tag, 0, 37), 'invalid winner code (valid tags are 0..37)')
        require(key > previous, 'unit rows must be sorted with unique keys')
        previous = key
    return rows


def load(root):
    # The provenance manifest itself has a separate bounded size; input data
    # budgets are explicit reviewed policy, not silent truncation or auto-growth.
    raw = read_limited(safe_path(root, MANIFEST), 4*1024**2)
    manifest = validate_manifest(parse(raw))
    for name, expected in manifest['checked_interfaces'].items():
        require(sha(read_limited(safe_path(root, name), 4*1024**2)) == expected,
                f'checked interface changed: {name}')
    inputdir = safe_path(root, INPUT_DIR)
    found = {p.name for p in inputdir.glob('*.rows.json')}
    expected = {Path(item['path']).name for item in manifest['unit_files']}
    require(found == expected, 'unit file inventory differs (missing or undeclared input)')
    limits = manifest['safety_limits']
    unique, inputs, input_rows, input_bytes = {}, [], 0, 0
    for item in manifest['unit_files']:
        data = read_limited(safe_path(root, item['path']), limits['input_bytes']-input_bytes)
        input_bytes += len(data)
        require(sha(data) == item['sha256'], f'input hash mismatch: {item["path"]}')
        record = parse(data)
        rows = validate_unit(record, item['unit'], manifest['source_digest'], limits['input_rows']-input_rows)
        input_rows += len(rows)
        for key, tag in rows:
            require(key not in unique or unique[key] == tag, f'conflicting winner codes for key {key}')
            unique[key] = tag
        inputs.append(dict(item, row_count=len(rows), frontier_indices=record['frontier_indices']))
    return manifest, raw, [[key, unique[key]] for key in sorted(unique)], inputs, input_rows, input_bytes


def render_data(rows, chunk_size):
    files, parts, definitions = {}, [], []
    for index, start in enumerate(range(0, len(rows), chunk_size)):
        suffix = f'{index:04d}'
        module = 'HintsTr_Data_P' + suffix
        codes, decoded = 'hint_codes_tr_p' + suffix, 'hint_rows_tr_p' + suffix
        entries = ';\n  '.join(f'({key}%positive, {tag}%nat)' for key, tag in rows[start:start+chunk_size])
        files[f'{PART_DIR}/{module}.v'] = (HEADER + 'From Coq Require Import List PArith.\n'
            'From BBB4.CensusTr Require Import HintTagTr.\nImport ListNotations.\n\n'
            f'Definition {codes} : list (positive * nat)%type := [\n  {entries}\n].\n\n'
            f'Definition {decoded} : list TrHintRow :=\n'
            '  fold_right (fun \'(key, code) acc =>\n'
            '    match tr_winner_decode code with\n'
            '    | Some tag => (key, tag) :: acc\n'
            '    | None => acc\n'
            f'    end) [] {codes}.\n').encode()
        parts.append(module)
        definitions.append(decoded)
    aggregate = HEADER + ('From Coq Require Import List.\n'
        'From BBB4.CensusTr Require Import HintTagTr.\nImport ListNotations.\n')
    if parts:
        aggregate += '\nFrom BBB4.CensusTr.HintParts Require Import\n  ' + '\n  '.join(parts) + '.\n'
        aggregate += '\nDefinition hint_rows_tr : list TrHintRow :=\n  concat [\n    ' + ';\n    '.join(definitions) + '\n  ].\n'
    else:
        aggregate += '\nDefinition hint_rows_tr : list TrHintRow := [].\n'
    aggregate += ('\n(** Informational marker, never a trusted proof premise. *)\n'
                  'Definition hint_data_schema_tr : nat := tr_hint_schema_version.\n')
    files[WRAPPER] = aggregate.encode()
    return files


def project_text(data, parts):
    require(b'\r' not in data and b'\0' not in data, 'unsupported _CoqProject encoding')
    lines = data.decode().splitlines(keepends=True)
    owned = set(INTERFACES) - {PROJECT_ANCHOR, 'theories/CensusTr/RunTr.v'} | {WRAPPER}
    def is_owned(line):
        return line in owned or re.fullmatch(re.escape(PART_DIR) + r'/HintsTr_Data_P[0-9]{4,}\.v', line)
    kept = [line for line in lines if not is_owned(line.rstrip('\n'))]
    require(sum(line.rstrip('\n') == PROJECT_ANCHOR for line in kept) == 1, 'unique RunTr_Compute project anchor required')
    registered = [INTERFACES[0], INTERFACES[1]] + parts + [WRAPPER, INTERFACES[2]] + INTERFACES[5:]
    index = next(i for i, line in enumerate(kept) if line.rstrip('\n') == PROJECT_ANCHOR)
    kept[index:index] = [name + '\n' for name in registered]
    return ''.join(kept).encode(), registered


def render(root):
    manifest, raw, rows, inputs, input_rows, input_bytes = load(root)
    chunks = (len(rows)+manifest['chunk_size']-1)//manifest['chunk_size']
    require(chunks <= manifest['safety_limits']['chunks'], 'chunks exceed declared safety limit; review chunk size/budget')
    files = render_data(rows, manifest['chunk_size'])
    parts = [name for name in files if name.startswith(PART_DIR + '/')]
    project, registered = project_text(read_limited(safe_path(root, '_CoqProject'), 16*1024**2), parts)
    included = [item['unit'] for item in inputs]
    metadata = {'format': 'tr-hint-generated-data-v1', 'schema_version': 1,
        'status': 'deterministically rendered advisory data; Coq validation is separate',
        'source_manifest_sha256': sha(raw), 'source_digest': manifest['source_digest'],
        'generator_sha256': sha(Path(__file__).read_bytes()),
        'checked_interfaces': manifest['checked_interfaces'], 'input_units': inputs,
        'coverage': {'units': UNITS, 'frontier_count': FRONTIER_COUNT, 'included_units': included,
            'omitted_units': [i for i in range(UNITS) if i not in included],
            'all_unit_records_present': len(included) == UNITS,
            'basis': 'Exact JSON shard inventory validation; this renderer does not rerun or authenticate the trace.'},
        'row_count': len(rows), 'input_row_count': input_rows,
        'same_winner_rows_deduplicated_across_units': input_rows-len(rows),
        'input_bytes': input_bytes, 'canonical_rows_sha256': sha(canonical(rows)),
        'chunk_count': chunks, 'chunk_size': manifest['chunk_size'],
        'coq_source_bytes': sum(map(len, files.values())), 'safety_limits': manifest['safety_limits'],
        'registered_project_paths': registered,
        'files_sha256': {name: sha(data) for name, data in sorted(files.items())}}
    files[OUTPUT_MANIFEST] = encoded(metadata)
    files['_CoqProject'] = project
    return files, metadata


def generate(root, check=False):
    root = Path(root).resolve()
    files, metadata = render(root)
    partdir = safe_path(root, PART_DIR)
    expected = {name for name in files if name.startswith(PART_DIR + '/')}
    found = set()
    if partdir.exists():
        for path in partdir.iterdir():
            if path.suffix != '.v':
                continue  # Existing compiler artifacts are outside generator ownership.
            require(re.fullmatch(r'HintsTr_Data_P[0-9]{4,}\.v', path.name), 'unexpected source in owned HintParts directory')
            safe_path(root, path.relative_to(root).as_posix())
            found.add(path.relative_to(root).as_posix())
    require(not found-expected, 'stale generated HintParts source; explicitly remove stale modules/artifacts before regeneration')
    # Validate all paths and contents before any mutation.
    changed = []
    for name, data in files.items():
        path = safe_path(root, name)
        require(not path.exists() or path.is_file(), f'non-file output path: {name}')
        if not path.exists() or path.read_bytes() != data:
            changed.append((path, data))
    require(not check or not changed, 'generated hints/project are stale: ' + ', '.join(str(p.relative_to(root)) for p, _ in changed))
    if not check:
        for path, data in changed:
            path.parent.mkdir(parents=True, exist_ok=True)
            fd, temporary = tempfile.mkstemp(prefix='.' + path.name + '.', dir=path.parent)
            try:
                with os.fdopen(fd, 'wb') as stream:
                    stream.write(data)
                os.replace(temporary, path)
            finally:
                if os.path.exists(temporary):
                    os.unlink(temporary)
    return {'status': 'checked' if check else 'generated', 'changed_files': len(changed),
            **{key: metadata[key] for key in ('row_count', 'input_row_count', 'input_bytes', 'chunk_count', 'chunk_size', 'coq_source_bytes')},
            'included_units': metadata['coverage']['included_units'], 'coq_executed': False}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--check', action='store_true', help='Compare generated sources/metadata/project; write nothing')
    args = parser.parse_args(argv)
    try:
        print(json.dumps(generate(args.repo, args.check), sort_keys=True))
    except (OSError, ValueError) as error:
        parser.exit(1, f'{error}\n')


if __name__ == '__main__':
    main()
