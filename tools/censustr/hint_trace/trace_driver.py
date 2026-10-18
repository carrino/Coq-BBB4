#!/usr/bin/env python3
"""Trace the unchanged fallback, one unit and one frontier shard per call.

Compile the optional Coq trace modules and inspect their projection assumptions
before planning. This driver never enumerates all units or starts a worker pool.

  plan --root FROZEN_TREE --outdir NEW_DIR --unit 10 [--frontier-index J]
  run --manifest NEW_DIR/manifest.json --kind inventory [--lock PATH]
  emit --manifest NEW_DIR/manifest.json --frontier-index J
  run --manifest NEW_DIR/manifest.json --kind shard --frontier-index J [--lock PATH]
  check --manifest NEW_DIR/manifest.json

Only run executes Coq. Standalone runs take an exclusive compiler lock outside
the timer. A supervisor can pass --lock PATH --inherited-lock-fd FD instead;
that mode validates and retains the inherited open file description without
acquiring or releasing its lock. The supervisor owns worker limits and cleanup.
Plan/emit/check are offline. Invalid output, stale sources, missing coverage,
bad keys/tags and conflicting winners fail closed. Generated hints carry no
proof authority: production reruns the checker on the actual machine.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
from datetime import datetime, timezone
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import resource
import shutil
import stat
import subprocess
import time

HERE = Path(__file__).resolve().parent
DEFAULT_LOCK = HERE.parents[2] / '.hint-trace.lock'
TRACE_NAMESPACE = 'BBB4HintTrace'
UNITS = 96
MAX_OUTPUT_BYTES = 256 * 1024 * 1024
TAG_SCHEMA = [
    *({'code': i, 'family': 'ngram', 'index': i} for i in range(4)),
    *({'code': 4+i, 'family': 'rank', 'index': i} for i in range(4)),
    *({'code': offset+i, 'family': family, 'horizon': horizon, 'index': i}
      for horizon, base in [('short', 8), ('full', 21)]
      for family, offset, count in [('qh_plain', base, 9),
                                    ('qh_lex', base+9, 3),
                                    ('qh_rw', base+12, 1)]
      for i in range(count)),
    *({'code': 34+i, 'family': 'rw', 'index': i} for i in range(4)),
]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest_bytes(data):
    return hashlib.sha256(data).hexdigest()


def digest_file(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def write_json(path, value):
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
    temporary.replace(path)


def source_files(root):
    """Hash the full source closure, not just the obvious top-level files."""
    dependencies = {}
    text = (root / '.Makefile.coq.d').read_text().replace('\\\n', ' ')
    for line in text.splitlines():
        heads, sep, tail = line.partition(':')
        if sep:
            for head in heads.split():
                if head.endswith('.vo'):
                    dependencies[head] = [p for p in tail.split() if p.endswith('.vo')]
    todo = ['theories/CensusTr/RunTr_WalkCompute.vo']
    targets = set()
    while todo:
        target = todo.pop()
        if target in targets:
            continue
        require(target in dependencies, f'Missing dependency graph entry: {target}')
        targets.add(target)
        todo.extend(dependencies[target])
    paths = [root / Path(target).with_suffix('.v') for target in sorted(targets)]
    paths += [HERE / name for name in ('TraceRungsTr.v', 'TraceWalkTr.v',
                                      'TraceAudit.v', 'trace_driver.py')]
    paths += [root / 'tools/censustr/decode_enc.py']
    return {str(path.resolve()): digest_file(path) for path in paths}


def compiled_files(root, sources):
    """Enforce a freshly compiled, frozen physical native closure before plan.

    A timestamp check is only a stale-file guard; it is not a proof that a
    binary corresponds to source. Use the same freshly validated isolated
    build for this snapshot, never copied stale MAIN objects.
    """
    files = {}
    for filename in sources:
        source = Path(filename)
        if source.suffix != '.v':
            continue
        vo = source.with_suffix('.vo')
        require(vo.is_file() and not vo.is_symlink(), f'Missing physical compiled prerequisite: {vo}')
        require(vo.stat().st_mtime_ns >= source.stat().st_mtime_ns,
                f'Source newer than compiled prerequisite: {source}')
        if source.is_relative_to(root / 'theories'):
            logical = 'BBB4_' + '_'.join(source.relative_to(root / 'theories').with_suffix('').parts)
        else:
            logical = TRACE_NAMESPACE + '_' + source.stem
        native = source.parent / '.coq-native' / ('N' + logical)
        require(native.with_suffix('.cmxs').is_file(), f'Missing eager native prerequisite: {native}.cmxs')
        for path in [vo, *(native.with_suffix(suffix) for suffix in ('.cmxs', '.cmi', '.cmx', '.o'))]:
            require(path.is_file() and not path.is_symlink(), f'Missing physical native prerequisite: {path}')
            require(path.stat().st_mtime_ns >= source.stat().st_mtime_ns,
                    f'Source newer than compiled/native prerequisite: {path}')
            files[str(path)] = digest_file(path)
    return files


def toolchain_identity(env=None):
    """Offline identity only: do not execute a compiler in plan/check."""
    result = {}
    for tool in ('coqc', 'ocamlc', 'ocamlopt'):
        binary = shutil.which(tool, path=(env or os.environ).get('PATH'))
        require(binary is not None, f'Missing tool: {tool}')
        path = Path(binary).resolve()
        result[tool] = {'path': str(path), 'sha256': digest_file(path)}
    return result


def manifest_digest(manifest):
    return digest_bytes(canonical({key: manifest[key] for key in (
        'source_sha256', 'compiled_sha256', 'toolchain', 'tag_schema',
        'policy', 'parameters_coq_source')}))


def verify_sources(manifest):
    for filename, expected in manifest['source_sha256'].items():
        require(digest_file(filename) == expected, f'Stale trace source: {filename}')
    for filename, expected in manifest['compiled_sha256'].items():
        require(digest_file(filename) == expected, f'Changed compiled prerequisite: {filename}')
    require(manifest_digest(manifest) == manifest['source_digest'], 'Source/artifact manifest digest mismatch')
    require(manifest['tag_schema'] == TAG_SCHEMA, 'Wrong tag schema/version')


def load_manifest(path):
    manifest = json.loads(path.read_text())
    require(manifest['format'] == 'tr-hints-manifest-v2', 'Wrong manifest format')
    require(manifest['trace_root'] == str(HERE), 'Different trace tool directory')
    require(manifest['policy']['decider'] == 'decider_tr_fallback' and
            manifest['policy']['coq_namespace'] == TRACE_NAMESPACE,
            'Trace must target the unchanged fallback')
    require(manifest['units'] == UNITS and 0 <= manifest['unit'] < UNITS,
            'Wrong modulo-96 unit assignment')
    verify_sources(manifest)
    return manifest


# Parse a typed constructor block, never all decimal strings in arbitrary text.
# Native Coq printing must match this strict format; unexpected printer output
# is a pilot failure to inspect, not a reason to weaken the parser silently.
TOKEN = re.compile(r'\s*(?:(?P<num>[0-9]+)|(?P<id>[A-Za-z_][A-Za-z_0-9\'.]*)|(?P<sym>[()%]))')


class PacketParser:
    def __init__(self, text, typename):
        pattern = (r'\s*=\s*(.*?)\s*:\s*'
                   r'(?:[A-Za-z_][A-Za-z_0-9]*\.)*' + re.escape(typename) + r'\s*')
        block = re.fullmatch(pattern, text, flags=re.S)
        require(block is not None, f'Missing, partial, duplicate, or mistyped {typename} block')
        body = block.group(1)
        self.tokens = []
        pos = 0
        while pos < len(body):
            token = TOKEN.match(body, pos)
            if token is None:
                require(body[pos:].strip() == '', f'Unexpected output near {body[pos:pos+80]!r}')
                break
            self.tokens.append(token.group(token.lastgroup))
            pos = token.end()
        self.at = 0

    def peek(self):
        return self.tokens[self.at] if self.at < len(self.tokens) else None

    def take(self):
        token = self.peek()
        require(token is not None, 'Truncated constructor output')
        self.at += 1
        return token

    def expect(self, wanted):
        actual = self.take()
        require(actual.rsplit('.', 1)[-1] == wanted,
                f'Expected {wanted}, got {actual}')

    def opens(self):
        count = 0
        while self.peek() == '(':
            self.take()
            count += 1
        return count

    def closes(self, count):
        for _ in range(count):
            self.expect(')')

    def number(self, scope='nat'):
        parens = self.opens()
        token = self.take()
        if scope == 'positive' and token.rsplit('.', 1)[-1] in ('xO', 'xI', 'xH'):
            # Coq's actual native printer emits BinNums constructors when
            # decimal positive notation has not been imported by the driver.
            # This is a single typed unary constructor spine, not numeric
            # token extraction. Bound its depth before accumulating an int.
            bits = []
            while token.rsplit('.', 1)[-1] in ('xO', 'xI'):
                bits.append(int(token.rsplit('.', 1)[-1] == 'xI'))
                require(len(bits) <= 64, 'Oversized positive constructor spine')
                child_parens = self.opens()
                parens += child_parens
                token = self.take()
                require(token.rsplit('.', 1)[-1] == 'xH' or child_parens > 0,
                        'A nonterminal positive child must be parenthesized')
            require(token.rsplit('.', 1)[-1] == 'xH',
                    f'Expected terminal positive xH, got {token}')
            value = 1
            for bit in reversed(bits):
                value = 2 * value + bit
        else:
            require(token.isdecimal(), f'Expected decimal {scope}, got {token}')
            value = int(token)
        scoped = False
        if self.peek() == '%':
            self.take()
            self.expect(scope)
            scoped = True
        self.closes(parens)
        if self.peek() == '%':
            require(not scoped, 'Duplicate numeric scope suffix')
            self.take()
            self.expect(scope)
        return value

    def boolean(self):
        parens = self.opens()
        token = self.take()
        require(token in ('true', 'false'), f'Expected Boolean, got {token}')
        self.closes(parens)
        return token == 'true'

    def chain(self, cons, nil, scopes):
        # Iterative even for a million rows; do not recurse in Python per row.
        values = []
        parens = 0
        while True:
            parens += self.opens()
            constructor = self.take().rsplit('.', 1)[-1]
            if constructor == nil:
                break
            require(constructor == cons, f'Expected {cons}/{nil}, got {constructor}')
            values.append(tuple(self.number(scope) for scope in scopes))
        self.closes(parens)
        return values

    def done(self):
        require(self.peek() is None, f'Extra material after packet: {self.peek()}')


def parse_inventory(text):
    p = PacketParser(text, 'TraceInventoryPacketV1')
    parens = p.opens()
    p.expect('TrInventoryV1')
    fields = [p.number() for _ in range(6)]
    indices = [v[0] for v in p.chain('TrIndicesConsV1', 'TrIndicesNilV1', ['nat'])]
    p.closes(parens)
    p.done()
    return dict(zip(('units', 'unit', 'frontier_count', 'levels', 'rounds',
                     'pop_exponent'), fields), indices=indices)


def parse_shard(text):
    p = PacketParser(text, 'TraceShardPacketV1')
    parens = p.opens()
    p.expect('TrShardV1')
    fields = [p.number() for _ in range(4)]
    present, complete, count = p.boolean(), p.boolean(), p.number()
    rows = p.chain('TrRowsConsV1', 'TrRowsNilV1', ['positive', 'nat'])
    p.closes(parens)
    p.done()
    require(len(rows) == count, 'Truncated rows or wrong row count')
    return dict(zip(('units', 'unit', 'index', 'frontier_count'), fields),
                present=present, complete=complete, row_count=count, rows=rows)


def decoder(root):
    path = root / 'tools/censustr/decode_enc.py'
    spec = importlib.util.spec_from_file_location('tr_hint_decode_enc', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.decode


def validated_rows(rows, root):
    decode = decoder(root)
    unique = {}
    for key, tag in rows:
        require(1 <= key <= 17**8, f'Invalid eight-slot machine key: {key}')
        require(0 <= tag < 38, f'Invalid/sentinel winner tag: {tag}')
        decode(key)  # Reuse the decoder, never its permissive numeric extractor.
        require(key not in unique or unique[key] == tag,
                f'Conflicting winners for key {key}: {unique.get(key)} vs {tag}')
        unique[key] = tag
    return [[key, unique[key]] for key in sorted(unique)]


def driver_text(expression):
    return f'''(** GENERATED UNTRUSTED fallback trace; one typed output only. *)
From BBB4HintTrace Require Import TraceWalkTr.
Set Printing Width 120.
Set Printing Depth 10000000.
Eval native_compute in ({expression}).
'''


def emit_driver(outdir, manifest, index=None):
    unit = manifest['unit']
    if index is None:
        filename = f'InventoryUnit{unit:02d}.v'
        expression = f'trace_inventory_packet {UNITS} {unit}'
        name = 'inventory'
    else:
        require(index >= 0 and index % UNITS == unit, 'Frontier belongs to a different unit')
        if manifest['inventory'] is not None:
            require(index in manifest['inventory']['indices'], 'Frontier not in the exact inventory')
        filename = f'ShardUnit{unit:02d}Frontier{index:06d}.v'
        expression = f'trace_shard_packet {UNITS} {unit} {index}'
        name = f'shard-{index}'
    text = driver_text(expression)
    path = outdir / filename
    if path.exists():
        require(path.read_text() == text, f'Refuse to overwrite changed driver: {path}')
    else:
        path.write_text(text)
    manifest['drivers'][name] = {'file': filename, 'sha256': digest_file(path)}


def plan(args):
    require(0 <= args.unit < UNITS, 'Unit must be in 0..95')
    root = args.root.resolve()
    require(HERE == root / 'tools/censustr/hint_trace',
            'Run the trace driver from the frozen checkout passed as --root')
    sources = source_files(root)
    artifacts = compiled_files(root, sources)
    policy = {'units': UNITS, 'frontier_levels': 3, 'rounds': 4096,
              'pop_exponent': 13, 'assignment': 'frontier_index mod 96 = unit',
              'row_order': 'reverse visit order; sorted/deduplicated only offline',
              'decisions': 'one trace_decider call per queue pop',
              'decider': 'decider_tr_fallback', 'coq_namespace': TRACE_NAMESPACE,
              'output_format': 'typed constructor chains, version 1'}
    config = (root / 'theories/CensusTr/RunTr_Compute.v').read_text()
    manifest = {'format': 'tr-hints-manifest-v2', 'unit': args.unit,
                'units': UNITS, 'root': str(root), 'trace_root': str(HERE),
                'proof_status': 'Compiled prerequisites required; inspect projection assumptions before tracing',
                'source_sha256': sources, 'compiled_sha256': artifacts,
                'tag_schema': TAG_SCHEMA, 'policy': policy,
                'parameters_coq_source': config, 'inventory': None,
                'drivers': {}, 'shards': {}, 'toolchain': toolchain_identity(),
                'runtime_versions': None}
    manifest['source_digest'] = manifest_digest(manifest)
    args.outdir.mkdir(parents=True, exist_ok=False)
    emit_driver(args.outdir, manifest)
    if args.frontier_index is not None:
        emit_driver(args.outdir, manifest, args.frontier_index)
    write_json(args.outdir / 'manifest.json', manifest)
    print(args.outdir / 'manifest.json')


def emit(args):
    manifest = load_manifest(args.manifest)
    require(manifest['inventory'] is not None, 'Accept the exact frontier inventory first')
    verify_inventory_record(args.manifest.parent, manifest)
    emit_driver(args.manifest.parent, manifest, args.frontier_index)
    write_json(args.manifest, manifest)


def verify_run_record(outdir, manifest, name):
    entry = manifest['drivers'][name]
    require(digest_file(outdir / entry['file']) == entry['sha256'], f'Changed driver {name}')
    record = json.loads((outdir / f'{name}.run.json').read_text())
    require(record['accepted'] is True and record['exit_code'] == 0
            and record['source_digest'] == manifest['source_digest']
            and record['toolchain'] == manifest['toolchain']
            and record['runtime_versions'] == manifest['runtime_versions']
            and record['driver_sha256'] == entry['sha256'], f'Incomplete or stale run record {name}')
    require(all(record[key] is None for key in ('OCAMLRUNPARAM', 'COQRUNPARAM', 'CAMLRUNPARAM')),
            f'Unexpected runtime environment for {name}')
    for stream in ('stdout', 'stderr'):
        path = outdir / f'{name}.{stream}'
        require(path.stat().st_size <= MAX_OUTPUT_BYTES, f'Oversized {stream}: {name}')
        require(digest_file(path) == record[f'{stream}_sha256'], f'Changed {stream}: {name}')
    return (outdir / f'{name}.stdout').read_text()


def validate_inventory_packet(packet, manifest):
    require(packet['units'] == UNITS and packet['unit'] == manifest['unit'], 'Inventory identity mismatch')
    require(packet['levels'] == 3 and packet['rounds'] == 4096 and packet['pop_exponent'] == 13,
            'Walk parameters changed')
    require(packet['frontier_count'] > 0, 'Empty frontier inventory')
    expected = list(range(manifest['unit'], packet['frontier_count'], UNITS))
    require(packet['indices'] == expected, 'Incomplete, duplicated, or reordered frontier inventory')


def verify_inventory_record(outdir, manifest):
    packet = parse_inventory(verify_run_record(outdir, manifest, 'inventory'))
    validate_inventory_packet(packet, manifest)
    require(packet == manifest['inventory'], 'Manifest inventory differs from native output')


def validate_shard_packet(packet, manifest, index):
    require(packet['units'] == UNITS and packet['unit'] == manifest['unit'], 'Shard unit mismatch')
    require(packet['index'] == index and index in manifest['inventory']['indices'], 'Wrong frontier index')
    require(packet['frontier_count'] == manifest['inventory']['frontier_count'], 'Frontier changed')
    require(packet['present'] and packet['complete'], 'Missing or unsuccessful subtree; discard rows')


def verify_shard_record(outdir, manifest, index):
    name = f'shard-{index}'
    entry = manifest['shards'][str(index)]
    path = outdir / entry['file']
    require(digest_file(path) == entry['sha256'], f'Changed shard {index}')
    artifact = json.loads(path.read_text())
    packet = parse_shard(verify_run_record(outdir, manifest, name))
    validate_shard_packet(packet, manifest, index)
    rows = validated_rows(packet['rows'], Path(manifest['root']))
    expected = {'format': 'tr-hint-shard-v1', 'source_digest': manifest['source_digest'],
                'unit': manifest['unit'], 'index': index, 'complete': True,
                'raw_row_count': packet['row_count'], 'rows': rows}
    require(artifact == expected, f'Artifact differs from complete native shard {index}')
    return rows



@contextmanager
def compiler_lock(path, inherited_fd=None):
    """Retain one open file description; never unlock an inherited lock.

    The caller supplying inherited_fd promises it already holds LOCK_EX.
    Identity validation catches a wrong file, but does not authenticate the
    supervisor's scheduling policy. Duplicating a descriptor retains its
    lock through compiler descendants even if a supervising process exits.
    """
    if inherited_fd is None:
        with path.open('a') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            yield lock.fileno()
        return
    require(inherited_fd >= 0, 'Invalid inherited lock descriptor')
    held = os.dup(inherited_fd)
    try:
        actual, expected = os.fstat(held), path.stat()
        require(stat.S_ISREG(actual.st_mode) and
                (actual.st_dev, actual.st_ino) == (expected.st_dev, expected.st_ino),
                'Inherited descriptor does not identify the requested lock file')
        yield held
    finally:
        os.close(held)  # No LOCK_UN: the parent and children share this lock.


def run(args):
    # Exactly one invocation, no automatic shard enumeration or retries.
    require(args.inherited_lock_fd is None or args.lock is not None,
            '--inherited-lock-fd requires an explicit --lock path')
    lock_path = args.lock if args.lock is not None else DEFAULT_LOCK
    # All run modes take the compiler lock before the per-manifest lock.
    # A standalone run must not invert an outer supervisor's lock order.
    with (
        compiler_lock(lock_path, args.inherited_lock_fd) as lock_fd,
        (args.manifest.parent / '.manifest.lock').open('a') as manifest_lock,
    ):
        fcntl.flock(manifest_lock, fcntl.LOCK_EX)
        manifest = load_manifest(args.manifest)
        outdir = args.manifest.parent.resolve()
        root = Path(manifest['root'])
        name = 'inventory' if args.kind == 'inventory' else f'shard-{args.frontier_index}'
        require(name in manifest['drivers'], f'Emit this one driver first: {name}')
        require(not (outdir / f'{name}.run.json').exists(), 'Existing run: use a new output directory')
        if args.kind == 'shard':
            require(manifest['inventory'] is not None, 'Accept the exact inventory first')
            verify_inventory_record(outdir, manifest)
            require(args.frontier_index in manifest['inventory']['indices'], 'Wrong shard assignment')
        entry = manifest['drivers'][name]
        fixture = outdir / entry['file']
        require(digest_file(fixture) == entry['sha256'], 'Generated driver changed')
        env = os.environ.copy()
        env.pop('OCAMLRUNPARAM', None)
        env.pop('COQRUNPARAM', None)
        env.pop('CAMLRUNPARAM', None)
        toolchain = toolchain_identity(env)
        require(toolchain == manifest['toolchain'], 'Toolchain changed between shards')
        versions = {tool: subprocess.check_output(
                        [toolchain[tool]['path'], option], env=env, text=True,
                        pass_fds=(lock_fd,)).strip()
                    for tool, option in [('coqc', '--version'), ('ocamlc', '-version'),
                                         ('ocamlopt', '-version')]}
        if manifest['runtime_versions'] is not None:
            require(versions == manifest['runtime_versions'], 'Compiler versions changed between shards')
        _, hard = resource.getrlimit(resource.RLIMIT_STACK)
        resource.setrlimit(resource.RLIMIT_STACK, (hard, hard))
        command = ['coqc', '-q', '-w', '-abstract-large-number', '-w',
                   '-deprecated-native-compiler-option', '-native-compiler', 'yes',
                   '-Q', str(root / 'theories'), 'BBB4',
                   '-Q', str(HERE), TRACE_NAMESPACE, str(fixture)]
        stdout, stderr = outdir / f'{name}.stdout', outdir / f'{name}.stderr'
        started = datetime.now(timezone.utc).isoformat()
        before = resource.getrusage(resource.RUSAGE_CHILDREN)
        wall = time.monotonic()
        def cap_output_files():
            _, maximum = resource.getrlimit(resource.RLIMIT_FSIZE)
            cap = MAX_OUTPUT_BYTES if maximum == resource.RLIM_INFINITY else min(MAX_OUTPUT_BYTES, maximum)
            resource.setrlimit(resource.RLIMIT_FSIZE, (cap, maximum))
        with stdout.open('wb') as output, stderr.open('wb') as error:
            result = subprocess.run(command, env=env, cwd=root, stdout=output,
                                    stderr=error, pass_fds=(lock_fd,), preexec_fn=cap_output_files)
        wall = time.monotonic() - wall
        after = resource.getrusage(resource.RUSAGE_CHILDREN)
        record = {'command': command, 'exit_code': result.returncode,
                  'started_utc': started, 'wall_seconds': wall,
                  'cpu_seconds': after.ru_utime + after.ru_stime - before.ru_utime - before.ru_stime,
                  'max_child_rss_bytes': int(after.ru_maxrss * 1024),
                  'rss_scope': 'Linux driver child maximum, including compiler version probes',
                  'source_digest': manifest['source_digest'], 'toolchain': toolchain,
                  'runtime_versions': versions,
                  'OCAMLRUNPARAM': None, 'COQRUNPARAM': None, 'CAMLRUNPARAM': None,
                  'stdout_sha256': digest_file(stdout), 'stderr_sha256': digest_file(stderr),
                  'driver_sha256': entry['sha256'], 'accepted': False,
                  'lock_path': str(lock_path.resolve()),
                  'lock_mode': 'inherited' if args.inherited_lock_fd is not None else 'standalone'}
        write_json(outdir / f'{name}.run.json', record)
        require(result.returncode == 0, f'Coq failed: inspect {stderr}')
        verify_sources(manifest)
        require(stdout.stat().st_size <= MAX_OUTPUT_BYTES, 'Output exceeds per-shard parser limit')
        text = stdout.read_text()
        packet = parse_inventory(text) if args.kind == 'inventory' else parse_shard(text)
        require(packet['units'] == UNITS and packet['unit'] == manifest['unit'], 'Packet identity mismatch')
        if args.kind == 'inventory':
            validate_inventory_packet(packet, manifest)
            manifest['inventory'] = packet
        else:
            validate_shard_packet(packet, manifest, args.frontier_index)
            rows = validated_rows(packet['rows'], root)
            # Reject conflicts with every already accepted shard in this unit.
            previous = []
            for index in manifest['shards']:
                previous.extend(verify_shard_record(outdir, manifest, int(index)))
            validated_rows(previous + rows, root)
            artifact = {'format': 'tr-hint-shard-v1', 'source_digest': manifest['source_digest'],
                        'unit': manifest['unit'], 'index': args.frontier_index,
                        'complete': True, 'raw_row_count': packet['row_count'], 'rows': rows}
            path = outdir / f'{name}.rows.json'
            write_json(path, artifact)
            manifest['shards'][str(args.frontier_index)] = {'file': path.name, 'sha256': digest_file(path)}
        record['accepted'] = True
        write_json(outdir / f'{name}.run.json', record)
        manifest['runtime_versions'] = versions
        write_json(args.manifest, manifest)
        print(f'Accepted {name}; source {manifest["source_digest"]}')


def check(args):
    manifest = load_manifest(args.manifest)
    outdir = args.manifest.parent
    require(manifest['inventory'] is not None, 'Missing inventory')
    verify_inventory_record(outdir, manifest)
    expected = manifest['inventory']['indices']
    require(set(manifest['shards']) == {str(i) for i in expected},
            'Incomplete or extra per-unit frontier shards')
    rows = []
    for index in expected:
        rows.extend(verify_shard_record(outdir, manifest, index))
    rows = validated_rows(rows, Path(manifest['root']))
    output = {'format': 'tr-hint-unit-v1', 'source_digest': manifest['source_digest'],
              'unit': manifest['unit'], 'complete': True, 'frontier_indices': expected,
              'row_count': len(rows), 'rows': rows}
    write_json(outdir / 'complete-unit.rows.json', output)
    print(f'Complete unit {manifest["unit"]}: {len(expected)} shards, {len(rows)} distinct winners')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    p = commands.add_parser('plan')
    p.add_argument('--root', type=Path, required=True)
    p.add_argument('--outdir', type=Path, required=True)
    p.add_argument('--unit', type=int, required=True)
    p.add_argument('--frontier-index', type=int)
    p.set_defaults(action=plan)
    p = commands.add_parser('emit')
    p.add_argument('--manifest', type=Path, required=True)
    p.add_argument('--frontier-index', type=int, required=True)
    p.set_defaults(action=emit)
    p = commands.add_parser('run')
    p.add_argument('--manifest', type=Path, required=True)
    p.add_argument('--kind', choices=('inventory', 'shard'), required=True)
    p.add_argument('--frontier-index', type=int)
    p.add_argument('--lock', type=Path, help='Shared compiler lock; defaults to checkout/.hint-trace.lock')
    p.add_argument('--inherited-lock-fd', type=int, help='Already exclusively locked inherited descriptor for --lock')
    p.set_defaults(action=run)
    p = commands.add_parser('check')
    p.add_argument('--manifest', type=Path, required=True)
    p.set_defaults(action=check)
    args = parser.parse_args()
    if args.command in ('plan', 'run'):
        args.action(args)
    else:
        # Serialize edits/checks to one manifest; different units remain separate.
        with (args.manifest.parent / '.manifest.lock').open('a') as manifest_lock:
            fcntl.flock(manifest_lock, fcntl.LOCK_EX)
            args.action(args)


if __name__ == '__main__':
    main()
