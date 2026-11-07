#!/usr/bin/env python3
"""Resume independently audited finite-observation proof parts.

Prepare the repository's observation native dependencies first. This runner
never admits dependencies or trusts a JSON 'passed' flag: resume requires the
same full input/spec/partition/tool/dependency identity and exact artifact
hashes. Each part gets its own recursive coqchk, without -admit or -norec.
Scheduling budgets stop new work, retaining pending families; selected proofs
do not establish universal census coverage. Requires POSIX process groups/flock.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import csv
import fcntl
import hashlib
import io
import json
import math
import os
from pathlib import Path
import re
import resource
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time

ROOT = Path(__file__).resolve().parents[2]
NAMESPACE = 'BBBWait42Observation'
ALLOWED_AXIOMS = {'FunctionalExtensionality.functional_extensionality_dep'}
BEGIN = 'OBSERVATION_ASSUMPTIONS_BEGIN'
END = 'OBSERVATION_ASSUMPTIONS_END'
MACHINE = re.compile(r'(?:---|[01][LR][ABCD]){2}(?:_(?:---|[01][LR][ABCD]){2}){3}')
HEADER = '''From Coq Require Import List Bool NArith.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import Deferred_Defs TNF_QH.
From BBBWait42 Require Import Spec FiniteObservation.
Import ListNotations.
'''


def digest(data):
    return hashlib.sha256(data).hexdigest()


def fingerprint(path):
    path = Path(path)
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return {'sha256': h.hexdigest(), 'bytes': path.stat().st_size}


def canonical(data):
    return json.dumps(data, sort_keys=True, separators=(',', ':')).encode()


def atomic_bytes(path, data):
    path = Path(path)
    fd, temp = tempfile.mkstemp(prefix='.' + path.name + '-', dir=path.parent)
    try:
        with os.fdopen(fd, 'wb') as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temp, path)
        directory = os.open(path.parent, os.O_RDONLY | getattr(os, 'O_DIRECTORY', 0))
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        if os.path.exists(temp):
            os.unlink(temp)


def atomic_json(path, data):
    atomic_bytes(path, json.dumps(data, sort_keys=True, indent=2).encode() + b'\n')


def json_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('duplicate JSON key: ' + key)
        result[key] = value
    return result


def uint(value, name, maximum=(1 << 63) - 1):
    if type(value) is not int or not 0 <= value <= maximum:
        raise ValueError('invalid nonnegative integer: ' + name)
    return value


def decimal(text, name, maximum=(1 << 63) - 1):
    if not isinstance(text, str) or not re.fullmatch(r'0|[1-9][0-9]*', text):
        raise ValueError('invalid decimal field: ' + name)
    return uint(int(text), name, maximum)


def read_bounded(path, maximum=128 * 1024 * 1024):
    with Path(path).open('rb') as stream:
        data = stream.read(maximum + 1)
    if len(data) > maximum:
        raise ValueError('input exceeds byte cap: ' + str(path))
    return data


def load_input(spec_path):
    """Hash exactly the immutable bytes parsed; reject malformed/duplicate rows."""
    spec_path = Path(spec_path).resolve()
    spec_bytes = read_bounded(spec_path, 4 * 1024 * 1024)
    spec = json.loads(spec_bytes, object_pairs_hook=json_object)
    if spec.get('schema_version') != 1:
        raise ValueError('unsupported observation spec schema')
    for name in ('rows', 'cutoff', 'upper_width', 'default_batch_size'):
        uint(spec.get(name), name, 1000000 if name == 'rows' else (1 << 63) - 1)
    if not 1 <= spec['default_batch_size'] <= 256:
        raise ValueError('default_batch_size must be 1..256')
    if not isinstance(spec.get('input'), str) or not spec['input']:
        raise ValueError('spec input must name a TSV file')
    input_path = (spec_path.parent / spec['input']).resolve()
    data = read_bounded(input_path)
    if digest(data) != spec.get('input_sha256'):
        raise ValueError('observation input SHA256 mismatch')
    reader = csv.DictReader(io.StringIO(data.decode('utf-8'), newline=''), delimiter='\t', strict=True)
    required = ['source_index', 'machine', 'ptr', 'width', 'tail_mask']
    if reader.fieldnames != required:
        raise ValueError('observation TSV header must be ' + ','.join(required))
    rows, identities, indices = [], set(), set()
    for row in reader:
        if None in row or any(v is None or '\n' in v or '\r' in v for v in row.values()):
            raise ValueError('malformed or multiline observation TSV row')
        if MACHINE.fullmatch(row['machine']) is None:
            raise ValueError('invalid machine table')
        for key in ('source_index', 'ptr', 'width', 'tail_mask'):
            row[key] = decimal(row[key], key)
        if row['ptr'] not in (1, 2, 3, 4) or row['tail_mask'] > 15:
            raise ValueError('invalid pointer or tail mask')
        if row['width'] > spec['upper_width']:
            raise ValueError('case width exceeds spec upper_width')
        identity = row['machine'], row['ptr']
        if identity in identities or row['source_index'] in indices:
            raise ValueError('duplicate machine/pointer or source index')
        identities.add(identity)
        indices.add(row['source_index'])
        rows.append(row)
        if len(rows) > spec['rows']:
            raise ValueError('input row count exceeds spec')
    if len(rows) != spec['rows']:
        raise ValueError('input row count differs from spec')
    bound = {'spec_path': str(spec_path), 'spec': {'sha256': digest(spec_bytes), 'bytes': len(spec_bytes)},
             'input_path': str(input_path), 'input': {'sha256': digest(data), 'bytes': len(data)}}
    return spec, rows, bound


def render_part(rows, cutoff, upper_width):
    text = HEADER + '''Record entry := Entry { source_index:N; pointer:nat; proof_case:observation_case }.
Definition mask (a b c d:bool) : St->bool := fun q =>
 match q with StA=>a|StB=>b|StC=>c|StD=>d end.
'''
    text += f'Definition cutoff : N := {cutoff}%N.\nDefinition upper_width : N := {upper_width}%N.\n'
    literals = []
    for row in rows:
        slots = row['machine'].replace('_', '')
        table = ';'.join('tN' if slots[i:i+3] == '---' else 't' + slots[i:i+3] for i in range(0, 24, 3))
        bits = ' '.join('true' if row['tail_mask'] & (1 << i) else 'false' for i in range(4))
        literals.append(f'Entry {row["source_index"]}%N {row["ptr"]} '
                        f'(mkObservationCase (row_to_tm [{table}]) (mask {bits}) {row["width"]}%N)')
    text += 'Definition entries : list entry := [\n' + ';\n'.join(literals) + '\n].\n'
    text += '''Definition cases := map proof_case entries.
Example all_checked : observation_batch_check cases cutoff upper_width = true.
Proof. native_compute. reflexivity. Qed.
Local Opaque observation_batch_check finite_observation_check.
Theorem all_completions : forall e, In e entries -> forall tm,
 TM_le (observation_machine (proof_case e)) tm ->
 WindowBound tm (N.to_nat cutoff) (N.to_nat upper_width).
Proof.
 intros e Hin tm Hle.
 apply (observation_batch_completion cases cutoff upper_width all_checked (proof_case e)).
 - unfold cases. now apply in_map.
 - exact Hle.
Qed.
Goal True. idtac "OBSERVATION_ASSUMPTIONS_BEGIN". exact I. Qed.
Print Assumptions all_completions.
Goal True. idtac "OBSERVATION_ASSUMPTIONS_END". exact I. Qed.
'''
    return text.encode()


def parse_assumptions(text):
    if text.count(BEGIN) != 1 or text.count(END) != 1:
        raise ValueError('missing or duplicate Print Assumptions markers')
    start, end = text.index(BEGIN) + len(BEGIN), text.index(END)
    if start >= end:
        raise ValueError('invalid assumptions marker order')
    body = text[start:end].strip()
    if body in ('Closed under the global context', 'Closed under the global context.'):
        return []
    lines = body.splitlines()
    if not lines or lines[0].strip() != 'Axioms:':
        raise ValueError('unrecognized Print Assumptions output')
    names = []
    for line in lines[1:]:
        if not line.strip() or line[0].isspace():
            continue
        match = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_'.]*)(?:\s*:.*)?", line)
        if not match:
            raise ValueError('unrecognized axiom declaration: ' + line)
        names.append(match[1])
    if not names or len(names) != len(set(names)) or not set(names) <= ALLOWED_AXIOMS:
        raise ValueError('unexpected axioms: ' + ', '.join(names))
    return sorted(names)


class ProcessManager:
    """All tool invocations live in tracked sessions, including preparation."""
    def __init__(self, memory_gib):
        self.memory_gib = memory_gib
        self.cancelled = threading.Event()
        self.lock = threading.Lock()
        self.processes = {}

    @staticmethod
    def kill_group(pid):
        for sig, pause in ((signal.SIGTERM, .15), (signal.SIGKILL, 0)):
            try:
                os.killpg(pid, sig)
            except ProcessLookupError:
                return
            if pause:
                time.sleep(pause)

    def terminate_all(self):
        self.cancelled.set()
        with self.lock:
            pids = list(self.processes)
        for pid in pids:
            self.kill_group(pid)

    def run(self, command, cwd, timeout, log=None):
        if self.cancelled.is_set():
            raise InterruptedError('runner interrupted')
        launch = [sys.executable, str(Path(__file__).resolve()), '_exec', str(self.memory_gib), *command]
        start = time.monotonic()
        target = log.open('wb') if log else tempfile.TemporaryFile()
        proc = None
        try:
            # The separate Python exec launcher applies limits without unsafe
            # preexec_fn calls from worker threads. Its entire process group is tracked.
            with self.lock:
                if self.cancelled.is_set():
                    raise InterruptedError('runner interrupted')
                blocked = None
                if threading.current_thread() is threading.main_thread():
                    blocked = signal.pthread_sigmask(signal.SIG_BLOCK, {signal.SIGINT, signal.SIGTERM})
                try:
                    proc = subprocess.Popen(launch, cwd=cwd, stdout=target, stderr=subprocess.STDOUT,
                                            start_new_session=True, close_fds=True)
                    self.processes[proc.pid] = proc
                finally:
                    if blocked is not None:
                        signal.pthread_sigmask(signal.SIG_SETMASK, blocked)
            status = 'ok'
            while proc.poll() is None:
                if self.cancelled.is_set():
                    status = 'interrupted'
                    break
                if time.monotonic() - start >= timeout:
                    status = 'timeout'
                    break
                time.sleep(.05)
            if status != 'ok':
                self.kill_group(proc.pid)
            proc.wait()
            # Successful parents may leave native/compiler descendants: do not
            # leak them into a later part, receipt, or interrupted run.
            self.kill_group(proc.pid)
            target.flush()
            output = ''
            if not log:
                target.seek(0)
                output = target.read().decode('utf-8', errors='replace')
            return {'command': command, 'returncode': proc.returncode, 'status': status,
                    'seconds': round(time.monotonic() - start, 3), 'output': output}
        finally:
            if proc is not None:
                if proc.poll() is None:
                    self.kill_group(proc.pid)
                    proc.wait()
                with self.lock:
                    self.processes.pop(proc.pid, None)
            target.close()


def resolve_tool(name):
    found = shutil.which(name)
    if not found:
        raise ValueError('tool not found: ' + name + '; prepare observation dependencies first')
    return str(Path(found).resolve())


def tool_identity(args, manager, root):
    tools, result = {}, {}
    for name in ('coqc', 'coqchk', 'coqdep'):
        tools[name] = resolve_tool(getattr(args, name))
        version = manager.run([tools[name], '--version'], root, 30)
        if version['status'] != 'ok' or version['returncode'] != 0:
            raise ValueError('cannot read tool version: ' + name)
        result[name] = {'path': tools[name], **fingerprint(tools[name]), 'version': version['output'].strip()}
        if name == 'coqdep' and 'unknown option' in version['output']:
            result[name]['version'] = None
            result[name]['version_note'] = 'coqdep has no version flag; exact binary hash and coqc suite version bind it'
            result[name]['suite_version'] = result['coqc']['version']
    for name, version_flag in (('coqnative', '--version'), ('ocamlc', '-version'), ('ocamlopt', '-version'), ('ocamlfind', 'printconf'), ('cc', '--version'), ('gcc', '--version'), ('ld', '--version'), ('as', '--version')):
        found = shutil.which(name)
        if found:
            path = str(Path(found).resolve())
            version = manager.run([path, version_flag], root, 30)
            result[name] = {'path': path, **fingerprint(path), 'version': version['output'].strip(),
                            'version_returncode': version['returncode']}
        else:
            result[name] = None
    result['python'] = {'path': str(Path(sys.executable).resolve()), **fingerprint(sys.executable), 'version': sys.version}
    return tools, result


def dependency_closure(root, output, coqlib, coqdep, flags, manager):
    """Resolve transitive source/.vo imports with coqdep, including stdlib."""
    generic = root / 'wait42/theories/FiniteObservation.v'
    probe = output / 'DependencyProbe.v'
    atomic_bytes(probe, HEADER.encode())
    seeds = [generic, probe]
    prelude = coqlib / 'theories/Init/Prelude.v'
    if prelude.exists():
        seeds.append(prelude)
    pending, seen, files = seeds, set(), {}
    plugin_roots = [coqlib / 'plugins', coqlib.parent / 'coq-core/plugins']
    plugin_artifacts = [p for base in plugin_roots if base.is_dir()
                        for p in base.rglob('*') if p.suffix in ('.cma', '.cmxs')]
    plugin_dirs = sorted({p.parent for p in plugin_artifacts})
    plugin_flags = [value for directory in plugin_dirs for value in ('-I', str(directory))]
    for meta in (coqlib / 'META', coqlib.parent / 'coq-core/META'):
        if meta.is_file():
            files[str(meta.resolve())] = fingerprint(meta)
    while pending:
        wave = [p.resolve() for p in pending if p.resolve() not in seen]
        if not wave:
            break
        seen.update(wave)
        for source in wave:
            if not source.is_file():
                raise ValueError('missing dependency source: ' + str(source))
            files[str(source)] = fingerprint(source)
            # Pin installed ML plugins referenced by this exact source closure.
            for declaration in re.findall(r'Declare\s+ML\s+Module\s+"([^"]+)"', source.read_text()):
                last = declaration.split('.')[-1]
                names = {declaration, last, last + '_plugin'}
                for artifact in plugin_artifacts:
                    if artifact.stem in names:
                        files[str(artifact.resolve())] = fingerprint(artifact)
            if source != probe.resolve():
                vo = source.with_suffix('.vo')
                if not vo.is_file():
                    raise ValueError('missing compiled dependency: ' + str(vo) + '; run observation dependency preparation first')
                files[str(vo)] = fingerprint(vo)
        command = [coqdep, '-boot', '-dyndep', 'no', *plugin_flags, '-R', str(coqlib / 'theories'), 'Coq', *flags, *map(str, wave)]
        result = manager.run(command, root, 120)
        text = result['output']
        if result['status'] != 'ok' or result['returncode'] != 0 or re.search(r'\b(?:Warning|Error):', text):
            raise ValueError('coqdep cannot resolve complete dependency closure; prepare dependencies first:\n' + text[-3000:])
        next_wave = []
        for line in text.replace('\\\n', '').splitlines():
            if ': ' not in line:
                continue
            left, right = line.split(': ', 1)
            if not any(p.endswith('.vo') for p in shlex.split(left)):
                continue
            for token in shlex.split(right):
                if token.endswith('.vo'):
                    vo = Path(token)
                    if not vo.is_absolute():
                        vo = root / vo
                    vo = vo.resolve()
                    if not vo.is_file():
                        raise ValueError('missing compiled dependency: ' + str(vo) + '; prepare dependencies first')
                    files[str(vo)] = fingerprint(vo)
                    next_wave.append(vo.with_suffix('.v'))
        pending = next_wave
    return dict(sorted(files.items()))


def verify_files(files):
    for name, expected in files.items():
        if not Path(name).is_file() or fingerprint(name) != expected:
            raise ValueError('fingerprinted file changed or missing: ' + name)


def part_paths(output, name):
    return {'source': output / (name + '.v'), 'vo': output / (name + '.vo'),
            'compile_log': output / (name + '.compile.log'), 'audit_log': output / (name + '.audit.log')}


def validate_receipt(path, identity, source_bytes, paths, expected):
    receipt = json.loads(path.read_bytes(), object_pairs_hook=json_object)
    if receipt.get('status') != 'checked':
        return False
    if receipt.get('identity') != identity:
        raise ValueError('receipt identity mismatch: ' + str(path))
    if receipt.get('artifacts', {}).get('source', {}).get('sha256') != digest(source_bytes):
        raise ValueError('receipt rendered source mismatch: ' + str(path))
    for key, artifact in paths.items():
        if not artifact.is_file() or fingerprint(artifact) != receipt.get('artifacts', {}).get(key):
            raise ValueError('receipt artifact hash mismatch: ' + str(artifact))
    for stage in ('compile', 'audit'):
        result = receipt.get(stage, {})
        if result.get('status') != 'ok' or result.get('returncode') != 0 or result.get('command') != expected[stage]:
            raise ValueError('receipt has no exact successful compile/audit command')
    if receipt.get('families') != expected['families'] or receipt.get('source_indices') != expected['source_indices']:
        raise ValueError('receipt family attribution mismatch')
    axioms = parse_assumptions(paths['compile_log'].read_text(errors='replace'))
    if axioms != receipt.get('axioms'):
        raise ValueError('receipt assumption evidence mismatch')
    return True


def archive_attempt(output, name):
    existing = list(output.glob(name + '.*'))
    if not existing:
        return
    destination = output / 'attempts' / (name + '-' + str(time.time_ns()))
    destination.mkdir(parents=True)
    for path in existing:
        if path.is_file() or path.is_symlink():
            path.rename(destination / path.name)


def run_part(part, context):
    name, source, rows = part
    output, manager = context['output'], context['manager']
    receipt_path = output / (name + '.receipt.json')
    paths = part_paths(output, name)
    receipt = {'schema_version': 1, 'part': name, 'identity': context['identity'],
               'families': len(rows), 'source_indices': [r['source_index'] for r in rows],
               'status': 'failed', 'coverage_proved': False}
    deadline = time.monotonic() + context['timeout']
    try:
        verify_files(context['frozen_files'])
        archive_attempt(output, name)
        atomic_bytes(paths['source'], source)
        command = [context['tools']['coqc'], *context['flags'], str(paths['source'])]
        receipt['compile'] = manager.run(command, context['root'], max(.001, deadline - time.monotonic()), paths['compile_log'])
        if receipt['compile']['status'] != 'ok' or receipt['compile']['returncode'] != 0:
            raise ValueError('compile ' + receipt['compile']['status'] + ' or nonzero exit')
        expected_source = {'sha256': digest(source), 'bytes': len(source)}
        if fingerprint(paths['source']) != expected_source:
            raise ValueError('generated part source changed during compilation')
        receipt['axioms'] = parse_assumptions(paths['compile_log'].read_text(errors='replace'))
        compiled_log = fingerprint(paths['compile_log'])
        if not paths['vo'].is_file():
            raise ValueError('coqc returned zero without producing .vo')
        compiled_vo = fingerprint(paths['vo'])
        command = [context['tools']['coqchk'], '-silent', '-bytecode-compiler', 'yes',
                   *context['flags'], NAMESPACE + '.' + name]
        receipt['audit'] = manager.run(command, context['root'], max(.001, deadline - time.monotonic()), paths['audit_log'])
        if receipt['audit']['status'] != 'ok' or receipt['audit']['returncode'] != 0:
            raise ValueError('recursive audit ' + receipt['audit']['status'] + ' or nonzero exit')
        verify_files(context['frozen_files'])
        receipt['artifacts'] = {key: fingerprint(path) for key, path in paths.items()}
        if receipt['artifacts']['source'] != expected_source:
            raise ValueError('generated part source changed before receipt')
        if receipt['artifacts']['vo'] != compiled_vo:
            raise ValueError('compiled .vo changed during recursive audit')
        if receipt['artifacts']['compile_log'] != compiled_log:
            raise ValueError('compile assumptions log changed during recursive audit')
        receipt['status'] = 'checked'
    except (Exception, KeyboardInterrupt) as error:
        receipt['error'] = str(error)
        receipt['status'] = 'interrupted' if manager.cancelled.is_set() else 'failed'
        receipt['artifacts'] = {key: fingerprint(path) for key, path in paths.items() if path.is_file()}
    atomic_json(receipt_path, receipt)
    return receipt


def execute(args):
    # Parse before invoking any proof tool or writing any generated proof.
    spec, rows, input_bound = load_input(args.spec)
    batch_size = args.batch_size if args.batch_size is not None else spec['default_batch_size']
    budgets = [args.timeout, args.memory_gib, args.disk_reserve_gib]
    if args.max_hours is not None:
        budgets.append(args.max_hours)
    if not all(math.isfinite(value) for value in budgets):
        raise ValueError('numeric budgets must be finite')
    if not 1 <= batch_size <= 256 or not 1 <= args.jobs <= 64 or args.timeout <= 0 or not .125 <= args.memory_gib <= 64:
        raise ValueError('invalid batch size, jobs, timeout, or memory budget')
    if args.max_batches is not None and args.max_batches < 0 or args.max_hours is not None and args.max_hours < 0 or args.disk_reserve_gib < 0:
        raise ValueError('negative scheduling budget')
    root, output = args.repo_root.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    lock_fd = os.open(output / '.runner.lock', os.O_RDWR | os.O_CREAT | getattr(os, 'O_NOFOLLOW', 0), 0o600)
    try:
        try:
            fcntl.flock(lock_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise ValueError('another runner holds the output directory lock') from error
        os.ftruncate(lock_fd, 0)
        os.write(lock_fd, (str(os.getpid()) + '\n').encode())
        return locked_execute(args, spec, rows, input_bound, batch_size, root, output)
    finally:
        os.close(lock_fd)


def locked_execute(args, spec, rows, input_bound, batch_size, root, output):
    manager = ProcessManager(args.memory_gib)
    old_handlers = {}
    def interrupt(signum, frame):
        manager.cancelled.set()
        raise KeyboardInterrupt
    for sig in (signal.SIGINT, signal.SIGTERM):
        old_handlers[sig] = signal.signal(sig, interrupt)
    pool = None
    try:
        tools, tool_bound = tool_identity(args, manager, root)
        if args.coqlib:
            coqlib = args.coqlib.resolve()
        else:
            result = manager.run([tools['coqc'], '-where'], root, 30)
            if result['returncode'] != 0 or result['status'] != 'ok':
                raise ValueError('cannot locate Coq standard library')
            coqlib = Path(result['output'].strip()).resolve()
        if not (coqlib / 'theories').is_dir():
            raise ValueError('Coq library must contain theories/: ' + str(coqlib))
        flags = ['-Q', str(root / 'theories'), 'BBB4', '-Q', str(root / 'wait42/theories'), 'BBBWait42',
                 '-Q', str(output), NAMESPACE]
        dependencies = dependency_closure(root, output, coqlib, tools['coqdep'], flags, manager)
        parts = [(f'Part{i // batch_size:06d}', render_part(rows[i:i+batch_size], spec['cutoff'], spec['upper_width']), rows[i:i+batch_size])
                 for i in range(0, len(rows), batch_size)]
        bound = {'schema_version': 1, 'inputs': input_bound, 'batch_size': batch_size,
                 'cutoff': spec['cutoff'], 'upper_width': spec['upper_width'], 'repo_root': str(root),
                 'coqlib': str(coqlib), 'flags': flags, 'tools': tool_bound,
                 'environment_path_variable_hashes': {name: digest(os.environ.get(name, '').encode()) for name in
                     ('PATH', 'COQPATH', 'COQLIB', 'OCAMLPATH', 'OCAMLLIB', 'OCAMLFIND_CONF', 'CAML_LD_LIBRARY_PATH', 'LD_LIBRARY_PATH')},
                 'runner': {'path': str(Path(__file__).resolve()), **fingerprint(__file__)},
                 'dependencies': dependencies,
                 'parts': [{'name': name, 'families': len(group), 'source_sha256': digest(source)} for name, source, group in parts]}
        identity = digest(canonical(bound))
        manifest_path = output / 'manifest.json'
        if manifest_path.exists():
            previous = json.loads(manifest_path.read_bytes(), object_pairs_hook=json_object)
            if not args.resume:
                raise ValueError('output already has a manifest; use --resume')
            if previous.get('identity') != identity or previous.get('bound') != bound:
                raise ValueError('resume identity mismatch (input/spec/partition/tools/dependencies/runner changed)')
        elif any(output.glob('Part*')):
            raise ValueError('part artifacts exist without an identity manifest')
        else:
            atomic_json(manifest_path, {'identity': identity, 'bound': bound, 'coverage_proved': False,
                                        'trust': 'selected family proofs only; no universal census bound'})
        frozen_files = dict(dependencies)
        frozen_files[input_bound['spec_path']] = input_bound['spec']
        frozen_files[input_bound['input_path']] = input_bound['input']
        frozen_files[str(Path(__file__).resolve())] = fingerprint(__file__)
        for info in tool_bound.values():
            if info is not None:
                frozen_files[info['path']] = {k: info[k] for k in ('bytes', 'sha256')}
        states, todo = {}, []
        resumed_cases = 0
        for part in parts:
            name, source, group = part
            receipt = output / (name + '.receipt.json')
            paths = part_paths(output, name)
            expected = {'compile': [tools['coqc'], *flags, str(paths['source'])],
                        'audit': [tools['coqchk'], '-silent', '-bytecode-compiler', 'yes', *flags, NAMESPACE + '.' + name],
                        'families': len(group), 'source_indices': [r['source_index'] for r in group]}
            if receipt.exists() and validate_receipt(receipt, identity, source, paths, expected):
                states[name] = 'checked'
                resumed_cases += len(group)
            else:
                states[name] = 'pending'
                todo.append(part)
        context = {'output': output, 'root': root, 'manager': manager, 'tools': tools, 'flags': flags,
                   'identity': identity, 'frozen_files': frozen_files, 'timeout': args.timeout}
        launched, start = 0, time.monotonic()
        group_sizes = {name: len(group) for name, _, group in parts}
        progress_path = output / 'progress.json'
        def progress(state, emit=False):
            result = {'schema_version': 1, 'identity': identity, 'state': state, 'coverage_proved': False,
                      'total_families': len(rows), 'total_batches': len(parts),
                      'checked_families': sum(group_sizes[name] for name, s in states.items() if s == 'checked'),
                      'checked_batches': sum(s == 'checked' for s in states.values()),
                      'failed_batches': sum(s in ('failed', 'interrupted') for s in states.values()),
                      'pending_batches': sum(s == 'pending' for s in states.values()),
                      'running_batches': sum(s == 'running' for s in states.values()),
                      'launched_this_run': launched, 'seconds': round(time.monotonic() - start, 3),
                      'notes': 'No universal bound or census coverage is claimed.'}
            result['status'] = ('COMPLETE' if state == 'completed' else
                                'FAILED' if state == 'failed' else
                                'INTERRUPTED' if state == 'interrupted' else
                                'PARTIAL' if state.startswith('partial_') else 'RUNNING')
            result['checked_cases'] = result['checked_families']
            result['resumed_cases'] = resumed_cases
            result['pending_cases'] = sum(group_sizes[name] for name, s in states.items() if s in ('pending', 'running'))
            result['failed_cases'] = sum(group_sizes[name] for name, s in states.items() if s in ('failed', 'interrupted'))
            atomic_json(progress_path, result)
            atomic_json(output / 'summary.json', result)
            if emit:
                print(json.dumps(result), flush=True)
            return result
        progress('running', emit=True)
        last_heartbeat = time.monotonic()
        futures, next_index, stop_reason = {}, 0, None
        pool = concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs)
        try:
            while next_index < len(todo) or futures:
                while next_index < len(todo) and len(futures) < args.jobs and not manager.cancelled.is_set():
                    if args.max_batches is not None and launched >= args.max_batches:
                        stop_reason = 'max_batches'; break
                    if args.max_hours is not None and time.monotonic() - start >= args.max_hours * 3600:
                        stop_reason = 'max_hours'; break
                    if shutil.disk_usage(output).free < args.disk_reserve_gib * 2**30:
                        stop_reason = 'disk_reserve'; break
                    part = todo[next_index]; next_index += 1
                    states[part[0]] = 'running'; launched += 1
                    futures[pool.submit(run_part, part, context)] = part[0]
                    progress('running')
                if not futures:
                    break
                done, _ = concurrent.futures.wait(futures, timeout=.25, return_when=concurrent.futures.FIRST_COMPLETED)
                for future in done:
                    name = futures.pop(future)
                    receipt = future.result()
                    states[name] = receipt['status']
                    progress('running', emit=True)
                if time.monotonic() - last_heartbeat >= 30:
                    progress('running', emit=True)
                    last_heartbeat = time.monotonic()
            pool.shutdown(wait=True)
            pool = None
            verify_files(frozen_files)
            for name, source, group in parts:
                if states[name] == 'checked':
                    paths = part_paths(output, name)
                    expected = {'compile': [tools['coqc'], *flags, str(paths['source'])],
                                'audit': [tools['coqchk'], '-silent', '-bytecode-compiler', 'yes', *flags, NAMESPACE + '.' + name],
                                'families': len(group), 'source_indices': [r['source_index'] for r in group]}
                    if not validate_receipt(output / (name + '.receipt.json'), identity, source, paths, expected):
                        raise ValueError('checked receipt changed before final report: ' + name)
            final = progress('failed' if any(s in ('failed', 'interrupted') for s in states.values()) else
                             ('partial_' + (stop_reason or 'pending') if any(s == 'pending' for s in states.values()) else 'completed'))
            print(json.dumps(final), flush=True)
            return 1 if final['failed_batches'] else 0
        except KeyboardInterrupt:
            for sig in old_handlers:
                signal.signal(sig, signal.SIG_IGN)
            manager.terminate_all()
            pool.shutdown(wait=True, cancel_futures=True)
            pool = None
            for future, name in futures.items():
                states[name] = 'interrupted' if future.cancelled() else future.result()['status']
            final = progress('interrupted')
            print(json.dumps(final), flush=True)
            return 130
    except Exception as error:
        # Integrity/preparation failures must not leave a stale RUNNING or
        # COMPLETE summary suggesting credit for this incompatible invocation.
        manager.terminate_all()
        if pool is not None:
            pool.shutdown(wait=True, cancel_futures=True)
            pool = None
        retained = sum(group_sizes.get(name, 0) for name, state in states.items() if state == 'checked') if 'states' in locals() and 'group_sizes' in locals() else 0
        failure = {'schema_version': 1, 'identity': locals().get('identity'),
                   'status': 'FAILED', 'state': 'integrity_failed', 'coverage_proved': False,
                   'total_families': len(rows), 'checked_cases': 0, 'checked_families': 0,
                   'new_checked_cases': 0, 'retained_checked_receipt_cases': retained,
                   'resumed_cases': 0, 'pending_cases': len(rows), 'running_batches': 0,
                   'failed_batches': 0, 'integrity_errors': 1, 'error': str(error),
                   'notes': 'Receipts remain on disk; no proof credit is claimed for this incompatible invocation.'}
        try:
            atomic_json(output / 'progress.json', failure)
            atomic_json(output / 'summary.json', failure)
        except OSError:
            pass
        raise
    finally:
        for sig in old_handlers:
            signal.signal(sig, signal.SIG_IGN)
        manager.terminate_all()
        if pool is not None:
            pool.shutdown(wait=True, cancel_futures=True)
        for sig, handler in old_handlers.items():
            signal.signal(sig, handler)


def limited_exec(argv):
    signal.pthread_sigmask(signal.SIG_UNBLOCK, {signal.SIGINT, signal.SIGTERM})
    memory = int(float(argv[0]) * 2**30)
    resource.setrlimit(resource.RLIMIT_AS, (memory, memory))
    soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
    requested = 64 * 1024 * 1024 if hard == resource.RLIM_INFINITY else min(hard, 64 * 1024 * 1024)
    if soft != resource.RLIM_INFINITY and soft < requested:
        resource.setrlimit(resource.RLIMIT_STACK, (requested, hard))
    os.execv(argv[1], argv[1:])


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if argv[:1] == ['_exec']:
        limited_exec(argv[1:])
        return 127
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--spec', type=Path, default=ROOT / 'wait42/research/observation-weekend.json')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--repo-root', type=Path, default=ROOT)
    parser.add_argument('--jobs', type=int, default=8)
    parser.add_argument('--batch-size', type=int)
    parser.add_argument('--max-batches', type=int)
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--timeout', type=float, default=3600)
    parser.add_argument('--memory-gib', type=float, default=2)
    parser.add_argument('--max-hours', type=float)
    parser.add_argument('--disk-reserve-gib', type=float, default=2)
    parser.add_argument('--coqc', default='coqc')
    parser.add_argument('--coqchk', default='coqchk')
    parser.add_argument('--coqdep', default='coqdep')
    parser.add_argument('--coqlib', type=Path)
    args = parser.parse_args(argv)
    try:
        return execute(args)
    except KeyboardInterrupt:
        print('interrupted during preparation; no proof credit', file=sys.stderr)
        return 130
    except (ValueError, OSError, csv.Error, json.JSONDecodeError) as error:
        print('replay_observations: ' + str(error), file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
