"""Shared, fail-closed inputs for the private BBB(2,4) build candidate.

Importing this file does not invoke Coq. A manifest is a reviewed source graph,
not evidence that any theorem has been proved.
"""
from __future__ import annotations

import hashlib
from contextlib import contextmanager
import fcntl
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys

TARGET = 205770076433044242247860
CORE_PINS = {
    'four/theories/Statement.v': 'ce3b64e04664a64e9e9398deda83bc05ea257689daf5ee4b1de17a3ae2fdca15',
    'four/theories/StatementTr.v': 'd24cad866f265739663332c11c9198bf9568c6f97bb7d795bb7d1bdc20776052',
    'four/theories/Spec.v': '173d0425555e8d496742ace290695453840fb06f58caee42eb4a53afe0db1f2d',
    'four/theories/ValueSpec.v': 'ef0a27758bc456f486f2dd51535cf40ea36b73a7c00130c3e9f2ab212304451a',
}
VALUE = 'four/theories/Value.v'
THEOREM = 'BBB24.Value.BBB24_state_value'
REPORT_PATH = 'four/build/state-value-report'
REPORT_NS = 'BBB24ValueReport'
# Enable native_compute without compiling native code for every selected module.
# Treat a native-to-VM fallback as an error before a large census is evaluated.
COMPILER_FLAGS = ('-q', '-noglob', '-w',
                  '-abstract-large-number,+native-compiler-disabled',
                  '-native-compiler', 'ondemand')
FE = 'FunctionalExtensionality.functional_extensionality_dep'
IDENT = re.compile(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z')
OBJECT_SUFFIXES = ('.vo', '.vos', '.vok', '.vio', '.cmxs', '.cmo', '.cmx', '.cma',
                   '.cmxa', '.cmi', '.o', '.a', '.so', '.pyc')
PHASES = {
    'ordinary': {'workers': 8, 'address_space_mib': 2048, 'rss_guard_mib': 1843},
    'provider': {'workers': 2, 'address_space_mib': 4096, 'rss_guard_mib': 3686},
    'checks': {'workers': 2, 'address_space_mib': 4096, 'rss_guard_mib': 3686},
    'assembly': {'workers': 1, 'address_space_mib': 12288, 'rss_guard_mib': 11059},
}


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def canonical(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + '.new')
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
    temporary.replace(path)


def archive_results(state, names):
    """Retain old evidence without presenting it as this invocation's result."""
    for name in names:
        path = state / name
        if path.exists():
            archive = state / 'prior-results' / (name + '.' + sha(path))
            archive.parent.mkdir(parents=True, exist_ok=True)
            path.replace(archive)


def relative(value):
    """Portable project paths: root directories may contain spaces; entries may not."""
    if not isinstance(value, str) or any(c.isspace() for c in value) or '\\' in value:
        raise ValueError('Project entry must be a POSIX relative path without whitespace: ' + repr(value))
    p = PurePosixPath(value)
    if not value or p.is_absolute() or '..' in p.parts or str(p) != value:
        raise ValueError('Invalid project-relative path: ' + repr(value))
    return p


def inside(root, value):
    p = root / relative(value)
    if not p.resolve().is_relative_to(root.resolve()):
        raise ValueError('Path leaves selected tree: ' + value)
    q = p
    while q != root:
        if q.is_symlink():
            raise ValueError('Symlink in selected source/object path: ' + str(q))
        q = q.parent
    return p


def clean_environment():
    env = os.environ.copy()
    for key in ('COQPATH', 'COQLIB', 'COQCORELIB', 'COQBIN', 'COQFLAGS', 'COQEXTRAFLAGS'):
        env.pop(key, None)
    env['COQPATH'] = ''
    env['COQ_COLORS'] = 'never'
    return env


@contextmanager
def exclusive_build_locks(tree, state):
    """One owner per state AND per tree, including callers using another state."""
    with (state / 'build.lock').open('w') as state_lock:
        fcntl.flock(state_lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        with (tree / '.proof24-build.lock').open('w') as tree_lock:
            fcntl.flock(tree_lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            yield


class Graph:
    def __init__(self, tree, manifest, expected_sha256, allow_value=False):
        self.tree = Path(tree).resolve(strict=True)
        self.manifest_path = Path(manifest).resolve(strict=True)
        self.digest = sha(self.manifest_path)
        if self.digest != expected_sha256:
            raise ValueError('Selected manifest SHA256 differs from reviewed pin')
        self.spec = json.loads(self.manifest_path.read_text())
        self.sources = self.spec['sources']
        self.deps = self.spec['local_dependencies']
        self.order = self.spec['compile_order']
        self.paths = self.spec['load_paths']
        self.roots = self.spec['roots']
        if set(self.order) != set(self.sources) or len(self.order) != len(self.sources):
            raise ValueError('compile_order must contain each selected source exactly once')
        if set(self.deps) != set(self.sources):
            raise ValueError('Dependency map must cover exactly the selected sources')
        if VALUE in self.sources or ((self.tree / VALUE).exists() and not allow_value):
            raise ValueError('Initial selected source graph must not contain Value.v')
        if not self.roots or not set(self.roots) <= set(self.sources):
            raise ValueError('Missing selected final root')
        seen = set()
        for source in self.order:
            relative(source)
            if not source.endswith('.v') or set(self.deps[source]) - seen:
                raise ValueError('Dependency order incomplete or not topological: ' + source)
            seen.add(source)
        for source, digest in CORE_PINS.items():
            if self.sources.get(source, {}).get('sha256') != digest:
                raise ValueError('Untrusted machine model/claim binding: ' + source)
        self._validate_paths()
        self.module = {s: self.logical(s) for s in self.order}
        if len(set(self.module.values())) != len(self.module):
            raise ValueError('Selected paths assign duplicate logical modules')
        pending = self.spec.get('pending_value_alias') or {}
        self.final_constant = pending.get('qualified_final_theorem')
        if not self.final_constant or not IDENT.fullmatch(self.final_constant):
            raise ValueError('Missing qualified final theorem constant')
        final_module = self.final_constant.rsplit('.', 1)[0]
        if final_module not in {self.module[s] for s in self.roots}:
            raise ValueError('Final theorem must belong to an explicit selected root')
        self.final_source = next(s for s in self.roots if self.module[s] == final_module)
        # Extra selected sources can introduce unchecked objects into -Q search roots.
        closure = self.closure(self.roots + list(CORE_PINS))
        if set(self.order) != closure:
            raise ValueError('Selected graph must be exactly the final/core source closure')
        policy = self.spec.get('resource_policy') or {}
        self.profiles = {name: dict(profile) for name, profile in PHASES.items()}
        for phase, override in policy.get('phase_profiles', {}).items():
            if phase not in PHASES or set(override) - set(PHASES[phase]):
                raise ValueError('Unknown resource profile field')
            self.profiles[phase].update(override)
        for phase, profile in self.profiles.items():
            if (any(type(value) is not int or value <= 0 for value in profile.values())
                    or profile['workers'] > PHASES[phase]['workers']
                    or profile['rss_guard_mib'] > profile['address_space_mib']):
                raise ValueError('Unsafe resource profile: ' + phase)
        self.phase = {s: ('ordinary' if s.startswith(('four/theories/', 'small/theories/'))
                          else 'provider') for s in self.order}
        self.phase.update(policy.get('source_phases', {}))
        self.phase.update({s: 'assembly' for s in policy.get('serial_sources', [])})
        if set(self.phase) != set(self.order) or set(self.phase.values()) - set(PHASES):
            raise ValueError('Unknown source or phase in resource policy')

    def _validate_paths(self):
        namespaces, physical = set(), set()
        for row in self.paths:
            path, ns = row['path'], row['namespace']
            relative(path)
            if not IDENT.fullmatch(ns) or not (ns == 'SmallBB' or ns.startswith('BBB24')):
                raise ValueError('Untrusted/shadowing namespace: ' + str(ns))
            if ns == REPORT_NS or ns.startswith(REPORT_NS + '.'):
                raise ValueError('Selected graph shadows the fresh report namespace')
            if (PurePosixPath(REPORT_PATH).is_relative_to(path)
                    or PurePosixPath(path).is_relative_to(REPORT_PATH)):
                raise ValueError('Selected load path overlaps the fresh report output')
            if ns in namespaces or path in physical:
                raise ValueError('Duplicate selected load-path binding')
            # No prefix aliases can shadow a module beneath another -Q binding.
            if any(ns.startswith(n + '.') or n.startswith(ns + '.') for n in namespaces):
                raise ValueError('Overlapping logical namespaces')
            if any(PurePosixPath(path).is_relative_to(p) or PurePosixPath(p).is_relative_to(path)
                   for p in physical):
                raise ValueError('Overlapping physical load paths')
            inside(self.tree, path)
            namespaces.add(ns)
            physical.add(path)
        bindings = {row['namespace']: row['path'] for row in self.paths}
        if bindings.get('BBB24') != 'four/theories' or bindings.get('SmallBB') != 'small/theories':
            raise ValueError('Selected project must preserve BBB24 and SmallBB core bindings')

    def logical(self, source):
        found = []
        for row in self.paths:
            p = PurePosixPath(source)
            root = PurePosixPath(row['path'])
            if p.is_relative_to(root):
                tail = p.relative_to(root).with_suffix('').parts
                name = '.'.join([row['namespace'], *tail])
                if not IDENT.fullmatch(name):
                    raise ValueError('Invalid Coq logical filename: ' + source)
                found.append(name)
        if len(found) != 1:
            raise ValueError('Source needs one selected -Q mapping: ' + source)
        return found[0]

    def closure(self, roots):
        result, todo = set(), list(roots)
        while todo:
            source = todo.pop()
            if source not in result:
                result.add(source)
                todo.extend(self.deps[source])
        return result

    @property
    def flags(self):
        return [arg for row in self.paths for arg in ('-Q', row['path'], row['namespace'])]

    def verify_sources(self):
        for source, row in self.sources.items():
            if sha(inside(self.tree, source)) != row['sha256']:
                raise ValueError('Selected source changed: ' + source)

    def verify_no_unselected(self, allow_value=False, reports=()):
        allowed = set(self.sources) | ({VALUE} if allow_value else set()) | set(reports)
        for row in self.paths:
            for p in (self.tree / row['path']).rglob('*.v'):
                if p.relative_to(self.tree).as_posix() not in allowed:
                    raise ValueError('Unselected source beneath active -Q root: ' + str(p))
        # A source-less stale .vo can also shadow an imported module.
        for row in self.paths:
            for p in (self.tree / row['path']).rglob('*'):
                if p.is_file() and p.suffix in OBJECT_SUFFIXES:
                    source = p.with_suffix('.v').relative_to(self.tree).as_posix()
                    if p.suffix not in ('.vo', '.vos', '.vok') or source not in allowed:
                        raise ValueError('Unselected/native object beneath active -Q root: ' + str(p))

    def verify_empty_objects(self):
        for p in self.tree.rglob('*'):
            if p.is_file() and (p.suffix in OBJECT_SUFFIXES or p.name == '.coq-native'):
                raise ValueError('Fresh preparation contains an object: ' + str(p))
        if any(self.tree.rglob('.coq-native')):
            raise ValueError('Fresh preparation contains native output')


def parse_assumptions(output):
    """Inspect Coq's actual final Print Assumptions block, including Unicode names."""
    if 'Axioms:' in output:
        tail = output.rsplit('Axioms:', 1)[1]
        declarations = re.findall(r'(?m)^([^\s:]+)\s*(?=\n?\s*:)', tail)
        # Unexpected unindented text must never be silently skipped (for example
        # a Unicode/grouped declaration outside the declaration regexp).
        top_level = [line for line in tail.splitlines() if line and not line[0].isspace()]
        if (declarations != [FE] or len(top_level) != 1
                or not (top_level[0] == FE or re.fullmatch(re.escape(FE) + r'\s*:.*', top_level[0]))):
            raise ValueError('Unexpected theorem assumptions: ' + repr(declarations))
        return declarations
    if 'Closed under the global context' not in output:
        raise ValueError('Missing Print Assumptions result')
    return []


def statement_check(constant, require, imports=''):
    if not IDENT.fullmatch(constant) or not IDENT.fullmatch(require):
        raise ValueError('Invalid final theorem import')
    # Require without Import prevents Value from replacing names in the check.
    require_line = 'From BBB24 Require Value.' if require == 'BBB24.Value' else f'Require {require}.'
    return f'''From Coq Require Import NArith.
From BBB24 Require Import Statement Spec ValueSpec.
{require_line}
{imports}
Definition checked_state_equality :
  BBB24_state_lower_bound score /\\ (forall tm : TM, QHBound score tm) :=
  ({constant} : BBB24.ValueSpec.BBB24_state_statement).
Example checked_numeric_target : scoreN = {TARGET}%N.
Proof. reflexivity. Qed.
Example checked_nat_target : score = N.to_nat {TARGET}%N.
Proof. reflexivity. Qed.
Check {constant}.
Check checked_state_equality.
Print AttainsSt.
Print QHBound.
Print BBB24_state_is.
Print BBB24_state_statement.
Eval vm_compute in scoreN.
Print Assumptions checked_state_equality.
'''


def selected_statement_check(graph, constant, require):
    # Extra explicit roots (for example Exports) must be inside the recursive
    # audit, even when Final's theorem itself does not depend on them.
    final_module = graph.final_constant.rsplit('.', 1)[0]
    modules = sorted({graph.module[source] for source in graph.roots} - {require, final_module})
    return statement_check(constant, require, '\n'.join('Require ' + name + '.' for name in modules))


def runtime_snapshot(env):
    """Only called by the explicitly executing build/report commands."""
    binaries = {}
    for name in ('coqc', 'coqchk', 'coqdep'):
        path = Path(shutil.which(name, path=env['PATH']) or '')
        if not path.is_file():
            raise ValueError('Missing Coq executable: ' + name)
        path = path.resolve()
        binaries[name] = {'path': str(path), 'sha256': sha(path)}
    def output(*args):
        return subprocess.check_output([binaries['coqc']['path'], *args], env=env, text=True).strip()
    where = Path(output('-where')).resolve(strict=True)
    # Hash runtime Coq objects and plugin code; no bare version-based cache.
    runtime = {}
    roots = [where]
    plugins = where.parent / 'coq-core'
    if plugins.is_dir() and not plugins.is_relative_to(where):
        roots.append(plugins)
    for name in ('stublibs', 'zarith'):
        root = where.parent / name
        if root.is_dir():
            roots.append(root)
    for root in roots:
        for p in sorted(root.rglob('*')):
            if p.is_file() and p.suffix in ('.vo', '.cmxs', '.cma', '.so'):
                runtime[str(p)] = sha(p)
    if not runtime:
        raise ValueError('Runtime has no Coq library/plugin files')
    return {'binaries': binaries, 'version': output('--version'), 'config': output('-config'),
            'where': str(where), 'library_files': runtime,
            'python': {'executable': str(Path(sys.executable).resolve()),
                       'sha256': sha(Path(sys.executable).resolve()), 'version': sys.version},
            'environment_hash': canonical({k: env.get(k) for k in
                ('PATH', 'OCAMLPATH', 'CAML_LD_LIBRARY_PATH', 'COQPATH', 'COQLIB', 'COQCORELIB')})}


def require_native_compiler(runtime):
    config = dict(line.split('=', 1) for line in runtime['config'].splitlines() if '=' in line)
    if config.get('COQ_NATIVE_COMPILER_DEFAULT') not in ('yes', 'ondemand'):
        raise ValueError('Selected census build requires native-capable Coq; '
                         'run tools/census_toolchain.sh from the repository root')


def receipt_key(graph, source, runtime_digest, dependencies):
    return {'manifest_sha256': graph.digest, 'source': source,
            'source_sha256': sha(inside(graph.tree, source)),
            'selected_paths_sha256': canonical(graph.paths),
            'runtime_sha256': runtime_digest,
            'dependencies': {d: canonical(dependencies[d]) for d in graph.deps[source]},
            'compiler_flags': list(COMPILER_FLAGS)}


def receipt_valid(path, expected, object_path):
    try:
        row = json.loads(Path(path).read_text())
        return (row['inputs'] == expected and row['object_sha256'] == sha(object_path)
                and row['object_bytes'] == Path(object_path).stat().st_size
                and row['compile_exit_code'] == 0)
    except (OSError, ValueError, KeyError, TypeError):
        return False
