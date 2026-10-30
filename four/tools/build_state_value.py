"""Selected source graph -> exact BBB(2,4) report; complete build under verification.

`inspect` never invokes Coq. `build` explicitly invokes Coq and can be expensive.
There is no theorem credit from inspect, preparation, or a compile receipt.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
from pathlib import Path
import re
import sys
import tempfile
import time

from proof24_common import (COMPILER_FLAGS, Graph, REPORT_PATH, REPORT_NS, VALUE, canonical, clean_environment, inside,
    archive_results, exclusive_build_locks,
    parse_assumptions, receipt_key, receipt_valid, require_native_compiler, runtime_snapshot, sha,
    selected_statement_check, write_json)
from proof24_resources import CommandBatch, check_disk, phase_limits, run_capped

FLAGS = list(COMPILER_FLAGS)


def implementation_pins():
    folder = Path(__file__).resolve().parent
    return {name: sha(folder / name) for name in
            ('proof24_common.py', 'proof24_resources.py', 'build_state_value.py', 'report_state_value.py')}


def alias_source(graph):
    module = graph.final_constant.rsplit('.', 1)[0]
    return ("(** Generated only after fresh final-theorem assumption and recursive kernel checks. *)\n"
            "From BBB24 Require Import ValueSpec.\n"
            f"Require {module}.\n"
            "Theorem BBB24_state_value : BBB24.ValueSpec.BBB24_state_statement.\n"
            f"Proof. exact {graph.final_constant}. Qed.\n")


def selected_project(graph, sources):
    return ''.join(f"-Q {r['path']} {r['namespace']}\n" for r in graph.paths) + ''.join(s + '\n' for s in sources)


def check_dependencies(graph, runtime, state, env, timeout):
    """Fresh coqdep must reproduce the reviewed local graph before any compile."""
    project = state / '_CoqProject.selected'
    project_text = selected_project(graph, graph.order)
    project.write_text(project_text)
    log = state / 'coqdep.log'
    limits = phase_limits('ordinary', 1, profiles=graph.profiles)
    # coqdep resolves project entries relative to the -f file's directory, not
    # its working directory. Keep relative entries/output (including when the
    # tree's parent path contains spaces) and avoid a large command-line list.
    # The state copy is durable evidence; only this temporary root copy is removed.
    with tempfile.NamedTemporaryFile(mode='w', encoding='utf-8', dir=graph.tree,
                                     prefix='_CoqProject.selected.') as selected:
        selected.write(project_text)
        selected.flush()
        command = [runtime['binaries']['coqdep']['path'], '-f', Path(selected.name).name]
        run_capped(command, graph.tree, env, log, limits, timeout)
    output = log.read_text()
    if re.search(r'(?i)warning|error', output):
        raise ValueError('coqdep emitted warnings/errors; inspect ' + str(log))
    observed = {}
    for line in output.splitlines():
        if ':' not in line:
            continue
        targets, inputs = line.split(':', 1)
        objects = [s for s in targets.split() if s.endswith('.vo')]
        if not objects:
            continue
        source = objects[0][:-3] + '.v'
        if source not in graph.sources:
            raise ValueError('coqdep returned an unselected source: ' + source)
        deps = set()
        for token in inputs.split():
            if token.endswith('.vo'):
                dependency = token[:-3] + '.v'
                if dependency not in graph.sources:
                    raise ValueError('coqdep dependency lies outside selected graph: ' + token)
                deps.add(dependency)
        observed[source] = deps
    if set(observed) != set(graph.sources):
        raise ValueError('coqdep did not cover exactly the selected graph')
    for source in graph.order:
        if observed[source] != set(graph.deps[source]):
            raise ValueError('Fresh coqdep disagrees with reviewed graph: ' + source)
    write_json(state / 'dependency-check.json', {'status': 'fresh coqdep graph matched',
        'manifest_sha256': graph.digest, 'log_sha256': sha(log),
        'runtime_sha256': canonical(runtime), 'local_dependencies_sha256': canonical(graph.deps)})


def verify_receipts(graph, state, runtime_digest):
    rows = {}
    for source in graph.order:
        key = receipt_key(graph, source, runtime_digest, rows)
        path = state / 'receipts' / (graph.module[source] + '.json')
        if not receipt_valid(path, key, graph.tree / Path(source).with_suffix('.vo')):
            raise ValueError('Stale/missing compile receipt or object: ' + source)
        rows[source] = json.loads(path.read_text())
    return rows


def compile_graph(graph, state, runtime, env, jobs, timeout, reserve_gib):
    runtime_digest = canonical(runtime)
    pending = set(graph.order)
    rows = {}
    completed, resumed = 0, 0
    while pending:
        ready = [s for s in graph.order if s in pending and set(graph.deps[s]) <= rows.keys()]
        if not ready:
            raise ValueError('No ready source in selected DAG')
        # Profiles never overlap; heavy providers/checks run with fewer workers,
        # global assembly runs alone. Available RAM is measured at every batch.
        phase = graph.phase[ready[0]]
        limits = phase_limits(phase, jobs, profiles=graph.profiles)
        batch = [s for s in ready if graph.phase[s] == phase][:limits['workers']]
        check_disk(graph.tree, reserve_gib)
        check_disk(state, reserve_gib)
        tasks = []
        for source in batch:
            key = receipt_key(graph, source, runtime_digest, rows)
            path = state / 'receipts' / (graph.module[source] + '.json')
            obj = graph.tree / Path(source).with_suffix('.vo')
            if receipt_valid(path, key, obj):
                rows[source] = json.loads(path.read_text())
                pending.remove(source)
                resumed += 1
                continue
            # Never consume a stale result if the new command fails.
            path.unlink(missing_ok=True)
            for suffix in ('.vo', '.vos', '.vok', '.vio'):
                obj.with_suffix(suffix).unlink(missing_ok=True)
            log = state / 'compile' / (graph.module[source] + '.log')
            log.parent.mkdir(parents=True, exist_ok=True)
            tasks.append((source, key, path, obj, log))
        if tasks:
            print(json.dumps({'phase': phase, 'workers': len(tasks), 'remaining': len(pending),
                              'sources': [t[0] for t in tasks]}), flush=True)
        owner = CommandBatch()
        with ThreadPoolExecutor(max_workers=limits['workers']) as pool:
            futures = {pool.submit(run_capped,
                [runtime['binaries']['coqc']['path'], *FLAGS, *graph.flags, source],
                graph.tree, env, log, limits, timeout, owner): (source, key, path, obj, log)
                for source, key, path, obj, log in tasks}
            try:
                for future in as_completed(futures):
                    source, key, path, obj, log = futures[future]
                    result = future.result()
                    if sha(graph.tree / source) != graph.sources[source]['sha256']:
                        raise ValueError('Source changed during compile: ' + source)
                    row = {'inputs': key, 'object_sha256': sha(obj), 'object_bytes': obj.stat().st_size,
                           'compile_exit_code': result['exit_code'], 'compile_log_sha256': sha(log),
                           'resource_profile': phase, 'execution': result,
                           'kernel_audit_status': 'pending; compilation alone is not an audit'}
                    write_json(path, row)
                    rows[source] = row
                    pending.remove(source)
                    completed += 1
            except BaseException:
                owner.cancel()
                for future in futures:
                    future.cancel()
                raise
    return rows, {'fresh_compiled': completed, 'exact_receipts_resumed': resumed}


def checked_root(graph, state, runtime, env, constant, require, name, timeout):
    """Fresh exact statement/assumptions check followed by FULL recursive coqchk."""
    report = graph.tree / REPORT_PATH
    report.mkdir(parents=True, exist_ok=True)
    source = report / (name + '.v')
    expected_source = selected_statement_check(graph, constant, require)
    source.write_text(expected_source)
    flags = [*graph.flags, '-Q', REPORT_PATH, REPORT_NS]
    limits = phase_limits('assembly', 1, profiles=graph.profiles)
    compile_log = state / (name + '-compile.log')
    audit_log = state / (name + '-coqchk.log')
    audit_log.unlink(missing_ok=True)
    run_capped([runtime['binaries']['coqc']['path'], *FLAGS, *flags,
                str(source.relative_to(graph.tree))], graph.tree, env, compile_log, limits, timeout)
    assumptions = parse_assumptions(compile_log.read_text())
    result = run_capped([runtime['binaries']['coqchk']['path'], '-silent', '-bytecode-compiler',
                         'yes', *flags, REPORT_NS + '.' + name], graph.tree, env,
                        audit_log, limits, timeout)
    if source.read_text() != expected_source:
        raise ValueError('Report theorem source changed during compile/audit')
    return {'mode': 'full-recursive', 'root': REPORT_NS + '.' + name,
            'source_sha256': sha(source), 'object_sha256': sha(source.with_suffix('.vo')),
            'assumptions': assumptions, 'compile_log_sha256': sha(compile_log),
            'audit_log_sha256': sha(audit_log), 'audit_execution': result}


def execute(graph, state, args):
    check_disk(graph.tree, args.disk_reserve_gib)
    check_disk(state, args.disk_reserve_gib)
    state.mkdir(parents=True, exist_ok=True)
    # Exclusive ownership covers compile objects, report roots and the gated alias.
    with exclusive_build_locks(graph.tree, state):
        archive_results(state, ['build-result.json', 'state-value-result.json',
                                'final-gate.json', 'value-alias.json'])
        if (graph.tree / VALUE).exists() and (graph.tree / VALUE).read_text() != alias_source(graph):
            raise ValueError('Existing Value.v is not this graph\'s gated alias')
        graph.verify_sources()
        graph.verify_no_unselected(allow_value=args.resume)
        env = clean_environment()
        runtime = runtime_snapshot(env)
        require_native_compiler(runtime)
        identity = {'manifest_sha256': graph.digest, 'runtime_sha256': canonical(runtime),
                    'implementation': implementation_pins(), 'tree': str(graph.tree)}
        initial = state / 'build-identity.json'
        if args.resume:
            if not initial.is_file() or json.loads(initial.read_text()) != identity:
                raise ValueError('Resume identity differs; use a new freshly prepared tree/state')
        else:
            if initial.exists():
                raise ValueError('Build state already exists; use --resume with exact receipts')
            graph.verify_empty_objects()
            write_json(initial, identity)
            write_json(state / 'runtime.json', runtime)
            write_json(state / 'fresh-start.json', {'selected_sources': len(graph.order),
                'project_objects': 0, 'manifest_sha256': graph.digest,
                'source_preparation_only_before_build': True})
        (state / 'receipts').mkdir(exist_ok=True)
        check_dependencies(graph, runtime, state, env, args.command_timeout)
        rows, counts = compile_graph(graph, state, runtime, env, args.jobs,
                                     args.command_timeout, args.disk_reserve_gib)
        # Recheck the complete current closure before asking the kernel to audit it.
        verify_receipts(graph, state, canonical(runtime))
        gate = checked_root(graph, state, runtime, env, graph.final_constant,
                            graph.final_constant.rsplit('.', 1)[0], 'CheckFinal', args.audit_timeout)
        graph.verify_sources()
        verify_receipts(graph, state, canonical(runtime))
        gate.update({'manifest_sha256': graph.digest, 'runtime_sha256': canonical(runtime),
                     'closure_receipts_sha256': canonical(rows)})
        write_json(state / 'final-gate.json', gate)
        # Value.v does not exist before the exact final theorem and its full closure
        # passed the actual assumptions check and fresh recursive kernel audit.
        value = graph.tree / VALUE
        value.write_text(alias_source(graph))
        log = state / 'Value-compile.log'
        run_capped([runtime['binaries']['coqc']['path'], *FLAGS, *graph.flags, VALUE],
                   graph.tree, env, log, phase_limits('assembly', 1, profiles=graph.profiles), args.command_timeout)
        write_json(state / 'value-alias.json', {'source_sha256': sha(value),
            'object_sha256': sha(value.with_suffix('.vo')), 'final_gate_sha256': sha(state / 'final-gate.json'),
            'manifest_sha256': graph.digest, 'runtime_sha256': canonical(runtime)})
        # Imported here to keep inspect entirely independent of execution code.
        from report_state_value import selected_report
        selected_report(graph, state, runtime, env, args.audit_timeout)
        if canonical(runtime_snapshot(env)) != canonical(runtime):
            raise ValueError('Coq runtime changed during the build; success is invalid')
        write_json(state / 'build-result.json', {'status': 'exact statement and full recursive kernel audit passed',
            'manifest_sha256': graph.digest, 'runtime_sha256': canonical(runtime), **counts,
            'Value_alias_created_after_final_recursive_audit': True,
            'result_report_sha256': sha(state / 'state-value-result.json')})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['inspect', 'build'])
    parser.add_argument('--tree', type=Path, required=True)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--state', type=Path)
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--jobs', type=int, default=8)
    parser.add_argument('--disk-reserve-gib', type=int, default=8)
    parser.add_argument('--command-timeout', type=int, default=6 * 3600)
    parser.add_argument('--audit-timeout', type=int, default=24 * 3600)
    args = parser.parse_args()
    if args.jobs < 1 or args.disk_reserve_gib < 1:
        raise ValueError('Jobs and disk reserve must be positive')
    graph = Graph(args.tree, args.manifest, args.manifest_sha256, allow_value=args.resume)
    if args.action == 'inspect':
        graph.verify_sources()
        graph.verify_no_unselected()
        graph.verify_empty_objects()
        print(json.dumps({'status': 'source-only selected graph inspected', 'sources': len(graph.order),
            'load_paths': len(graph.paths), 'manifest_sha256': graph.digest,
            'Coq_invoked': False, 'kernel_audit_executed': False, 'proof_credit': 0}, indent=2))
        return 0
    if not args.state:
        raise ValueError('An explicit disk-backed --state directory is required')
    state = args.state.resolve()
    if state.is_relative_to(graph.tree):
        raise ValueError('Build state/logs must be outside the selected source tree')
    execute(graph, state, args)
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, RuntimeError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(2)
