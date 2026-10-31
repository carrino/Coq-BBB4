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

from proof24_common import (COMPILER_FLAGS, PHASES, Graph, REPORT_PATH, REPORT_NS, VALUE, canonical, clean_environment, inside,
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


# Reviewed execution-policy migrations preserve compiler, monitor and reporter
# bytes from the native-census fix and bounded provider scheduler. Source graph,
# runtime and tree must still match, and every object receipt is checked again.
SCHEDULER_PREDECESSOR = {
    'proof24_common.py': 'fcf4cf5ecd8baa311773f0ebaa3f590412ac8fa63dfe345f2ef6bc6f71a432b0',
    'proof24_resources.py': '4464141932bdcd63bd2ea5aa9ecc5d3b44c0c9e12e196e11d0218320f9a36c40',
    'build_state_value.py': 'ced36b3d0c4359de56cb502f210a28a89f42a88ad5f07e9d26d0470a5461156d',
    'report_state_value.py': '5c67ad828c41f0958b0d8bbaac63f5086268a70c4fe94b454c497cc095c197b6',
}


# The bounded provider scheduler kept the same compiler, monitor and reporter.
# Its completed receipts also survive an audit-GC-only execution-policy upgrade.
AUDIT_PREDECESSOR = {
    **SCHEDULER_PREDECESSOR,
    'build_state_value.py': 'c1e0d5dcc8ac519c4b2074b17d50c927ffc25a7e2a887b9bed84f5db7c9db052',
}
MEMORY_PREDECESSOR = {
    **AUDIT_PREDECESSOR,
    'build_state_value.py': '3f7af4787e63fa731b9523200bb9ae2c1785015d237d07cdf2bd309ef4d1c5ea',
}
DEFAULT_AUDIT_GC = 'o=40,O=60'


def audit_environment(env):
    audit_env = env.copy()
    if 'STATE24_COQCHK_OCAMLRUNPARAM' in env:
        audit_env['OCAMLRUNPARAM'] = env['STATE24_COQCHK_OCAMLRUNPARAM']
    else:
        audit_env.setdefault('OCAMLRUNPARAM', DEFAULT_AUDIT_GC)
    return audit_env


def audit_limits(graph, env, default=None):
    """Optional serial audit budget; retain the normal RAM/cgroup admission check."""
    requested = env.get('STATE24_AUDIT_RSS_GIB')
    if requested is None:
        return default if default is not None else phase_limits('assembly', 1, profiles=graph.profiles)
    if not re.fullmatch(r'[1-9][0-9]*', requested):
        raise ValueError('STATE24_AUDIT_RSS_GIB must be a positive integer number of GiB')
    rss_mib = int(requested) * 1024
    profiles = dict(graph.profiles)
    profiles['assembly'] = {**profiles.get('assembly', PHASES['assembly']),
                           'workers': 1, 'rss_guard_mib': rss_mib,
                           'address_space_mib': rss_mib + 2048}
    return phase_limits('assembly', 1, profiles=profiles)


def resume_identity(state, identity, provider_light):
    initial = state / 'build-identity.json'
    if not initial.is_file():
        raise ValueError('Missing resume identity')
    previous = json.loads(initial.read_text())
    if previous == identity:
        return
    unchanged = set(SCHEDULER_PREDECESSOR) - {'build_state_value.py'}
    predecessors = [{**identity, 'implementation': implementation}
                    for implementation in (SCHEDULER_PREDECESSOR, AUDIT_PREDECESSOR, MEMORY_PREDECESSOR)]
    if (not provider_light or previous not in predecessors
            or any(identity['implementation'].get(name) != SCHEDULER_PREDECESSOR[name]
                   for name in unchanged)):
        raise ValueError('Resume identity differs; use a new freshly prepared tree/state')
    write_json(state / 'scheduler-upgrade.json', {
        'scope': 'execution policy only; no compiler/source/runtime/receipt relaxation',
        'previous_identity': previous, 'current_identity': identity,
        'fresh_object_receipt_validation_required': True,
        'fresh_final_recursive_audits_required': True})
    write_json(initial, identity)
    print('Upgraded the reviewed execution policy; current compile receipts will be checked.',
          flush=True)


def memory_limited_failure(error, log):
    """Only an owned-process memory limit permits the existing full-budget retry."""
    message = str(error)
    if message.startswith('Child session exceeded RSS guard: '):
        return True
    if message.startswith('Command failed, exit '):
        return bool(re.search(
            r'^(?:Fatal error: (?:out of memory|exception Out_of_memory)|Error: Out of memory\.)\s*$',
            log.read_text(), re.IGNORECASE | re.MULTILINE))
    return False


def compile_graph(graph, state, runtime, env, jobs, timeout, reserve_gib, provider_light=False):
    runtime_digest = canonical(runtime)
    pending = set(graph.order)
    rows = {}
    completed, resumed, light_attempts, memory_retries = 0, 0, 0, 0

    def save(task, result, phase, limits, log, retry=None):
        nonlocal completed
        source, key, path, obj, _ = task
        if sha(graph.tree / source) != graph.sources[source]['sha256']:
            raise ValueError('Source changed during compile: ' + source)
        row = {'inputs': key, 'object_sha256': sha(obj), 'object_bytes': obj.stat().st_size,
               'compile_exit_code': result['exit_code'], 'compile_log_sha256': sha(log),
               'compile_log': str(log.relative_to(state)),
               'resource_profile': phase, 'execution': result,
               'resource_limits': {k: limits[k] for k in ('address_space_bytes', 'rss_guard_bytes')},
               'kernel_audit_status': 'pending; compilation alone is not an audit'}
        if retry is not None:
            row['light_memory_retry'] = retry
        write_json(path, row)
        rows[source] = row
        pending.remove(source)
        completed += 1

    def batch(tasks, limits, phase, light=False, retries=None):
        """Every child is owned; a light memory failure cancels only that child."""
        failed = {}
        owners = {task[0]: CommandBatch() for task in tasks}

        def attempt(task):
            source, _, _, obj, normal_log = task
            log = normal_log.with_suffix('.light.log') if light else normal_log
            try:
                result = run_capped(
                    [runtime['binaries']['coqc']['path'], *FLAGS, *graph.flags, source],
                    graph.tree, env, log, limits, timeout, owners[source])
                return result, log, None
            except RuntimeError as error:
                if not light or not memory_limited_failure(error, log):
                    raise
                # run_capped has terminated/reaped this whole child session.
                # Failed output never receives a receipt or reaches a dependent.
                for suffix in ('.vo', '.vos', '.vok', '.vio'):
                    obj.with_suffix(suffix).unlink(missing_ok=True)
                return None, log, {'reason': str(error), 'log': str(log.relative_to(state)),
                    'log_sha256': sha(log), 'address_space_bytes': limits['address_space_bytes'],
                    'rss_guard_bytes': limits['rss_guard_bytes']}

        if tasks:
            print(json.dumps({'phase': phase, 'workers': len(tasks), 'remaining': len(pending),
                              'sources': [t[0] for t in tasks]}), flush=True)
        with ThreadPoolExecutor(max_workers=limits['workers']) as pool:
            futures = {}
            try:
                for task in tasks:
                    futures[pool.submit(attempt, task)] = task
                for future in as_completed(futures):
                    task = futures[future]
                    result, log, retry = future.result()
                    if retry is not None:
                        failed[task[0]] = retry
                    else:
                        save(task, result, phase, limits, log,
                             (retries or {}).get(task[0]))
            except BaseException:
                for owner in owners.values():
                    owner.cancel()
                for future in futures:
                    future.cancel()
                raise
        return failed

    while pending:
        ready = [s for s in graph.order if s in pending and set(graph.deps[s]) <= rows.keys()]
        if not ready:
            raise ValueError('No ready source in selected DAG')
        phase = graph.phase[ready[0]]
        light = provider_light and phase == 'provider'
        # A light provider attempt borrows the frozen ordinary budget. Its
        # complete batch ends before any full-budget provider retry starts.
        limits = phase_limits('ordinary' if light else phase, jobs, profiles=graph.profiles)
        sources = [s for s in ready if graph.phase[s] == phase][:limits['workers']]
        check_disk(graph.tree, reserve_gib)
        check_disk(state, reserve_gib)
        tasks = []
        for source in sources:
            key = receipt_key(graph, source, runtime_digest, rows)
            path = state / 'receipts' / (graph.module[source] + '.json')
            obj = graph.tree / Path(source).with_suffix('.vo')
            if receipt_valid(path, key, obj):
                rows[source] = json.loads(path.read_text())
                pending.remove(source)
                resumed += 1
                continue
            path.unlink(missing_ok=True)
            for suffix in ('.vo', '.vos', '.vok', '.vio'):
                obj.with_suffix(suffix).unlink(missing_ok=True)
            log = state / 'compile' / (graph.module[source] + '.log')
            log.parent.mkdir(parents=True, exist_ok=True)
            tasks.append((source, key, path, obj, log))
        if light:
            light_attempts += len(tasks)
        failed = batch(tasks, limits, 'provider-light' if light else phase, light)
        retry_tasks = [task for task in tasks if task[0] in failed]
        memory_retries += len(retry_tasks)
        while retry_tasks:
            # Never exceed the original reviewed provider cap, and never retry
            # a statement/type error, timeout, disk error or system-RAM guard.
            limits = phase_limits('provider', jobs, profiles=graph.profiles)
            check_disk(graph.tree, reserve_gib)
            check_disk(state, reserve_gib)
            selected = retry_tasks[:limits['workers']]
            batch(selected, limits, 'provider', retries=failed)
            retry_tasks = retry_tasks[len(selected):]
    return rows, {'fresh_compiled': completed, 'exact_receipts_resumed': resumed,
                  'provider_light_attempts': light_attempts, 'provider_memory_retries': memory_retries}

def checked_root(graph, state, runtime, env, constant, require, name, timeout):
    """Fresh exact statement/assumptions check followed by FULL recursive coqchk."""
    report = graph.tree / REPORT_PATH
    report.mkdir(parents=True, exist_ok=True)
    source = report / (name + '.v')
    expected_source = selected_statement_check(graph, constant, require)
    source.write_text(expected_source)
    flags = [*graph.flags, '-Q', REPORT_PATH, REPORT_NS]
    limits = phase_limits('assembly', 1, profiles=graph.profiles)
    audit_budget = audit_limits(graph, env, limits)
    compile_log = state / (name + '-compile.log')
    audit_log = state / (name + '-coqchk.log')
    audit_log.unlink(missing_ok=True)
    run_capped([runtime['binaries']['coqc']['path'], *FLAGS, *flags,
                str(source.relative_to(graph.tree))], graph.tree, env, compile_log, limits, timeout)
    assumptions = parse_assumptions(compile_log.read_text())
    audit_env = audit_environment(env)
    trace = env.get('STATE24_COQCHK_TRACE') == '1'
    verbosity = [] if trace else ['-silent']
    policy = {'status': 'policy recorded before audit; no proof credit',
              'verification_mode': 'full-recursive', 'trace_enabled': trace,
              'ocamlrunparam': audit_env['OCAMLRUNPARAM'],
              'address_space_bytes': audit_budget['address_space_bytes'],
              'rss_guard_bytes': audit_budget['rss_guard_bytes'], 'timeout_seconds': timeout,
              'requested_rss_gib': env.get('STATE24_AUDIT_RSS_GIB')}
    archive_results(state, [name + '-audit-policy.json', name + '-audit-failure.json'])
    write_json(state / (name + '-audit-policy.json'), policy)
    print(json.dumps({'phase': 'audit', 'mode': 'full-recursive',
        'root': REPORT_NS + '.' + name, 'workers': 1,
        'ocamlrunparam': audit_env['OCAMLRUNPARAM'],
        'rss_guard_mib': audit_budget['rss_guard_bytes'] // (1024 * 1024)}), flush=True)
    started = time.monotonic()
    try:
        result = run_capped([runtime['binaries']['coqchk']['path'], *verbosity, '-bytecode-compiler',
                            'yes', *flags, REPORT_NS + '.' + name], graph.tree, audit_env,
                           audit_log, audit_budget, timeout)
    except (OSError, ValueError, RuntimeError) as error:
        write_json(state / (name + '-audit-failure.json'), {
            **policy, 'status': 'audit failed; no proof credit', 'error': str(error),
            'elapsed_seconds': round(time.monotonic() - started, 3),
            'audit_log_sha256': sha(audit_log) if audit_log.is_file() else None})
        raise
    result = {**result, 'ocamlrunparam': audit_env['OCAMLRUNPARAM'], 'trace_enabled': trace}
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
        if 'STATE24_AUDIT_RSS_GIB' in env:
            audit_limits(graph, env)  # Reject an unfit override before source compilation.
        runtime = runtime_snapshot(env)
        require_native_compiler(runtime)
        identity = {'manifest_sha256': graph.digest, 'runtime_sha256': canonical(runtime),
                    'implementation': implementation_pins(), 'tree': str(graph.tree)}
        initial = state / 'build-identity.json'
        if args.resume:
            resume_identity(state, identity, args.provider_light)
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
                                     args.command_timeout, args.disk_reserve_gib, args.provider_light)
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
    parser.add_argument('--provider-light', action='store_true',
                        help='Try providers with the ordinary worker budget; retry memory-limited files at their original provider budget')
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
