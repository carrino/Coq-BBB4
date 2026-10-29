"""Print the actual exact state BBB(2,4) claim only after a full kernel audit.

The selected-graph mode checks compile receipts and bindings, then builds a fresh
report root and runs full recursive coqchk. No cached-closure shortcut is offered.
The existing base-project source preflight and negative checks are preserved.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import shlex
import subprocess
import sys

from proof24_common import (CORE_PINS, FE, Graph, TARGET, THEOREM, VALUE, canonical,
    archive_results, clean_environment, exclusive_build_locks, parse_assumptions, runtime_snapshot, sha,
    selected_statement_check, statement_check, write_json)

FOUR = Path(__file__).resolve().parents[1]


def banner(output, location):
    print('=' * 72)
    print(f'BBB(2,4) = {TARGET} -- state based, kernel checked')
    print(f'{THEOREM} : BBB24.ValueSpec.BBB24_state_statement')
    print('The champion attains this score, and every two-state, four-symbol '
          'machine satisfies the upper bound.')
    print(output.rstrip())
    print('Full recursive coqchk: passed. Logs: ' + str(location))
    print('=' * 72)


def selected_report(graph, state, runtime, env, timeout):
    # Build imports the reporter only after its helpers have been initialized.
    from build_state_value import (REPORT_PATH, alias_source, checked_root,
                                   implementation_pins, verify_receipts)
    runtime_digest = canonical(runtime)
    archive_results(state, ['state-value-result.json'])
    identity = json.loads((state / 'build-identity.json').read_text())
    expected_identity = {'manifest_sha256': graph.digest, 'runtime_sha256': runtime_digest,
                         'implementation': implementation_pins(), 'tree': str(graph.tree)}
    if identity != expected_identity:
        raise ValueError('Reporter build identity differs from current selected inputs')
    graph.verify_sources()
    graph.verify_no_unselected(allow_value=True)
    rows = verify_receipts(graph, state, runtime_digest)
    value = graph.tree / VALUE
    if value.read_text() != alias_source(graph):
        raise ValueError('Value.v is not the audited final theorem alias')
    gate_path = state / 'final-gate.json'
    gate = json.loads(gate_path.read_text())
    if (gate.get('mode') != 'full-recursive'
            or gate.get('audit_execution', {}).get('exit_code') != 0
            or gate.get('manifest_sha256') != graph.digest
            or gate.get('runtime_sha256') != runtime_digest
            or gate.get('closure_receipts_sha256') != canonical(rows)
            or gate.get('assumptions') not in ([], [FE])):
        raise ValueError('Missing/current final-theorem recursive audit gate')
    report = graph.tree / REPORT_PATH
    if (report / 'CheckFinal.v').read_text() != selected_statement_check(
            graph, graph.final_constant, graph.final_constant.rsplit('.', 1)[0]):
        raise ValueError('Final gate is not the exact expected statement check')
    for key, path in [('source_sha256', report / 'CheckFinal.v'),
                      ('object_sha256', report / 'CheckFinal.vo'),
                      ('compile_log_sha256', state / 'CheckFinal-compile.log'),
                      ('audit_log_sha256', state / 'CheckFinal-coqchk.log')]:
        if gate[key] != sha(path):
            raise ValueError('Final audit receipt no longer matches: ' + str(path))
    alias = json.loads((state / 'value-alias.json').read_text())
    if (alias != {'source_sha256': sha(value), 'object_sha256': sha(value.with_suffix('.vo')),
                  'final_gate_sha256': sha(gate_path), 'manifest_sha256': graph.digest,
                  'runtime_sha256': runtime_digest}):
        raise ValueError('Stale Value alias receipt')
    current = checked_root(graph, state, runtime, env, THEOREM, 'BBB24.Value', 'CheckValue', timeout)
    # Recheck everything after the actual report audit, before any success banner.
    graph.verify_sources()
    verify_receipts(graph, state, runtime_digest)
    if sha(value) != alias['source_sha256'] or sha(value.with_suffix('.vo')) != alias['object_sha256']:
        raise ValueError('Value source/object changed during report audit')
    if canonical(runtime_snapshot(env)) != runtime_digest:
        raise ValueError('Coq runtime changed during report audit')
    output = (state / 'CheckValue-compile.log').read_text()
    parse_assumptions(output)
    write_json(state / 'state-value-result.json', {'status': 'PASSED',
        'score_decimal': str(TARGET), 'convention': 'state-based; last configuration index plus one',
        'theorem': THEOREM, 'type': 'BBB24.ValueSpec.BBB24_state_statement',
        'manifest_sha256': graph.digest, 'runtime_sha256': runtime_digest,
        'actual_assumptions': current['assumptions'], 'kernel_verification': current,
        'verification_scope': 'fresh full recursive coqchk on BBB24ValueReport.CheckValue; no -admit/-norec flags'})
    banner(output, state)


def legacy_report(four):
    """Existing base-project path. Hundreds of generated paths require selected mode."""
    tokens = shlex.split((four / '_CoqProject').read_text(), comments=True)
    flags, bindings = [], {}
    i = 0
    while i < len(tokens):
        token = tokens[i]
        if token in ('-R', '-I'):
            raise ValueError('Use a reviewed selected manifest for extra load paths')
        if token == '-Q':
            if i + 2 >= len(tokens):
                raise ValueError('Truncated project -Q binding')
            physical, namespace = tokens[i + 1:i + 3]
            expected = {'BBB24': four / 'theories', 'SmallBB': four.parent / 'small/theories'}
            if namespace in bindings or namespace not in expected or (four / physical).resolve() != expected[namespace].resolve():
                raise ValueError('Untrusted base-project mapping; use selected graph mode')
            bindings[namespace] = physical
            flags.extend(tokens[i:i + 3])
            i += 3
        else:
            i += 1
    if 'BBB24' not in bindings:
        raise ValueError('Missing trusted BBB24 model binding')
    # These are fixed project source pins. A reviewed model change must explicitly
    # update this allowlist; arbitrary project remapping cannot redefine the claim.
    for source, expected in CORE_PINS.items():
        if sha(four.parent / source) != expected:
            raise ValueError('Untrusted machine model/claim source: ' + source)
    build = four / 'build/state-value-report'
    build.mkdir(parents=True, exist_ok=True)
    source = build / 'CheckValue.v'
    source.write_text(statement_check(THEOREM, 'BBB24.Value'))
    flags.extend(['-Q', str(build), 'BBB24ValueReport'])
    compile_log = build / 'compile.log'
    audit_log = build / 'coqchk.log'
    # A failed current compile must not leave a stale success log visible.
    audit_log.unlink(missing_ok=True)
    env = clean_environment()
    # Pinning source files alone cannot bind already-existing core objects to
    # the intended model. Refresh these four small trusted modules so a stale
    # Value object from a different model fails Coq's import consistency check.
    for model_source in CORE_PINS:
        source_path = four.parent / model_source
        with (build / (source_path.stem + '-compile.log')).open('w') as stream:
            subprocess.run(['coqc', '-q', '-noglob', '-native-compiler', 'no', *flags, str(source_path)],
                           cwd=four, env=env, stdout=stream, stderr=subprocess.STDOUT, check=True)
    with compile_log.open('w') as stream:
        subprocess.run(['coqc', '-q', '-noglob', '-native-compiler', 'no', *flags, str(source)],
                       cwd=four, env=env, stdout=stream, stderr=subprocess.STDOUT, check=True)
    output = compile_log.read_text()
    parse_assumptions(output)
    with audit_log.open('w') as stream:
        subprocess.run(['coqchk', '-silent', '-bytecode-compiler', 'yes', *flags,
                        'BBB24ValueReport.CheckValue'], cwd=four, env=env, stdout=stream,
                       stderr=subprocess.STDOUT, check=True)
    banner(output, build)
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-source', action='store_true')
    parser.add_argument('--four', type=Path, default=FOUR)
    parser.add_argument('--tree', type=Path)
    parser.add_argument('--manifest', type=Path)
    parser.add_argument('--manifest-sha256')
    parser.add_argument('--state', type=Path)
    parser.add_argument('--audit-timeout', type=int, default=24 * 3600)
    args = parser.parse_args()
    selected = (args.tree, args.manifest, args.manifest_sha256, args.state)
    if any(selected):
        if not all(selected):
            raise ValueError('Selected report requires --tree --manifest --manifest-sha256 --state')
        graph = Graph(args.tree, args.manifest, args.manifest_sha256, allow_value=True)
        if args.check_source:
            graph.verify_sources()
            from build_state_value import alias_source
            if not (graph.tree / VALUE).is_file() or (graph.tree / VALUE).read_text() != alias_source(graph):
                raise ValueError('Missing audited final Value.v alias; run the selected full build')
            return 0
        from proof24_resources import check_disk
        state = args.state.resolve(strict=True)
        if state.is_relative_to(graph.tree):
            raise ValueError('Reporter state/logs must be outside selected source tree')
        check_disk(state, 1)
        with exclusive_build_locks(graph.tree, state):
            env = clean_environment()
            selected_report(graph, state, runtime_snapshot(env), env, args.audit_timeout)
        return 0
    four = args.four.resolve(strict=True)
    if not (four / 'theories/Value.v').is_file():
        print(f'BBB(2,4) = {TARGET}: the final global equality theorem is not assembled.', file=sys.stderr)
        print('Missing four/theories/Value.v. Use make proof-2-4-checkpoint to audit '
              'the current partial development.', file=sys.stderr)
        return 2
    if args.check_source:
        return 0
    return legacy_report(four)


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(2)
