#!/usr/bin/env python3
"""Replay instruction observations with the existing audited batch supervisor.

The state runner stays byte-for-byte unchanged. This adapter supplies a separate
Coq checker, namespace and input specification, and binds its own source into
the supervisor's dependency identity before any receipt can be reused.
"""
from pathlib import Path
import sys

import replay_observations as supervisor

MODE = 'instruction'
TAIL_INVARIANT = 'total-state-mask-with-both-symbols-observed'
NAMESPACE = 'BBBWait42InstructionObservation'
HEADER = '''From Coq Require Import List Bool NArith.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import Deferred_Defs TNF_QH.
From BBBWait42 Require Import Spec FiniteInstructionObservation.
Import ListNotations.
'''


def render_part(rows, cutoff, upper_width):
    text = HEADER + '''Record entry := Entry {
 source_index:N; pointer:nat; proof_case:instruction_observation_case }.
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
                        f'(mkInstructionObservationCase (row_to_tm [{table}]) (mask {bits}) {row["width"]}%N)')
    text += 'Definition entries : list entry := [\n' + ';\n'.join(literals) + '\n].\n'
    text += '''Definition cases := map proof_case entries.
Example all_checked : instruction_observation_batch_check cases cutoff upper_width = true.
Proof. native_compute. reflexivity. Qed.
Local Opaque instruction_observation_batch_check finite_instruction_observation_check.
Theorem all_completions : forall e, In e entries -> forall tm,
 TM_le (instruction_observation_machine (proof_case e)) tm ->
 WindowBoundTr tm (N.to_nat cutoff) (N.to_nat upper_width).
Proof.
 intros e Hin tm Hle.
 apply (instruction_observation_batch_completion cases cutoff upper_width all_checked (proof_case e)).
 - unfold cases. now apply in_map.
 - exact Hle.
Qed.
Goal True. idtac "OBSERVATION_ASSUMPTIONS_BEGIN". exact I. Qed.
Print Assumptions all_completions.
Goal True. idtac "OBSERVATION_ASSUMPTIONS_END". exact I. Qed.
'''
    return text.encode()


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    original_load = supervisor.load_input
    original_closure = supervisor.dependency_closure

    def load_instruction_input(path):
        spec, rows, bound = original_load(path)
        if spec.get('beep_mode') != MODE or spec.get('tail_invariant') != TAIL_INVARIANT:
            raise ValueError('instruction replay requires explicit instruction mode and total-state tail invariant')
        return spec, rows, bound

    def bound_closure(*args, **kwargs):
        files = original_closure(*args, **kwargs)
        adapter = Path(__file__).resolve()
        files[str(adapter)] = supervisor.fingerprint(adapter)
        return dict(sorted(files.items()))

    old_values = (supervisor.HEADER, supervisor.NAMESPACE, supervisor.render_part,
                  supervisor.load_input, supervisor.dependency_closure)
    try:
        supervisor.HEADER = HEADER
        supervisor.NAMESPACE = NAMESPACE
        supervisor.render_part = render_part
        supervisor.load_input = load_instruction_input
        supervisor.dependency_closure = bound_closure
        if not any(arg == '--spec' or arg.startswith('--spec=') for arg in argv):
            argv = ['--spec', str(supervisor.ROOT / 'wait42/research/instruction-observations.json'), *argv]
        return supervisor.main(argv)
    finally:
        (supervisor.HEADER, supervisor.NAMESPACE, supervisor.render_part,
         supervisor.load_input, supervisor.dependency_closure) = old_values


if __name__ == '__main__':
    raise SystemExit(main())
