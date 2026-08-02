#!/usr/bin/env python3
"""The `make proof' report: state the top-level BBB(4) result.

REPORTING ONLY.  Nothing here carries proof weight: the Coq kernel certified
theories/Closeout/BBB4_Theorem.v and BBB4_Value.v before this script runs,
and the lists it prints are the same tables (tools/closeout/core_rows.txt,
shadow_rows.tsv) whose rows are baked into the kernel-checked
[remaining_rows]/[shrows_00] literals.  The script cross-checks the counts
and fails loudly on mismatch.

Two shapes:
  * residue EMPTY (the 2026-08-01 state): headline the value theorem,
    BBB4_value : BBB4_is 32779478, from BBB4_Value.v;
  * residue non-empty (historical / if rows are ever re-opened): the old
    skipped-machine listing around bbb4_target.
"""

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CORE = os.path.join(ROOT, 'tools', 'closeout', 'core_rows.txt')
SHADOWS = os.path.join(ROOT, 'tools', 'closeout', 'shadow_rows.tsv')
THEOREM_V = os.path.join(ROOT, 'theories', 'Closeout', 'BBB4_Theorem.v')
VALUE_V = os.path.join(ROOT, 'theories', 'Closeout', 'BBB4_Value.v')
VALUE_VO = VALUE_V + 'o'

CHAMPION = '1RB1LD_1RC1RB_1LC1LA_0RC0RD'
CHAMPION_SCORE = 32779478

LINE = '=' * 72


def crosscheck(core, shadows):
    txt = open(THEOREM_V).read()
    m = re.search(r'the (\d+) distinct undecided', txt)
    if not m or int(m.group(1)) != len(core):
        sys.exit('proof_report: core count mismatch between %s and %s.  '
                 'Re-run `make closeout`.' % (THEOREM_V, CORE))
    m = re.search(r'(\d+) 0RB re-root shadows', txt)
    if not m or int(m.group(1)) != len(shadows):
        sys.exit('proof_report: shadow count mismatch between %s and %s.  '
                 'Re-run `make closeout`.' % (THEOREM_V, SHADOWS))
    if '{:,}'.format(CHAMPION_SCORE) not in txt:
        sys.exit('proof_report: champion score %d not found in %s'
                 % (CHAMPION_SCORE, THEOREM_V))


def report_value():
    if not os.path.exists(VALUE_V):
        sys.exit('proof_report: residue is empty but %s is missing -- '
                 'the value theorem is not in the tree.' % VALUE_V)
    if '{:,}'.format(CHAMPION_SCORE) not in open(VALUE_V).read():
        sys.exit('proof_report: champion score %d not found in %s'
                 % (CHAMPION_SCORE, VALUE_V))
    if not os.path.exists(VALUE_VO):
        # `make proof` compiles BBB4_Value.v on the line before this report
        # runs, so a missing .vo here means the report is being run outside
        # `make proof` (e.g. the CI smoke test, which has no census switch).
        print('proof_report: NOTE: %s not compiled in this checkout -- '
              'the report states the tree\'s claim; run `make proof` to '
              'kernel-check it here.' % os.path.relpath(VALUE_VO, ROOT))
    print(LINE)
    print('BBB(4) = {score:,} -- kernel-checked (Coq 8.18)'.format(
        score=CHAMPION_SCORE))
    print(LINE)
    print('''
theories/Closeout/BBB4_Value.v:

  BBB4_value : BBB4_is {score}

where [BBB4_is B] is the state-level Beeping Busy Beaver value spec --

  ATTAINED:  exists tm q s,  QuietAfter tm q s  /\\  S s = B
  MAXIMAL:   forall tm,      QHBound B tm

-- some state of some (4,2) machine makes its last visit at
configuration index B-1 (harness score exactly B), and no state of any
(4,2) machine is ever quiet after a later index.  [BBB4_is_unique]
confirms the spec pins a single number.  Unfolded:

  * UPPER: every (4,2) Turing machine either quasihalts with every
    eventually-quiet state quiet before index {score:,}, or never
    quasihalts (bbb4_unconditional; the residue lists are EMPTY and
    [not_skipped_nil] discharges the last disjunct of bbb4_target).
  * LOWER: the champion {champ}
    quasihalts with [StD]'s last visit at index {prev:,} -- score
    exactly {score:,}, kernel-checked by a second binary-fuel
    vm_compute (Machines/Counters/Champion_*.v, [champion_attains]).

Sharper, in previous-record terms (BBB4_Theorem.v):

  bbb4_decided_le_prev_champion_or_champion : forall tm,
    ~ skipped D_remaining tm ->
    QHBound 66349 tm \\/ NeverQuasiHaltsSt tm \\/ QHBound {score} tm

-- and the hypothesis is now discharged for every machine: each one
quasihalts by the PREVIOUS champion's 66,349, or never quasihalts, or
quasihalts by the champion's {score:,}.  Exactly one census row is in
the third case: the champion and its orbit (the single `iqhch' line of
tools/closeout/frozen_map.tsv; that count is untrusted bookkeeping).

Axiom footprint: functional_extensionality_dep, and nothing else
(printed by Print Assumptions during the build above; independently
checkable with coqchk -o).  Trust tier: this build LOADED the committed
census .vo -- re-derive them from source with `make census-verify` to
remove that trust (docs/VERIFYING.md).
'''.format(score=CHAMPION_SCORE, prev=CHAMPION_SCORE - 1, champ=CHAMPION))
    print(LINE)


def report_skipped(core, shadows):
    print(LINE)
    print('BBB(4) TOP-LEVEL RESULT -- kernel-checked (Coq 8.18)')
    print(LINE)
    print('''
theories/Closeout/BBB4_Theorem.v:

  bbb4_target : forall tm,
    QHBound {score} tm \\/ NeverQuasiHaltsSt tm \\/ skipped D_remaining tm

Every (4,2) Turing machine either

  * QUASIHALTS with every eventually-quiet state quiet before index
    {score:,} -- i.e. its BBB score is at most the champion's -- or
  * NEVER QUASIHALTS,

EXCEPT the machines the theorem SKIPS: the {n} still-undecided CORE
machines listed below, plus {s} SHADOWS -- 0RB machines whose all-blank
prefix re-roots them into the orbit of a core machine ([skipped]'s
second disjunct, Closeout/ShadowKit.v).  A shadow is not a separate
problem: it resolves automatically the moment its core machine is
boarded.

This is NOT a proof that BBB(4) = {score:,} while any core machine
remains skipped; the value follows when the list below is empty.  The
precise scope of the claim is docs/CLAIMS.md; the core machines, mapped
by shape and blocker, are docs/RESIDUE_MAP.md.

Axiom footprint: functional_extensionality_dep, and nothing else.
'''.format(score=CHAMPION_SCORE, n=len(core), s=len(shadows)))
    print('SKIPPED -- the %d undecided core machines' % len(core))
    print('(tools/closeout/core_rows.txt):')
    print()
    for mach in core:
        print('  ' + mach)
    print()
    print('(Plus %d SHADOWS -- 0RB re-roots of core machines, skipped with'
          % len(shadows))
    print(' them and resolved with them; the full machine ~> partner map is')
    print(' tools/closeout/shadow_rows.tsv.)')
    print()
    print(LINE)


def main():
    core = [l.strip() for l in open(CORE) if l.strip()]
    shadows = [l.rstrip('\n').split('\t')
               for l in open(SHADOWS).read().splitlines()[1:] if l.strip()]
    crosscheck(core, shadows)
    if not core and not shadows:
        report_value()
    else:
        report_skipped(core, shadows)


if __name__ == '__main__':
    try:
        main()
    except BrokenPipeError:
        sys.exit(0)
