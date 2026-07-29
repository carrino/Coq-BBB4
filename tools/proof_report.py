#!/usr/bin/env python3
"""The `make proof' report: state the top-level BBB(4) theorem, the skipped
core machines, and their 0RB re-root shadows.

REPORTING ONLY.  Nothing here carries proof weight: the Coq kernel certified
theories/Closeout/BBB4_Theorem.v before this script runs, and the lists it
prints are the same tables (tools/closeout/core_rows.txt, shadow_rows.tsv)
whose rows are baked into the kernel-checked [remaining_rows]/[shrows_00]
literals.  The script cross-checks the counts and fails loudly on mismatch."""

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CORE = os.path.join(ROOT, 'tools', 'closeout', 'core_rows.txt')
SHADOWS = os.path.join(ROOT, 'tools', 'closeout', 'shadow_rows.tsv')
THEOREM_V = os.path.join(ROOT, 'theories', 'Closeout', 'BBB4_Theorem.v')

CHAMPION = '1RB1LD_1RC1RB_1LC1LA_0RC0RD'
CHAMPION_SCORE = 32779478


def main():
    core = [l.strip() for l in open(CORE) if l.strip()]
    shadows = [l.rstrip('\n').split('\t')
               for l in open(SHADOWS).read().splitlines()[1:] if l.strip()]

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

    line = '=' * 72
    print(line)
    print('BBB(4) TOP-LEVEL RESULT -- kernel-checked (Coq 8.18)')
    print(line)
    print('''
theories/Closeout/BBB4_Theorem.v:

  bbb4_target : forall tm,
    QHBound {score:,} tm \\/ NeverQuasiHaltsSt tm \\/ skipped D_remaining tm

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

The champion {champ} is itself one of the core
machines (its 32.8M-step prefix has no certificate yet), so this is NOT
a proof that BBB(4) = {score:,}.  The precise scope of the claim is
docs/CLAIMS.md; the core machines, mapped by shape and blocker, are
docs/RESIDUE_MAP.md.

Sharper, in previous-record terms:

  bbb4_decided_le_prev_champion : forall tm,
    ~ skipped D_remaining tm ->
    QHBound 66349 tm \\/ NeverQuasiHaltsSt tm

-- every machine NOT skipped quasihalts by the PREVIOUS champion's
score, 66,349, or never quasihalts.  The four previous champions
(scores 2,512..66,349) are among the decided, so among all known
(4,2) machines, only the current champion exceeds the previous record.

Axiom footprint: functional_extensionality_dep, and nothing else
(printed by Print Assumptions during the build above; independently
checkable with coqchk -o).
'''.format(score=CHAMPION_SCORE, n=len(core), s=len(shadows), champ=CHAMPION))
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
    print(line)


if __name__ == '__main__':
    try:
        main()
    except BrokenPipeError:
        sys.exit(0)
