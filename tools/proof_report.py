#!/usr/bin/env python3
"""The `make proof' report: state the top-level BBB(4) theorem and list the
skipped residue machines.

REPORTING ONLY.  Nothing here carries proof weight: the Coq kernel certified
theories/Closeout/BBB4_Theorem.v before this script runs, and the residue
list it prints is the same table (tools/closeout/frozen_unproven.txt) whose
rows are baked into the theorem's [remaining_rows] literal.  The script
cross-checks the two counts and fails loudly on any mismatch."""

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
UNPROVEN = os.path.join(ROOT, 'tools', 'closeout', 'frozen_unproven.txt')
THEOREM_V = os.path.join(ROOT, 'theories', 'Closeout', 'BBB4_Theorem.v')

CHAMPION = '1RB1LD_1RC1RB_1LC1LA_0RC0RD'
CHAMPION_SCORE = 32779478


def main():
    residue = [l.strip() for l in open(UNPROVEN) if l.strip()]

    # The count the kernel actually checked: remaining_rows' length is fixed
    # at generation time and quoted in the theorem file's header.
    txt = open(THEOREM_V).read()
    m = re.search(r'(\d+) SKIPPED residue machines', txt)
    if not m:
        sys.exit('proof_report: cannot find the residue count in %s'
                 % THEOREM_V)
    if int(m.group(1)) != len(residue):
        sys.exit('proof_report: MISMATCH -- %s says %s residue machines, '
                 'but %s lists %d.  Re-run `make closeout`.'
                 % (THEOREM_V, m.group(1), UNPROVEN, len(residue)))
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
    QHBound {score:,} tm \\/ NeverQuasiHaltsSt tm \\/ Deferred D_remaining tm

Every (4,2) Turing machine either

  * QUASIHALTS with every eventually-quiet state quiet before index
    {score:,} -- i.e. its BBB score is at most the champion's -- or
  * NEVER QUASIHALTS,

EXCEPT the {n} residue machines listed below, which are still undecided
and are SKIPPED by the theorem (the [Deferred D_remaining] disjunct).

The champion {champ} is itself one of the skipped
machines (its 32.8M-step prefix has no certificate yet), so this is NOT
a proof that BBB(4) = {score:,}.  The precise scope of the claim is
docs/CLAIMS.md; the residue, mapped by shape and blocker, is
docs/RESIDUE_MAP.md.

Sharper, in previous-record terms:

  bbb4_decided_le_prev_champion : forall tm,
    ~ Deferred D_remaining tm ->
    QHBound 66349 tm \\/ NeverQuasiHaltsSt tm

-- every machine NOT in the skipped list quasihalts by the PREVIOUS
champion's score, 66,349, or never quasihalts.  The four previous
champions (scores 2,512..66,349) are among the decided, so among all
known (4,2) machines, only the current champion exceeds the previous
record.

Axiom footprint: functional_extensionality_dep, and nothing else
(printed by Print Assumptions during the build above; independently
checkable with coqchk -o).
'''.format(score=CHAMPION_SCORE, n=len(residue), champ=CHAMPION))
    print('SKIPPED -- the %d undecided residue machines' % len(residue))
    print('(tools/closeout/frozen_unproven.txt):')
    print()
    for i in range(0, len(residue), 2):
        print('  ' + '  '.join(residue[i:i + 2]))
    print()
    print(line)


if __name__ == '__main__':
    try:
        main()
    except BrokenPipeError:
        sys.exit(0)
