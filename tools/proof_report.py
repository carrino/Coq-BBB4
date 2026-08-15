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
    BBB4_value : BBB4_statement (the claim of BBB4_Spec.v), from
    BBB4_Value.v;
  * residue non-empty (historical / if rows are ever re-opened): the old
    skipped-machine listing around bbb4_target.
"""

import os
import subprocess
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
The claim (theories/BBB4_Spec.v; model in BBB4_Statement.v):

  Attains tm B   :=  exists q s,  QuietAfter tm q s  /\\  S s = B
  BBB4_is B      :=  (exists tm, Attains tm B)                    (* ATTAINED *)
                     /\\ (forall tm B', Attains tm B' -> B' <= B)  (* MAXIMAL  *)
  BBB4_statement :=  BBB4_is champion_score    (champion_score = {score:,})

The proof (theories/Closeout/BBB4_Value.v):

  BBB4_value : BBB4_statement

  * LOWER: the champion {champ} ([tm_champion])
    attains exactly {score:,} -- [StD]'s last visit is at index
    {prev:,}, pinned by two binary-fuel vm_computes
    ([champion_attains]).
  * UPPER: every (4,2) machine quasihalts with every quiet state quiet
    before index {score:,}, or never quasihalts
    ([bbb4_unconditional]; the residue lists are EMPTY).

Axiom footprint: functional_extensionality_dep, and nothing else
([Print Assumptions BBB4_value] above; [BBB4_is_unique] is axiom-free
and pins the number).  {tier}
'''.format(score=CHAMPION_SCORE, prev=CHAMPION_SCORE - 1, champ=CHAMPION,
           tier=trust_tier()))
    print(LINE)


def trust_tier():
    """Which trust rung did THIS build stand on?

    The line here used to be the static "this build LOADED the committed
    census .vo", which is right for `make proof' and flatly wrong after
    `make proof-all' -- and proof-all printed both claims, three lines
    apart, with this one looking the more authoritative.

    Decided from evidence rather than from a flag the caller passes:
    census_probes/walk-stamp holds the census input hash that was WALKED
    on this machine (Makefile, _census-prepare).  If it matches the
    current inputs, these .vo are this machine's walk output, whoever
    started it.  If it is absent or stale, they came from the commit.
    """
    try:
        here = os.path.dirname(os.path.abspath(__file__))
        stamp = os.path.join(here, os.pardir, 'census_probes', 'walk-stamp')
        with open(stamp) as f:
            walked = f.read().strip()
        cur = subprocess.run(
            [sys.executable, os.path.join(here, 'census_cache.py'),
             '--print-hash'], capture_output=True, text=True, timeout=300)
        if cur.returncode == 0 and walked and walked == cur.stdout.strip():
            return ('Trust tier: the census .vo loaded here were WALKED on '
                    'this\nmachine from source -- census_probes/walk-stamp '
                    'matches these inputs.\nNothing committed was trusted; '
                    'coqchk -o re-verifies the proof terms.')
    except Exception:
        pass
    return ('Trust tier: this build LOADED the committed\ncensus .vo -- '
            're-derive them from source with `make proof-all`\n'
            '(docs/VERIFYING.md); coqchk -o re-verifies the compiled '
            'proof terms.')


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
