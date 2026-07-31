#!/usr/bin/env python3
"""Board every row of a valfam sweep whose closure LadderCheck can state.

Reads a `valfam.py --json` sweep, keeps the rows the Stage-B closure
applies to, emits a board for each with `emit_ladder.py`, compiles it, and
adds the ones that compile to `_CoqProject`.  Then `make closeout` picks
them up: `inventory.py` already scans `theories/Machines/**/*.v` for
`Theorem _ : NeverQuasiHaltsSt _`, and a ladder board is one more file with
one more such theorem.

The filter is exactly what `LadderCheck.board_neverqh` asks for and no more
(LADDER_PLAN 4i):

  * `closed` -- the prover found a family, arms and a differential;
  * `code = binary` and `value_step_per_anchor_visit = 1` -- the class
    successor lemma is stated for that pair only;
  * every phase's fill lands in a phase the family HAS -- the closure
    carries the phase CYCLE (LADDER_PLAN 4n), so a family with more than one
    terminator is stated rather than refused, and a fill that widens by
    nothing (a lap into the next terminator at the same width) is fine;
  * the fill target names no more digits than the law widens by (plus the
    one guaranteed copy) -- the target's own prefix and suffix are fine, they
    ride along as the fixed words either side of the run;
  * `states_infinitely_often` names ABCD or exactly three of them --
    [board_neverqh] concludes `NeverQuasiHaltsSt` for the first and
    [board_iqh] the R_QH triple for the second, quiet in the missing state
    (LADDER_PLAN 4k step 2).  A row missing two or more states is neither.

Everything here is UNTRUSTED bookkeeping.  A row that passes the filter and
whose board does not compile is REPORTED, not silently dropped.

Usage:  board_ladder.py SWEEP.jsonl [--jobs N] [--dry-run]
"""
import argparse
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))


def wanted(r):
    """(True, None) if the closure applies, else (False, why not)."""
    if not r.get('closed'):
        return False, r.get('reason') or 'not closed'
    fam = r.get('family') or {}
    if fam.get('code') != 'binary':
        return False, 'code %s' % fam.get('code')
    if fam.get('value_step_per_anchor_visit', 1) != 1:
        return False, 'step %s' % fam.get('value_step_per_anchor_visit')
    fills = r.get('fill_by_phase') or [r.get('fill')]
    nph = len(fills)
    for ph, f in enumerate(fills):
        if not 0 <= f.get('lands_in_phase', 0) < nph:
            return False, ('phase %d fills into phase %d, which this family '
                           'does not have' % (ph, f.get('lands_in_phase')))
        m = len(f.get('target_prefix') or []) + len(f.get('target_suffix') or [])
        if m > 1 + f.get('widens_by', 0):
            return False, ('phase %d fill target names %d digits but widens '
                           'by %d' % (ph, m, f.get('widens_by')))
    live = (r.get('liveness') or {}).get('states_infinitely_often')
    if live not in ('ABCD', 'BCD', 'ACD', 'ABD', 'ABC'):
        return False, 'live=%s (neither closer states this)' % live
    return True, None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('sweep')
    ap.add_argument('--dry-run', action='store_true')
    ap.add_argument('--out', default=os.path.join(ROOT, 'theories/Machines/Ladder'))
    a = ap.parse_args()

    rows = [json.loads(l) for l in open(a.sweep) if l.strip()]
    keep, skip = [], []
    for r in rows:
        ok, why = wanted(r)
        (keep if ok else skip).append((r, why))

    print('sweep %s: %d rows, %d the closure applies to' %
          (a.sweep, len(rows), len(keep)))
    reasons = {}
    for _, why in skip:
        reasons[why] = reasons.get(why, 0) + 1
    for why, n in sorted(reasons.items(), key=lambda kv: -kv[1]):
        print('  skipped %4d  %s' % (n, why))
    if a.dry_run:
        for r, _ in keep:
            print('  WOULD BOARD %s' % r['spec'])
        return 0

    built, failed = [], []
    for r, _ in keep:
        spec = r['spec']
        cj = os.path.join('/tmp', 'cert_%s.json' % spec.replace('-', '_'))
        with open(cj, 'w') as f:
            json.dump(r, f)
        vf = os.path.join(a.out, 'LDR_%s.v' % spec.replace('-', '_'))
        e = subprocess.run([sys.executable, os.path.join(HERE, 'emit_ladder.py'),
                            cj, '-o', vf], capture_output=True, text=True)
        if e.returncode != 0 or 'closure BUILT' not in e.stdout:
            failed.append((spec, (e.stdout + e.stderr).strip().splitlines()[-1]
                           if (e.stdout + e.stderr).strip() else 'emit failed'))
            continue
        c = subprocess.run(['coqc', '-Q', 'theories', 'BBB4', vf],
                           cwd=ROOT, capture_output=True, text=True)
        if c.returncode != 0:
            failed.append((spec, 'coqc: ' + (c.stderr.strip().splitlines() or
                                             ['?'])[-1]))
            continue
        built.append(spec)
        print('  BOARDED %s' % spec)

    # add what compiled to _CoqProject, next to the other ladder boards
    cp = os.path.join(ROOT, '_CoqProject')
    txt = open(cp).read()
    added = 0
    for spec in built:
        line = 'theories/Machines/Ladder/LDR_%s.v\n' % spec.replace('-', '_')
        if line not in txt:
            i = txt.rindex('theories/Machines/Ladder/')
            j = txt.index('\n', i) + 1
            txt = txt[:j] + line + txt[j:]
            added += 1
    open(cp, 'w').write(txt)

    print('boarded %d, failed %d, %d added to _CoqProject'
          % (len(built), len(failed), added))
    for spec, why in failed:
        print('  FAILED %-30s %s' % (spec, why))
    return 0


if __name__ == '__main__':
    sys.exit(main())
