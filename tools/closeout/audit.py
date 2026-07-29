#!/usr/bin/env python3
"""Audit the generated closeout tables against the frozen deferred list.

The Coq kernel already guarantees SOUNDNESS of [closeout_partial]: the split
check is a [vm_compute]d [forallb] over [deferred_rows], and every [covers]
proof is re-checked against the board theorem.  What the kernel does NOT
police is whether the tables say what we CLAIM they say -- a [remaining_rows]
padded with rows that are not on the frozen list, or that double-lists a
machine already proven, would still yield a true theorem while making the
"1,589 remaining" headline wrong.

This script re-parses the two generated tables back into machine strings and
checks the claim:

  proven_rows  \\subseteq frozen        (no invented rows)
  remaining_rows \\subseteq frozen      (no invented rows)
  proven_rows  \\cap remaining_rows = 0 (no double-listing)
  proven_rows  \\cup remaining_rows = frozen  (nothing dropped)
  no duplicates within either table

Exit 0 + a one-line scoreboard iff every check passes.
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if not os.path.isdir(os.path.join(ROOT, 'theories')):
    ROOT = '/home/user/Coq-BBB4'
SHORT_RE = re.compile(r'^\s*\[(t[0-9A-Za-z;]+)\](?:;)?\s*$')


def rows_of(path, defname):
    """Parse `Definition <defname> ... := [ [tXXX;...]; ... ].` into specs."""
    txt = open(path).read()
    m = re.search(r'Definition\s+%s\b.*?:=\s*(.*?)\n\]\.' % re.escape(defname),
                  txt, re.S)
    if not m:
        raise SystemExit('audit: cannot find table %s in %s' % (defname, path))
    body = m.group(1)
    specs = []
    for line in body.splitlines():
        mm = SHORT_RE.match(line)
        if not mm:
            continue
        toks = mm.group(1).split(';')
        if len(toks) != 8:
            raise SystemExit('audit: bad row arity in %s: %r' % (defname, line))
        out = []
        for t in toks:
            assert t.startswith('t'), t
            out.append('---' if t == 'tN' else t[1:])
        specs.append('_'.join(out[i] + out[i + 1] for i in (0, 2, 4, 6)))
    return specs


def main():
    frozen = [l.strip() for l in
              open(os.path.join(ROOT, 'tools/census_residue.txt'))] + \
             [l.strip() for l in
              open(os.path.join(ROOT, 'tools/census_holdouts_kept.txt'))]
    frozen = [f for f in frozen if f]
    fset = set(frozen)

    co = os.path.join(ROOT, 'theories/Closeout/Closeout.v')
    remaining = rows_of(co, 'remaining_rows')
    proven = []
    for i in range(1000):
        stage = os.path.join(ROOT, 'theories/Closeout/CB_%02d.v' % i)
        if not os.path.exists(stage):
            break
        proven += rows_of(stage, 'cbrows_%02d' % i)

    pset, rset = set(proven), set(remaining)
    bad = []
    if len(proven) != len(pset):
        bad.append('proven table has %d duplicate rows' % (len(proven) - len(pset)))
    if len(remaining) != len(rset):
        bad.append('remaining table has %d duplicate rows' % (len(remaining) - len(rset)))
    inv_p, inv_r = pset - fset, rset - fset
    if inv_p:
        bad.append('%d proven rows are NOT on the frozen list (e.g. %s)'
                   % (len(inv_p), sorted(inv_p)[0]))
    if inv_r:
        bad.append('%d remaining rows are NOT on the frozen list (e.g. %s)'
                   % (len(inv_r), sorted(inv_r)[0]))
    both = pset & rset
    if both:
        bad.append('%d rows appear in BOTH tables (e.g. %s)'
                   % (len(both), sorted(both)[0]))
    missed = fset - pset - rset
    if missed:
        bad.append('%d frozen rows in NEITHER table (e.g. %s)'
                   % (len(missed), sorted(missed)[0]))

    if bad:
        print('CLOSEOUT AUDIT: FAIL')
        for b in bad:
            print('  - ' + b)
        sys.exit(1)

    pct = 100.0 * len(pset) / len(fset)
    print('CLOSEOUT AUDIT: OK')
    print('  frozen deferred rows      %5d' % len(fset))
    print('  settled by a board        %5d  (%.1f%%)' % (len(pset), pct))
    print('  remaining (D_remaining)   %5d' % len(rset))
    print('  tables partition the frozen list exactly; no invented or duplicate rows')


if __name__ == '__main__':
    main()
