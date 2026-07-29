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

    remaining = rows_of(os.path.join(ROOT, 'theories/Closeout/CoreRows.v'),
                        'remaining_rows')
    shadow = rows_of(os.path.join(ROOT, 'theories/Closeout/SH_00.v'),
                     'shrows_00')
    proven = []
    for i in range(1000):
        stage = os.path.join(ROOT, 'theories/Closeout/CB_%02d.v' % i)
        if not os.path.exists(stage):
            break
        proven += rows_of(stage, 'cbrows_%02d' % i)

    pset, rset, sset = set(proven), set(remaining), set(shadow)
    bad = []
    if len(proven) != len(pset):
        bad.append('proven table has %d duplicate rows' % (len(proven) - len(pset)))
    if len(remaining) != len(rset):
        bad.append('core table has %d duplicate rows' % (len(remaining) - len(rset)))
    if len(shadow) != len(sset):
        bad.append('shadow table has %d duplicate rows' % (len(shadow) - len(sset)))
    for nm, s in (('proven', pset), ('core', rset), ('shadow', sset)):
        inv = s - fset
        if inv:
            bad.append('%d %s rows are NOT on the frozen list (e.g. %s)'
                       % (len(inv), nm, sorted(inv)[0]))
    for a, b_, nm in ((pset, rset, 'proven+core'), (pset, sset, 'proven+shadow'),
                      (rset, sset, 'core+shadow')):
        both = a & b_
        if both:
            bad.append('%d rows appear in BOTH %s tables (e.g. %s)'
                       % (len(both), nm, sorted(both)[0]))
    missed = fset - pset - rset - sset
    if missed:
        bad.append('%d frozen rows in NO table (e.g. %s)'
                   % (len(missed), sorted(missed)[0]))

    # the shadow relation itself, re-derived independently of the emitter
    import shadowlib
    for spec in sorted(sset):
        m = shadowlib.parse(spec)
        qt = shadowlib.qstar(m)
        if qt is None:
            bad.append('shadow row %s has no blank prefix' % spec)
            continue
        base = shadowlib.swap_uv(m, 'A', qt[0])
        ok = any(shadowlib.le(shadowlib.parse(p), shadowlib.apply_ops(base, ops))
                 for ops in shadowlib._OPS_CHOICES for p in rset)
        if not ok:
            bad.append('shadow row %s: re-root not in the core orbit' % spec)

    if bad:
        print('CLOSEOUT AUDIT: FAIL')
        for b in bad:
            print('  - ' + b)
        sys.exit(1)

    pct = 100.0 * len(pset) / len(fset)
    print('CLOSEOUT AUDIT: OK')
    print('  frozen deferred rows      %5d' % len(fset))
    print('  settled by a board        %5d  (%.1f%%)' % (len(pset), pct))
    print('  core undecided (listed)   %5d' % len(rset))
    print('  0RB shadows of the core   %5d  (resolve with their core rows)'
          % len(sset))
    print('  tables partition the frozen list exactly; no invented or duplicate rows;')
    print('  every shadow re-root independently re-verified in the core orbit')


if __name__ == '__main__':
    main()
