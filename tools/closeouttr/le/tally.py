#!/usr/bin/env python3
"""LE: the counts of SCOPING_INSTR 7.4.LE, from the committed files.

    python3 tools/closeouttr/le/tally.py [MEASURE.tsv ...]

Rows: tools/closeouttr/le/rows_{dn,sp,qh}.txt (the LE rows at the start).
Boarded: closeouttr_boarded.tsv rows whose batch is CBT_LE_*.  Finder
verdicts: vf_ce3.jsonl (CE3's valfam run) and vf_*.jsonl (this run), plus
famclose's fc_*.jsonl.  A measure.py output, if given, adds the emitter's
reason for every row the finder closed and LE did not board.
"""
import collections
import glob
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..', '..'))


def main():
    rows = {}
    for k in ('dn', 'sp', 'qh'):
        for l in open(os.path.join(HERE, 'rows_%s.txt' % k)):
            if l.strip():
                rows[l.strip()] = k.upper()
    boarded = {}
    for l in open(os.path.join(REPO, 'closeouttr_boarded.tsv')):
        f = l.rstrip('\n').split('\t')
        if len(f) >= 2 and f[0] in rows:
            boarded[f[0]] = f[1]
    rem = set(l.strip() for l in open(os.path.join(REPO, 'closeouttr_remaining.txt')))
    vf = {}
    for p in [os.path.join(HERE, 'vf_ce3.jsonl')] + sorted(glob.glob(os.path.join(HERE, 'vf_[0-9].jsonl'))) \
            + sorted(glob.glob(os.path.join(HERE, 'fc_*.jsonl'))):
        for l in open(p):
            if not l.strip():
                continue
            c = json.loads(l)
            s = c['spec']
            if s in rows and (c.get('closed') or s not in vf):
                vf[s] = c
    why = {}
    for p in sys.argv[1:]:
        for l in open(p):
            f = l.rstrip('\n').split('\t')
            if len(f) >= 3 and f[2] != 'finder':
                why[f[0]] = f[3] if len(f) > 3 else f[2]
    out = collections.Counter()
    for s, k in rows.items():
        if s in boarded:
            st = 'boarded by ' + boarded[s].split('_')[1] if boarded[s].startswith('CBT_') else 'boarded'
        elif s not in rem:
            st = 'closed elsewhere'
        elif s not in vf:
            st = 'finder not run yet'
        elif not vf[s].get('closed'):
            r = str(vf[s].get('reason') or 'families found but none closed')
            st = 'finder: ' + r.split(':')[0][:40]
        else:
            st = 'closed, not boarded: ' + why.get(s, '?').split(':')[0][:60]
        out[(k, st)] += 1
    for k in ('DN', 'SP', 'QH'):
        print(k, sum(v for (kk, _), v in out.items() if kk == k))
        for (kk, st), v in sorted(out.items(), key=lambda x: -x[1]):
            if kk == k:
                print('  %5d  %s' % (v, st))


if __name__ == '__main__':
    main()
