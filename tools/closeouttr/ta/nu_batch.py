#!/usr/bin/env python3
"""TriNuTr certificates (ta/nu_find.py output) -> closeout batches.

    python3 tools/closeouttr/ta/nu_batch.py NU.jsonl [...] --tag TA [--chunk 12] [--skip SPEC]

A row is one line, `apply coversTr_nqh, (tri_nu_sound _ (mkNC TC LIVE))`
(`_mirror` when the families were found on the mirrored machine; the
`coversTr_qh3` / `tri_nu_sound_qh` forms for quasihalting rows).  TC is
TriGlueTr's certificate with an empty rank list; LIVE is, per instruction,
the modulus l, the number K of rankings, and per node (level, E,
[V_0 .. V_(K-1)]).  Only rows still in
closeouttr_remaining.txt are written.  Compile each batch before
committing; drop a row Coq rejects with --skip SPEC.  Then run
tools/closeouttr/gen_closeout_tr.py.
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import ti_batch as T                            # noqa: E402
from cbt import REPO, next_free, write_batch    # noqa: E402


def cvec(V):
    return '(%d,[%s])' % (V[0], ';'.join(str(x) for x in V[1]))


def render(c):
    tc = dict(c, ranks=[])
    text = T.render(tc)
    # T.render's certificate is the (mkTC ...) term; lift it into (mkNC ... live)
    start = text.index('(mkTC ')
    depth, end = 0, None
    for i in range(start, len(text)):
        if text[i] == '(':
            depth += 1
        elif text[i] == ')':
            depth -= 1
            if depth == 0:
                end = i + 1
                break
    live = '[' + ';\n      '.join(
        '((%s,%s), (%d, %d, [%s]))' % (T.ST[t[0]], T.SYM[t[1]], ell, K,
                                      ';'.join('(%d,%s,[%s])' % (lv, cvec(E),
                                                                 ';'.join(cvec(V) for V in Vs))
                                               for lv, E, Vs in rows))
        for t, (ell, K, rows) in c['live']) + ']'
    nc = '(mkNC %s\n      %s)' % (text[start:end], live)
    if c.get('qh'):
        lemma = 'tri_nu_sound_qh_mirror' if c['mir'] else 'tri_nu_sound_qh'
        return 'apply coversTr_qh3, (%s _\n      %s).\n  vm_cast_no_check (eq_refl true).' % (
            lemma, nc)
    lemma = 'tri_nu_sound_mirror' if c['mir'] else 'tri_nu_sound'
    return 'apply coversTr_nqh, (%s _\n      %s).\n  vm_cast_no_check (eq_refl true).' % (
        lemma, nc)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('found', nargs='+')
    ap.add_argument('--tag', default='TA')
    ap.add_argument('--chunk', type=int, default=12)
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--skip', action='append', default=[])
    a = ap.parse_args()
    rem = T.remaining()
    certs, seen = [], set()
    for p in a.found:
        for line in open(p):
            c = json.loads(line)
            s = c['spec']
            if 'err' in c or s not in rem or s in seen or s in a.skip:
                continue
            seen.add(s)
            live = c['live']
            c = T.detuple(dict(c, ranks=[]))
            c['live'] = live
            certs.append(c)
    if a.limit:
        certs = certs[:a.limit]
    nn = next_free(a.tag)
    made = []
    for i in range(0, len(certs), a.chunk):
        chunk = certs[i:i + a.chunk]
        entries = [(c['spec'], render(c)) for c in chunk]
        made.append(write_batch(a.tag, nn, ['From BBB4.Checkers Require Import LapDecider.',
                                            'From BBB4.Counters Require Import TriGlueTr TriNuTr.'],
                                entries, 'Collatz-like rounds by the block-family glue with an '
                                         'l-adic liveness (TriNuTr, tri_nu_check)'))
        nn += 1
    print('%d rows -> %d batch file(s): %s' % (len(certs), len(made),
          ' '.join(os.path.relpath(p, REPO) for p in made)))


if __name__ == '__main__':
    main()
