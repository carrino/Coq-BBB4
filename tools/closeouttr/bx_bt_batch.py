#!/usr/bin/env python3
"""Blank-tail quasihalters -> closeout batches (UNTRUSTED finder + writer),
for theories/Counters/BlankTailTr.v.

    python3 tools/closeouttr/bx_bt_batch.py find ROWS.txt OUT.tsv [--steps 40000000]
    python3 tools/closeouttr/bx_bt_batch.py batch OUT.tsv --tag BX

A row qualifies when, after N0 steps, the machine is in a state q whose
blank transition is a self-loop (q, 0) -> (w, d, q), the head reads a blank
and the half-tape ahead (direction d) is blank: from N0 on only (q, 0)
fires.  `find` runs each row STEPS steps, takes N0 = one past the last fire
of every instruction but the most recent one, re-runs to N0 and checks the
landing; it writes (spec, q, w, d, N0).  The kernel re-runs the prefix
([blank_tail_tr_checkb], binary fuel) and rejects anything else.  Only rows
still in closeouttr_remaining.txt are written.  N0 must be at most B_close
(32,779,478).
"""
import argparse
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from cbt import REPO, next_free, write_batch  # noqa: E402

B_CLOSE = 32779478
ST = ['StA', 'StB', 'StC', 'StD']


def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


def run(tab, n):
    """(q, tape, pos, last) after n steps, or None if it halts"""
    tape, pos, q, last = {}, 0, 0, {}
    for t in range(n):
        h = tape.get(pos, 0)
        tr = tab[(q, h)]
        if tr is None:
            return None
        last[(q, h)] = t
        w, d, nq = tr
        tape[pos] = w
        pos += d
        q = nq
    return q, tape, pos, last


def find1(spec, steps):
    tab = parse(spec)
    r = run(tab, steps)
    if r is None:
        return None
    last = r[3]
    if len(last) < 2:
        return None
    ins = sorted(last, key=lambda k: last[k])
    q, a = ins[-1]
    tr = tab[(q, a)]
    if a != 0 or tr is None or tr[2] != q:
        return None
    n0 = last[ins[-2]] + 1
    if n0 > B_CLOSE or q == 0:
        return None
    q2, tape, pos, _ = run(tab, n0)
    w, d, _ = tr
    if q2 != q or tape.get(pos, 0) != 0:
        return None
    if any(v != 0 and (k - pos) * d > 0 for k, v in tape.items()):
        return None
    return (spec, q, w, 'DR' if d > 0 else 'DL', n0)


def cmd_find(a):
    specs = [l.split()[0] for l in open(a.rows) if l.strip() and not l.startswith('#')]
    n = 0
    with open(a.out, 'w') as f:
        for s in specs:
            r = find1(s, a.steps)
            if r:
                f.write('%s\t%s\t%d\t%s\t%d\n' % (r[0], ST[r[1]], r[2], r[3], r[4]))
                n += 1
    print('%d of %d rows end in a blank tail' % (n, len(specs)))


def cmd_batch(a):
    rem = set(l.strip() for l in open(os.path.join(REPO, 'closeouttr_remaining.txt')))
    entries = []
    for line in open(a.found):
        spec, q, w, d, n0 = line.split()
        if spec not in rem:
            continue
        pf = ('apply coversTr_qh3, (blank_tail_tr_board _ %s S%s %s %s%%N); '
              '[reflexivity | reflexivity | vm_cast_no_check (eq_refl true) | '
              'apply N_le_dec; vm_cast_no_check (eq_refl true)].' % (q, w, d, n0))
        entries.append((spec, pf))
    if not entries:
        print('nothing to write')
        return
    p = write_batch(a.tag, next_free(a.tag),
                    ['From Coq Require Import NArith.',
                     'From BBB4.Counters Require Import BlankTailTr.'],
                    entries, 'quasihalting by a blank-tail march (BlankTailTr)')
    print('%d rows -> %s' % (len(entries), os.path.relpath(p, REPO)))


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest='cmd', required=True)
    p = sp.add_parser('find')
    p.add_argument('rows')
    p.add_argument('out')
    p.add_argument('--steps', type=int, default=40000000)
    p = sp.add_parser('batch')
    p.add_argument('found')
    p.add_argument('--tag', default='BX')
    a = ap.parse_args()
    {'find': cmd_find, 'batch': cmd_batch}[a.cmd](a)


if __name__ == '__main__':
    main()
