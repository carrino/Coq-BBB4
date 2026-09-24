#!/usr/bin/env python3
"""Quasihalting counter and cycler results -> closeout batches (UNTRUSTED generator).

    python3 tools/closeouttr/qc_batch.py lap BOARD.v [...] --tag QC [--chunk 25]
    python3 tools/closeouttr/qc_batch.py tc CERTS.tsv --tag QC

`lap`: lap-certificate boards rendered by tools/counters/emit_lapcert.py
--qh (the LAPQ_<ID>.v text, each proving
[qhtr_<ID> : NonHalt tm_<ID> /\\ QHBoundTr 32779478 tm_<ID> /\\ QuasiHaltsTr
tm_<ID>] through [QHConveyorTr.lap_qh_stage]).  The boards go INSIDE the
batch file, one [Module] each, so a batch is self-contained: nothing is
added under theories/Machines and no _CoqProject line outlives a
regenerate of the shared files.  The board's own imports become a
top-level [Require] and an [Import] local to its module (two boards'
alphabet modules never meet).  The row lemma is
[coversTr_qh3_at] at the board's machine; the 8-way case split fails to
compile on any row/board mismatch.

`tc`: quiet-instruction cyclers, rows `spec side n1 P W` of
tools/censustr/tc_find.py (an in-place cycler has net displacement 0 and
the same lap checker takes it); the row lemma is
[QHConveyorTr.tcycler_qh_stage] (side R) or [tcycler_qh_stage_L].

Only rows still in closeouttr_remaining.txt are written.  Compile each
batch before committing; drop a row Coq rejects with --skip SPEC and
regenerate.  Then run tools/closeouttr/gen_closeout_tr.py.
"""
import argparse
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from cbt import REPO, next_free, write_batch  # noqa: E402

REQ_RE = re.compile(r'^From\s+(\S+)\s+Require\s+Import\s+([^.]+)\.', re.M)
THM_RE = re.compile(r'^Theorem (qhtr_\w+) : NonHalt (tm_\w+) /\\ QHBoundTr 32779478 \2 /\\ QuasiHaltsTr \2\.', re.M)
SPEC_RE = re.compile(r'TRANSITION-LEVEL QUASIHALTING-side board for machine (\S+), ')


def remaining():
    return set(l.strip() for l in open(os.path.join(REPO, 'closeouttr_remaining.txt')))


def read_board(path):
    """-> (spec, [(from, [mods])], body, theorem, tm)"""
    src = open(path).read()
    m = SPEC_RE.search(src)
    if not m:
        raise SystemExit('%s: no machine line in the header' % path)
    head, sep, body = src.partition('\nImport ListNotations.\n')
    if not sep:
        raise SystemExit('%s: no Import ListNotations line' % path)
    reqs = [(fr, mods.split()) for fr, mods in REQ_RE.findall(head)]
    th = THM_RE.findall(body)
    if len(th) != 1:
        raise SystemExit('%s: want exactly one qhtr theorem, found %d' % (path, len(th)))
    return m.group(1), reqs, body.strip('\n'), th[0][0], th[0][1]


def lap(a):
    rem = remaining()
    boards, seen = [], set()
    for p in a.boards:
        spec, reqs, body, th, tm = read_board(p)
        if spec in rem and spec not in seen and spec not in a.skip:
            seen.add(spec)
            boards.append((spec, reqs, body, th, tm))
    nn = next_free(a.tag)
    made = []
    for i in range(0, len(boards), a.chunk):
        chunk = boards[i:i + a.chunk]
        base = '%s_%02d' % (a.tag, nn)
        # the Coq standard library stays imported at top level (the batch
        # header needs Arith/List anyway); BBB4 modules are only Required
        # there and Imported inside each board's module
        req, top_import, have = [], [], set()
        for _, reqs, _, _, _ in chunk:
            for fr, mods in reqs:
                for md in mods:
                    if (fr, md) in have:
                        continue
                    have.add((fr, md))
                    if fr == 'Coq':
                        top_import.append(md)
                    else:
                        req.append('From %s Require %s.' % (fr, md))
        requires = []
        if top_import:
            requires.append('From Coq Require Import %s.' % ' '.join(top_import))
        requires += req
        pre, entries = [], []
        for k, (spec, reqs, body, th, tm) in enumerate(chunk):
            mod = 'B_%s_%03d' % (base, k)
            imps = ['%s.%s' % (fr, md) for fr, mods in reqs if fr != 'Coq' for md in mods]
            pre.append('(** board for %s (emit_lapcert.py --qh) *)\nModule %s.\nImport %s.\nImport ListNotations.\n\n%s\n\nEnd %s.\n'
                       % (spec, mod, ' '.join(imps), body, mod))
            entries.append((spec, 'apply (coversTr_qh3_at %s.%s); [exact %s.%s |]. '
                                  'intros q s; destruct q, s; reflexivity.' % (mod, tm, mod, th)))
        made.append(write_batch(a.tag, nn, requires, entries,
                                'quasihalting counters by lap certificate (LapGlueQHTr, lap_qh_stage), '
                                'the boards inline', preamble='\n'.join(pre)))
        nn += 1
    print('%d boards -> %d batch file(s): %s' % (len(boards), len(made),
          ' '.join(os.path.relpath(p, REPO) for p in made)))


def tc(a):
    rem = remaining()
    rows, seen = [], set()
    for f in a.certs:
        for line in open(f):
            x = line.split()
            if len(x) < 5 or x[0] not in rem or x[0] in seen or x[0] in a.skip:
                continue
            seen.add(x[0])
            rows.append((x[0], x[1], int(x[2]), int(x[3]), int(x[4])))
    if not rows:
        sys.exit('no remaining rows')
    entries = [(spec, 'apply coversTr_qh3, (%s _ %d %d %d 32779478). all: vm_cast_no_check (eq_refl true).'
                % ('tcycler_qh_stage' if side == 'R' else 'tcycler_qh_stage_L', n1, P, W))
               for spec, side, n1, P, W in rows]
    p = write_batch(a.tag, next_free(a.tag), ['From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.'],
                    entries, 'quiet-instruction cyclers (TCyclerQHTr, tcycler_qh_stage)')
    print('%d rows -> %s' % (len(rows), os.path.relpath(p, REPO)))


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest='cmd', required=True)
    p = sp.add_parser('lap')
    p.add_argument('boards', nargs='+')
    p.add_argument('--chunk', type=int, default=25)
    p = sp.add_parser('tc')
    p.add_argument('certs', nargs='+')
    for p in sp.choices.values():
        p.add_argument('--tag', default='QC')
        p.add_argument('--skip', action='append', default=[])
    a = ap.parse_args()
    {'lap': lap, 'tc': tc}[a.cmd](a)


if __name__ == '__main__':
    main()
