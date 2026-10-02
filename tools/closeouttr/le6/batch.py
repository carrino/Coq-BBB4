#!/usr/bin/env python3
"""LE6 boards -> closeout batches (UNTRUSTED generator; SCOPING_INSTR 7.4.LE6).

    python3 tools/closeouttr/le6/batch.py CERTS.jsonl... --kind zeckd --tag LE6 [--chunk 40] [--jobs 4]

LE3's `step_batch.py` (see le4/batch.py) with the LE6 kind added and the
boards emitted and compiled in parallel: each `closed` certificate still open
is emitted (`--qh` for the class-QH rows), compiled, and kept only if it
compiled and carries the machine theorem; kept boards go to
theories/Machines/LadderTr/<PFX>[Q]_<ID>.v, into _CoqProject after the kind's
checker, and into CBT_<TAG>_<NN>.v batches.  Then run gen_closeout_tr.py.
"""
import argparse
import json
import os
import shutil
import sys
import tempfile
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'le3'))
import step_batch as SB  # noqa: E402

SB.KINDS['zeckd'] = (
    os.path.join(HERE, 'emit_zeckd.py'), 'theories/Checkers/LadderCheckZeckDTr.v', 'LDRZD',
    lambda f: f.get('numeration') == 'zeckd',
    'Zeckendorf countdowns over two token words, by LadderCheckZeckDTr')

TMP = None


def work(a):
    c, qh = a
    d = tempfile.mkdtemp(dir=TMP)
    v, why = SB.board(c, d, qh)
    return c['spec'], qh, v, why


def main():
    global TMP
    ap = argparse.ArgumentParser()
    ap.add_argument('found', nargs='+')
    ap.add_argument('--tag', default='LE6')
    ap.add_argument('--chunk', type=int, default=40)
    ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--skip', action='append', default=[])
    ap.add_argument('--kind', default='zeckd', choices=sorted(SB.KINDS))
    a = ap.parse_args()
    emit, SB.ANCHOR, SB.PFX, want, blurb = SB.KINDS[a.kind]
    SB.EMIT = os.path.join(SB.HERE, emit)
    REPO = SB.REPO
    remaining = set(l.strip() for l in open(os.path.join(REPO, 'closeouttr_remaining.txt')))
    qhc = set(l.split('\t')[0] for l in open(os.path.join(REPO, 'closeouttr_classes.tsv'))
              if l.split('\t')[1:2] == ['QH'])
    certs, seen = [], set()
    for f in a.found:
        for line in open(f):
            if not line.strip():
                continue
            c = json.loads(line)
            s = c.get('spec')
            if (c.get('closed') and s in remaining and s not in seen
                    and s not in a.skip and want(c['family'])):
                seen.add(s)
                certs.append(c)
    os.makedirs(SB.BOARDS, exist_ok=True)
    kept = []
    with tempfile.TemporaryDirectory() as tmp:
        TMP = tmp
        with Pool(a.jobs) as P:
            for s, qh, v, why in P.imap_unordered(
                    work, [(c, c['spec'] in qhc) for c in sorted(certs, key=lambda c: c['spec'])]):
                if v is None:
                    print('%-30s no board: %s' % (s, why[:160]), flush=True)
                    continue
                dst = os.path.join(SB.BOARDS, os.path.basename(v))
                shutil.copy(v, dst)
                kept.append((s, qh))
                print('%-30s board %s' % (s, os.path.relpath(dst, REPO)), flush=True)
    kept.sort()
    PFX = SB.PFX
    SB.add_to_coqproject(['theories/Machines/LadderTr/%s_%s.v'
                          % (PFX + 'Q' if qh else PFX, SB.mid(s)) for s, qh in kept])
    nn = SB.next_free(a.tag)
    made = []
    for i in range(0, len(kept), a.chunk):
        chunk = kept[i:i + a.chunk]
        req = ['From BBB4.Machines.LadderTr Require %s.'
               % ' '.join('%s_%s' % (PFX + 'Q' if qh else PFX, SB.mid(s)) for s, qh in chunk)]
        entries = []
        for s, qh in chunk:
            m = SB.mid(s)
            if qh:
                entries.append((s, 'apply (coversTr_qh3_at %sQ_%s.tm_%s); '
                                   '[exact %sQ_%s.qhtr_%s | intros q s; destruct q, s; '
                                   'reflexivity].' % (PFX, m, m, PFX, m, m)))
            else:
                entries.append((s, 'apply (coversTr_nqh_at %s_%s.tm_%s); '
                                   '[exact %s_%s.nqhtr_%s | intros q s; destruct q, s; '
                                   'reflexivity].' % (PFX, m, m, PFX, m, m)))
        made.append(SB.write_batch(a.tag, nn, req, entries, blurb))
        nn += 1
    print('%d of %d closed rows boarded -> %d batch file(s): %s'
          % (len(kept), len(certs), len(made),
             ' '.join(os.path.relpath(p, REPO) for p in made)))


if __name__ == '__main__':
    main()
