#!/usr/bin/env python3
"""Phase-run boards -> closeout batches (UNTRUSTED; SCOPING_INSTR
7.4.LE5).  LE3's `run_batch.py` for `phrun2.py` / `emit_phrun.py`:

    python3 tools/closeouttr/le5/phrun_batch.py phrun.jsonl --tag LE5 [--chunk 40]

Boards go to LDRP_<ID>.v ([nqhtr_<ID>]) or LDRPQ_<ID>.v ([qhtr_<ID>]), into
_CoqProject after LadderCheckPhRunTr.v.  Then run gen_closeout_tr.py.
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'le3'))
from cbt import REPO, next_free, write_batch  # noqa: E402
import step_batch as SB  # noqa: E402

EMIT = os.path.join(HERE, 'emit_phrun.py')
EMIT_TIMEOUT = 900


def board(spec, det, tmp, qh):
    m = SB.mid(spec)
    v = os.path.join(tmp, '%s_%s.v' % ('LDRPQ' if qh else 'LDRP', m))
    try:
        r = subprocess.run([sys.executable, EMIT, spec, det, '-o', v]
                           + (['--qh'] if qh else []), capture_output=True, text=True,
                           timeout=EMIT_TIMEOUT)
    except subprocess.TimeoutExpired:
        return None, 'emit timeout %d s' % EMIT_TIMEOUT
    if not os.path.exists(v):
        return None, 'emit failed: ' + ((r.stderr + r.stdout).strip().splitlines() or ['?'])[-1]
    if 'Theorem %s_%s ' % ('qhtr' if qh else 'nqhtr', m) not in open(v).read():
        why = [l for l in open(v) if 'NOT BUILT' in l]
        return None, (why[0].strip() if why else 'no closure')
    r = subprocess.run(['coqc', '-Q', os.path.join(REPO, 'theories'), 'BBB4', v],
                       capture_output=True, text=True, cwd=tmp)
    if r.returncode != 0:
        err = [l for l in (r.stdout + r.stderr).splitlines()
               if l.startswith('Error') or 'line' in l]
        return None, 'coqc: ' + ' '.join(err[-2:])[:200]
    return v, None


def _board(t):
    s, det, tmp, qh = t
    return s, qh, board(s, det, tmp, qh)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('detect')
    ap.add_argument('--tag', default="LE5")
    ap.add_argument('--chunk', type=int, default=40)
    ap.add_argument('--skip', action='append', default=[])
    ap.add_argument('--jobs', type=int, default=1)
    a = ap.parse_args()
    det = os.path.abspath(a.detect)
    remaining = set(l.strip() for l in open(os.path.join(REPO, 'closeouttr_remaining.txt')))
    qhc = set(l.split('\t')[0] for l in open(os.path.join(REPO, 'closeouttr_classes.tsv'))
              if l.split('\t')[1:2] == ['QH'])
    rows = []
    for l in open(det):
        r = json.loads(l)
        if r.get('anchor') and r['spec'] in remaining and r['spec'] not in a.skip:
            rows.append(r['spec'])
    kept = []
    with tempfile.TemporaryDirectory() as tmp, Pool(a.jobs) as pool:
        todo = [(s, det, tmp, s in qhc) for s in sorted(set(rows))]
        for s, qh, (v, why) in pool.imap(_board, todo):
            if v is None:
                print('%-30s no board: %s' % (s, why[:160]), flush=True)
                continue
            dst = os.path.join(SB.BOARDS, os.path.basename(v))
            shutil.copy(v, dst)
            kept.append((s, qh))
            print('%-30s board %s' % (s, os.path.relpath(dst, REPO)), flush=True)
    SB.ANCHOR = 'theories/Checkers/LadderCheckPhRunTr.v'
    p = os.path.join(REPO, '_CoqProject')
    lines = open(p).read().splitlines()
    new = ['theories/Machines/LadderTr/%s_%s.v' % ('LDRPQ' if qh else 'LDRP', SB.mid(s))
           for s, qh in kept]
    new = [x for x in new if x not in set(lines)]
    i = lines.index(SB.ANCHOR) + 1
    while i < len(lines) and lines[i].startswith('theories/Machines/LadderTr/LDRP'):
        i += 1
    lines[i:i] = new
    open(p, 'w').write('\n'.join(lines) + '\n')
    nn = next_free(a.tag)
    made = []
    for i in range(0, len(kept), a.chunk):
        chunk = kept[i:i + a.chunk]
        req = ['From BBB4.Machines.LadderTr Require %s.'
               % ' '.join('%s_%s' % ('LDRPQ' if qh else 'LDRP', SB.mid(s)) for s, qh in chunk)]
        entries = []
        for s, qh in chunk:
            m = SB.mid(s)
            if qh:
                entries.append((s, 'apply (coversTr_qh3_at LDRPQ_%s.tm_%s); '
                                   '[exact LDRPQ_%s.qhtr_%s | intros q s; destruct q, s; '
                                   'reflexivity].' % (m, m, m, m)))
            else:
                entries.append((s, 'apply (coversTr_nqh_at LDRP_%s.tm_%s); '
                                   '[exact LDRP_%s.nqhtr_%s | intros q s; destruct q, s; '
                                   'reflexivity].' % (m, m, m, m)))
        made.append(write_batch(a.tag, nn, req, entries,
                                'counters with phases and a run (x, W_p, T^m, V_p), '
                                'by LadderCheckPhRunTr'))
        nn += 1
    print('%d of %d terminator-run rows boarded -> %d batch file(s): %s'
          % (len(kept), len(set(rows)), len(made),
             ' '.join(os.path.relpath(p, REPO) for p in made)))


if __name__ == '__main__':
    main()
