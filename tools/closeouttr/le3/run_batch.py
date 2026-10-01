#!/usr/bin/env python3
"""Terminator-run boards -> closeout batches (UNTRUSTED; SCOPING_INSTR 7.4.LE3).

    python3 tools/closeouttr/le3/run_batch.py termrun.jsonl --tag LE3 [--chunk 40]

For every row termrun_detect.py read (still in closeouttr_remaining.txt),
runs emit_run.py (with --qh for the class-QH rows), compiles the board, keeps
it if it compiled and carries the machine theorem: LDRR_<ID>.v ([nqhtr_<ID>])
or LDRRQ_<ID>.v ([qhtr_<ID>]), into _CoqProject after LadderCheckRunTr.v, and
writes the batches.  Then run tools/closeouttr/gen_closeout_tr.py.
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
sys.path.insert(0, HERE)
from cbt import REPO, next_free, write_batch  # noqa: E402
import step_batch as SB  # noqa: E402

EMIT = os.path.join(HERE, 'emit_run.py')


def board(spec, det, tmp, qh):
    m = SB.mid(spec)
    v = os.path.join(tmp, '%s_%s.v' % ('LDRRQ' if qh else 'LDRR', m))
    r = subprocess.run([sys.executable, EMIT, spec, det, '-o', v]
                       + (['--qh'] if qh else []), capture_output=True, text=True)
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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('detect')
    ap.add_argument('--tag', default='LE3')
    ap.add_argument('--chunk', type=int, default=40)
    ap.add_argument('--skip', action='append', default=[])
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
    with tempfile.TemporaryDirectory() as tmp:
        for s in sorted(set(rows)):
            qh = s in qhc
            v, why = board(s, det, tmp, qh)
            if v is None:
                print('%-30s no board: %s' % (s, why[:160]), flush=True)
                continue
            dst = os.path.join(SB.BOARDS, os.path.basename(v))
            shutil.copy(v, dst)
            kept.append((s, qh))
            print('%-30s board %s' % (s, os.path.relpath(dst, REPO)), flush=True)
    SB.ANCHOR = 'theories/Checkers/LadderCheckRunTr.v'
    p = os.path.join(REPO, '_CoqProject')
    lines = open(p).read().splitlines()
    new = ['theories/Machines/LadderTr/%s_%s.v' % ('LDRRQ' if qh else 'LDRR', SB.mid(s))
           for s, qh in kept]
    new = [x for x in new if x not in set(lines)]
    i = lines.index(SB.ANCHOR) + 1
    while i < len(lines) and lines[i].startswith('theories/Machines/LadderTr/LDRR'):
        i += 1
    lines[i:i] = new
    open(p, 'w').write('\n'.join(lines) + '\n')
    nn = next_free(a.tag)
    made = []
    for i in range(0, len(kept), a.chunk):
        chunk = kept[i:i + a.chunk]
        req = ['From BBB4.Machines.LadderTr Require %s.'
               % ' '.join('%s_%s' % ('LDRRQ' if qh else 'LDRR', SB.mid(s)) for s, qh in chunk)]
        entries = []
        for s, qh in chunk:
            m = SB.mid(s)
            if qh:
                entries.append((s, 'apply (coversTr_qh3_at LDRRQ_%s.tm_%s); '
                                   '[exact LDRRQ_%s.qhtr_%s | intros q s; destruct q, s; '
                                   'reflexivity].' % (m, m, m, m)))
            else:
                entries.append((s, 'apply (coversTr_nqh_at LDRR_%s.tm_%s); '
                                   '[exact LDRR_%s.nqhtr_%s | intros q s; destruct q, s; '
                                   'reflexivity].' % (m, m, m, m)))
        made.append(write_batch(a.tag, nn, req, entries,
                                'terminator-run counters (x then a growing run T^m), '
                                'by LadderCheckRunTr'))
        nn += 1
    print('%d of %d terminator-run rows boarded -> %d batch file(s): %s'
          % (len(kept), len(set(rows)), len(made),
             ' '.join(os.path.relpath(p, REPO) for p in made)))


if __name__ == '__main__':
    main()
