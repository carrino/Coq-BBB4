#!/usr/bin/env python3
"""LE7 mirrored-counter boards (UNTRUSTED; SCOPING_INSTR 7.4.LE7): over
`mirror_detect.py`'s readings (the best one, then every one in `cands`), the
first reading whose increments split on the anchor cell
(`mirror_split.split_of`) and whose board `emit_mirror.py` builds and coqc
accepts.

    python3 tools/closeouttr/le7/mirror_batch.py MIRROR.jsonl --tag LE7 [--chunk 10] [--jobs 4] [--dry]

Boards go to theories/Machines/LadderTr/LDMIR_<ID>.v ([nqhtr_<ID>]) or
LDMIRQ_<ID>.v ([qhtr_<ID>]), into _CoqProject after LadderCheckMirrorTr.v.
Then run gen_closeout_tr.py.
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
sys.path.insert(0, os.path.join(HERE, '..', 'le3'))
sys.path.insert(0, HERE)
from cbt import REPO, next_free, write_batch  # noqa: E402
import step_batch as SB  # noqa: E402
import mirror_split as MS  # noqa: E402

EMIT = os.path.join(HERE, 'emit_mirror.py')
EMIT_TIMEOUT = 600
ANCHOR = 'theories/Checkers/LadderCheckMirrorTr.v'


def board1(spec, det, d, qh):
    m = SB.mid(spec)
    v = os.path.join(d, '%s_%s.v' % ('LDMIRQ' if qh else 'LDMIR', m))
    dp = os.path.join(d, 'det.jsonl')
    with open(dp, 'w') as f:
        f.write(json.dumps(det) + '\n')
    try:
        r = subprocess.run([sys.executable, EMIT, spec, dp, '-o', v] + (['--qh'] if qh else []),
                           capture_output=True, text=True, timeout=EMIT_TIMEOUT)
    except subprocess.TimeoutExpired:
        return None, 'emit timeout'
    if not os.path.exists(v):
        return None, 'emit failed: ' + ((r.stderr + r.stdout).strip().splitlines() or ['?'])[-1]
    if 'Theorem %s_%s ' % ('qhtr' if qh else 'nqhtr', m) not in open(v).read():
        why = [l for l in open(v) if 'NOT BUILT' in l]
        return None, (why[0].strip() if why else 'no closure')
    r = subprocess.run(['coqc', '-Q', os.path.join(REPO, 'theories'), 'BBB4', v],
                       capture_output=True, text=True, cwd=d)
    if r.returncode != 0:
        err = [l for l in (r.stdout + r.stderr).splitlines() if l.startswith('Error') or 'line' in l]
        return None, 'coqc: ' + ' '.join(err[-2:])[:200]
    return v, None


def _board(t):
    spec, dets, tmp, qh = t
    whys = []
    for i, det in enumerate(dets):
        try:
            sp = MS.split_of(spec, det)
        except Exception as e:  # noqa: BLE001
            sp, whys = None, whys + ['c%d split error %r' % (i, e)]
        if sp is None:
            whys.append('c%d no split' % i)
            continue
        det = dict(det, split=sp)
        d = os.path.join(tmp, '%s_c%d' % (SB.mid(spec), i))
        os.makedirs(d, exist_ok=True)
        v, why = board1(spec, det, d, qh)
        if v is not None:
            return spec, qh, v, det
        whys.append('c%d %s' % (i, why[:100]))
    return spec, qh, None, '; '.join(whys[:6])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('detect')
    ap.add_argument('--tag', default='LE7')
    ap.add_argument('--chunk', type=int, default=10)
    ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--skip', action='append', default=[])
    ap.add_argument('--dry', action='store_true')
    ap.add_argument('--log', default=None)
    a = ap.parse_args()
    remaining = set(l.strip() for l in open(os.path.join(REPO, 'closeouttr_remaining.txt')))
    qhc = set(l.split('\t')[0] for l in open(os.path.join(REPO, 'closeouttr_classes.tsv'))
              if l.split('\t')[1:2] == ['QH'])
    jobs = []
    with tempfile.TemporaryDirectory() as tmp:
        for l in open(a.detect):
            r = json.loads(l)
            if not r.get('anchor') or r['spec'] not in remaining or r['spec'] in a.skip:
                continue
            dets = [r] + [c for c in r.get('cands', []) if c != {k: v for k, v in r.items()
                                                                  if k != 'cands'}]
            dets = [{k: v for k, v in x.items() if k != 'cands'} for x in dets]
            jobs.append((r['spec'], dets, tmp, r['spec'] in qhc))
        kept = []
        logf = open(a.log, 'a') if a.log else None
        with Pool(a.jobs) as pool:
            for s, qh, v, det in pool.imap_unordered(_board, jobs):
                if logf:
                    logf.write(json.dumps(dict(spec=s, ok=v is not None,
                                               det=det if v else None,
                                               why=None if v else det)) + '\n')
                    logf.flush()
                if v is None:
                    print('%-30s no board: %s' % (s, det[:240]), flush=True)
                    continue
                print('%-30s board (anchor %s, split %s)' % (s, det['anchor'], det['split']),
                      flush=True)
                if not a.dry:
                    shutil.copy(v, os.path.join(SB.BOARDS, os.path.basename(v)))
                kept.append((s, qh))
    if a.dry or not kept:
        print('%d of %d rows board' % (len(kept), len(jobs)))
        return
    kept.sort()
    p = os.path.join(REPO, '_CoqProject')
    lines = open(p).read().splitlines()
    new = ['theories/Machines/LadderTr/%s_%s.v' % ('LDMIRQ' if qh else 'LDMIR', SB.mid(s))
           for s, qh in kept]
    new = [x for x in new if x not in set(lines)]
    i = lines.index(ANCHOR) + 1
    while i < len(lines) and lines[i].startswith('theories/Machines/LadderTr/LDMIR'):
        i += 1
    lines[i:i] = new
    open(p, 'w').write('\n'.join(lines) + '\n')
    nn = next_free(a.tag)
    made = []
    for j in range(0, len(kept), a.chunk):
        chunk = kept[j:j + a.chunk]
        req = ['From BBB4.Machines.LadderTr Require %s.'
               % ' '.join('%s_%s' % ('LDMIRQ' if qh else 'LDMIR', SB.mid(s)) for s, qh in chunk)]
        entries = []
        for s, qh in chunk:
            m = SB.mid(s)
            if qh:
                entries.append((s, 'apply (coversTr_qh3_at LDMIRQ_%s.tm_%s); '
                                   '[exact LDMIRQ_%s.qhtr_%s | intros q s; destruct q, s; '
                                   'reflexivity].' % (m, m, m, m)))
            else:
                entries.append((s, 'apply (coversTr_nqh_at LDMIR_%s.tm_%s); '
                                   '[exact LDMIR_%s.nqhtr_%s | intros q s; destruct q, s; '
                                   'reflexivity].' % (m, m, m, m)))
        made.append(write_batch(a.tag, nn, req, entries,
                                'mirrored binary counters (one counter held on both sides '
                                'of the head), by LadderCheckMirrorTr'))
        nn += 1
    print('%d of %d rows boarded -> %d batch file(s): %s'
          % (len(kept), len(jobs), len(made), ' '.join(os.path.relpath(x, REPO) for x in made)))


if __name__ == '__main__':
    main()
