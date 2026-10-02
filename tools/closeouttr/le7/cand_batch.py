#!/usr/bin/env python3
"""LE7 boards from multi-candidate readings (UNTRUSTED; SCOPING_INSTR 7.4.LE7).
Each record is {spec, cands: [...]}; the candidates are emitted in order by
the kind's emitter and compiled, and the first that boards is kept.

    --kind run2z0   run2_all.py records, le7/emit_run2z0.py, [LadderCheckRun2zTr],
                    boards LDRZM_ / LDRZMQ_ after LadderCheckRun2zTr.v
    --kind run3     run3_all.py records, le5/emit_run3.py, [LadderCheckRun3Tr],
                    boards LDR3_ / LDR3Q_ after LadderCheckRun3Tr.v
    --kind tank     tank_detect.py records, le7/emit_tank.py, [LadderCheckTankTr],
                    boards LDTNK_ / LDTNKQ_ after LadderCheckTankTr.v
    --kind ph1      phase models ({spec, anchor, model}), le7/emit_ph_model.py,
                    [LadderCheckPhRun1Tr], boards LDPH1_ / LDPH1Q_ after LadderCheckPhRun1Tr.v

    python3 tools/closeouttr/le7/cand_batch.py CANDS.jsonl --kind run3 --tag LE7 \\
        [--chunk 10] [--jobs 3] [--max-cands 6] [--dry] [--log LOG]

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
from cbt import REPO, next_free, write_batch  # noqa: E402
import step_batch as SB  # noqa: E402

KINDS = {
    'run2z0': dict(emit=os.path.join(HERE, 'emit_run2z0.py'), pfx='LDRZM',
                   anchor='theories/Checkers/LadderCheckRun2zTr.v',
                   blurb='binary marker-run counters with a plain refill, re-anchored '
                         '(LE6 B2 rows), by LadderCheckRun2zTr with z = [0]'),
    'run3': dict(emit=os.path.join(HERE, '..', 'le5', 'emit_run3.py'), pfx='LDR3',
                 anchor='theories/Checkers/LadderCheckRun3Tr.v',
                 blurb='terminator-run counters whose top digit has its own words, '
                       're-anchored (LE6 B2 rows), by LadderCheckRun3Tr'),
    'tank': dict(emit=os.path.join(HERE, 'emit_tank.py'), pfx='LDTNK',
                 anchor='theories/Checkers/LadderCheckTankTr.v',
                 blurb='binary counters that widen into a tank, an empty tank refilling, '
                       'by LadderCheckTankTr'),
    'ph1': dict(emit=os.path.join(HERE, 'emit_ph_model.py'), pfx='LDPH1',
                anchor='theories/Checkers/LadderCheckPhRun1Tr.v',
                blurb='phase-run counters whose last top word is the run word, from a '
                      'given phase model, by LadderCheckPhRun1Tr'),
}
EMIT_TIMEOUT = 150
K = {}


def board1(spec, det, d, qh):
    m = SB.mid(spec)
    v = os.path.join(d, '%s%s_%s.v' % (K['pfx'], 'Q' if qh else '', m))
    dp = os.path.join(d, 'det.jsonl')
    with open(dp, 'w') as f:
        f.write(json.dumps(det) + '\n')
    try:
        r = subprocess.run([sys.executable, K['emit'], spec, dp, '-o', v] + (['--qh'] if qh else []),
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
    spec, cands, tmp, qh, kind = t
    K.update(KINDS[kind])
    whys = []
    for i, c in enumerate(cands):
        d = os.path.join(tmp, '%s_c%d' % (SB.mid(spec), i))
        os.makedirs(d, exist_ok=True)
        v, why = board1(spec, c, d, qh)
        if v is not None:
            return spec, qh, v, i, c
        whys.append('c%d %s' % (i, why[:90]))
    return spec, qh, None, None, '; '.join(whys[:6])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cands')
    ap.add_argument('--kind', required=True, choices=sorted(KINDS))
    ap.add_argument('--tag', default='LE7')
    ap.add_argument('--chunk', type=int, default=10)
    ap.add_argument('--jobs', type=int, default=3)
    ap.add_argument('--max-cands', type=int, default=6)
    ap.add_argument('--skip', action='append', default=[])
    ap.add_argument('--dry', action='store_true')
    ap.add_argument('--log', default=None)
    a = ap.parse_args()
    K.update(KINDS[a.kind])
    remaining = set(l.strip() for l in open(os.path.join(REPO, 'closeouttr_remaining.txt')))
    qhc = set(l.split('\t')[0] for l in open(os.path.join(REPO, 'closeouttr_classes.tsv'))
              if l.split('\t')[1:2] == ['QH'])
    kept = []
    logf = open(a.log, 'a') if a.log else None
    with tempfile.TemporaryDirectory() as tmp:
        jobs = []
        for l in open(a.cands):
            r = json.loads(l)
            if r['cands'] and r['spec'] in remaining and r['spec'] not in a.skip:
                jobs.append((r['spec'], r['cands'][:a.max_cands], tmp, r['spec'] in qhc, a.kind))
        with Pool(a.jobs) as pool:
            for s, qh, v, i, c in pool.imap_unordered(_board, jobs):
                if logf:
                    logf.write(json.dumps(dict(spec=s, kind=a.kind, ok=v is not None,
                                               cand=c if v else None, why=None if v else c)) + '\n')
                    logf.flush()
                if v is None:
                    print('%-30s no board: %s' % (s, c[:240]), flush=True)
                    continue
                print('%-30s board (cand %d, anchor %s)' % (s, i, c['anchor']), flush=True)
                if not a.dry:
                    shutil.copy(v, os.path.join(SB.BOARDS, os.path.basename(v)))
                kept.append((s, qh))
    if a.dry or not kept:
        print('%d of %d rows board' % (len(kept), len(jobs)))
        return
    kept.sort()
    pfx = K['pfx']
    p = os.path.join(REPO, '_CoqProject')
    lines = open(p).read().splitlines()
    new = ['theories/Machines/LadderTr/%s%s_%s.v' % (pfx, 'Q' if qh else '', SB.mid(s))
           for s, qh in kept]
    new = [x for x in new if x not in set(lines)]
    i = lines.index(K['anchor']) + 1
    while i < len(lines) and lines[i].startswith('theories/Machines/LadderTr/' + pfx):
        i += 1
    lines[i:i] = new
    open(p, 'w').write('\n'.join(lines) + '\n')
    nn = next_free(a.tag)
    made = []
    for j in range(0, len(kept), a.chunk):
        chunk = kept[j:j + a.chunk]
        req = ['From BBB4.Machines.LadderTr Require %s.'
               % ' '.join('%s%s_%s' % (pfx, 'Q' if qh else '', SB.mid(s)) for s, qh in chunk)]
        entries = []
        for s, qh in chunk:
            m = SB.mid(s)
            b = '%s%s_%s' % (pfx, 'Q' if qh else '', m)
            if qh:
                entries.append((s, 'apply (coversTr_qh3_at %s.tm_%s); [exact %s.qhtr_%s | '
                                   'intros q s; destruct q, s; reflexivity].' % (b, m, b, m)))
            else:
                entries.append((s, 'apply (coversTr_nqh_at %s.tm_%s); [exact %s.nqhtr_%s | '
                                   'intros q s; destruct q, s; reflexivity].' % (b, m, b, m)))
        made.append(write_batch(a.tag, nn, req, entries, K['blurb']))
        nn += 1
    print('%d of %d rows boarded -> %d batch file(s): %s'
          % (len(kept), len(jobs), len(made), ' '.join(os.path.relpath(x, REPO) for x in made)))


if __name__ == '__main__':
    main()
