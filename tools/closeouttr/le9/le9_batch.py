#!/usr/bin/env python3
"""LE9 boards (UNTRUSTED; SCOPING_INSTR 7.4.LE9): emit, compile and batch.

    python3 tools/closeouttr/le9/le9_batch.py --kind tankph ROWS... --tag LE9 [--dry]

Kinds:
    tankph   le9/emit_tankph.py + le9/tankph_models.jsonl, [LadderCheckTankPhTr],
             boards LDTPH_ / LDTPHQ_ after LadderCheckTankPhTr.v
    dbounce  le9/emit_dbounce.py, [DoubleBounceTr], boards LDDB_ / LDDBQ_ after
             DoubleBounceTr.v
    phbin    le9/emit_phbin.py + le9/phbin_models.jsonl, [PhBinCountTr], boards
             LDPB_ / LDPBQ_ after PhBinCountTr.v
    topmap   le9/emit_topmap.py (rows hand-modelled in its ROWS), [TopMapTr], boards
             LDTM_ / LDTMQ_ after TopMapTr.v
    runph    le9/emit_runph.py + le9/runph_models.jsonl, [RunPhCountTr], boards
             LDRP_ / LDRPQ_ after RunPhCountTr.v

Each row is emitted, compiled alone (wall time and peak RSS are printed), and
the boards that compile are copied to theories/Machines/LadderTr/, listed in
_CoqProject after the checker, and collected into new CBT_<TAG>_<NN>.v batches.
Only rows still in closeouttr_remaining.txt are written.  Then run
gen_closeout_tr.py.
"""
import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
from cbt import REPO, next_free, write_batch  # noqa: E402

BOARDS = os.path.join(REPO, 'theories', 'Machines', 'LadderTr')

KINDS = {
    'tankph': dict(emit=[os.path.join(HERE, 'emit_tankph.py'), '{spec}',
                         os.path.join(HERE, 'tankph_models.jsonl')],
                   pfx='LDTPH', anchor='theories/Checkers/LadderCheckTankPhTr.v',
                   blurb='binary counters that widen into a tank, with a cycle of suffix '
                         'phases between refills, by LadderCheckTankPhTr'),
    'dbounce': dict(emit=[os.path.join(HERE, 'emit_dbounce.py'), '{spec}'],
                    pfx='LDDB', anchor='theories/Counters/DoubleBounceTr.v',
                    blurb='bouncers that double their block each round, by DoubleBounceTr'),
    'phbin': dict(emit=[os.path.join(HERE, 'emit_phbin.py'), '{spec}',
                        os.path.join(HERE, 'phbin_models.jsonl')],
                  pfx='LDPB', anchor='theories/Counters/PhBinCountTr.v',
                  blurb='binary counters with phases, each its own anchor, by PhBinCountTr'),
    'runph': dict(emit=[os.path.join(HERE, 'emit_runph.py'), '{spec}',
                        os.path.join(HERE, 'runph_models.jsonl')],
                  pfx='LDRP', anchor='theories/Counters/RunPhCountTr.v',
                  blurb='binary counters beside a growing marker run, with phases between '
                        'refills, by RunPhCountTr'),
    'topmap': dict(emit=[os.path.join(HERE, 'emit_topmap.py'), '{spec}'],
                   pfx='LDTM', anchor='theories/Counters/TopMapTr.v',
                   blurb='binary counters whose tops are a map on (width, run, phase), by TopMapTr'),
}


def mid(spec):
    return spec.replace('-', '_')


def board1(kind, spec, qh, d):
    K = KINDS[kind]
    v = os.path.join(d, '%s%s_%s.v' % (K['pfx'], 'Q' if qh else '', mid(spec)))
    cmd = [sys.executable] + [a.format(spec=spec) for a in K['emit']] + ['-o', v] + (['--qh'] if qh else [])
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=600)
    if not os.path.exists(v) or 'Theorem %s_%s ' % ('qhtr' if qh else 'nqhtr', mid(spec)) not in open(v).read():
        return None, 'emit: ' + ((r.stderr + r.stdout).strip().splitlines() or ['?'])[-1]
    r = subprocess.run(['/usr/bin/time', '-f', 'TIME %e %M', 'coqc', '-Q',
                        os.path.join(REPO, 'theories'), 'BBB4', v],
                       capture_output=True, text=True, cwd=d)
    t = re.findall(r'TIME ([\d.]+) (\d+)', r.stderr)
    if r.returncode != 0:
        err = [l for l in (r.stdout + r.stderr).splitlines() if l.startswith('Error') or 'line' in l]
        return None, 'coqc: ' + ' '.join(err[-2:])[:300]
    return v, 'ok %ss %d MB' % (t[-1][0], int(t[-1][1]) // 1024) if t else 'ok'


def add_to_coqproject(anchor, pfx, paths):
    p = os.path.join(REPO, '_CoqProject')
    lines = open(p).read().splitlines()
    have = set(lines)
    new = [x for x in paths if x not in have]
    i = lines.index(anchor) + 1
    while i < len(lines) and lines[i].startswith('theories/Machines/LadderTr/' + pfx):
        i += 1
    lines[i:i] = new
    open(p, 'w').write('\n'.join(lines) + '\n')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('rows', nargs='+')
    ap.add_argument('--kind', required=True, choices=sorted(KINDS))
    ap.add_argument('--tag', default='LE9')
    ap.add_argument('--chunk', type=int, default=8)
    ap.add_argument('--dry', action='store_true')
    a = ap.parse_args()
    K = KINDS[a.kind]
    remaining = set(l.strip() for l in open(os.path.join(REPO, 'closeouttr_remaining.txt')))
    qhc = set(l.split('\t')[0] for l in open(os.path.join(REPO, 'closeouttr_classes.tsv'))
              if l.split('\t')[1:2] == ['QH'])
    kept = []
    with tempfile.TemporaryDirectory() as tmp:
        for spec in a.rows:
            if spec not in remaining:
                print('%-30s not remaining, skipped' % spec)
                continue
            qh = spec in qhc
            d = os.path.join(tmp, mid(spec))
            os.makedirs(d)
            v, why = board1(a.kind, spec, qh, d)
            print('%-30s %s' % (spec, why), flush=True)
            if v is None:
                continue
            if not a.dry:
                shutil.copy(v, os.path.join(BOARDS, os.path.basename(v)))
            kept.append((spec, qh))
    if a.dry or not kept:
        print('%d of %d rows board' % (len(kept), len(a.rows)))
        return
    pfx = K['pfx']
    add_to_coqproject(K['anchor'], pfx,
                      ['theories/Machines/LadderTr/%s%s_%s.v' % (pfx, 'Q' if qh else '', mid(s))
                       for s, qh in kept])
    nn = next_free(a.tag)
    made = []
    for j in range(0, len(kept), a.chunk):
        chunk = kept[j:j + a.chunk]
        req = ['From BBB4.Machines.LadderTr Require %s.'
               % ' '.join('%s%s_%s' % (pfx, 'Q' if qh else '', mid(s)) for s, qh in chunk)]
        entries = []
        for s, qh in chunk:
            m = mid(s)
            b = '%s%s_%s' % (pfx, 'Q' if qh else '', m)
            if qh:
                entries.append((s, 'apply (coversTr_qh3_at %s.tm_%s); [exact %s.qhtr_%s | '
                                   'intros q s; destruct q, s; reflexivity].' % (b, m, b, m)))
            else:
                entries.append((s, 'apply (coversTr_nqh_at %s.tm_%s); [exact %s.nqhtr_%s | '
                                   'intros q s; destruct q, s; reflexivity].' % (b, m, b, m)))
        made.append(write_batch(a.tag, nn, req, entries, K['blurb']))
        nn += 1
    print('%d of %d rows boarded -> %s' % (len(kept), len(a.rows),
                                           ' '.join(os.path.relpath(x, REPO) for x in made)))


if __name__ == '__main__':
    main()
