#!/usr/bin/env python3
"""Step-s ladder boards -> closeout batches (UNTRUSTED generator; SCOPING_INSTR
7.4.LE3).

    python3 tools/closeouttr/le3/step_batch.py STEP.jsonl... --tag LE3 [--chunk 40]

For every `closed` row of the valfam output (`vf_step.py`) whose family adds a
step > 1 per visit and that is still in closeouttr_remaining.txt, this runs
`emit_step.py` (with `--qh` for the class-QH rows), compiles the board, and
keeps it only if it compiled and carries the machine theorem.  Kept boards go
to theories/Machines/LadderTr/LDRS_<ID>.v (never-QH, [nqhtr_<ID>]) or
LDRSQ_<ID>.v (QH, [qhtr_<ID>]) and into _CoqProject after
LadderCheckStepTr.v; each batch row applies [coversTr_nqh_at] or
[coversTr_qh3_at].  Then run tools/closeouttr/gen_closeout_tr.py.
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
from cbt import REPO, next_free, write_batch  # noqa: E402

BOARDS = os.path.join(REPO, 'theories', 'Machines', 'LadderTr')
EMIT = os.path.join(HERE, 'emit_step.py')
ANCHOR = 'theories/Checkers/LadderCheckStepTr.v'
PFX = 'LDRS'
# --kind zeck: the Zeckendorf rows (valfam's "fibonacci(shifted)"), emit_zeck.py,
# LadderCheckZeckTr, LDRZ_/LDRZQ_ boards
KINDS = {
    'step': ('emit_step.py', 'theories/Checkers/LadderCheckStepTr.v', 'LDRS',
             lambda f: f.get('value_step_per_anchor_visit', 1) > 1,
             'counters that add a step s > 1 per anchor visit, by the value-family '
             'ladder (LadderCheckStepTr)'),
    'zeck': ('emit_zeck.py', 'theories/Checkers/LadderCheckZeckTr.v', 'LDRZ',
             lambda f: f.get('numeration') == 'fibonacci(shifted)',
             'Zeckendorf counters (weights 1, 2, 3, 5, ...), by LadderCheckZeckTr'),
}


def mid(spec):
    return spec.replace('-', '_')


def board(cert, tmp, qh):
    m = mid(cert['spec'])
    j = os.path.join(tmp, m + '.json')
    json.dump(cert, open(j, 'w'))
    v = os.path.join(tmp, '%s_%s.v' % (PFX + 'Q' if qh else PFX, m))
    r = subprocess.run([sys.executable, EMIT] + (['--qh'] if qh else [])
                       + [j, '-o', v], capture_output=True, text=True)
    if not os.path.exists(v):
        return None, 'emit failed: ' + (r.stderr.strip().splitlines() or ['?'])[-1]
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


def add_to_coqproject(paths):
    p = os.path.join(REPO, '_CoqProject')
    lines = open(p).read().splitlines()
    have = set(lines)
    new = [x for x in paths if x not in have]
    if not new:
        return
    i = lines.index(ANCHOR) + 1
    while i < len(lines) and lines[i].startswith('theories/Machines/LadderTr/' + PFX):
        i += 1
    lines[i:i] = new
    open(p, 'w').write('\n'.join(lines) + '\n')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('found', nargs='+')
    ap.add_argument('--tag', default='LE3')
    ap.add_argument('--chunk', type=int, default=40)
    ap.add_argument('--skip', action='append', default=[])
    ap.add_argument('--kind', default='step', choices=sorted(KINDS))
    a = ap.parse_args()
    global EMIT, ANCHOR, PFX
    emit, ANCHOR, PFX, want, blurb = KINDS[a.kind]
    EMIT = os.path.join(HERE, emit)
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
                    and s not in a.skip
                    and want(c['family'])):
                seen.add(s)
                certs.append(c)
    os.makedirs(BOARDS, exist_ok=True)
    kept = []
    with tempfile.TemporaryDirectory() as tmp:
        for c in sorted(certs, key=lambda c: c['spec']):
            qh = c['spec'] in qhc
            v, why = board(c, tmp, qh)
            if v is None:
                print('%-30s no board: %s' % (c['spec'], why[:160]), flush=True)
                continue
            dst = os.path.join(BOARDS, os.path.basename(v))
            shutil.copy(v, dst)
            kept.append((c['spec'], qh))
            print('%-30s board %s' % (c['spec'], os.path.relpath(dst, REPO)), flush=True)
    add_to_coqproject(['theories/Machines/LadderTr/%s_%s.v'
                       % (PFX + 'Q' if qh else PFX, mid(s)) for s, qh in kept])
    nn = next_free(a.tag)
    made = []
    for i in range(0, len(kept), a.chunk):
        chunk = kept[i:i + a.chunk]
        req = ['From BBB4.Machines.LadderTr Require %s.'
               % ' '.join('%s_%s' % (PFX + 'Q' if qh else PFX, mid(s))
                          for s, qh in chunk)]
        entries = []
        for s, qh in chunk:
            m = mid(s)
            if qh:
                entries.append((s, 'apply (coversTr_qh3_at %sQ_%s.tm_%s); '
                                   '[exact %sQ_%s.qhtr_%s | intros q s; destruct q, s; '
                                   'reflexivity].' % (PFX, m, m, PFX, m, m)))
            else:
                entries.append((s, 'apply (coversTr_nqh_at %s_%s.tm_%s); '
                                   '[exact %s_%s.nqhtr_%s | intros q s; destruct q, s; '
                                   'reflexivity].' % (PFX, m, m, PFX, m, m)))
        made.append(write_batch(a.tag, nn, req, entries, blurb))
        nn += 1
    print('%d of %d closed rows boarded -> %d batch file(s): %s'
          % (len(kept), len(certs), len(made),
             ' '.join(os.path.relpath(p, REPO) for p in made)))


if __name__ == '__main__':
    main()
