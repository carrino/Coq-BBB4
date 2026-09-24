#!/usr/bin/env python3
"""Instruction-level ladder boards -> closeout batches for class SP
(UNTRUSTED generator).

    # 1. the untrusted finder, per row (about a minute each)
    cd tools/ladder && python3 valfam.py --list ROWS --cap 150 --json vf.jsonl
    # 2. boards + batches
    python3 tools/closeouttr/sp_ladder_batch.py vf.jsonl --tag SP [--chunk 50]

For every `closed` row of the valfam output that is still in
closeouttr_remaining.txt, this runs `emit_ladder.py --tr` (the board of
LadderCheck, re-pointed at the machine wrapped at its never-fired
instructions, closed by [LadderCheckTr.boardph_neverqhtr] to
[NeverQuasiHaltsTr]), compiles the board, and keeps it only if it compiled
AND carries the machine theorem (a row whose closure the emitter could not
build gets a board without one).  The kept boards go to
theories/Machines/LadderTr/LDRT_<ID>.v and into _CoqProject; each batch row
applies [coversTr_nqh_at] to the board's [nqhtr_<ID>].  Then run
tools/closeouttr/gen_closeout_tr.py.
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from cbt import REPO, next_free, write_batch  # noqa: E402

BOARDS = os.path.join(REPO, 'theories', 'Machines', 'LadderTr')
EMIT = os.path.join(REPO, 'tools', 'ladder', 'emit_ladder.py')
ANCHOR = 'theories/Checkers/LadderCheckTr.v'


def mid(spec):
    return spec.replace('-', '_')


def board(cert, tmp):
    """emit + compile one board; the path of a good one, or (None, why)"""
    m = mid(cert['spec'])
    j = os.path.join(tmp, m + '.json')
    json.dump(cert, open(j, 'w'))
    v = os.path.join(tmp, 'LDRT_%s.v' % m)
    r = subprocess.run([sys.executable, EMIT, '--tr', j, '-o', v],
                       capture_output=True, text=True)
    if r.returncode != 0 or not os.path.exists(v):
        return None, 'emit failed: ' + (r.stderr.strip().splitlines() or ['?'])[-1]
    if 'Theorem nqhtr_%s ' % m not in open(v).read():
        why = [l for l in open(v) if 'NOT BUILT' in l]
        return None, (why[0].strip() if why else 'no closure')
    r = subprocess.run(['coqc', '-Q', os.path.join(REPO, 'theories'), 'BBB4', v],
                       capture_output=True, text=True, cwd=tmp)
    if r.returncode != 0:
        return None, 'coqc: ' + (r.stdout + r.stderr).strip().splitlines()[-1]
    return v, None


def add_to_coqproject(paths):
    p = os.path.join(REPO, '_CoqProject')
    lines = open(p).read().splitlines()
    have = set(lines)
    new = [x for x in paths if x not in have]
    if not new:
        return
    i = lines.index(ANCHOR) + 1
    while i < len(lines) and lines[i].startswith('theories/Machines/LadderTr/'):
        i += 1
    lines[i:i] = new
    open(p, 'w').write('\n'.join(lines) + '\n')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('found', nargs='+', help='valfam --json output (JSON lines)')
    ap.add_argument('--tag', default='SP')
    ap.add_argument('--chunk', type=int, default=50)
    ap.add_argument('--skip', action='append', default=[])
    a = ap.parse_args()
    remaining = set(l.strip() for l in open(os.path.join(REPO, 'closeouttr_remaining.txt')))
    certs, seen = [], set()
    for f in a.found:
        for line in open(f):
            if not line.strip():
                continue
            c = json.loads(line)
            s = c.get('spec')
            if c.get('closed') and s in remaining and s not in seen and s not in a.skip:
                seen.add(s)
                certs.append(c)
    os.makedirs(BOARDS, exist_ok=True)
    kept = []
    with tempfile.TemporaryDirectory() as tmp:
        for c in sorted(certs, key=lambda c: c['spec']):
            v, why = board(c, tmp)
            if v is None:
                print('%-30s no board: %s' % (c['spec'], why[:120]), flush=True)
                continue
            dst = os.path.join(BOARDS, os.path.basename(v))
            shutil.copy(v, dst)
            kept.append(c['spec'])
            print('%-30s board %s' % (c['spec'], os.path.relpath(dst, REPO)), flush=True)
    add_to_coqproject(['theories/Machines/LadderTr/LDRT_%s.v' % mid(s) for s in kept])
    nn = next_free(a.tag)
    made = []
    for i in range(0, len(kept), a.chunk):
        chunk = kept[i:i + a.chunk]
        req = ['From BBB4.Machines.LadderTr Require %s.'
               % ' '.join('LDRT_%s' % mid(s) for s in chunk)]
        entries = [(s, 'apply (coversTr_nqh_at LDRT_%s.tm_%s); '
                       '[exact LDRT_%s.nqhtr_%s | intros q s; destruct q, s; reflexivity].'
                    % (mid(s), mid(s), mid(s), mid(s))) for s in chunk]
        made.append(write_batch(a.tag, nn, req, entries,
                                'never-QH by the value-family ladder at the instruction '
                                'level (LadderCheckTr)'))
        nn += 1
    print('%d of %d closed rows boarded -> %d batch file(s): %s'
          % (len(kept), len(certs), len(made),
             ' '.join(os.path.relpath(p, REPO) for p in made)))


if __name__ == '__main__':
    main()
