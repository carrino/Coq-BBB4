#!/usr/bin/env python3
"""UNTRUSTED: close a row from its value FAMILY alone, when valfam's arm
miner did not (SCOPING_INSTR 7.4.CE3).

valfam reads a counter in two stages: the FAMILY (anchor, digits, fill law,
boot) and then ARMS mined by symbolic replay, whose step counts are affine.
A row whose carry costs quadratic time has a family and no such arms, and is
filed as "families found but none closed".  But [emit_ladder.closure_data]
never uses the mined arms: it builds the class arms from the family, and
with [LadderNest] it can prove a quadratic arm as a chain of chains.  So
this driver skips the arm miner: for each candidate family of the pool it
writes a certificate carrying the family, its fill laws and its boot (and no
arms), and asks the emitter for a closure.  The first family whose board
carries the machine theorem is kept, marked [closed], for
tools/closeouttr/sp_ladder_batch.py.

    python3 famclose.py --list ROWS --json fc.jsonl [--jobs 3] [--qh]

The output is one line per row (resumable), [closed] or with the reason each
family failed.  Nothing here carries proof weight.
"""
import argparse
import copy
import json
import multiprocessing as mp
import os
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

import valfam as VF                                              # noqa: E402
from engine import parse_tm                                      # noqa: E402
from trace import simulate                                       # noqa: E402

EMIT = os.path.join(HERE, 'emit_ladder.py')


def family_certs(spec, steps=20000, cap=90.0, numeration=False, most=8):
    """[(i, cert)] for the first [most] one-parameter families of the pool,
    each with its fill laws and boot; no arms."""
    VF._WALKS.clear()
    VF._COVERS.clear()
    tm = parse_tm(spec)
    snaps = simulate(tm, steps)
    if snaps and snaps[-1][1] is None:
        return []
    from discover import mine_shapes, build_ladder
    table = mine_shapes(snaps)
    rules = build_ladder(tm, table, time_cap=max(20.0, cap * 0.35))
    if not rules:
        return []
    fams = VF.find_families(tm, snaps, rules, numeration=numeration)
    out = []
    for i, (fam, _ft, _ch) in enumerate(fams[:most]):
        if fam.otmpl is not None:
            continue
        try:
            walk = VF.anchor_cells(fam, tm)
            VF.fit_phases(fam, walk)
            obs = VF.observe_fill(fam, walk)
            if fam.fills is None:
                fam.fills = VF.fit_fills(fam, obs) or [VF.fam_fill(fam, 0)]
            if any(f.moves_p() for f in fam.fills):
                continue
            bt, bds, bp, bph = VF.find_boot(fam, snaps)
        except Exception:                                   # noqa: BLE001
            continue
        if bt is None or not bds:
            continue
        out.append((i, {
            'spec': spec, 'closed': False, 'famclose': i,
            'family': fam.json(), 'fill': fam.fill.json(),
            'fill_by_phase': [f.json() for f in fam.fills],
            'boot': {'steps_from_blank': bt, 'digits_lsb_first': bds,
                     'value': fam.value(bds), 'p': bp, 'phase': bph,
                     'cells': fam.encode(bds, bph, bp)},
            'liveness': {}, 'arms': [], 'ladder': []}))
    return out


def try_cert(cert, qh, tmp):
    """None if the emitted board carries the machine theorem, else why not"""
    mid = cert['spec'].replace('-', '_')
    j = os.path.join(tmp, mid + '.json')
    json.dump(cert, open(j, 'w'))
    v = os.path.join(tmp, mid + '.v')
    try:
        r = subprocess.run([sys.executable, EMIT, '--tr'] + (['--qh'] if qh else [])
                           + [j, '-o', v], capture_output=True, text=True,
                           timeout=600)
    except subprocess.TimeoutExpired:
        return 'emit timeout'
    if r.returncode != 0 or not os.path.exists(v):
        return 'emit failed: ' + (r.stderr.strip().splitlines() or ['?'])[-1][:150]
    txt = open(v).read()
    if ('Theorem %s_%s ' % ('qhtr' if qh else 'nqhtr', mid)) in txt:
        return None
    why = [l for l in txt.splitlines() if 'NOT BUILT' in l]
    return why[0].split('--', 1)[-1].strip()[:200] if why else 'no closure'


def run_row(args):
    spec, qh, cap, numeration = args
    t0 = time.time()
    res = {'spec': spec, 'closed': False, 'famclose_tried': []}
    try:
        cands = family_certs(spec, cap=cap, numeration=numeration)
    except Exception as e:                                  # noqa: BLE001
        res['reason'] = 'family pass failed: %r' % (e,)
        return res
    if not cands:
        res['reason'] = 'no one-parameter family with a boot'
        return res
    with tempfile.TemporaryDirectory() as tmp:
        for i, cert in cands:
            why = try_cert(cert, qh, tmp)
            if why is None:
                cert = copy.deepcopy(cert)
                cert['closed'] = True
                cert['seconds'] = round(time.time() - t0, 1)
                return cert
            res['famclose_tried'].append({'family': i, 'reason': why})
    res['reason'] = 'no family closes'
    res['seconds'] = round(time.time() - t0, 1)
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list', required=True)
    ap.add_argument('--json', required=True)
    ap.add_argument('--jobs', type=int, default=2)
    ap.add_argument('--cap', type=float, default=90.0)
    ap.add_argument('--qh', action='store_true',
                    help='the rows quasihalt: LDRQ boards (emit --tr --qh)')
    ap.add_argument('--numeration', action='store_true')
    a = ap.parse_args()
    specs = [l.split()[0] for l in open(a.list) if l.strip()]
    done = set()
    if os.path.exists(a.json):
        for l in open(a.json):
            try:
                done.add(json.loads(l)['spec'])
            except (ValueError, KeyError):
                pass
    todo = [(s, a.qh, a.cap, a.numeration) for s in specs if s not in done]
    with open(a.json, 'a') as jf, mp.Pool(a.jobs) as pool:
        for r in pool.imap_unordered(run_row, todo):
            jf.write(json.dumps(r) + '\n')
            jf.flush()
            print('%-30s %s' % (r['spec'], 'CLOSED' if r['closed']
                                else r.get('reason')), flush=True)


if __name__ == '__main__':
    main()
