#!/usr/bin/env python3
"""Per-row table of the MPU survey (UNTRUSTED bookkeeping).

    python3 tools/closeouttr/mp/survey_report.py > tools/closeouttr/mp/survey_unlearned.tsv

Columns: spec, class, shape group (survey_groups.py), routes tried (earlier
workstreams' recorded verdicts, then this survey's runs in
tools/closeouttr/mp/runs/), result.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CT = os.path.join(HERE, '..')
REPO = os.path.join(CT, '..', '..')
sys.path.insert(0, HERE)
from survey_groups import G  # noqa: E402


def jl(p):
    out = {}
    if os.path.exists(p):
        for l in open(p):
            if l.strip():
                d = json.loads(l)
                out[d['spec']] = d
    return out


def jlist(p):
    out = {}
    if os.path.exists(p):
        for d in json.load(open(p)):
            out[d['spec']] = d
    return out


def tsv(p, k=0):
    out = {}
    for l in open(p):
        if l.startswith('#') or not l.strip():
            continue
        x = l.rstrip('\n').split('\t')
        out.setdefault(x[k], []).append(x)
    return out


rows = [l.strip() for l in open(os.path.join(HERE, 'rows_unlearned.txt')) if l.strip()]
cls = {l.split('\t')[0]: l.split('\t')[1] for l in open(os.path.join(REPO, 'closeouttr_classes.tsv'))
       if not l.startswith('#') and '\t' in l}
R = os.path.join(HERE, 'runs')
blc5 = jl(os.path.join(CT, 'blc5', 'sweep191.jsonl'))
blti = jl(os.path.join(CT, 'bl', 'find1.jsonl'))
hy2 = tsv(os.path.join(CT, 'hy2', 'residue.tsv'))
ng = tsv(os.path.join(CT, 'ng_probe_dn.tsv'))
rk8old = json.load(open(os.path.join(CT, 'bx', 'ng_rk8.json')))
mbold = {}
for f in ('mb/mb_find_144.json', 'mb/mb_found_longper.json', 'bl/mb_long.json'):
    mbold.update(jlist(os.path.join(CT, f)))
hy3 = jl(os.path.join(R, 'hy3.jsonl'))
hy3old = tsv(os.path.join(CT, 'hy3', 'residue.tsv'))
mb50 = jlist(os.path.join(R, 'mb50.json'))
mbh = jlist(os.path.join(R, 'mb_heavy.json'))
mbm = jlist(os.path.join(R, 'mbmem.json'))
hy2w = jl(os.path.join(R, 'hy2w.jsonl'))
rk8 = json.load(open(os.path.join(R, 'rk8.json'))) if os.path.exists(os.path.join(R, 'rk8.json')) else {}
boarded = {}
for f in sorted(os.listdir(os.path.join(REPO, 'theories', 'CloseoutTr'))):
    if f.startswith('CBT_MPU_') and f.endswith('.v'):
        for l in open(os.path.join(REPO, 'theories', 'CloseoutTr', f)):
            if l.startswith('(* spec '):
                boarded[l.split()[2]] = f[:-2]

print('# spec\tclass\tgroup\troutes tried (verdict)\tresult')
for r in rows:
    tr = ['lx5: ' + str(blc5.get(r, {}).get('err', '?'))]
    if r in blti:
        tr.append('bl_ti: fail')
    if r in hy2:
        tr.append('hy2: ' + hy2[r][0][2])
    tr.append('rk4-6: ' + ','.join(x[2] for x in ng.get(r, [])))
    if r in rk8old:
        tr.append('rk8(BX): ' + rk8old[r]['rk:8:0'][0])
    if r in rk8:
        tr.append('rk8: ' + rk8[r]['rk:8:0'][0])
    if r in mbold:
        tr.append('mb(MB/BL): ' + ('ok %s nodes' % mbold[r].get('nodes') if mbold[r].get('ok') else 'no'))
    if r in mb50:
        tr.append('mb pmax32: ' + ('ok' if mb50[r].get('ok') else ','.join(mb50[r].get('why', {}))))
    if r in mbh:
        tr.append('mb pmax64 polish900: ok %s nodes' % mbh[r].get('nodes'))
    if r in mbm:
        tr.append('mb pmax32 5GB 600s: no')
    if r in hy3old:
        tr.append('hy3_ti(HY3): ' + hy3old[r][0][2])
    if r in hy3:
        tr.append('hy3_ti: ' + ('ok' if 'err' not in hy3[r] else 'fail'))
    if r in hy2w:
        tr.append('hy2w: ' + hy2w[r].get('err', 'ok'))
    res = 'boarded ' + boarded[r] if r in boarded else 'open'
    print('\t'.join([r, cls.get(r, '?'), G[r], '; '.join(tr), res]))
