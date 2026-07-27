#!/usr/bin/env python3
"""UNTRUSTED Stage-C prototype for the nested lap.

STAGE C PROTOTYPE: do the BOOT and EXIT chains derive with the EXISTING
chain search?  That is the only open question left in NESTED_LAP_PLAN -- the
Coq (Stage B) is done and the inner family is found (Stage A).

Endpoints, all affine in the outer index j (so ordinary sside's, a=1):

  outer all-ones   B0_out = rep uS_out (j+obS) ++ soS_out ++ tail_out
  inner start      Cin(pow2 j)        = rep uD_in j ++ soD_in ++ tail_in
  inner fill       Cin(fill(pow2 j))  = rep uS_in j ++ soD_in ++ tail_in
  outer successor  B1_out = rep uD_out (S j) ++ soD_out ++ tail_out

(E(2q)=A++E(q) and E(1)=C give E(2^j) = rep A j ++ C, with A=uD, C=soD;
 all-ones of width j+1 is rep B j ++ C with B=uS.)
"""
import sys, os, json, collections
sys.path.insert(0, '/home/user/Coq-BBB4/tools/counters')
os.chdir('/home/user/Coq-BBB4')
import emit_lapcert as EL
import innerfam as IF
from emit_interleave import parse
from mirror_common import mirror_spec
import lapcert as LC
LAB = 'ABCD'

def try_machine(spec, K=6):
    r = IF.phase_probe(spec, K=K)
    if r is None or not r['inner']:
        return None
    exact = [i for i in r['inner'] if i['kind'].startswith('EXACT')]
    if not exact:
        return dict(spec=spec, why='inner not at pow2 j (octave/offset)')
    # MEASURED (docs/NESTED_LAP_PLAN.md Stage C): the best-scoring key is
    # almost never the one the boot chain can land on -- enumerate, do not
    # rank.  This prototype still takes the first; that is the known defect.
    name_in, st_in, tail_in, far_in = exact[0]['key']
    tab = parse(spec)
    dout, din = EL.ENCDATA[r['enc']], EL.ENCDATA[name_in]
    st_out = LAB.index(r['st0'])
    tail_out, far_out = tuple(r['tail']), tuple(r['far'])
    Fout = (far_out, (), 0, 0, ())
    Fin = (tuple(far_in), (), 0, 0, ())
    ob = dout['obS']
    if ob >= 1:
        B0out = (st_out, (dout['uS'], dout['uS'], 1, ob - 1,
                          dout['soS'] + tail_out), 0, Fout)
    else:
        B0out = (st_out, ((), dout['uS'], 1, 0, dout['soS'] + tail_out), 0, Fout)
    B1out = (st_out, ((), dout['uD'], 1, 1, dout['soD'] + tail_out), 0, Fout)
    ti = tuple(tail_in)
    CinS = (st_in, ((), din['uD'], 1, 0, din['soD'] + ti), 0, Fin)   # pow2 j
    CinF = (st_in, ((), din['uS'], 1, 0, din['soD'] + ti), 0, Fin)   # fill
    out = dict(spec=spec, outer=r['enc'], inner=name_in,
               st_out=r['st0'], st_in=LAB[st_in])
    for tag, a, b in (('boot', B0out, CinS), ('exit', CinF, B1out)):
        ch = None
        for (el, er) in ((True, True), (False, True), (True, False)):
            try:
                ch = LC.derive_chain(tab, el, er, a, b)
            except Exception:
                ch = None
            if ch is not None:
                out[tag] = '%s len=%d el=%s er=%s' % (tag, len(ch), el, er)
                break
        if ch is None:
            out[tag] = None
    return out

rows = []
for line in open(sys.argv[1]):
    spec = line.strip()
    if not spec: continue
    got = None
    for s in (spec, mirror_spec(spec)):
        try:
            got = try_machine(s)
        except Exception as e:
            got = dict(spec=s, why='ERR %s' % e)
        if got and got.get('boot') and got.get('exit'):
            break
    if got is None:
        print('%s  NO-INNER' % spec, flush=True); rows.append(None); continue
    print('%s  out=%s@%s in=%s@%s  boot=%s  exit=%s' % (
        spec, got.get('outer'), got.get('st_out'), got.get('inner'),
        got.get('st_in'), got.get('boot'), got.get('exit')), flush=True)
    rows.append(got)

ok = [r for r in rows if r and r.get('boot') and r.get('exit')]
bo = [r for r in rows if r and r.get('boot')]
print('\n=== %d/%d machines: BOTH boot and exit chains derived ===' % (len(ok), len(rows)))
print('=== %d had a boot chain ===' % len(bo))
