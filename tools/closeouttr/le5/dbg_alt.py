import json, sys
import emit_ph as P
E = P.E
spec = sys.argv[1]
det = [json.loads(l) for l in open(sys.argv[2]) if spec in l][0]
E.TR_PINS = E.unfired(spec, 10 ** 6)
md = P.model_alt(spec, det, -1)
print(md['phases'], md['mvT'], md['boot'])
xe, xn, nr = P.flags(md)
fT, A, B, g = P.rank_fire(md)
print('fT', fT, A, B, g, 'nr', nr)
tab = E.parse_tm(spec)
D0, D1 = (P.bits(w) for w in md['D'])
PH = md['phases']
def conf(p, sd):
    q, hs, side, oth = PH[p]['key']
    O = (P.bits(oth), (), 0, 0, ())
    return (q, sd, hs, O) if side == 'L' else (q, O, hs, sd)
want = [(q_, s_) for q_ in range(4) for s_ in range(2) if (q_, s_) not in E.TR_PINS]
for p, t in md['mvT'].items():
    for r in range(0, 4):
        for st in (0, 1, 2):
            c0 = conf(p, P.blk(D1 * r, D1, st, P.bits(PH[p]['W'])))
            c1 = conf(t[1], P.blk(D0 * (r + t[2]), D0, st, P.bits(PH[t[1]]['W'])))
            try:
                ch = P.Arms(tab).derive(True, True, c0, c1, 'x')
                sv = P.nvisits_f(tab, want, True, True, c0, ch)
                print(p, r, st, 'ok', 'missing', [i for i in want if i not in sv])
            except P.NoClosure as e:
                print(p, r, st, str(e)[:70])
