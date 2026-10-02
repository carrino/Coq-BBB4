import json, sys
import emit_phrun as P
E = P.E
spec = sys.argv[1]
det = [json.loads(l) for l in open('phrun_res.jsonl') if spec in l][0]
E.TR_PINS = E.unfired(spec, 10 ** 6)
names, idx, mvT, mvE, xe, nm = P.table_moves(det)
print(names, mvT, mvE, xe)
seq = P.visits(spec, det)
bt = P.find_boot(seq, det, idx, nm, mvT, mvE, xe, -1)
print('boot', bt)
nr = P.runless(names, mvT, mvE, bt[1][1], bt[1][2])
print('nr', nr, 'rank', P.rank(names, mvT, mvE) if True else None)
tab = E.parse_tm(spec)
T = P.bits(det['T']); pre = P.bits(det['pre']); D0, D1 = (P.bits(w) for w in det['D'])
W = [P.bits(w.split('|')[0]) for w in names]; V = [P.bits(w.split('|')[1]) for w in names]
q, hs, side = det['anchor']; left = side == 'L'; OTHER = ((), (), 0, 0, ())
conf = lambda sd: (q, sd, hs, OTHER) if left else (q, OTHER, hs, sd)
for p in range(len(names)):
    t = mvE[p]
    if t[0] != 'ER': continue
    _e, a, q2, c = t
    for r in range(0, 4):
        c0 = conf(P.blk(pre + W[p] + T * r, T, 0, V[p]))
        ok = None
        for f1 in P._splits(r + a):
            c1 = conf(P.blk(pre + D0 * f1, D0, 0, D0 * (r + a - f1) + W[q2] + T * c + V[q2]))
            try:
                ch = P.Arms(tab).derive(True, True, c0, c1, 'x'); ok = (f1, ch); break
            except P.NoClosure as e: ok = str(e)
        print('refill', p, r, ok if isinstance(ok, str) else 'ok')
        # simulate concretely
        got = E.LC.srun(tab, True, True, [('SWin', 2000)], c0)
        print('   sim', got[0] if got else None)
want = [(q_, s_) for q_ in range(4) for s_ in range(2) if (q_, s_) not in E.TR_PINS]
print('want', want, 'pins', E.TR_PINS)
for p in range(len(names)):
    t = mvE[p]
    if t[0] != 'ER': continue
    _e, a, q2, c = t
    for r in range(0, 3):
        for st in (0, 1):
            c0 = conf(P.blk(pre + W[p] + T * r, T, st, V[p]))
            for f1 in P._splits(r + a):
                c1 = conf(P.blk(pre + D0 * f1, D0, st, D0 * (r + a - f1) + W[q2] + T * c + V[q2]))
                try:
                    ch = P.Arms(tab).derive(True, True, c0, c1, 'x'); break
                except P.NoClosure: ch = None
            seen = P.nvisits(tab, want, c0, ch)
            print('fires p=%d r=%d st=%d' % (p, r, st), sorted(seen), 'missing', [i for i in want if i not in seen])
