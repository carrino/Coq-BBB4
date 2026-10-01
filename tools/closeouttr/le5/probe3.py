import json, sys, time
sys.path.insert(0, '.')
import emit_run3 as R
E = R.E
spec = sys.argv[1]
det = [json.loads(l) for l in open(sys.argv[2]) if json.loads(l)['spec'] == spec][0]
E.TR_PINS = E.unfired(spec, 10 ** 6)
seq = R.visits_seq(spec, det)
a, c = R.read_law(seq)
print('law', a, c, 'visits', len(seq))
tab = E.parse_tm(spec)
t = time.time()
cd = R.S.two_pass(lambda _c, _t: R.closure_data_run(det, tab, a, c, None), None, tab)
print(type(cd).__name__, cd if isinstance(cd, Exception) else {k: cd[k] for k in ('n0i', 'sti', 'n0t', 'stt', 'n0n', 'stn', 'n0r', 'str')}, '%.1fs' % (time.time() - t))
