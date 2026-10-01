"""which right/left folds miss during the exploration (UNTRUSTED diagnostics)"""
import os, sys, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'mp'))
import mp_find, rng6, lg_batch as G
spec = sys.argv[1]; G.MAXFAM = int(sys.argv[2])
import find6
lang, mir, info = find6.get_lang(spec)
t0 = info.get('tboot') or 20000
miss = collections.Counter(); hit = collections.Counter()
class MD(dict):
    def get(self, k, d=None):
        r = dict.get(self, k, d)
        sd, cur, kind, rel = k
        key = (sd, str(cur)[:30] if sd == 'L' else (cur[1][1] if isinstance(cur, tuple) and len(cur) > 1 and isinstance(cur[1], tuple) else cur), kind, rel)
        (miss if r is None else hit)[(sd, kind, rel)] += 1
        return r
orig = rng6.X6.__init__
def init(self, *a, **k):
    orig(self, *a, **k); self.foldmap = MD(self.foldmap)
rng6.X6.__init__ = init
try:
    X, pins, boot = rng6.explore_row(spec, lang, t0, mir); print('CLOSED', len(X.fams))
except rng6.Fail as e:
    print('FAIL', e)
kn = lang.nfa.kinds
def nm(k):
    sd, kind, rel = k
    side, pre, u = kn[kind]
    return (sd, ''.join(map(str, pre)), ''.join(map(str, u)), rel)
print('MISSES')
for k, v in miss.most_common(30):
    print(' ', nm(k), v, 'hits', hit[k])
print('HITS')
for k, v in hit.most_common(30):
    print(' ', nm(k), v)
