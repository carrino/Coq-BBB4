"""does the real run's family set converge? data pass at growing leaf counts (UNTRUSTED)"""
import os, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'mp'))
import mp_find, rng6, lg3, lg4, lg_batch as G, ti_batch as T
spec = sys.argv[1]; nl = int(sys.argv[2])
G.MAXFAM = 100000
lang, mir, info = mp_find.get_lang(spec)
t0 = info.get('tboot') or 20000
tab = T.parse(spec)
if mir: tab = T.mirror(tab)
r2 = T.run_conc(tab, 60000)
pins = set(k for k in tab if k not in r2[4])
lg4.CANON['on'] = len(lang.unit) > 1 or len(lang.unitL) > 1
X = rng6.X6(tab, pins, lang)
boot = lg3.boot_of(X, tab, t0)
orig = X.fam_of
cnt = [0]; hist = []
def fo(*a, **k):
    r = orig(*a, **k); cnt[0] += 1
    if cnt[0] % 1000 == 0:
        hist.append((cnt[0], len(X.fams))); print(cnt[0], len(X.fams), flush=True)
    return r
X.fam_of = fo
t = time.time()
try:
    X.data_pass(boot, nl)
except T.Fail as e:
    print('stopped', e)
print('final', cnt[0], len(X.fams), round(time.time()-t,1))
