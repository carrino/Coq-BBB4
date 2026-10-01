"""try6 with per-family timing (UNTRUSTED diagnostics)"""
import os, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'mp'))
import mp_find, rng6, lg3                                          # noqa: E402
spec = sys.argv[1]
import find6
lang, mir, info = find6.get_lang(spec)
t0 = info.get('tboot') or 20000
orig = rng6.X6.explore_fam
def ef(self, fid, todo):
    t = time.time()
    try:
        return orig(self, fid, todo)
    finally:
        dt = time.time() - t
        if dt > 2:
            F = self.fams[fid]
            print('FAM %d %.1fs leaves=%d unodes=%d n=%d %s' % (fid, dt, len(self.fleaves.get(fid, [])),
                  len(self.utrees.get(fid, [])), F.n, lg3.fmt_key(F.key)[:200]), dict(rng6.STATS), flush=True)
rng6.X6.explore_fam = ef
t = time.time()
try:
    X, pins, boot = rng6.explore_row(spec, lang, t0, mir)
    print('CLOSED', len(X.fams), 'families', dict(rng6.STATS), round(time.time() - t, 1), 's')
except rng6.Fail as e:
    print('FAIL', e, dict(rng6.STATS), round(time.time() - t, 1), 's')
