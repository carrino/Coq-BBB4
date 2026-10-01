"""quick experiment: explore one row with/without range voids (UNTRUSTED)"""
import os, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'mp'))
import mp_find                                     # noqa: E402
import rng6                                        # noqa: E402
spec = sys.argv[1]
t0 = int(sys.argv[2]) if len(sys.argv) > 2 else 0
lang, mir, info = mp_find.get_lang(spec)
if not t0:
    t0 = info.get('tboot') or 20000
t = time.time()
try:
    X, pins, boot = rng6.explore_row(spec, lang, t0, mir)
    print('CLOSED', len(X.fams), 'families', dict(rng6.STATS), round(time.time() - t, 1), 's')
except rng6.Fail as e:
    print('FAIL', e, dict(rng6.STATS), round(time.time() - t, 1), 's')
