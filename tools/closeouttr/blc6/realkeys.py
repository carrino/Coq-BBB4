import os, sys, time, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'mp'))
import mp_find, rng6, lg3, lg4, lg_batch as G, ti_batch as T
spec = sys.argv[1]; nl = int(sys.argv[2])
G.MAXFAM = 100000
lang, mir, info = mp_find.get_lang(spec)
print('lang a', lang.a, 'unit', lang.unit, 'unitL', lang.unitL, 'seps', lang.seps, 'sepsL', lang.sepsL, 'mir', mir)
t0 = info.get('tboot') or 20000
tab = T.parse(spec)
if mir: tab = T.mirror(tab)
r2 = T.run_conc(tab, 60000)
pins = set(k for k in tab if k not in r2[4])
lg4.CANON['on'] = len(lang.unit) > 1 or len(lang.unitL) > 1
X = rng6.X6(tab, pins, lang)
boot = lg3.boot_of(X, tab, t0)
seen = collections.Counter()
orig = X.fam_of
def fo(q,h,L,R,tails,boot=False):
    n0=len(X.fams); r = orig(q,h,L,R,tails,boot)
    if len(X.fams)>n0 and len(X.fams)>int(sys.argv[3]):
        print('NEW', len(X.fams)-1, q, h, 'L=',[ (x[0],''.join(map(str,x[1])), x[2][0] if x[0]=='B' else '') for x in L][:8], 'R=',[(x[0],''.join(map(str,x[1])), x[2][0] if x[0]=='B' else '') for x in R][:8], 'tails', {k:(None if v is None else str(v[0])[:60]) for k,v in tails.items()})
    return r
X.fam_of = fo
try:
    X.data_pass(boot, nl)
except T.Fail as e:
    print('stopped', e)
print('final', len(X.fams))
