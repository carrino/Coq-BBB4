"""MP diagnostic (UNTRUSTED; SCOPING_INSTR.md §7.4.MP): blc4/diag4.py on a CACHED language
(mp_find.py's pickle), with the first unreal families whose parent is real.

    cd tools/closeouttr && [MP_DEPTH=3] python3 mp/diag_mp.py SPEC NLEAVES MAXFAM LANG.pkl
"""
import os, sys, pickle
sys.path.insert(0,'blc4'); sys.path.insert(0,'blc3'); sys.path.insert(0,'.')
import learn4 as L, lg4, lg3, lg_batch as G, ti_batch as T
spec = sys.argv[1]; nl = int(sys.argv[2]); G.MAXFAM = int(sys.argv[3])
lang, mir, info = pickle.load(open(sys.argv[4],'rb'))
if os.environ.get('MP_DEPTH'):
    sys.path.insert(0,'mp'); import lang_mp; lang=lang_mp.with_depth(lang)
t0 = info.get('tboot') or 20000
tab = T.parse(spec)
if mir: tab = T.mirror(tab)
r2 = T.run_conc(tab, 60000)
pins = set(k for k in tab if k not in r2[4])
lg4.CANON['on'] = len(lang.unit) > 1 or len(lang.unitL) > 1
Xr = lg4.X4(tab, pins, lang)
boot = lg3.boot_of(Xr, tab, t0)
try: Xr.data_pass(boot, nl)
except T.Fail as e: print('data pass stopped:', e)
real = set(Xr.fidx); print('real run: %d families' % len(real))
Xe = lg4.X4(tab, pins, lang)
parent = {}; orig = Xe.explore_fam; cur = [None]
def ef(fid, todo):
    cur[0] = fid; return orig(fid, todo)
Xe.explore_fam = ef
of = Xe.fam_of
def fo(*a, **k):
    n0 = len(Xe.fams); r = of(*a, **k)
    if len(Xe.fams) > n0: parent[r[0]] = cur[0]
    return r
Xe.fam_of = fo
boot = lg3.boot_of(Xe, tab, t0)
try:
    Xe.explore(boot); print('exploration closes')
except T.Fail as e: print('exploration:', e)
bad = [i for i, F in enumerate(Xe.fams) if F.key not in real]
print('%d of %d explored families the real run never visits' % (len(bad), len(Xe.fams)))
# first-generation unreal: parent is real
first=[i for i in bad if parent.get(i) is not None and Xe.fams[parent[i]].key in real]
print('%d unreal families with a real parent' % len(first))
for i in first[:int(os.environ.get('DIAG_N', '25'))]:
    p = parent.get(i)
    print('  %d %s' % (i, lg3.fmt_key(Xe.fams[i].key)[:260]))
    print('     <- %d %s' % (p, lg3.fmt_key(Xe.fams[p].key)[:260]))
pickle.dump(([lg3.fmt_key(F.key) for F in Xr.fams],[lg3.fmt_key(F.key) for F in Xe.fams],parent), open('diag_%s.pkl'%spec,'wb'))
