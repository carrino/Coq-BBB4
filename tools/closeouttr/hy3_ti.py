#!/usr/bin/env python3
"""TriGlueTr families seeded at the ANCHORS (UNTRUSTED finder), for the HY3
workstream (SCOPING_INSTR.md §7.4.HY3).

    python3 tools/closeouttr/hy3_ti.py find ROWS.txt OUT.jsonl [--jobs 4] [--timeout 300]
    python3 tools/closeouttr/hy3_ti.py batch OUT.jsonl [...] --tag HY3 [--chunk 10]

The unary counters of §7.4.HY2's residue ("two blocks of one unit, one
growing linearly and one slowly") are two-block transfers with a reset:
at every sweep turn the tape is

    Lpre  u^a  Mid  v^b  Rpost        (a, b) -> (a + da, b - 1) per lap,

and when b runs out the machine rewrites the tape into a new pair
(a0, alpha * a + beta).  TriGlueTr's families (symbolic tapes with affine
exponents, one LapDecider chain per leaf, affine rankings for the fires)
state this exactly; what failed was the search.  `ti_batch.py` turns every
literal run of two or more copies into a fresh variable, so the constant
junctions (`11111`, `(1)^4`) become variables too, and a variable explored
at every length opens shapes the machine never produces (a 1-block that is
always `3a + 4` long, explored mod 3).  `bl_ti.py` gives variables a
lattice `c + g*x`, but seeds it by a generic concrete pass, which on these
rows either keeps the boot's blocks concrete (a leaf then runs the whole
lap cell by cell: "leaf too long") or starts them generic ("too many
families").

Here the seed is read off the run itself.  The configurations at the sweep
turns, normalized as the explorer normalizes a leaf's end, are grouped by
family key; over one key's turns a block exponent that never changes is a
constant (lattice step 0) and one that does gets `c` = the least value
seen and `g` = the gcd of the differences.  The boot is the first turn of
a frequent key, and every family met later starts as a constant (bl_ti's
G0 = 0) and is widened only by the affine exponents leaves land on it
with.  Everything after the seed (the lattice explorer, the rankings, the
replayed checks, the certificate and its rendering) is bl_ti's and
ti_batch's: the row is one `tri_sound` line, exactly as in `CBT_TI_*`.
"""
import argparse
import collections
import json
import math
import os
import signal
import sys
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ti_batch as T                            # noqa: E402
import bl_ti as B                               # noqa: E402

C = T.C
N_RUN = int(os.environ.get('HY3_NRUN', 2000000))
MIN_SAMPLES = 6
MAX_BOOTS = 6
BOOT_MAX = int(os.environ.get('HY3_BOOTMAX', 3000000))
BIGC = 0            # a block of at least BIGC units starts as a variable


class HFam(B.LFam):
    """bl_ti's lattice family; with BIGC, a block of at least BIGC units that
    the run never saw change (lattice step 0) starts as [c, oo) instead of
    the one value, so a leaf crosses it by a cycle instead of cell by cell"""

    def __init__(self, key, vals):
        super().__init__(key, vals)
        if BIGC:
            for k, c in enumerate(self.c):
                if self.g[k] == 0 and c >= BIGC:
                    self.g[k] = 1


B.LFam = HFam


def turns(tab, n):
    """(t, q, L, h, R) at every sweep turn at the tape's extreme, sides
    nearest-first (the head's cell excluded), blanks kept"""
    size = 2 * n + 16 if n < 200000 else 800000
    tape = bytearray(size)
    off = size // 2
    pos, q, lo, hi, lastd = off, 0, off, off, 0
    out = []
    for t in range(n):
        h = tape[pos]
        tr = tab[(q, h)]
        if tr is None:
            return out
        w, d, nq = tr
        if lastd and d != lastd and (pos <= lo or pos >= hi):
            L = tuple(tape[lo:pos][::-1])
            R = tuple(tape[pos + 1:hi + 1])
            out.append((t, q, L, h, R))
        tape[pos] = w
        pos += d
        q = nq
        lastd = d
        if pos < lo:
            lo = pos
        elif pos > hi:
            hi = pos
        if pos <= 1 or pos >= size - 2:
            return out
    return out


def keyed(q, L, h, R):
    Ls = T.generalize(C.nstrip(C.norm([('L', L)])))
    Rs = T.generalize(C.nstrip(C.norm([('L', R)])))
    key = (q, h, T.shape(Ls), T.shape(Rs))
    ex = [e[0] for e in T.exps(Ls) + T.exps(Rs)]
    return key, ex


def anchor_seeds(tab):
    """{key: (c, g)} over the turns, and the candidate boots [(t0, key)]"""
    obs = collections.defaultdict(list)
    for t, q, L, h, R in turns(tab, N_RUN):
        key, ex = keyed(q, L, h, R)
        obs[key].append((t, ex))
    seeds = {}
    boots = []
    for key, vs in obs.items():
        if len(vs) < MIN_SAMPLES:
            continue
        exs = [v[1] for v in vs]
        n = len(exs[0])
        c = [min(e[k] for e in exs) for k in range(n)]
        g = [0] * n
        for e in exs:
            for k in range(n):
                g[k] = math.gcd(g[k], e[k] - c[k])
        if not any(g):
            continue
        seeds[key] = (c, g)
        late = sum(1 for v in vs if v[0] > N_RUN // 2)
        boots.append(((late, len(vs)), key, [v[0] for v in vs]))
    # the keys the run keeps coming back to late first (the steady state),
    # not the early transients
    boots.sort(key=lambda b: (-b[0][0], -b[0][1]))
    return seeds, [(ts, key) for _, key, ts in boots[:MAX_BOOTS]]


def find_boot(tab, pins, t0, seeds):
    tabw = {k: (None if k in pins else v) for k, v in tab.items()}
    r = T.run_conc(tab, t0)
    if r is None:
        return dict(err='halts')
    q, L, h, R, _ = r
    boot = (q, C.nstrip(C.norm([('L', L)])), h, C.nstrip(C.norm([('L', R)])))
    B.SEEDS = seeds
    B.G0 = 0
    X = B.LExplorer(tab, pins)
    X.explore(boot)
    cert = B.assemble(X, t0, False, pins)
    cert['qh'] = False
    err = T.fams_ok(tabw, cert)
    if err:
        return dict(err='fams: ' + err)
    if not T.boot_ok(cert, tab):
        return dict(err='boot')
    fired = [set(C.leaf_fired(tabw, dict(chain=lf['chain'], el=lf['el'], er=lf['er'],
                                         c0=lf['c0']))) for lf in cert['leaves']]
    last = None
    for P in T.PLIST:
        lv = T.live_search(cert, tabw, fired, P)
        if isinstance(lv, dict):
            cert.update(lv)
            err = T.live_ok(cert, tabw, fired)
            if err:
                return dict(err='live: ' + err)
            if T.nodeidx(cert, [(l, tuple(r)) for l, r in cert['S']], cert['P'], cert['f0'],
                         cert['v0']) is None:
                return dict(err='boot node')
            return cert
        last = lv
    return dict(err='norank %s' % (last,), nfam=len(cert['fams']))


UNIT_SETS = (('u4', T.GEN_UNITS), ('z6', [(0,)] + T._prim_units(6)))
CONFIGS = [(u, 0) for u in UNIT_SETS] + [(u, 16) for u in UNIT_SETS]


def find_dir(tab):
    """find_dir1 under each block alphabet in UNIT_SETS (the units a literal
    run may be read as a block of): ti_batch's primitive units of up to 4
    cells, then blanks and units of up to 6 cells; then both again with
    big constant blocks generic (BIGC); the first success"""
    global BIGC
    errs = []
    for (name, units), big in CONFIGS:
        T.GEN_UNITS = units
        BIGC = big
        r = find_dir1(tab)
        if 'err' not in r:
            r['units'] = '%s/%d' % (name, big)
            return r
        errs.append('%s/%d: %s' % (name, big, r['err']))
    return dict(err=' | '.join(errs))


def find_dir1(tab):
    r2 = T.run_conc(tab, 60000)
    if r2 is None:
        return dict(err='halts')
    pins = set(k for k in tab if k not in r2[4])
    seeds, boots = anchor_seeds(tab)
    if not boots:
        return dict(err='no anchor key')
    errs = []
    for ts, key in boots:
        # the first turn of the key, and a later one (past the transients)
        for t0 in sorted(set([ts[0], ts[len(ts) // 2]])):
            if t0 > BOOT_MAX:
                continue
            try:
                r = find_boot(tab, pins, t0, seeds)
            except T.Fail as e:
                r = dict(err=str(e))
            except (T.Req, RecursionError):
                r = dict(err='recursion')
            if 'err' not in r:
                return r
            errs.append('t%d %s' % (t0, r['err']))
    return dict(err='; '.join(errs[:4]))


class Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise Timeout()


def find(spec, timeout):
    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(timeout)
    try:
        r = find_dir(T.parse(spec))
    except Timeout:
        r = dict(err='timeout')
    finally:
        signal.alarm(0)
    r['spec'] = spec
    return r


def _find1(args):
    return find(*args)


def cmd_find(a):
    specs = [l.split()[0] for l in open(a.rows) if l.strip() and not l.startswith('#')]
    done = set()
    if os.path.exists(a.out):
        done = set(json.loads(l)['spec'] for l in open(a.out))
    todo = [(s, a.timeout) for s in specs if s not in done]
    stats = collections.Counter()
    with open(a.out, 'a') as f, Pool(a.jobs, maxtasksperchild=1) as pool:
        for r in pool.imap_unordered(_find1, todo):
            f.write(json.dumps(T.jsonable(r)) + '\n')
            f.flush()
            stats['ok' if 'err' not in r else r['err'].split(';')[0][:60]] += 1
    for k, v in stats.most_common():
        print('%5d  %s' % (v, k))


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    f = sub.add_parser('find')
    f.add_argument('rows')
    f.add_argument('out')
    f.add_argument('--jobs', type=int, default=4)
    f.add_argument('--timeout', type=int, default=300)
    f.add_argument('--maxfam', type=int, default=T.MAXFAM)
    b = sub.add_parser('batch')
    b.add_argument('found', nargs='+')
    b.add_argument('--tag', required=True)
    b.add_argument('--chunk', type=int, default=10)
    b.add_argument('--skip', action='append', default=[])
    b.add_argument('--limit', type=int, default=0)
    a = ap.parse_args()
    if a.cmd == 'find':
        T.MAXFAM = a.maxfam
        cmd_find(a)
    else:
        T.cmd_batch(a)


if __name__ == '__main__':
    main()
