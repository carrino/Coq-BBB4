#!/usr/bin/env python3
"""BLC3: learn a block list's JOINT tail language from a long run
(UNTRUSTED; SCOPING_INSTR.md §7.4.BLC3).

    python3 tools/closeouttr/blc3/learn3.py find ROWS.txt OUT.jsonl [--jobs 4] [--timeout 300]
    python3 tools/closeouttr/blc3/learn3.py batch OUT.jsonl --tag BLC3 [--chunk 10]

From `lsnap` (a C simulator, compiled on first use) the learner takes
  * ANCHOR lists: the whole tape each time the head steps past the end of
    the list where its largest block b_0 sits;
  * SNAPSHOTS: the tape every S steps (for the left tails).
It parses each tape with lg3.parse (one-cell unit, separator words learned
from the gaps between long runs), reads a list as symbols x_i = (w_i, d_i),
d_i = b_i - a b_(i+1), and fits:
  * F, a bounded-partial-sum automaton: a centre per (position class,
    separator word), states (class, absolute partial sum) in the range the
    anchors show; the last M symbols, the last block and the trailing word
    form the END table;
  * the left tails' sub-automaton: b_0's shift (left tails carry b_0 + shift)
    and the transitions of F the left tails take.
Then lg3 explores, assembles and replays everything (ListGlue2Tr).
"""
import argparse
import collections
import itertools
import json
import os
import signal
import subprocess
import sys
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..'))
import lg3                                          # noqa: E402
import lg_batch as G                                # noqa: E402
import ti_batch as T                                # noqa: E402

G.MAXFAM = int(os.environ.get("LG3_MAXFAM", "800"))

LSNAP = os.environ.get('LSNAP', '/tmp/blc3_lsnap')
UNIT = (1,)
LONG = 4            # a run this long is a list element when learning separators
SEPMIN = 0.01       # a separator word rarer than this share of the gaps is junk
MAXW = 4            # longest separator word


def lsnap_bin():
    if not os.path.exists(LSNAP):
        subprocess.check_call(['cc', '-O2', '-o', LSNAP, os.path.join(HERE, 'lsnap.c')])
    return LSNAP


def snaps(spec, t0, t1, every, k=0):
    out = subprocess.run([lsnap_bin(), spec, str(t0), str(t1), str(every), str(k)],
                         capture_output=True, text=True, timeout=600).stdout
    rows = []
    for line in out.splitlines():
        f = line.split()
        kind, side, t, q, h, pos, n = f[0], f[1], int(f[2]), int(f[3]), int(f[4]), int(f[5]), int(f[6])
        cells = []
        for r in f[7:]:
            s, ln = r.split('*')
            cells.append((int(s), int(ln)))
        rows.append((kind, side, t, q, h, pos, cells))
    return rows


def mirror_spec(spec):
    return '_'.join(''.join(p[i:i + 3].replace('R', 'x').replace('L', 'R').replace('x', 'L')
                            for i in (0, 3)) for p in spec.split('_'))


def mirror_row(r):
    kind, side, t, q, h, pos, cells = r
    n = sum(ln for _, ln in cells)
    side = {'L': 'R', 'R': 'L'}.get(side, side)
    return (kind, side, t, q, h, n - 1 - pos, list(reversed(cells)))


def runs_tokens(cells, pos=None):
    """tape-order tokens (lg3.tape_tokens' format) of a run list: runs of the
    unit longer than 3 cells are blocks, everything else cells; side 'R'
    (or 'L' / 'H' around pos)"""
    toks = []
    i = 0
    for s, ln in cells:
        if (s,) == UNIT and ln > 3 and (pos is None or not i <= pos < i + ln):
            sd = 'R' if pos is None or i > pos else 'L'
            toks.append(('b', UNIT, (ln, ()), sd))
        elif (s,) == UNIT and ln > 3:
            if pos > i:
                toks.append(('b', UNIT, (pos - i, ()), 'L'))
            toks.append(('c', s, 'H'))
            if i + ln - 1 > pos:
                toks.append(('b', UNIT, (i + ln - 1 - pos, ()), 'R'))
        else:
            for j in range(ln):
                c = i + j
                sd = 'R' if pos is None else ('H' if c == pos else ('L' if c < pos else 'R'))
                toks.append(('c', s, sd))
        i += ln
    return toks


def strip_cells(cells):
    while cells and cells[0][0] == 0:
        cells = cells[1:]
    while cells and cells[-1][0] == 0:
        cells = cells[:-1]
    return cells


def learn_seps(lists_cells):
    """the gap words between two runs of the unit both at least LONG long"""
    cnt = collections.Counter()
    for cells in lists_cells:
        for i in range(len(cells)):
            if (cells[i][0],) != UNIT or cells[i][1] < LONG:
                continue
            j = i + 1
            w = []
            while j < len(cells) and not ((cells[j][0],) == UNIT and cells[j][1] >= LONG):
                w.extend([cells[j][0]] * cells[j][1])
                j += 1
            if j < len(cells) and 0 < len(w) <= MAXW:
                cnt[tuple(w)] += 1
    tot = sum(cnt.values())
    return sorted([w for w, c in cnt.items() if c >= SEPMIN * tot], key=lambda w: (-len(w), w))


def read_list(cells, seps, a):
    """the anchor tape as (symbols, bk, end word), or None"""
    toks = runs_tokens(cells)
    el = lg3.parse(toks, UNIT, seps)
    if not el or el[0][0] != 'E':
        return None
    # the far end: a trailing gap that is no separator is the end word
    endw = ()
    if el[-1][0] == 'G':
        if any(t[0] != 'c' for t in el[-1][3]):
            return None
        endw = tuple(t[1] for t in el[-1][3])
        el = el[:-1]
    bs, ws = [], []
    for k, x in enumerate(el):
        if k % 2 == 0:
            if x[0] != 'E' or x[3][1]:
                return None
            bs.append(x[3][0])
        else:
            w = lg3.gap_word(x, seps)
            if w is None:
                return None
            ws.append(w)
    if len(bs) < 3:
        return None
    syms = [(ws[i], bs[i] - a * bs[i + 1]) for i in range(len(bs) - 1)]
    return syms, bs[-1], endw, bs


# ------------------------------------------------------------------- F ----

def fit_F(data, M):
    """data: [(syms, bk, endw)].  The bounded-partial-sum automaton: classes
    by position mod m (position 0, b_0's digit, a class of its own), a
    centre per (class, word); states (class, sum).  Returns the fit or None"""
    def cls(i, m):
        return 'b0' if i == 0 else i % m
    best = None
    for m in (1, 2):
        groups = collections.defaultdict(collections.Counter)
        for syms, bk, endw in data:
            core = syms[:len(syms) - M]
            for i, (w, d) in enumerate(core):
                groups[(cls(i, m), w)][d] += 1
        keys = sorted(groups, key=str)
        cand = []
        for k in keys:
            ds = groups[k]
            lo, hi = min(ds), max(ds)
            if hi - lo > 8:
                break
            cand.append(range(lo, hi + 1))
        else:
            ncomb = 1
            for c in cand:
                ncomb *= len(c)
            if ncomb > 20000:
                continue
            for cs in itertools.product(*cand):
                cen = dict(zip(keys, cs))
                lo = hi = 0
                for syms, bk, endw in data:
                    s = 0
                    for i, (w, d) in enumerate(syms[:len(syms) - M]):
                        s += d - cen[(cls(i, m), w)]
                        lo, hi = min(lo, s), max(hi, s)
                    if hi - lo > 6:
                        break
                if hi - lo > 6:
                    continue
                key = (hi - lo, m)
                if best is None or key < best[0]:
                    best = (key, m, cen, lo, hi)
    if best is None:
        return None
    _, m, cen, lo, hi = best
    syms_of = collections.defaultdict(set)      # class -> symbols seen
    for syms, bk, endw in data:
        for i, x in enumerate(syms[:len(syms) - M]):
            syms_of[cls(i, m)].add(x)
    fwd = {}
    q0 = ('b0', 0)
    todo, seen = [q0], set()
    while todo:
        q = todo.pop()
        if q in seen:
            continue
        seen.add(q)
        c, s = q
        for x in syms_of[c]:
            s2 = s + x[1] - cen[(c, x[0])]
            if lo <= s2 <= hi:
                q2 = ((1 if c == 'b0' else c + 1) % m, s2)
                fwd[(q, x)] = q2
                todo.append(q2)
    # the end: the state after the core, then the last M symbols and b_k
    end = collections.defaultdict(set)
    for syms, bk, endw in data:
        q = q0
        ok = True
        for x in syms[:len(syms) - M]:
            q = fwd.get((q, x))
            if q is None:
                ok = False
                break
        if not ok:
            return None
        end[q].add((tuple(syms[len(syms) - M:]), bk, endw))
    return dict(m=m, cen=cen, lo=lo, hi=hi, fwd=fwd, end=dict(end), q0=q0, M=M)


def expand_end(fit):
    """an END table of M symbols as single-symbol ends: intermediate states
    ('E', q, prefix) for the symbols before the last"""
    fwd = dict(fit['fwd'])
    end = collections.defaultdict(list)
    for q, lst in fit['end'].items():
        for tailsyms, bk, endw in lst:
            cur = q
            for i, x in enumerate(tailsyms[:-1]):
                nxt = ('E', q, tailsyms[:i + 1])
                if fwd.get((cur, x), nxt) != nxt:
                    # an end symbol that is also a core transition: keep both
                    nxt2 = fwd[(cur, x)]
                    nxt = nxt2
                else:
                    fwd[(cur, x)] = nxt
                cur = nxt
            end[cur].append((tailsyms[-1], bk, endw))
    return fwd, dict(end)


# ---------------------------------------------------------------- left ----

def left_samples(snaps_l, seps, a):
    out = []
    for kind, side, t, q, h, pos, cells in snaps_l:
        # trim blanks, keep pos
        lead = 0
        while cells and cells[0][0] == 0:
            lead += cells[0][1]
            cells = cells[1:]
        cells = strip_cells(cells)
        p = pos - lead
        if p < 0:
            continue
        toks = runs_tokens(cells, p)
        if not any(t_[-1] == 'H' for t_ in toks):
            continue
        el = lg3.parse(toks, UNIT, seps)
        hidx = next(i for i, t_ in enumerate(toks) if t_[-1] == 'H')
        bs, ws = [], []
        for k, x in enumerate(el):
            if x[2] > hidx:
                break
            if k % 2 == 0:
                if x[0] != 'E':
                    break
                bs.append(x[3])
            else:
                w = lg3.gap_word(x, seps)
                if w is None:
                    break
                ws.append(w)
        # drop the two elements nearest the head (the window)
        bs = bs[:-2]
        if len(bs) < 2 or any(b[1] for b in bs):
            continue
        bs = [b[0] for b in bs]
        out.append([(ws[i], bs[i] - a * bs[i + 1]) for i in range(len(bs) - 1)])
    return out


def fit_left(fwd, q0, samples):
    """b_0's shift and the left sub-automaton"""
    best = None
    for sh in (0, 1, -1, 2, -2):
        ok = 0
        for s in samples:
            q = fwd.get((q0, (s[0][0], s[0][1] - sh)))
            if q is None:
                continue
            for x in s[1:]:
                q = fwd.get((q, x))
                if q is None:
                    break
            if q is not None:
                ok += 1
        if best is None or ok > best[0]:
            best = (ok, sh)
    ok, sh = best
    if not samples or ok < 0.99 * len(samples):
        return None
    lstart, lfwd = set(), {}
    for s in samples:
        x0 = (s[0][0], s[0][1] - sh)
        q = fwd.get((q0, x0))
        if q is None:
            continue
        lstart.add((x0, q))
        for x in s[1:]:
            q2 = fwd.get((q, x))
            if q2 is None:
                break
            lfwd[(q, x)] = q2
            q = q2
    return sh, sorted(lstart), lfwd


# ---------------------------------------------------------------- learn ----

def learn(spec, t1=4000000, every=97):
    """(lang, mirror) or raises Fail"""
    rows = snaps(spec, 50000, t1, 0)

    anc = {'L': [r for r in rows if r[0] == 'A' and r[1] == 'L'],
           'R': [r for r in rows if r[0] == 'A' and r[1] == 'R']}
    # b_0's end: the anchor side whose first run is the longest
    sizes = {}
    for sd in ('L', 'R'):
        ls = [strip_cells(r[6]) for r in anc[sd][-50:]]
        if not ls:
            continue
        ends = [(c[0][1] if sd == 'L' else c[-1][1]) for c in ls if c]
        sizes[sd] = sorted(ends)[len(ends) // 2] if ends else 0
    if not sizes:
        raise T.Fail('learn: no anchors')
    sd = max(sizes, key=lambda s: (len(anc[s]), sizes[s]))
    mir = sd == 'R'
    if mir:
        rows = [mirror_row(r) for r in rows]
    # the deep snapshots, in the oriented machine's own view
    deep = snaps(mirror_spec(spec) if mir else spec, 50000, t1, every, 4)
    alists = [strip_cells(r[6]) for r in rows if r[0] == 'A' and r[1] == 'L']
    if len(alists) < 20:
        raise T.Fail('learn: %d anchors' % len(alists))
    seps = learn_seps(alists)
    if not seps:
        raise T.Fail('learn: no separators')
    # the ratio
    rs = collections.Counter()
    for cells in alists[-20:]:
        big = [ln for s, ln in cells if (s,) == UNIT and ln >= 20]
        for x, y in zip(big, big[1:]):
            rs[round(x / y)] += 1
    if not rs:
        raise T.Fail('learn: no ratio')
    a = rs.most_common(1)[0][0]
    if a < 2:
        raise T.Fail('learn: ratio %d' % a)
    data = []
    bad = 0
    for cells in alists:
        r = read_list(cells, seps, a)
        if r is None:
            bad += 1
            continue
        data.append(r[:3])
    if len(data) < 20 or bad > 0.05 * len(alists):
        raise T.Fail('learn: %d anchor lists parse (%d do not)' % (len(data), bad))
    fit = None
    for M in (1, 2, 3):
        fit = fit_F(data, M)
        if fit is not None:
            break
    if fit is None:
        raise T.Fail('learn: no bounded-partial-sum automaton')
    fwd, end = expand_end(fit)
    snapl = [r for r in deep if r[0] == 'S']
    ls = left_samples(snapl, seps, a)
    fl = fit_left(fwd, fit['q0'], ls)
    if fl is None:
        raise T.Fail('learn: left tails off the automaton')
    sh, lstart, lfwd = fl
    end2 = {q: [(x, bk) for x, bk, endw in lst] for q, lst in end.items()}
    endw = set(endw for lst in end.values() for _, _, endw in lst)
    if endw - {()}:
        raise T.Fail('learn: end words %s' % sorted(endw))
    lang = lg3.Lang(a, UNIT, fwd, end2, fit['q0'], shift=sh, lfwd=lfwd, lstart=lstart, seps=seps)
    info = dict(a=a, seps=seps, m=fit['m'], M=fit['M'], range=(fit['lo'], fit['hi']), shift=sh,
                nanchor=len(data), nleft=len(ls))
    return lang, mir, info


def find_row(spec, t0s=(20000, 100000)):
    lang, mir, info = learn(spec)
    errs = []
    for t0 in t0s:
        try:
            r = lg3.find_dir(spec, lang, t0, mir=mir, ndata=0)
        except T.Fail as e:
            r = dict(err=str(e))
        if 'err' not in r:
            r['spec'] = spec
            r['learn'] = info
            return r
        errs.append('t%d %s' % (t0, r['err']))
    return dict(spec=spec, err=' / '.join(errs), learn=info)


class Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise Timeout()


def find(spec, timeout=0):
    if timeout:
        signal.signal(signal.SIGALRM, _alarm)
        signal.alarm(timeout)
    try:
        return find_row(spec)
    except T.Fail as e:
        return dict(spec=spec, err=str(e))
    except Timeout:
        return dict(spec=spec, err='timeout')
    except RecursionError:
        return dict(spec=spec, err='recursion')
    finally:
        if timeout:
            signal.alarm(0)


def _find1(args):
    return find(*args)


def cmd_find(a):
    specs = [l.split()[0] for l in open(a.rows) if l.strip() and not l.startswith('#')]
    done = set()
    if os.path.exists(a.out):
        done = set(json.loads(l)['spec'] for l in open(a.out))
    todo = [(s, a.timeout) for s in specs if s not in done]
    lsnap_bin()
    stats = collections.Counter()
    with open(a.out, 'a') as f, Pool(a.jobs) as pool:
        for r in pool.imap_unordered(_find1, todo):
            f.write(json.dumps(G.jsonable(r)) + '\n')
            f.flush()
            stats['ok' if 'err' not in r else 'fail'] += 1
            print(r['spec'], r.get('err', 'OK')[:200], flush=True)
    print(dict(stats))


def cmd_batch(a):
    from cbt import next_free, write_batch
    rem = T.remaining()
    certs, seen = [], set()
    for p in a.found:
        for line in open(p):
            c = json.loads(line)
            s = c['spec']
            if 'err' in c or s not in rem or s in seen or s in a.skip:
                continue
            seen.add(s)
            certs.append(G.detuple(c))
    nn = next_free(a.tag)
    made = []
    for i in range(0, len(certs), a.chunk):
        chunk = certs[i:i + a.chunk]
        entries = [(c['spec'], lg3.render2(c)) for c in chunk]
        made.append(write_batch(a.tag, nn, ['From BBB4.Checkers Require Import LapDecider.',
                                            'From BBB4.Counters Require Import TriGlueTr ListGlue2Tr.'],
                                entries, 'block-list rows by the joint-language list glue '
                                         '(ListGlue2Tr, lg2_check)'))
        nn += 1
    print('%d rows -> %d batch file(s): %s' % (len(certs), len(made),
          ' '.join(os.path.relpath(p, T.REPO) for p in made)))


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest='cmd', required=True)
    p = sp.add_parser('find')
    p.add_argument('rows')
    p.add_argument('out')
    p.add_argument('--jobs', type=int, default=4)
    p.add_argument('--timeout', type=int, default=300)
    p = sp.add_parser('batch')
    p.add_argument('found', nargs='+')
    p.add_argument('--tag', default='BLC3')
    p.add_argument('--chunk', type=int, default=10)
    p.add_argument('--skip', action='append', default=[])
    a = ap.parse_args()
    {'find': cmd_find, 'batch': cmd_batch}[a.cmd](a)


if __name__ == '__main__':
    main()
