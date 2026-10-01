#!/usr/bin/env python3
"""BLC4: blc3/learn3.py generalised (UNTRUSTED; SCOPING_INSTR.md §7.4.BLC4).

    python3 tools/closeouttr/blc4/learn4.py find ROWS.txt OUT.jsonl [--jobs 4] [--timeout 300]
    python3 tools/closeouttr/blc4/learn4.py batch OUT.jsonl --tag BLC4 [--chunk 6]

What changes against learn3:
  * the unit is learned (the cell whose long runs make the list: `1` or `0`);
  * separators up to MAXW = 8 cells (`111111`, `11011`);
  * a constant word BEYOND b_0 (`1111` / `11` before `0^994`) is a left end
    word: the left tails end in a terminator item (lg4.Lang4.lends);
  * the far end: the list is read from b_0 while its gaps are separators;
    the last element before the first other gap is b_k, and every cell
    after it is the END word (lg4: one END kind per word).
"""
import argparse
import collections
import json
import os
import signal
import sys
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..'))
sys.path.insert(0, os.path.join(HERE, '..', 'blc3'))
import learn3 as L3                                 # noqa: E402
import lg3                                          # noqa: E402
import lg4                                          # noqa: E402
import lg_batch as G                                # noqa: E402
import ti_batch as T                                # noqa: E402
import ti_coq as C                                  # noqa: E402

G.MAXFAM = int(os.environ.get("LG4_MAXFAM", "800"))
L3.MAXW = 8
MAXEND = 40         # longest end word


def set_unit(u):
    L3.UNIT = tuple(u)


def canon_rot(u):
    return min(lg4.rotations(u))


def tokens(cells, W, pos=None):
    """tape-order tokens of a run list (lg3.tape_tokens' format): a one-cell
    unit's long runs are blocks (learn3.runs_tokens), a multi-cell unit's
    tape is all cells (parse4 finds the stretches)"""
    if len(W) == 1:
        old = L3.UNIT
        L3.UNIT = tuple(W)
        try:
            return L3.runs_tokens(cells, pos)
        finally:
            L3.UNIT = old
    toks = []
    i = 0
    for s_, ln in cells:
        for j in range(ln):
            c = i + j
            sd = 'R' if pos is None else ('H' if c == pos else ('L' if c < pos else 'R'))
            toks.append(('c', s_, sd))
        i += ln
    return toks


def find_class(lists, minlen=20):
    """the primitive word (canonical rotation) whose periodic stretches of at
    least minlen cells cover the most of the tapes"""
    cov = collections.Counter()
    for cells in lists:
        w = []
        for s_, ln in cells:
            w.extend([s_] * ln)
        for p in (1, 2, 3, 4):
            j = p
            n = len(w)
            while j < n:
                if w[j] != w[j - p]:
                    j += 1
                    continue
                a0 = j
                while j < n and w[j] == w[j - p]:
                    j += 1
                s0 = a0 - p
                if j - s0 >= minlen and s0 > 0 and j < n:
                    u = tuple(w[s0:s0 + p])
                    if len(C.primroot(u)[0]) == p:
                        cov[canon_rot(u)] += j - s0
    if not cov:
        return None
    best = max(cov.values())
    return min((u for u, c in cov.items() if c >= 0.8 * best), key=len)


def gap_triples(el, toks, W, pseps, mincopy):
    out = []
    for g in range(1, len(el) - 1):
        w = lg4.word_at(el, toks, g, W, pseps)
        if w is None or len(w[1]) > L3.MAXW:
            continue
        if el[g - 1][3][0] >= mincopy and el[g + 1][3][0] >= mincopy:
            out.append(w)
    return out


def read_list(cells, W, pseps, a, seps):
    """an anchor tape as (symbols, bk, end word, blocks, left end word), or
    None.  b_0 is the largest element; the list runs from it while the gaps
    are separators"""
    toks = tokens(cells, W)
    el = lg4.parse4(toks, W, pseps, 'R')
    big = [k for k, x in enumerate(el) if x[0] == 'E' and not x[3][1]]
    if not big:
        return None
    k0 = max(big, key=lambda k: el[k][3][0])
    lend = lg4.tok_cells(toks[0:el[k0][1]])
    if lend is None or len(lend) > MAXEND:
        return None
    bs, ws = [el[k0][3][0]], []
    k = k0 + 1
    endw = ()
    while k < len(el):
        w = lg4.word_at(el, toks, k, W, pseps)
        if w is not None and w in seps:
            ws.append(w)
            bs.append(el[k + 1][3][0])
            k += 2
            continue
        endw = lg4.tok_cells(toks[el[k - 1][2]:])
        if endw is None or len(endw) > MAXEND:
            return None
        break
    if len(bs) < 3:
        return None
    syms = [(ws[i], bs[i] - a * bs[i + 1]) for i in range(len(bs) - 1)]
    return syms, bs[-1], endw, bs, lend


def left_part(cells, pos, WL, pseps, seps):
    """the left form of a snapshot: (left end word, [bL_0..], [wL_0..]) of
    the elements wholly left of the head, read from the head outward while
    the gaps are separators, or None"""
    lead = 0
    while cells and cells[0][0] == 0:
        lead += cells[0][1]
        cells = cells[1:]
    cells = L3.strip_cells(cells)
    p = pos - lead
    if p < 0:
        return None
    toks = tokens(cells, WL, p)
    if not any(t_[-1] == 'H' for t_ in toks):
        return None
    el = lg4.parse4(toks, WL, pseps, 'L')
    hidx = next(i for i, t_ in enumerate(toks) if t_[-1] == 'H')
    left = [x for x in el if x[2] <= hidx]
    if left and left[-1][0] == 'G':
        left = left[:-1]
    bs, ws = [], []
    k = len(left) - 1
    while k >= 0 and left[k][0] == 'E':
        bs.insert(0, left[k][3])
        w = lg4.word_at(left, toks, k - 1, WL, pseps) if k >= 2 else None
        if w is not None and (seps is None or w in seps):
            ws.insert(0, w)
            k -= 2
            continue
        break
    if k < 0 or not bs or any(b[1] for b in bs):
        return None
    lend = lg4.tok_cells(toks[0:left[k][1]])
    if lend is None or len(lend) > MAXEND:
        return None
    return lend, [b[0] for b in bs], ws, (el, toks, hidx)


def left_seps(snaps_s, WL, pseps):
    cnt = collections.Counter()

    def depth(r):
        lead = 0
        for s_, ln in r[6]:
            if s_ != 0:
                break
            lead += ln
        return r[5] - lead
    deepest = sorted(snaps_s[-6000:], key=depth)[-500:]
    for kind, side, t, q, h, pos, cells in deepest:
        cut, i = [], 0
        for s_, ln in cells:
            if i > pos:
                break
            cut.append((s_, ln))
            i += ln
        cells = cut
        lp = left_part(cells, pos, WL, pseps, None)
        if lp is None:
            continue
        el, toks, hidx = lp[3]
        left = [x for x in el if x[2] <= hidx]
        for w in gap_triples(left, toks, WL, pseps, 2 if len(WL) > 1 else L3.LONG):
            cnt[w] += 1
    tot = sum(cnt.values())
    return sorted([w for w, c in cnt.items() if c >= L3.SEPMIN * tot], key=str)


def fit_left2(deep, fwd, q0, W, pseps, seps, a, WL, psepsL, sepsL, drop=2):
    """the left automaton on F's states: each left sample aligned with the
    anchor list it was swept from (the [drop] elements nearest the head are
    the window's).  Returns (lstart, lfwd, lends, nsamples, nconflicts)"""
    states = None
    lstart, lfwd, lends = set(), {}, set()
    votes = collections.defaultdict(collections.Counter)
    n = 0
    need = 0
    for r in deep:
        kind, side, t, q, h, pos, cells = r
        if kind == 'A' and side == 'L':
            cc = L3.strip_cells(cells)
            rl = read_list(cc, W, pseps, a, seps)
            if rl is None:
                states = None
                continue
            states = [q0]
            for x in rl[0]:
                q2 = fwd.get((states[-1], x))
                if q2 is None:
                    break
                states.append(q2)
            # cheap filter: the head must be past b_0 .. b_(drop-1)
            bl = rl[3]
            need = len(W) * sum(bl[:drop]) * 9 // 10
            continue
        if kind != 'S' or states is None:
            continue
        lead = 0
        for s_, ln in cells:
            if s_ != 0:
                break
            lead += ln
        if pos - lead < need:
            continue
        # only the cells up to the head matter
        cut, i = [], 0
        for s_, ln in cells:
            if i > pos:
                break
            cut.append((s_, ln))
            i += ln
        lp = left_part(cut, pos, WL, psepsL, set(sepsL))
        if lp is None:
            continue
        lend, bs, ws, _ = lp
        bs = bs[:len(bs) - (drop - 1)] if drop > 1 else bs
        if len(bs) < 2 or len(bs) > len(states):
            continue
        n += 1
        lends.add(lend)
        for i in range(len(bs) - 1):
            x = (ws[i], bs[i] - a * bs[i + 1])
            votes[(states[i], x)][states[i + 1]] += 1
    nconf = 0
    for (qq, x), c in votes.items():
        q2, _ = c.most_common(1)[0]
        nconf += sum(c.values()) - c[q2]
        if qq == q0:
            lstart.add((x, q2))
        else:
            lfwd[(qq, x)] = q2
    return sorted(lstart, key=str), lfwd, lends, n, nconf


def learn(spec, t1=4000000, every=97):
    rows = L3.snaps(spec, 50000, t1, 0)
    anc = {'L': [r for r in rows if r[0] == 'A' and r[1] == 'L'],
           'R': [r for r in rows if r[0] == 'A' and r[1] == 'R']}
    alls = {sd: [L3.strip_cells(r[6]) for r in anc[sd][-50:]] for sd in anc}
    W = find_class(alls['L'][-20:] + alls['R'][-20:])
    if W is None:
        raise T.Fail('learn: no long runs')
    # b_0's end: the anchor side whose tape starts with the largest element
    sizes = {}
    for sd in ('L', 'R'):
        if not alls[sd]:
            continue
        ends = []
        for c in alls[sd][-20:]:
            cc = c if sd == 'L' else [(s_, ln) for s_, ln in reversed(c)]
            Wd = W if sd == 'L' else tuple(reversed(W))
            el = lg4.parse4(tokens(cc, Wd), Wd, [], 'R')
            es = [x[3][0] for x in el if x[0] == 'E' and not x[3][1]]
            ends.append(es[0] if es else 0)
        sizes[sd] = sorted(ends)[len(ends) // 2]
    if not sizes:
        raise T.Fail('learn: no anchors')
    sd = max(sizes, key=lambda s_: (len(anc[s_]), sizes[s_]))
    mir = sd == 'R'
    if mir:
        rows = [L3.mirror_row(r) for r in rows]
        W = canon_rot(tuple(reversed(W)))
    deep = L3.snaps(L3.mirror_spec(spec) if mir else spec, 50000, t1, every, 4)
    alists = [L3.strip_cells(r[6]) for r in rows if r[0] == 'A' and r[1] == 'L']
    if len(alists) < 20:
        raise T.Fail('learn: %d anchors' % len(alists))
    pseps = []
    if len(W) == 1:
        set_unit(W)
        pseps = L3.learn_seps(alists)
    cnt = collections.Counter()
    for cells in alists[-300:]:
        toks = tokens(cells, W)
        el = lg4.parse4(toks, W, pseps, 'R')
        for w in gap_triples(el, toks, W, pseps, 2 if len(W) > 1 else L3.LONG):
            cnt[w] += 1
    tot = sum(cnt.values())
    seps = set(w for w, c in cnt.items() if c >= L3.SEPMIN * tot)
    if not seps:
        raise T.Fail('learn: no separators')
    rs = collections.Counter()
    for cells in alists[-20:]:
        el = lg4.parse4(tokens(cells, W), W, pseps, 'R')
        big = [x[3][0] for x in el if x[0] == 'E' and not x[3][1] and x[3][0] * len(W) >= 20]
        for x, y in zip(big, big[1:]):
            if y:
                rs[round(x / y)] += 1
    if not rs:
        raise T.Fail('learn: no ratio')
    a = rs.most_common(1)[0][0]
    if a < 2:
        raise T.Fail('learn: ratio %d' % a)
    data = []
    bad = 0
    for cells in alists:
        r = read_list(cells, W, pseps, a, seps)
        if r is None:
            bad += 1
            continue
        data.append(r[:3])
    if len(data) < 20 or bad > 0.05 * len(alists):
        raise T.Fail('learn: %d anchor lists parse (%d do not)' % (len(data), bad))
    fit = None
    for M in (1, 2, 3):
        fit = L3.fit_F(data, M)
        if fit is not None:
            break
    if fit is None:
        raise T.Fail('learn: no bounded-partial-sum automaton')
    fwd, end = L3.expand_end(fit)
    snapl = [r for r in deep if r[0] == 'S']
    lefts = []
    for kind, side, t, q, h, pos, cells in snapl[-400:]:
        i = 0
        lc = []
        for s_, ln in cells:
            if i + ln <= pos:
                lc.append((s_, ln))
            i += ln
        lefts.append(L3.strip_cells(lc))
    WL = find_class(lefts) or W
    psepsL = []
    if len(WL) == 1:
        old = L3.UNIT
        L3.UNIT = WL
        try:
            psepsL = L3.learn_seps([c for c in lefts if c])
        finally:
            L3.UNIT = old
    sepsL = left_seps(snapl, WL, psepsL)
    lstart, lfwd, lendsL, nl, nconf = fit_left2(deep, fwd, fit['q0'], W, pseps, seps, a, WL,
                                                psepsL, sepsL)
    if nl < 20:
        lstart, lfwd, lendsL, nl, nconf = fit_left2(deep, fwd, fit['q0'], W, pseps, seps, a, WL,
                                                    psepsL, sepsL, drop=1)
    if nl < 20 or not lstart:
        raise T.Fail('learn: %d left samples' % nl)
    if nconf > 0.01 * nl:
        raise T.Fail('learn: left samples disagree on F states (%d of %d)' % (nconf, nl))
    if () in lendsL and len(lendsL) > 1:
        raise T.Fail('learn: left end words %s' % sorted(lendsL))
    lendsL.discard(())
    lang = lg4.Lang4(a, W, fwd, end, fit['q0'], lfwd, lstart, sorted(seps, key=str), lends=lendsL,
                     unitL=WL, sepsL=sepsL, psepsR=pseps, psepsL=psepsL)
    info = dict(unit=list(W), a=a, seps=sorted(seps, key=str), m=fit['m'], M=fit['M'],
                range=(fit['lo'], fit['hi']), nanchor=len(data), nleft=nl,
                lends=sorted(lendsL), nendw=len(lang.endws), unitL=list(WL), sepsL=sepsL,
                nconf=nconf)
    return lang, mir, info


def find_row(spec, t0s=(20000, 100000)):
    lang, mir, info = learn(spec)
    errs = []
    for t0 in t0s:
        try:
            r = lg4.find_dir(spec, lang, t0, mir=mir)
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
    L3.lsnap_bin()
    stats = collections.Counter()
    with open(a.out, 'a') as f, Pool(a.jobs, maxtasksperchild=1) as pool:
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
                                         'with end words (ListGlue2Tr, lg2_check)'))
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
    p.add_argument('--tag', default='BLC4')
    p.add_argument('--chunk', type=int, default=6)
    p.add_argument('--skip', action='append', default=[])
    a = ap.parse_args()
    {'find': cmd_find, 'batch': cmd_batch}[a.cmd](a)


if __name__ == '__main__':
    main()
