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

G.MAXFAM = int(os.environ.get("LG4_MAXFAM", "800"))
L3.MAXW = 8
MAXEND = 40         # longest end word


def set_unit(u):
    L3.UNIT = tuple(u)


def read_list(cells, seps, a):
    """an anchor tape as (symbols, bk, end word, blocks, left end word), or None"""
    toks = L3.runs_tokens(cells)
    el = lg3.parse(toks, L3.UNIT, seps)
    if not el:
        return None
    big = [k for k, x in enumerate(el) if x[0] == 'E' and not x[3][1]]
    if not big:
        return None
    k0 = max(big, key=lambda k: el[k][3][0])
    lend = lg4.tok_cells(toks[0:el[k0][1]])
    if lend is None or len(lend) > MAXEND:
        return None
    el = el[k0:]
    bs, ws = [el[0][3]], []
    k = 1
    endw = ()
    while k < len(el):
        g = el[k]
        w = lg3.gap_word(g, seps) if g[0] == 'G' else None
        if w is not None and k + 1 < len(el) and el[k + 1][0] == 'E':
            ws.append(w)
            bs.append(el[k + 1][3])
            k += 2
            continue
        endw = lg4.tok_cells(toks[g[1]:el[-1][2]])
        if endw is None or len(endw) > MAXEND:
            return None
        break
    if any(b[1] for b in bs) or len(bs) < 3:
        return None
    bs = [b[0] for b in bs]
    syms = [(ws[i], bs[i] - a * bs[i + 1]) for i in range(len(bs) - 1)]
    return syms, bs[-1], endw, bs, lend


def left_part(cells, pos, uL, sepsL):
    """the left form of a snapshot: (left end word, [bL_0..], [wL_0..]) of
    the elements wholly left of the head, or None"""
    lead = 0
    while cells and cells[0][0] == 0:
        lead += cells[0][1]
        cells = cells[1:]
    cells = L3.strip_cells(cells)
    p = pos - lead
    if p < 0:
        return None
    old = L3.UNIT
    L3.UNIT = uL
    try:
        toks = L3.runs_tokens(cells, p)
    finally:
        L3.UNIT = old
    if not any(t_[-1] == 'H' for t_ in toks):
        return None
    el = lg3.parse(toks, uL, sepsL)
    hidx = next(i for i, t_ in enumerate(toks) if t_[-1] == 'H')
    # from the head outward while the gaps are separators; the cells beyond
    # the last element are the left end word
    left = [x for x in el if x[2] <= hidx]
    if left and left[-1][0] == 'G':
        left = left[:-1]
    bs, ws = [], []
    k = len(left) - 1
    while k >= 0 and left[k][0] == 'E':
        bs.insert(0, left[k][3])
        if k >= 2 and left[k - 1][0] == 'G' and left[k - 2][0] == 'E' and \
                lg3.gap_word(left[k - 1], sepsL) is not None:
            ws.insert(0, lg3.gap_word(left[k - 1], sepsL))
            k -= 2
            continue
        break
    if k < 0 or not bs:
        return None
    lend = lg4.tok_cells(toks[0:left[k][1]])
    if lend is None or len(lend) > MAXEND:
        return None
    if any(b[1] for b in bs):
        return None
    return lend, [b[0] for b in bs], ws


def left_unit(snaps_s):
    """the cell of the long runs left of the head"""
    cnt = collections.Counter()
    for kind, side, t, q, h, pos, cells in snaps_s[-400:]:
        i = 0
        for s_, ln in cells:
            if i + ln <= pos and ln >= 20 and i > 0:
                cnt[s_] += 1
            i += ln
    return (cnt.most_common(1)[0][0],) if cnt else None


def left_seps(snaps_s, uL):
    cnt = collections.Counter()
    for kind, side, t, q, h, pos, cells in snaps_s[-2000:]:
        i = 0
        left = []
        for s_, ln in cells:
            if i + ln <= pos:
                left.append((s_, ln))
            i += ln
        left = L3.strip_cells(left)
        for j in range(len(left)):
            if (left[j][0],) != uL or left[j][1] < L3.LONG:
                continue
            k = j + 1
            w = []
            while k < len(left) and not ((left[k][0],) == uL and left[k][1] >= L3.LONG):
                w.extend([left[k][0]] * left[k][1])
                k += 1
            if k < len(left) and 0 < len(w) <= L3.MAXW:
                cnt[tuple(w)] += 1
    tot = sum(cnt.values())
    return sorted([w for w, c in cnt.items() if c >= L3.SEPMIN * tot], key=lambda w: (-len(w), w))


def fit_left2(deep, fwd, q0, seps, a, uL, sepsL):
    """the left automaton on F's states: each left sample aligned with the
    anchor list it was swept from.  Returns (lstart, lfwd, lends, nsamples,
    nconflicts)"""
    states = None
    lstart, lfwd, lends = set(), {}, set()
    votes = collections.defaultdict(collections.Counter)
    n = 0
    for r in deep:
        kind, side, t, q, h, pos, cells = r
        if kind == 'A' and side == 'L':
            rl = read_list(L3.strip_cells(cells), seps, a)
            if rl is None:
                states = None
                continue
            syms = rl[0]
            states = [q0]
            for x in syms:
                q2 = fwd.get((states[-1], x))
                if q2 is None:
                    break
                states.append(q2)
            continue
        if kind != 'S' or states is None:
            continue
        lp = left_part(cells, pos, uL, sepsL)
        if lp is None:
            continue
        lend, bs, ws = lp
        bs = bs[:-2]
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


def pick_unit(alists):
    """the cell whose long runs (>= 20) are most numerous inside the tapes"""
    cnt = collections.Counter()
    for cells in alists[-20:]:
        for s, ln in cells[1:-1]:
            if ln >= 20:
                cnt[s] += 1
    if not cnt:
        return None
    return (cnt.most_common(1)[0][0],)


def learn(spec, t1=4000000, every=97):
    rows = L3.snaps(spec, 50000, t1, 0)
    anc = {'L': [r for r in rows if r[0] == 'A' and r[1] == 'L'],
           'R': [r for r in rows if r[0] == 'A' and r[1] == 'R']}
    alls = {sd: [L3.strip_cells(r[6]) for r in anc[sd][-50:]] for sd in anc}
    unit = pick_unit(alls['L'] + alls['R'])
    if unit is None:
        raise T.Fail('learn: no long runs')
    set_unit(unit)
    sizes = {}
    for sd in ('L', 'R'):
        ls = alls[sd]
        if not ls:
            continue
        ends = []
        for c in ls:
            runs = [ln for s, ln in (c if sd == 'L' else list(reversed(c)))[:3] if (s,) == unit]
            ends.append(runs[0] if runs else 0)
        sizes[sd] = sorted(ends)[len(ends) // 2] if ends else 0
    if not sizes:
        raise T.Fail('learn: no anchors')
    sd = max(sizes, key=lambda s: (len(anc[s]), sizes[s]))
    mir = sd == 'R'
    if mir:
        rows = [L3.mirror_row(r) for r in rows]
    deep = L3.snaps(L3.mirror_spec(spec) if mir else spec, 50000, t1, every, 4)
    alists = [L3.strip_cells(r[6]) for r in rows if r[0] == 'A' and r[1] == 'L']
    if len(alists) < 20:
        raise T.Fail('learn: %d anchors' % len(alists))
    seps = L3.learn_seps(alists)
    if not seps:
        raise T.Fail('learn: no separators')
    rs = collections.Counter()
    for cells in alists[-20:]:
        big = [ln for s, ln in cells if (s,) == unit and ln >= 20]
        for x, y in zip(big, big[1:]):
            rs[round(x / y)] += 1
    if not rs:
        raise T.Fail('learn: no ratio')
    a = rs.most_common(1)[0][0]
    if a < 2:
        raise T.Fail('learn: ratio %d' % a)
    data, lends = [], set()
    bad = 0
    for cells in alists:
        r = read_list(cells, seps, a)
        if r is None:
            bad += 1
            continue
        data.append(r[:3])
        lends.add(r[4])
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
    uL = left_unit(snapl) or unit
    sepsL = left_seps(snapl, uL)
    lstart, lfwd, lendsL, nl, nconf = fit_left2(deep, fwd, fit['q0'], seps, a, uL, sepsL)
    if nl < 20 or not lstart:
        raise T.Fail('learn: %d left samples' % nl)
    if nconf > 0.01 * nl:
        raise T.Fail('learn: left samples disagree on F states (%d of %d)' % (nconf, nl))
    if () in lendsL and len(lendsL) > 1:
        raise T.Fail('learn: left end words %s' % sorted(lendsL))
    lendsL.discard(())
    lang = lg4.Lang4(a, unit, fwd, end, fit['q0'], lfwd, lstart, seps, lends=lendsL, unitL=uL,
                     sepsL=sepsL)
    sh = None
    ls = [0] * nl
    info = dict(unit=list(unit), a=a, seps=seps, m=fit['m'], M=fit['M'],
                range=(fit['lo'], fit['hi']), shift=sh, nanchor=len(data), nleft=len(ls),
                lends=sorted(lendsL), nendw=len(lang.endws), unitL=list(uL), sepsL=sepsL,
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
