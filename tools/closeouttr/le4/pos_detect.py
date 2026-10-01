#!/usr/bin/env python3
"""UNTRUSTED finder: positional counters read straight off the anchor
visits, with no ladder (SCOPING_INSTR 7.4.LE4).

valfam names a counter's digit words from its mined ladder rules
(`digit_words`): a word whose run count moves by one in some rule.  When
the miner names none (the rule windows straddle the digits, or the fill
passes the anchor several times), valfam reports "no value family" although
the anchor visits read as an ordinary base-b odometer.  This finder skips
the ladder.  For every end anchor (q, hs, side) with a constant far side it
tries every near-head prefix (<= 3 cells), every terminator the visits end
with (<= 8 cells), every digit width (1-4 cells) and every assignment of
the observed words to the values 0..b-1 (b = 2..4), decodes the visits
LSB nearest the head, drops the visits that do not decode or repeat the
previous value (the fill passing the anchor again), and keeps a family when
the rest is one chain of +1 steps and fills (>= 80 states, >= 2 fills) whose
fill law `pre ++ m^(k+s-|pre|-|suf|) ++ suf` is one law.  Output: one
valfam-shaped certificate per row (single phase, `code: binary`, step 1,
no arms), for `sp_ladder_batch.py` / `emit_ladder.py --tr`, which builds
its own closure arms and replays everything in the kernel.

    python3 pos_detect.py ROWS.txt OUT.jsonl [--steps 300000] [--jobs 4]
"""
import argparse
import itertools
import json
import os
import sys
from collections import Counter
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from zeck2_detect import visits, rstrip0  # noqa: E402

MIN_CHAIN = 80
MIN_FILLS = 2
NVIS = 2500    # the first visits with the usual far side: the early widths, many fills


def decode(cells, pre, T, l, words):
    """digits (LSB first) with pre ++ words ++ T == cells up to trailing
    blanks, or None"""
    n = len(cells)
    if cells[:len(pre)] != pre:
        return None
    body = cells[len(pre):]
    if T:
        if len(body) < len(T) or body[len(body) - len(T):] != T:
            return None
        body = body[:len(body) - len(T)]
    elif body and len(body) % l:
        body = body + [0] * (l - len(body) % l)
    if len(body) % l:
        return None
    ds = []
    for i in range(0, len(body), l):
        w = tuple(body[i:i + l])
        if w not in words:
            return None
        ds.append(words[w])
    del n
    return ds


def val(ds, b):
    v = 0
    for d in reversed(ds):
        v = v * b + d
    return v


def fit_fill(pairs, b):
    """(s, pre, mid, suf) for the fills [(width, digits after)], or None"""
    ss = set(len(nd) - w for w, nd in pairs)
    if len(ss) != 1:
        return None
    s = ss.pop()
    if s < 0:
        return None
    best = None
    for pl in range(0, 4):
        for sl in range(0, 4):
            P = pairs[0][1][:pl]
            S = pairs[0][1][len(pairs[0][1]) - sl:] if sl else []
            mids = set()
            ok = True
            for w, nd in pairs:
                if len(nd) < pl + sl or nd[:pl] != P or (sl and nd[len(nd) - sl:] != S):
                    ok = False
                    break
                mids |= set(nd[pl:len(nd) - sl])
            if not ok or len(mids) > 1:
                continue
            m = mids.pop() if mids else 0
            if best is None or pl + sl < best[0]:
                best = (pl + sl, (s, P, m, S))
    return best and best[1]


def chain(seq, b):
    """the longest run of +1 / fill steps in [(i, ds)]: (start, end, fills)"""
    best = (0, 0, [])
    st, fills = 0, []
    for j in range(1, len(seq)):
        (_, a), (_, c) = seq[j - 1], seq[j]
        w = len(a)
        if w and val(a, b) == b ** w - 1:
            ok = len(c) >= w
            if ok:
                fills.append((w, c))
        else:
            ok = len(c) == w and val(c, b) == val(a, b) + 1
        if not ok:
            if j - st > best[1] - best[0]:
                best = (st, j, fills)
            st, fills = j, []
    if len(seq) - st > best[1] - best[0]:
        best = (st, len(seq), fills)
    return best


def wordseq(c, pre, T, l):
    """the l-cell words of c between pre and T (padded with blanks when T is
    empty), or None"""
    if c[:len(pre)] != pre:
        return None
    body = c[len(pre):]
    if T:
        if len(body) < len(T) or body[len(body) - len(T):] != T:
            return None
        body = body[:len(body) - len(T)]
    elif len(body) % l:
        body = body + [0] * (l - len(body) % l)
    if len(body) % l or not body:
        return None
    return [tuple(body[i:i + l]) for i in range(0, len(body), l)]


def try_key(vs):
    far = Counter(tuple(v[2]) for v in vs).most_common(1)[0][0]
    sel = [v for v in vs if tuple(v[2]) == far][:NVIS]
    if len(sel) < MIN_CHAIN:
        return None
    last = sel[-1][1]
    for l in (1, 2, 3, 4):
        for np_ in range(0, 4):
            pre = last[:np_]
            for nt in range(0, min(8, len(last) - np_) + 1):
                T = last[len(last) - nt:] if nt else []
                if T and T[-1] == 0:
                    continue
                wsq = [(k, wordseq(v[1], pre, T, l)) for k, v in enumerate(sel)]
                wsq = [(k, w) for k, w in wsq if w is not None]
                if len(wsq) < MIN_CHAIN:
                    continue
                body_words = Counter(x for _, w in wsq[-200:] for x in w)
                ws = [w for w, _ in body_words.most_common()]
                if not 2 <= len(ws) <= 4 or len(set(x for _, w in wsq for x in w)) != len(ws):
                    continue
                b = len(ws)
                for perm in itertools.permutations(range(b)):
                    words = {w: perm[i] for i, w in enumerate(ws)}
                    if not T and words.get(tuple([0] * l), 0) != 0:
                        continue
                    seq = []
                    for k, w in wsq:
                        ds = [words[x] for x in w]
                        if seq and seq[-1][1] == ds:
                            continue
                        seq.append((k, ds))
                    if len(seq) < MIN_CHAIN:
                        continue
                    s0, s1, fills = chain(seq, b)
                    if s1 - s0 < MIN_CHAIN or len(fills) < MIN_FILLS:
                        continue
                    f = fit_fill(fills, b)
                    if f is None:
                        continue
                    k0, ds0 = seq[s0]
                    return dict(far=list(far), pre=pre, T=T, l=l, b=b,
                                digits=[list(w) for w, _ in sorted(words.items(),
                                                                   key=lambda kv: kv[1])],
                                fill=f, boot=sel[k0], ds0=ds0, n=s1 - s0, nf=len(fills))
    return None


def find(spec, steps=300000):
    vis = visits(spec, steps)
    for key, vs in sorted(vis.items(), key=lambda kv: -len(kv[1])):
        if len(vs) < MIN_CHAIN:
            continue
        got = try_key(vs)
        if got is None:
            continue
        q, hs, side = key
        s, P, m, S = got['fill']
        fill = dict(widens_by=s, target_prefix=P, target_fill_digit=m, target_suffix=S,
                    lands_in_phase=0)
        t0, near, far = got['boot']
        return dict(
            spec=spec, closed=True, kind='pos', chain=got['n'], fills_seen=got['nf'],
            family=dict(state='ABCD'[q], head=hs, side=side, other_side_cells=got['far'],
                        digits=got['digits'], near_head_prefix=got['pre'],
                        terminator=got['T'], terminators_by_phase=[got['T']], n_phases=1,
                        base=got['b'], digit_len=got['l'], code='binary',
                        value_step_per_anchor_visit=1, order='LSB nearest head'),
            fill=fill, fill_by_phase=[fill], arms=[], ladder=[],
            liveness=dict(states_infinitely_often='ABCD'),
            boot=dict(steps_from_blank=t0, digits_lsb_first=got['ds0'], phase=0,
                      cells=near, value=val(got['ds0'], got['b']), p=0))
    return dict(spec=spec, closed=False)


def work(a):
    spec, steps = a
    try:
        return find(spec, steps)
    except Exception as e:  # noqa: BLE001
        return dict(spec=spec, closed=False, error=repr(e))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('rows')
    ap.add_argument('out')
    ap.add_argument('--steps', type=int, default=300000)
    ap.add_argument('--jobs', type=int, default=4)
    a = ap.parse_args()
    rows = [l.split()[0] for l in open(a.rows) if l.strip()]
    done = set()
    if os.path.exists(a.out):
        done = set(json.loads(l)['spec'] for l in open(a.out) if l.strip())
    todo = [(r, a.steps) for r in rows if r not in done]
    n = 0
    with Pool(a.jobs) as pool, open(a.out, 'a') as fo:
        for c in pool.imap_unordered(work, todo):
            fo.write(json.dumps(c) + '\n')
            fo.flush()
            if c.get('closed'):
                n += 1
                f = c['family']
                print(c['spec'], f['state'] + str(f['head']), f['side'], 'b', f['base'],
                      'digits', f['digits'], 'pre', f['near_head_prefix'], 'T', f['terminator'],
                      'fill', c['fill'], 'chain', c['chain'], flush=True)
            elif c.get('error'):
                print(c['spec'], 'ERROR', c['error'], flush=True)
    print('%d found' % n, file=sys.stderr)


if __name__ == '__main__':
    main()
