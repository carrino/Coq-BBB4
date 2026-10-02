#!/usr/bin/env python3
"""LE7 UNTRUSTED reader: LE6's relaxed marker-run reading
(`le6/run2_relax.py`, `pre ++ x ++ M ++ T^m ++ suf`) that keeps EVERY lawful
candidate, not the best-ranked one.  The ranking (most lawful steps) picks
the wrong anchor on LE6's B2 rows: on `0RB1LA_1LC1RD_1LA1LD_1RB0LA` it took
`B1` with `M = 11`, `T = 01` (one refill seen), where `[A0] x 0 (11)^m`, x over
`11` / `10`, is a plain increment with a three-step refill.  The batch
(`run2z0_batch.py`) tries the candidates in order until one boards.

    python3 tools/closeouttr/le7/run2_all.py ROWS OUT.jsonl [--jobs 4] [--steps N]

One record per row: {spec, cands: [termrun2_detect records]}.
"""
import argparse
import json
import os
import sys
from collections import Counter
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'le6'))
sys.path.insert(0, os.path.join(HERE, '..', 'le4'))
sys.path.insert(0, os.path.join(HERE, '..', 'le3'))
import run2_relax as RR  # noqa: E402  (installs the padded read)
import termrun_detect as TD  # noqa: E402
import fastsim  # noqa: E402
from termrun2_detect import lawful  # noqa: E402

TD.anchor_strings = fastsim.anchor_strings
STEPS = [600000]
KEEP = 16


def detect(spec):
    cands = {}
    for key, strs in TD.anchor_strings(spec, STEPS[0]).items():
        strs = strs[len(strs) // 4:][:RR.WIN]
        if len(strs) < 30:
            continue
        for l in (1, 2, 3):
            for pl in range(0, 3):
                for sl in range(0, 3):
                    pre = strs[-1][:pl]
                    suf = strs[-1][len(strs[-1]) - sl:] if sl else ''
                    bodies = [s[len(pre):len(s) - len(suf)] if suf else s[len(pre):]
                              for s in strs if s.startswith(pre) and s.endswith(suf)]
                    tails = Counter(b[-l:] for b in bodies if len(b) >= l)
                    for T, _n in tails.most_common(3):
                        for ml in (1, 2, 3, 4):
                            Ms = Counter()
                            for b in bodies:
                                bb = b
                                while bb.endswith(T) and len(bb) > len(T):
                                    bb = bb[:len(bb) - len(T)]
                                if len(bb) >= ml:
                                    Ms[bb[-ml:]] += 1
                            # LE7: the marker may be a blank beyond the tape
                            mc = [M for M, _k in Ms.most_common(2)]
                            mc += [M for M in ('0' * ml,) if M not in mc]
                            for M in mc:
                                # a cheap pre-filter on a sample before the full window
                                smp = strs[::max(1, len(strs) // 400)]
                                if sum(1 for s in smp if RR.read(s, l, pre, suf, T, M)) \
                                        < 0.7 * RR.FRAC * len(smp):
                                    continue
                                rd = [RR.read(s, l, pre, suf, T, M) for s in strs]
                                ok = [r for r in rd if r]
                                if len(ok) < RR.FRAC * len(strs):
                                    continue
                                words = Counter(w for ws, _m in ok for w in ws)
                                ms = Counter(m for _ws, m in ok)
                                if len(words) != 2 or len(ms) < 3:
                                    continue
                                law = lawful(ok, sorted(words))
                                if law[0] < 40 or law[1] < 2 or law[2] < 1:
                                    continue
                                k = (tuple(key), l, pre, suf, T, M)
                                cands[k] = dict(spec=spec, anchor=list(key), l=l, pre=pre,
                                                suf=suf, T=T, M=M, words=sorted(words),
                                                parsed=len(ok), total=len(strs),
                                                mmax=max(ms), lawful=law)
    out = sorted(cands.values(), key=lambda c: (-c['lawful'][2], -c['lawful'][1],
                                                -c['lawful'][0], -c['parsed']))
    return out[:KEEP]


def work(spec):
    try:
        return dict(spec=spec, cands=detect(spec))
    except Exception as e:  # noqa: BLE001
        return dict(spec=spec, cands=[], error=repr(e))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('rows')
    ap.add_argument('out')
    ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--steps', type=int, default=STEPS[0])
    a = ap.parse_args()
    STEPS[0] = a.steps
    rows = [l.split()[0] for l in open(a.rows) if l.strip()]
    done = set()
    if os.path.exists(a.out):
        done = set(json.loads(l)['spec'] for l in open(a.out))
    with Pool(a.jobs) as pool, open(a.out, 'a') as f:
        for r in pool.imap_unordered(work, [s for s in rows if s not in done]):
            f.write(json.dumps(r) + '\n')
            f.flush()
            print(r['spec'], len(r['cands']), r.get('error', ''), flush=True)


if __name__ == '__main__':
    main()
