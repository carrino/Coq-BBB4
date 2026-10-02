#!/usr/bin/env python3
"""LE6 UNTRUSTED reader: LE4's marker-run reading (`termrun2_detect.py`,
LadderCheckRun2Tr's shape `pre ++ x ++ M ++ T^m ++ suf`) with the thresholds
relaxed for the COUNTDOWN rows of LE6's survey:

* the anchor key also catches the head passing mid-sweep, so as few as 10%
  of its visits parse (LE4: 50%); the laws skip the others, as before;
* refills get exponentially rarer, so the run is longer (1.5M steps) and the
  window is every visit from the first quarter on (LE4: 3,000 from 150,000
  steps).

A countdown is LE4's increment with the two digit words swapped, which
`lawful` already tries.  Output: termrun2_detect.py's records, so
`le4/run2_batch.py` boards them unchanged.

    python3 tools/closeouttr/le6/run2_relax.py ROWS OUT.jsonl [--jobs 4] [--steps N]
"""
import argparse
import json
import os
import sys
from collections import Counter
from multiprocessing import Pool

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'le4'))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'le3'))
import termrun_detect as TD  # noqa: E402
import termrun2_detect as TD2  # noqa: E402
from termrun2_detect import lawful  # noqa: E402


_read0 = TD2.read


def read_padded(st, l, pre, suf, T, M):
    """LE6: TD2.read, also with the visit string padded by up to len(M) + l
    blanks (a refilled x whose top word and the marker end in blanks beyond
    the tape's last nonzero cell)"""
    r = _read0(st, l, pre, suf, T, M)
    if r is not None or suf:
        return r
    for k in range(1, len(M) + l + 1):
        r = _read0(st + '0' * k, l, pre, suf, T, M)
        if r is not None:
            return r
    return None


TD2.read = read_padded
read = read_padded

STEPS = [1500000]
FRAC = 0.1
WIN = 20000


def detect(spec):
    best = None
    for key, strs in TD.anchor_strings(spec, STEPS[0]).items():
        strs = strs[len(strs) // 4:][:WIN]
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
                    for T, _n in tails.most_common(2):
                        for ml in (1, 2, 3, 4):
                            Ms = Counter()
                            for b in bodies:
                                bb = b
                                while bb.endswith(T) and len(bb) > len(T):
                                    bb = bb[:len(bb) - len(T)]
                                if len(bb) >= ml:
                                    Ms[bb[-ml:]] += 1
                            for M, _k in Ms.most_common(2):
                                rd = [read(s, l, pre, suf, T, M) for s in strs]
                                ok = [r for r in rd if r]
                                if len(ok) < FRAC * len(strs):
                                    continue
                                words = Counter(w for ws, _m in ok for w in ws)
                                ms = Counter(m for _ws, m in ok)
                                if len(words) != 2 or len(ms) < 3:
                                    continue
                                law = lawful(ok, sorted(words))
                                if law[0] < 40 or law[1] < 2 or law[2] < 1:
                                    continue
                                cand = dict(spec=spec, anchor=list(key), l=l, pre=pre,
                                            suf=suf, T=T, M=M, words=sorted(words),
                                            parsed=len(ok), total=len(strs),
                                            mmax=max(ms), lawful=law)
                                if best is None or (cand['lawful'], cand['parsed']) > \
                                        (best['lawful'], best['parsed']):
                                    best = cand
    return best


def work(spec):
    try:
        return detect(spec) or dict(spec=spec, anchor=None)
    except Exception as e:  # noqa: BLE001
        return dict(spec=spec, anchor=None, error=repr(e))


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
            if r.get('anchor'):
                print(r['spec'], r.get('anchor'), r.get('M'), r.get('T'), r.get('words'),
                      r.get('mmax'), r.get('lawful'), '%s/%s' % (r.get('parsed'), r.get('total')), flush=True)


if __name__ == '__main__':
    main()
