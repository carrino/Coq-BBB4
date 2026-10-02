#!/usr/bin/env python3
"""LE7 UNTRUSTED reader: LE5's `termrun3_detect.py` (`x ++ E_e ++ T^m`, a
top digit with its own words, `LadderCheckRun3Tr`) keeping EVERY lawful
candidate instead of the best-ranked one, as `run2_all.py` does for the
marker runs.  On `0RB1LA_1LC1RD_...`-type rows LE5's pick (anchor `A1`) has no
narrowing program while other anchors read the same counter.

The candidate loop is LE5's `detect`, taken from its source with the one line
that keeps the best replaced by an append (so the two cannot drift apart).

    python3 tools/closeouttr/le7/run3_all.py ROWS OUT.jsonl [--jobs 4]

One record per row: {spec, cands: [termrun3_detect records]}.
"""
import argparse
import inspect
import json
import os
import sys
import textwrap
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'le5'))
import termrun3_detect as T3  # noqa: E402

KEEP = 12

_src = textwrap.dedent(inspect.getsource(T3.detect))
_old = """                                    if best is None or (cand['lawful'], cand['parsed']) > \\
                                            (best['lawful'], best['parsed']):
                                        best = cand
    return best"""
assert _old in _src, 'termrun3_detect.detect changed'
_src = _src.replace('def detect(', 'def detect_all(').replace('    best = None\n', '    best = []\n', 1)
_src = _src.replace(_old, """                                    best.append(cand)
    return best""")
exec(compile(_src, T3.__file__, 'exec'), T3.__dict__)


def detect(spec):
    out = T3.detect_all(spec)
    out.sort(key=lambda c: (-c['lawful'][2], -c['lawful'][1], -c['lawful'][0], -c['parsed']))
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
    a = ap.parse_args()
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
