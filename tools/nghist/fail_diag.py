#!/usr/bin/env python3
"""Failure-mode diagnostic over the unboarded residue (UNTRUSTED).

For each machine, at its oracle/base param ladder, classify WHY it does not
board never-QH:
  NOCLOSE    - grow() never reaches a closed set (fuel/MAXNODES/rounds)
  BIGCTX     - closes but nctx > MAXCTX (emission cap)
  PREFIXQUIET- an obliged state's q-avoiding subgraph is the whole closure
               (prefix-only state: genuine quasihalter shape -> wrap route)
  BIGSUB     - some state's q-avoiding subgraph > CERT_MAXNODES (search skipped)
  NOMEAS     - rank + single measures + lex tuple all fail on some state
  OK         - boards (should not appear for unboarded, unless params differ)
Reports the FIRST param combo that closes, else NOCLOSE at all combos.
"""
import sys, os, json
from concurrent.futures import ProcessPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import nghist_prove as P
import oracle_sweep as OS

MAXCTX = 1200

def diag_one(m):
    tm = P.decode(m)
    plans = OS.nqh_plan(m)
    verdicts = []
    for (k, n, t, fuel) in plans:
        g = None
        try:
            g = P.grow(tm, k, n, t, fuel)
        except Exception:
            pass
        if g is None:
            verdicts.append(('NOCLOSE', k, n, t))
            continue
        a0, lset, rset, seen, edges = g
        if len(seen) > MAXCTX:
            verdicts.append(('BIGCTX', k, n, t, len(seen)))
            continue
        appearing = set(a[0] for a in seen)
        obliged = appearing | P.visited_states_prefix(tm, k, t)
        verdict = 'OK'
        detail = None
        for q in sorted(obliged):
            nodes = [a for a in seen if a[0] != q]
            if q not in appearing:
                verdict = 'PREFIXQUIET'; detail = q
                break
            nodeset = set(nodes)
            adj = {a: [b for b in edges[a] if b in nodeset] for a in nodes}
            if P.try_rank(nodes, adj) is not None:
                continue
            if len(nodes) > P.CERT_MAXNODES:
                verdict = 'BIGSUB'; detail = (q, len(nodes))
                break
            c = P.cert_for_state(tm, seen, edges, q, n=n)
            if c is None:
                verdict = 'NOMEAS'; detail = q
                break
        verdicts.append((verdict, k, n, t, len(seen), detail))
        if verdict in ('OK', 'PREFIXQUIET', 'BIGSUB', 'NOMEAS'):
            break   # closed & analyzed: enough
    return {'m': m, 'v': verdicts}

def main():
    sample_file, outf = sys.argv[1], sys.argv[2]
    ms = [l.strip() for l in open(sample_file) if l.strip()]
    n = int(os.environ.get('DIAG_LIMIT', len(ms)))
    ms = ms[:n]
    with open(outf, 'w') as f, ProcessPoolExecutor(max_workers=3) as ex:
        for i, r in enumerate(ex.map(diag_one, ms, chunksize=4)):
            f.write(json.dumps(r) + '\n')
            if (i + 1) % 100 == 0:
                f.flush(); sys.stderr.write('%d/%d\n' % (i + 1, len(ms)))
    sys.stderr.write('DONE %d\n' % len(ms))

if __name__ == '__main__':
    main()
