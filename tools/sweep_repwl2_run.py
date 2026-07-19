#!/usr/bin/env python3
"""Streaming, resumable LEVER C sweep runner (UNTRUSTED measurement).

Per-RUNG timeout (SIGALRM in-worker): an expensive rung that blows the
budget is recorded as a rung-timeout and the ladder continues, so no
single pathological rung poisons the whole machine.  First-catch
semantics: rungs tried in the ladder order, stop at first catch.

Usage:
  run_sweep.py MACHINES_TXT OUT_TSV RUNGSET NPROC RUNG_TIMEOUT_S

RUNGSET: base|ext|aff|l6|l5|all  (see RUNGSETS)
Out row (TSV, resume-safe by col0):
  machine  status  L,T,t  gate  ms  nodes  pops  rung_timeouts
status in {hit, miss, partial}.  partial = no catch but >=1 rung
timed out (machine not fully decided -> listed as unresolved).
"""
import os
import sys
import signal
import time
import multiprocessing as mp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sweep2 as S

BASE = S.BASE_RUNGS
EXT = S.EXT_RUNGS
L6 = [(6, 2, 0), (6, 3, 0), (6, 4, 0)]
L5 = [(5, 2, 0), (5, 3, 0), (5, 4, 0)]
EXT_NOL6 = [r for r in EXT if r[0] != 6]

RUNGSETS = {
    "base": BASE,
    "ext": EXT,
    "all": BASE + EXT,
    "aff": BASE + EXT_NOL6,       # affordable: no L=6
    "l6": L6,
    "l5": L5,
    # main full-sweep ladder: base + T=2 extension + cheap T=3 confirm
    "main": [(2, 2, 0), (3, 2, 0), (4, 2, 0), (2, 3, 0),
             (5, 2, 0), (6, 2, 0), (7, 2, 0),
             (3, 3, 0), (4, 3, 0), (5, 3, 0)],
    # expensive rungs measured on a sample (expected ~0 yield)
    "exp": [(3, 4, 0), (4, 4, 0), (5, 4, 0), (6, 3, 0), (6, 4, 0)],
    # pure T=2 extension only (fastest, for max coverage)
    "t2": [(5, 2, 0), (6, 2, 0), (7, 2, 0)],
    # full T>=3 / T=4 extension grid (marginal yield over T=2 ext)
    "t3": [(3, 3, 0), (4, 3, 0), (5, 3, 0), (6, 3, 0),
           (3, 4, 0), (4, 4, 0), (5, 4, 0), (6, 4, 0)],
}

_TO = [20]
_RUNGS = [BASE + EXT]


class Alarm(Exception):
    pass


def _handler(signum, frame):
    raise Alarm()


def work(m):
    t0 = time.time()
    signal.signal(signal.SIGALRM, _handler)
    tbl = S.rp.parse(m)
    rung_to = []
    for (L, T, t) in _RUNGS[0]:
        signal.alarm(_TO[0])
        try:
            rr = S.try_rung(tbl, L, T, t)
        except Alarm:
            rung_to.append(f"{L},{T},{t}")
            continue
        except Exception as e:
            signal.alarm(0)
            return (m, "err", f"{L},{T},{t}", repr(e)[:60],
                    int((time.time()-t0)*1000), "", "", "")
        finally:
            signal.alarm(0)
        if rr["caught"]:
            return (m, "hit", f"{L},{T},{t}", rr["gate"],
                    int((time.time()-t0)*1000), rr["nodes"], rr["pops"],
                    ";".join(rung_to))
    st = "partial" if rung_to else "miss"
    return (m, st, "", "", int((time.time()-t0)*1000), "", "",
            ";".join(rung_to))


def main():
    src, out_path, rungset = sys.argv[1], sys.argv[2], sys.argv[3]
    nproc, _TO[0] = int(sys.argv[4]), int(sys.argv[5])
    _RUNGS[0] = RUNGSETS[rungset]
    done = set()
    if os.path.exists(out_path):
        with open(out_path) as f:
            for line in f:
                if line.strip():
                    done.add(line.split("\t")[0])
    machines = [l.strip() for l in open(src)
                if l.strip() and l.strip() not in done]
    print(f"sweeping {len(machines)} (skip {len(done)}) rungs={rungset} "
          f"({len(_RUNGS[0])} rungs) nproc={nproc} rung_to={_TO[0]}s",
          flush=True)
    nhit = npar = 0
    t0 = time.time()
    with open(out_path, "a") as out, mp.Pool(nproc) as pool:
        for i, r in enumerate(pool.imap_unordered(work, machines,
                                                  chunksize=1)):
            out.write("\t".join(str(x) for x in r) + "\n")
            out.flush()
            if r[1] == "hit":
                nhit += 1
            elif r[1] == "partial":
                npar += 1
            if (i + 1) % 100 == 0:
                el = time.time() - t0
                rate = (i + 1) / el
                rem = (len(machines) - i - 1) / rate / 60
                print(f"{i+1}/{len(machines)} hit={nhit} partial={npar} "
                      f"{rate:.2f}m/s eta={rem:.0f}min", flush=True)
    print(f"DONE swept={len(machines)} hit={nhit} partial={npar} "
          f"elapsed={(time.time()-t0)/60:.1f}min", flush=True)


if __name__ == "__main__":
    main()
