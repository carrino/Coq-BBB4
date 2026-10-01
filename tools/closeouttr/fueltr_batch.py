#!/usr/bin/env python3
"""Find instruction-target FuelWideTr certificates and write closeout batches.

By default the finder selects rows also in tools/fuel_manifest.tsv;
--all probes every requested row still absent from a closeout batch.
The landed fuel generator supplies the abstraction, measures and serialization.
Only the target deletion in the SCC graph changes to a (state, symbol) pair.
Every candidate is independently replayed by instruction_check, then by Coq.

  python3 tools/closeouttr/fueltr_batch.py find ROWS OUTPUT --timeout 60
  python3 tools/closeouttr/fueltr_batch.py batch OUTPUT --start 5 --chunk 4
"""
import argparse
import csv
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
import multiprocessing as mp
import queue
import re
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE.parent))
import bulk_prover as bp
import gen_fuel_certs as gf
from cbt import write_batch


def instruction_procedure(tbl, n, adj, fseen, qq, cands):
    """Rules (a)/(b) + the per-SCC runner kill (c2) over the refined
    q-avoiding graph.  Returns (comps, gate) or None.  Mirrors
    bulk_prover.procedure with two changes:

    - a stuck cyclic SCC all of whose nodes move right with
      (window or class) fuel is discharged into the runner gate and
      its intra edges leave the peeling graph;
    - every emitted rank component is computed over the peeling graph
      PLUS the collected gate edges, so it stays non-increasing
      (equal) on gate-internal edges -- which the runner disjunct of
      [fw_edge_ok] requires of every component.  Gate SCCs cannot
      merge outside nodes into their component: any such cycle would
      have made those nodes part of the SCC at kill time."""
    nodes = [fa for fa in fseen if fa[0][:2] != qq]
    Kc = len(nodes) + 2
    alive = {}
    for fa in nodes:
        for fb in adj[fa]:
            if fb[0][:2] != qq:
                alive[(fa, fb)] = True
    comps = []
    gate = set()
    gate_edges = []
    rounds = 0
    while True:
        rounds += 1
        if rounds > 300:
            return None
        adjmap = {}
        for (u, v) in alive:
            adjmap.setdefault(u, []).append(v)
        comp_list = bp.sccs(nodes, lambda v: adjmap.get(v, []))
        cyclic = [c for c in comp_list
                  if len(c) > 1 or c[0] in adjmap.get(c[0], [])]
        if not cyclic:
            comps.append(("rank",
                          gf.scc_rank(nodes, list(alive) + gate_edges)))
            return comps, gate
        comps.append(("rank", gf.scc_rank(nodes, list(alive) + gate_edges)))
        progress = False
        for c in cyclic:
            cs = set(c)
            intra = [(u, v) for (u, v) in alive if u in cs and v in cs]
            done = False
            for (patt, reg) in cands:
                ds = {e: bp.pdelta(tbl, n, patt, reg, e[0][0]) for e in intra}
                if (all(d <= 0 for d in ds.values())
                        and any(d < 0 for d in ds.values())):
                    comps.append(("meas", patt, reg, 1,
                                  {v: 0 for v in c}, cs))
                    for e in intra:
                        if ds[e] < 0:
                            del alive[e]
                    progress = True
                    done = True
                    break
            if done:
                continue
            for (patt, reg) in cands:
                W = [(u, v, Kc * bp.pdelta(tbl, n, patt, reg, u[0]) + 1)
                     for (u, v) in intra]
                phi = bp.bellman_potentials(list(cs), W)
                if phi is not None:
                    comps.append(("meas", patt, reg, Kc, phi, cs))
                    for e in intra:
                        del alive[e]
                    progress = True
                    done = True
                    break
            if done:
                continue
            # the runner kill (c2): every node of the SCC moves right
            # with window-or-class fuel
            if all(gf.fw_moves_right(tbl, u) and gf.fw_rfuel(u) for u in cs):
                gate |= cs
                for e in intra:
                    del alive[e]
                    gate_edges.append(e)
                progress = True
        if not progress:
            return None



def instruction_check(tbl, n, adj, seen, target, comps, gate):
    for a in gate:
        if a[0][:2] == target or not gf.fw_moves_right(tbl, a) or not gf.fw_rfuel(a):
            return False
    return all(a[0][:2] == target or all(
        b[0][:2] == target or gf.fw_edge_ok(tbl, n, comps, gate, a, b)
        for b in adj[a]) for a in seen)


def warmup_fires(tbl, t):
    tape, pos, q, fired = {}, 0, 0, set()
    for _ in range(t):
        sym = tape.get(pos, 0)
        fired.add((q, sym))
        tr = tbl[(q, sym)]
        if tr is None:
            return None
        w, d, q = tr
        tape[pos] = w
        pos += 1 if d == "R" else -1
    return fired


def emit_cert(per_target):
    arms = []
    for q in range(4):
        for s in range(2):
            comps, gate = per_target.get((q, s), ([], set()))
            body = "[" + ";\n   ".join(gf.emit_fcomp(c) for c in comps) + "]"
            arms.append("  | (St%s, S%d) => (%s,\n   %s)" %
                        (chr(65 + q), s, body, gf.emit_fkeys(gate)))
    return "fun target : Instr => match target with\n" + "\n".join(arms) + "\n  end"


def find_one(spec, n0, n_extra, warmups):
    first_fail = None
    for mirrored in (True, False):
        for n in range(n0, n0 + n_extra + 1):
            tbl = bp.parse(gf.mirror_mtext(spec) if mirrored else spec)
            for t in warmups:
                result = bp.build_closure(tbl, n, t)
                if result is None:
                    continue
                seen, lset, rset, a0, _ = result
                tape, pos, _ = gf.sim_tape(tbl, t)
                lc = min(sum(v == 1 for p, v in tape.items() if p < pos), 2)
                rc = min(sum(v == 1 for p, v in tape.items() if p > pos), 2)
                refined = gf.build_fw_closure(tbl, lset, rset, (a0, lc, rc))
                if refined is None:
                    continue
                adj = gf.fw_adj(tbl, lset, rset, refined)
                targets = sorted({a[0][:2] for a in refined} | warmup_fires(tbl, t))
                cands = gf.exhaustive_cands(n)
                per_target = {}
                for target in targets:
                    found = instruction_procedure(tbl, n, adj, refined, target, cands)
                    if found is None or not instruction_check(
                            tbl, n, adj, refined, target, *found):
                        first_fail = first_fail or dict(n=n, t=t, mirrored=mirrored,
                            target=list(target), contexts=len(refined))
                        break
                    per_target[target] = found
                else:
                    return dict(spec=spec, status="found", n=n, t=t,
                        mirrored=mirrored, contexts=len(refined),
                        fuel=8 * len(refined) + 64,
                        rounds=len(lset) + len(rset) + 4,
                        cert=emit_cert(per_target))
    return dict(spec=spec, status="no certificate", first_fail=first_fail)


def work(queue, spec, n0, n_extra, warmups):
    try:
        queue.put(find_one(spec, n0, n_extra, warmups))
    except Exception as e:
        queue.put(dict(spec=spec, status="error", error=repr(e)))



def existing_rows():
    result = set()
    for path in (ROOT / "theories/CloseoutTr").glob("CBT_*.v"):
        result.update(re.findall(r"\(\* spec (\S+) \*\)", path.read_text()))
    return result


def run_timed(spec, n0, n_extra, warmups, timeout):
    start = time.monotonic()
    ctx = mp.get_context("spawn")
    results = ctx.Queue()
    proc = ctx.Process(target=work, args=(results, spec, n0, n_extra, warmups))
    proc.start()
    try:
        result = results.get(timeout=timeout)
    except queue.Empty:
        result = dict(spec=spec, status="timeout")
        proc.terminate()
    proc.join()
    results.close()
    result["seconds"] = round(time.monotonic() - start, 3)
    result.update(probe_n0=n0, probe_n_extra=n_extra, probe_warmups=warmups,
                  probe_timeout=timeout)
    return result


def write_records(tag, nn, indexed, overwrite=False):
    entries, preamble = [], []
    for idx, rec in indexed:
        name = "fueltr_%s_%02d_%04d" % (tag, nn, idx)
        preamble.append("Definition %s : Instr -> list ngcomp * list positive :=\n%s." %
                        (name, rec["cert"]))
        proof = "apply coversTr_nqh. "
        if rec["mirrored"]:
            proof += "apply neverqhtr_mirror. "
        proof += ("apply (ngram_check_neverqh_fuelwtr_sound _ %d %d %d %d %s). " %
            (rec["n"], rec["t"], rec["fuel"], rec["rounds"], name))
        proof += "vm_compute. reflexivity."
        entries.append((rec["spec"], proof))
    path = Path(write_batch(tag, nn,
        ["From BBB4.Checkers Require Import NGram FuelWideTr.",
         "From BBB4.CensusTr Require Import TNF_QHTr."], entries,
        "instruction-target lexicographic and fuel certificates (FuelWideTr)",
        overwrite=overwrite, preamble="\n\n".join(preamble)))
    # Removing a duplicate must not rename the remaining row theorems.
    names = {dense: original for dense, (original, _) in enumerate(indexed)}
    base = "%s_%02d" % (tag, nn)
    pat = r"\b(r|cv)_" + re.escape(base) + r"_(\d{4})\b"
    text = re.sub(pat, lambda m: "%s_%s_%04d" %
                  (m.group(1), base, names[int(m.group(2))]), path.read_text())
    path.write_text(text)
    print(path)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="mode", required=True)
    find = sub.add_parser("find")
    find.add_argument("rows")
    find.add_argument("output")
    find.add_argument("--timeout", type=int, default=60)
    find.add_argument("--n-extra", type=int, default=1)
    find.add_argument("--warmups", default="0,64,256")
    find.add_argument("--all", action="store_true")
    find.add_argument("--n0", type=int, default=2)
    find.add_argument("--jobs", type=int, default=1)
    batch = sub.add_parser("batch")
    batch.add_argument("input")
    batch.add_argument("--start", type=int, default=5)
    batch.add_argument("--chunk", type=int, default=4)
    batch.add_argument("--tag", default="AST")
    rewrite = sub.add_parser("rewrite")
    rewrite.add_argument("input", nargs="+")
    rewrite.add_argument("--tag", default="AST")
    rewrite.add_argument("--batch", type=int, required=True)
    rewrite.add_argument("--exclude", action="append", default=[])
    args = ap.parse_args()
    if args.mode == "find":
        rows = set(Path(args.rows).read_text().split())
        manifest = list(csv.DictReader(open(ROOT / "tools/fuel_manifest.tsv"), delimiter="\t"))
        completed = set()
        output = Path(args.output)
        if output.exists():
            completed = {json.loads(line)["spec"] for line in output.read_text().splitlines()}
        if args.all:
            candidates = [(spec, args.n0) for spec in sorted(rows - existing_rows())]
        else:
            candidates = [(rec["machine"], int(rec["n"])) for rec in manifest
                          if rec["machine"] in rows]
        candidates = [(spec, n0) for spec, n0 in candidates if spec not in completed]
        warmups = list(map(int, args.warmups.split(",")))
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            futures = [pool.submit(run_timed, spec, n0, args.n_extra, warmups,
                                   args.timeout) for spec, n0 in candidates]
            for future in as_completed(futures):
                result = future.result()
                with output.open("a") as f:
                    f.write(json.dumps(result, sort_keys=True) + "\n")
                print(result["spec"], result["status"], result["seconds"], flush=True)
    elif args.mode == "batch":
        records = [json.loads(line) for line in Path(args.input).read_text().splitlines()]
        existing = existing_rows()
        records = [r for r in records if r["status"] == "found"
                   and r["spec"] not in existing]
        for offset in range(0, len(records), args.chunk):
            nn = args.start + offset // args.chunk
            write_records(args.tag, nn, list(enumerate(records[offset:offset + args.chunk])))
    else:
        records = {r["spec"]: r for source in args.input
                   for r in map(json.loads, Path(source).read_text().splitlines())
                   if r["status"] == "found"}
        path = ROOT / "theories/CloseoutTr" / ("CBT_%s_%02d.v" % (args.tag, args.batch))
        pat = (r"\(\* spec (\S+) \*\)\s+Definition r_" + re.escape(args.tag) +
               r"_%02d_(\d{4})" % args.batch)
        indexed = [(int(idx), records[spec]) for spec, idx in re.findall(pat, path.read_text())
                   if spec not in set(args.exclude)]
        if not indexed:
            raise SystemExit("no retained rows; refusing to overwrite")
        write_records(args.tag, args.batch, indexed, overwrite=True)


if __name__ == "__main__":
    main()
