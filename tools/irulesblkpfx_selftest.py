#!/usr/bin/env python3
"""Differential self-check for the Phase-2 prefix cert emitter.

Re-parses every generated IRulesBlkPfx_Batch_0*.v machine block
COUNT-wise (machines, rules, runs, prefix-flag-set rules, BVm lattice
runs, blocks) and compares against the SOURCE certificates the emitter
was fed.  All 50 machines must match on every count, else exit 1.

The generated .v is scraped with regexes independent of the emitter's
formatting choices; the "expected" side reuses the emitter's own
[parse_cert]/[cert_stats] over the raw certs.  Any drift between the
cert and its Coq literal (a dropped run, a mis-parsed prefix flag, a
lattice run silently downgraded to a plain var) shows up as a mismatch.

Usage: irulesblkpfx_selftest.py            (default dirs + batch glob)
       irulesblkpfx_selftest.py --v6 DIR --v7 DIR --batches GLOB
"""
import sys, os, re, glob

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_irulesblkpfx_certs import parse_cert, cert_stats, cname

V6_DIR = "/home/user/BBB/results/certs_v6res90"
V7_DIR = "/home/user/BBB/results/certs_v7res46"
BATCH_GLOB = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                          "..", "theories", "Machines",
                          "IRulesBlkPfx_Batch_0*.v")

PFX_RE = re.compile(r"\((true|false), (true|false)\)")


def split_blocks(text):
    """Map cname -> per-machine text block from a generated batch file."""
    blocks = {}
    # each machine starts at "Definition tmbp_<nm> : TM"
    idxs = [(m.start(), m.group(1))
            for m in re.finditer(r"Definition tmbp_(\S+) : TM", text)]
    for i, (start, nm) in enumerate(idxs):
        end = idxs[i + 1][0] if i + 1 < len(idxs) else len(text)
        blocks[nm] = text[start:end]
    return blocks


def actual_counts(block):
    rules = block.count("mkBRuleP")
    vm = block.count("BVm (")
    runs = block.count("BC (") + block.count("BV (") + block.count("BVm (")
    pfx_set = 0
    npair = 0
    for pl, pr in PFX_RE.findall(block):
        npair += 1
        if pl == "true" or pr == "true":
            pfx_set += 1
    # a %nat block-table cell like (2%nat, [S0; S1]) is not a bool pair,
    # so npair counts exactly one prefix tuple per rule.
    blks = block.count("%nat, [")
    return {"rules": rules, "runs": runs, "pfx_set": pfx_set,
            "vm_runs": vm, "blks": blks, "pfx_pairs": npair}


def find_cert(machine, dirs):
    for d in dirs:
        p = os.path.join(d, machine + ".cert")
        if os.path.exists(p):
            return p
    return None


def main():
    args = sys.argv[1:]
    v6, v7, bglob = V6_DIR, V7_DIR, BATCH_GLOB
    i = 0
    while i < len(args):
        if args[i] == "--v6": v6 = args[i + 1]; i += 2
        elif args[i] == "--v7": v7 = args[i + 1]; i += 2
        elif args[i] == "--batches": bglob = args[i + 1]; i += 2
        else: i += 1

    # gather emitted blocks across all batch files
    emitted = {}
    for bf in sorted(glob.glob(bglob)):
        for nm, block in split_blocks(open(bf).read()).items():
            emitted[nm] = (os.path.basename(bf), block)

    fields = ["rules", "runs", "pfx_set", "vm_runs", "blks"]
    print(f"{'machine':<32} {'file':<26} "
          + " ".join(f"{f:>8}" for f in fields) + "  ok")
    print("-" * 110)
    nmatch = 0
    nfail = 0
    for machine in sorted(
            [os.path.basename(p)[:-5]
             for p in glob.glob(os.path.join(v6, "*.cert"))
             + glob.glob(os.path.join(v7, "*.cert"))]):
        nm = cname(machine)
        cert = find_cert(machine, (v6, v7))
        exp = cert_stats(parse_cert(cert))
        if nm not in emitted:
            print(f"{machine:<32} {'<MISSING FROM BATCHES>':<26}")
            nfail += 1
            continue
        bfile, block = emitted[nm]
        act = actual_counts(block)
        ok = all(exp[f] == act[f] for f in fields) and act["pfx_pairs"] == exp["rules"]
        cells = " ".join(
            (f"{act[f]:>8}" if exp[f] == act[f] else f"{act[f]:>4}!={exp[f]}")
            for f in fields)
        print(f"{machine:<32} {bfile:<26} {cells}  {'OK' if ok else 'FAIL'}")
        if ok:
            nmatch += 1
        else:
            nfail += 1
    print("-" * 110)
    total = nmatch + nfail
    print(f"# {nmatch}/{total} machines match count-wise "
          f"({nfail} mismatch)")
    if nfail:
        sys.exit(1)


if __name__ == "__main__":
    main()
