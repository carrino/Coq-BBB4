#!/usr/bin/env python3
"""RE-VALIDATE the re-root bridge over the CURRENT 16,022 census residue.

UNTRUSTED measurement only (no proof claims).  Reuses reroot_mapper.py.

Reconstructs list B/C exactly as regen_residue.py builds the residue:
    B (wrap-QH survivors) = wrap_residue_caught - qhbound_caught - qhbound_lex_caught
    C (never-QH survivors) = wrap_residue_survivors - repwl_residue_caught
    residue = B | C   (disjoint; 9,775 + 6,247 = 16,022)

Emits:
    reroot_mapping_16022.tsv   (same schema as reroot_mapping.tsv + summary comments)
    cert_matches_16022.tsv     (census, upstream_tnf, family, list, nstates, dropped)
    cert_board_16022.tsv       (census, core upstream_tnf, cert path, exists?)
and prints the old-vs-new summary block.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
TOOLS = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import reroot_mapper as rm

BBB = "/home/user/BBB"
CERT_ROOT = os.path.join(BBB, "results")
HOLDOUTS = os.path.join(BBB, "BBB4_holdouts_3713.txt")

# The 9 families the original recon counted as "cert-boardable": each has an
# EXISTING census checker, so the census can re-run its own decider on the clean
# 4-state re-root target (rank / irules / modclass~irules / fuel / drift /
# neverqh / rwlsilent / v6res90~v7res46~irules).  These define the headline
# apples-to-apples "cert-boardable" number.
BOARDABLE_FAMILIES = [
    "certs_drift", "certs_fuel", "certs_irules", "certs_modclass",
    "certs_neverqh", "certs_rank", "certs_rwlsilent", "certs_v6res90",
    "certs_v7res46",
]
# All families present (for broader coverage reporting only).
CERT_FAMILIES = [
    "certs", "certs_2b", "certs_bouncer", "certs_drift", "certs_fuel",
    "certs_geom", "certs_irules", "certs_modclass", "certs_neverqh",
    "certs_neverqh_rwl", "certs_quietctl", "certs_quietfar", "certs_rank",
    "certs_rwlrank", "certs_rwlsilent", "certs_tight", "certs_tngram",
    "certs_v6res90", "certs_v7res46",
]


def tsv_col0(path):
    with open(path) as f:
        next(f)
        return {l.split("\t")[0] for l in f if l.strip() and not l.startswith("#")}


def txt(path):
    return {l.strip() for l in open(path)
            if l.strip() and not l.startswith("#")}


def canon_key(machine_str):
    """Canonicalize an upstream TNF string the same way the mapper does,
       dropping dead/padding states so a 3-state cert (padded _------) and a
       3-state re-root land on the same key. Returns None on parse trouble."""
    try:
        s, _ = rm.canon(rm.parse(machine_str), start=0)
        return s
    except Exception:
        return None


def build_cert_index(families):
    """key(canonical upstream tnf) -> (family, cert_path).  Prefers the family
       order in `families` on collision; records every family a key appears in."""
    index = {}
    fam_of = {}
    for fam in families:
        d = os.path.join(CERT_ROOT, fam)
        if not os.path.isdir(d):
            continue
        for fn in os.listdir(d):
            if not fn.endswith(".cert"):
                continue
            stem = fn[:-len(".cert")]
            key = canon_key(stem)
            if key is None:
                continue
            path = os.path.join(d, fn)
            if key not in index:
                index[key] = (fam, path)
                fam_of[key] = {fam}
            else:
                fam_of[key].add(fam)
    return index, fam_of


def build_holdout_index():
    index = {}
    for h in txt(HOLDOUTS):
        key = canon_key(h)
        if key is not None:
            index[key] = h
    return index


def main():
    # --- reconstruct B / C exactly as regen_residue.py does ---
    wrap_qh = tsv_col0(os.path.join(TOOLS, "wrap_residue_caught.tsv"))
    core = txt(os.path.join(TOOLS, "wrap_residue_survivors.txt"))
    qhb = tsv_col0(os.path.join(TOOLS, "qhbound_caught.tsv"))
    qlx = tsv_col0(os.path.join(TOOLS, "qhbound_lex_caught.tsv"))
    rw = tsv_col0(os.path.join(TOOLS, "repwl_residue_caught.tsv"))
    listB = (wrap_qh - qhb - qlx)          # wrap-QH survivors
    listC = (core - rw)                    # never-QH survivors
    residue = txt(os.path.join(TOOLS, "census_residue.txt"))

    assert len(residue) == 16022, len(residue)
    assert not (listB & listC), len(listB & listC)
    assert listB | listC == residue, (
        "B|C != residue", len(listB | listC), len((listB | listC) ^ residue))
    list_of = {}
    for m in listB:
        list_of[m] = "B"
    for m in listC:
        list_of[m] = "C"
    print(f"[recon] |B wrap-QH survivors| = {len(listB)}  "
          f"|C never-QH survivors| = {len(listC)}  total = {len(residue)}")

    # --- build cert + holdout indices ---
    # boardable = the 9 families with an existing census checker (headline number)
    cert_index, _ = build_cert_index(BOARDABLE_FAMILIES)
    # broad = every cert family present, for coverage reporting only
    broad_index, broad_fam_of = build_cert_index(CERT_FAMILIES)
    holdout_index = build_holdout_index()
    print(f"[recon] boardable cert keys = {len(cert_index)}  "
          f"all-family cert keys = {len(broad_index)}  "
          f"holdout keys = {len(holdout_index)}")

    # --- run the mapper over all 16,022 machines ---
    rows = []
    n_never1 = 0
    for m in sorted(residue):
        r = rm.upstream_tnf(m)
        tnf = r["tnf"]
        mode = r["mode"]
        nsa = r["nstates_after"]
        dropped = r["dropped_states"]
        ndrop = len(dropped) if dropped is not None else ""
        status = "none"
        family = ""
        broad_fams = ""
        key = None
        if tnf is not None:
            key = canon_key(tnf)
            # cert-first precedence: a per-machine cert DECIDES the machine even
            # though its upstream TNF may still sit in the original 3,713 holdout
            # list (the mass-decider undecided set, pre per-machine certs).
            if key in cert_index:
                status = "cert"
                family = cert_index[key][0]
            elif key in holdout_index:
                status = "holdout"
            if key in broad_index:
                broad_fams = ",".join(sorted(broad_fam_of[key]))
        else:
            n_never1 += 1
        rows.append(dict(census=m, tnf=tnf if tnf else "", status=status,
                         family=family, lst=list_of[m], mode=mode,
                         nsa=nsa if nsa is not None else "", ndrop=ndrop,
                         key=key, broad_fams=broad_fams))

    # --- write mapping tsv ---
    map_path = os.path.join(HERE, "reroot_mapping_16022.tsv")
    with open(map_path, "w") as f:
        f.write("census_machine\tupstream_tnf\tupstream_status\tcert_family\t"
                "list\tmode\tnstates_after\tdropped\n")
        for r in rows:
            f.write(f"{r['census']}\t{r['tnf']}\t{r['status']}\t{r['family']}\t"
                    f"{r['lst']}\t{r['mode']}\t{r['nsa']}\t{r['ndrop']}\n")

    # --- cert matches tsv ---
    cert_rows = [r for r in rows if r["status"] == "cert"]
    cm_path = os.path.join(HERE, "cert_matches_16022.tsv")
    with open(cm_path, "w") as f:
        f.write("census_machine\tupstream_tnf\tcert_family\tlist\t"
                "nstates_after\tdropped\n")
        for r in sorted(cert_rows, key=lambda x: (x["family"], x["census"])):
            f.write(f"{r['census']}\t{r['tnf']}\t{r['family']}\t{r['lst']}\t"
                    f"{r['nsa']}\t{r['ndrop']}\n")

    # --- cert board tsv (with real path + existence check) ---
    cb_path = os.path.join(HERE, "cert_board_16022.tsv")
    n_exist = 0
    with open(cb_path, "w") as f:
        f.write("census_machine\tupstream_core_tnf\tcert_family\tcert_path\texists\n")
        for r in sorted(cert_rows, key=lambda x: (x["family"], x["census"])):
            fam, path = cert_index[r["key"]]
            ex = os.path.isfile(path)
            n_exist += int(ex)
            f.write(f"{r['census']}\t{r['tnf']}\t{fam}\t{path}\t{int(ex)}\n")

    # --- summary counts ---
    holdout_rows = [r for r in rows if r["status"] == "holdout"]
    # nstates_after distribution by mode
    from collections import Counter
    mode_ct = Counter(r["mode"] for r in rows)
    nsa_by_mode = Counter((r["mode"], r["nsa"]) for r in rows)
    le3 = [r for r in rows if r["nsa"] != "" and r["nsa"] <= 3]
    le3_by = Counter((r["mode"], r["nsa"]) for r in le3)
    # dedup: distinct mapped tnf
    mapped_keys = [r["key"] for r in rows if r["key"] is not None]
    distinct = set(mapped_keys)
    from collections import Counter as C2
    nstate_of_key = {}
    for r in rows:
        if r["key"] is not None:
            nstate_of_key[r["key"]] = r["nsa"]
    distinct_by_nstate = C2(nstate_of_key[k] for k in distinct)
    # riders: reroot rows whose key equals a direct1 residue row's key
    direct1_keys = {r["key"] for r in rows if r["mode"] == "direct1"}
    riders = [r for r in rows if r["mode"] == "reroot" and r["key"] in direct1_keys]
    riders_by_list = Counter(r["lst"] for r in riders)

    print("\n================ SUMMARY (16,022 residue) ================")
    print(f"total rows                 : {len(rows)}")
    print(f"mode distribution          : {dict(mode_ct)}")
    print(f"unmapped (never1, no rep)  : {n_never1}")
    print(f"nstates_after<=3 (core-red): {len(le3)}   breakdown {dict(le3_by)}")
    print(f"upstream cert-boardable    : {len(cert_rows)}  (cert files exist: {n_exist})")
    print(f"upstream holdout matches   : {len(holdout_rows)}  (holdout AND no boardable cert)")
    # broader coverage: match against ALL cert families (not just the 9 boardable)
    broad_rows = [r for r in rows if r["broad_fams"]]
    print(f"match ANY cert family      : {len(broad_rows)}  (superset of boardable)")
    broad_extra = Counter()
    for r in broad_rows:
        if r["status"] != "cert":
            for fam in r["broad_fams"].split(","):
                broad_extra[fam] += 1
    if broad_extra:
        print(f"  non-boardable-only family hits: {dict(broad_extra)}")
    print(f"distinct mapped upstream   : {len(distinct)}   by nstate {dict(distinct_by_nstate)}")
    print(f"dedup: {len(mapped_keys)} rows -> {len(distinct)} distinct "
          f"({len(mapped_keys)-len(distinct)} riders)")
    print(f"reroot rows landing on a direct1 residue key: {len(riders)}  "
          f"by list {dict(riders_by_list)}")
    print("\ncert family breakdown:")
    fam_ct = Counter((r["family"], r["lst"]) for r in cert_rows)
    for (fam, lst), n in sorted(fam_ct.items()):
        print(f"  {fam:20s} {lst}  {n}")
    print("\nnstates_after full distribution by mode:")
    for k in sorted(nsa_by_mode):
        print(f"  {k}: {nsa_by_mode[k]}")
    # list x mode
    lm = Counter((r["lst"], r["mode"]) for r in rows)
    print("\nlist x mode:")
    for k in sorted(lm):
        print(f"  {k}: {lm[k]}")
    # core-reducible by list
    le3_list = Counter(r["lst"] for r in le3)
    print(f"\ncore-reducible (<=3) by list: {dict(le3_list)}")

    # write a machine-readable summary block appended to the mapping file
    with open(map_path, "a") as f:
        f.write(f"# SUMMARY total={len(rows)} modes={dict(mode_ct)} "
                f"never1={n_never1} core_le3={len(le3)} "
                f"cert={len(cert_rows)} holdout={len(holdout_rows)} "
                f"distinct={len(distinct)} riders={len(riders)}\n")
        f.write(f"# core_le3_breakdown={dict(le3_by)}\n")
        f.write(f"# distinct_by_nstate={dict(distinct_by_nstate)}\n")
        f.write(f"# listB(wrapQH)={len(listB)} listC(neverQH)={len(listC)}\n")
    print(f"\n[wrote] {map_path}")
    print(f"[wrote] {cm_path}")
    print(f"[wrote] {cb_path}")


if __name__ == "__main__":
    main()
