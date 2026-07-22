#!/usr/bin/env python3
"""Recompute the census residue after the verified-tier sweeps and
regenerate the Deferred_* tables (UNTRUSTED tooling).

Two stages:

  (1) Reconstruct the PRE-SHRINK deferred set exactly as the committed
      Deferred_* tables encode it:

        residue = (wrap_residue_caught - qhbound_caught - qhbound_lex_caught)
                  + (wrap_residue_survivors - repwl_residue_caught)

      i.e. the 52,326-machine raw residue minus everything the first-wave
      census tiers (wrapped QHBound plain/lex, RepWL) decide at walk time
      -- 16,022 machines -- and the 3,713 BBB(4) holdouts, for a total of
      19,735.  Set relations are asserted so a stale input fails loudly.

  (2) SHRINK (default): subtract the four measured lever drop-lists that
      the HEAD tier wiring now decides at walk time, so they leave the
      deferred list:

        - proven_dropped        (lever A, 3,620)  -- proven never-QH
                                                     holdouts, via the
                                                     proven tier
        - provenqh_dropped      (lever A, 16)     -- proven-QH holdouts
                                                     probe-confirmed R_QH
                                                     through tier Q
        - qhbound_lex2_caught   (lever B, 2,533)  -- wrap-QH residue
                                                     caught by the extended
                                                     QHBound ladder
        - repwl2_caught         (lever C, 592)    -- never-QH residue
                                                     caught by the extended
                                                     RepWL ladder

      leaving 77 holdouts + 12,897 residue = 12,974 machines.  Every
      arithmetic identity is asserted (old 19,735; the four drops
      3,620/16/2,533/592, each a subset of the right parent, pairwise
      disjoint, no double-drop; the 2 stay-QH holdouts kept; new 12,974;
      no new machines).

Pass --legacy to skip stage (2) and regenerate the pre-shrink 19,735 set
(the committed HEAD tables), for reproducibility / backward-compat.

Usage: regen_residue.py HOLDOUTS OUTDIR [--legacy]
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

# the two proven-QH holdouts that MUST STAY deferred (probe-confirmed
# they do not leave via tier Q under the census bound)
STAY = {
    "1RB---_1LC0LB_0RC0LD_1RD1RB",
    "1RB---_1RC0RB_0LC0RD_1LD1LB",
}


def tsv_col0(path):
    with open(path) as f:
        next(f)
        return {l.split("\t")[0] for l in f if l.strip() and not l.startswith("#")}


def txt(path):
    return {l.strip() for l in open(path)
            if l.strip() and not l.startswith("#")}


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    flags = {a for a in sys.argv[1:] if a.startswith("--")}
    holdouts_path, outdir = args[0], args[1]
    legacy = "--legacy" in flags

    # --- stage (1): reconstruct the pre-shrink 19,735 set ---
    wrap_qh = tsv_col0(os.path.join(HERE, "wrap_residue_caught.tsv"))
    core = txt(os.path.join(HERE, "wrap_residue_survivors.txt"))
    qhb = tsv_col0(os.path.join(HERE, "qhbound_caught.tsv"))
    qlx = tsv_col0(os.path.join(HERE, "qhbound_lex_caught.tsv"))
    rw = tsv_col0(os.path.join(HERE, "repwl_residue_caught.tsv"))

    assert len(wrap_qh) == 20568, len(wrap_qh)
    assert len(core) == 31758, len(core)
    assert not (wrap_qh & core)
    assert qhb <= wrap_qh, len(qhb - wrap_qh)
    assert qlx <= wrap_qh, len(qlx - wrap_qh)
    assert not (qhb & qlx)
    assert rw <= core, len(rw - core)

    residue = (wrap_qh - qhb - qlx) | (core - rw)
    holdouts = txt(holdouts_path)
    assert len(residue) == 16022, len(residue)
    assert len(holdouts) == 3713, len(holdouts)
    assert not (holdouts & residue), len(holdouts & residue)
    old = holdouts | residue
    assert len(old) == 19735, len(old)
    print(f"[stage 1] pre-shrink set: {len(holdouts)} holdouts + "
          f"{len(residue)} residue = {len(old)}")

    if legacy:
        new_holdouts = sorted(holdouts)
        new_residue = sorted(residue)
        print("[legacy] no drops applied")
    elif "--proven-only" in flags:
        # PROVEN-ONLY: drop ONLY the 3,620 proven never-QH holdouts (lever A);
        # keep the B/C residue catches (qhb-lex, RepWL) and the 16 provenQH
        # DEFERRED, so the census walk stays LIGHT (deferred-lookup skip, not
        # the expensive in-walk ladder).  D_census = 93 holdouts + 16,022
        # residue = 16,115.  See the 2026-07-19/20 post-mortem: the full
        # 12,974 shrink's in-walk tiers make the native_compute walk
        # hours-long per subtree and cannot certify under container preemption.
        proven = txt(os.path.join(HERE, "proven_dropped.txt"))
        assert len(proven) == 3670, len(proven)
        stray = proven - holdouts
        assert not stray, ("proven_dropped not in holdouts", len(stray))
        assert not (STAY & proven), "stay-QH machine in proven drop list"
        new_holdouts = sorted(holdouts - proven)
        new_residue = sorted(residue)               # B/C stay deferred
        assert len(new_holdouts) == 43, len(new_holdouts)
        assert len(new_residue) == 16022, len(new_residue)
        newset = set(new_holdouts) | set(new_residue)
        assert len(newset) == 16065, len(newset)
        assert newset == old - proven, "new set != old minus proven"
        assert STAY <= newset, "stay-QH machine lost"
        print(f"[proven-only] {len(new_holdouts)} holdouts + "
              f"{len(new_residue)} residue = {len(newset)} "
              f"(dropped {len(proven)} proven; B/C + provenQH kept deferred)")
    elif "--provenqh" in flags:
        # PROVEN + PROVEN-QH: the committed R_NeverQH proven tier (3,670) AND
        # the committed R_QH proven-QH tier (Census/ProvenQH_Data.v).  Every
        # dropped machine has a committed in-Coq theorem the census decider
        # returns directly (proven -> R_NeverQH, provenqh -> R_QH), so it
        # leaves D_census at ZERO walk cost.  The proven-QH drop set is read
        # from tools/provenqh_map.tsv (= provenqh_list) and split into the
        # holdout-side and residue-side machines it actually contains.
        proven = txt(os.path.join(HERE, "proven_dropped.txt"))
        assert len(proven) == 3670, len(proven)
        assert not (proven - holdouts), "proven_dropped not in holdouts"
        assert not (STAY & proven), "stay-QH machine in proven drop list"
        pqmap = tsv_col0(os.path.join(HERE, "provenqh_map.tsv"))
        pq_hold = pqmap & holdouts
        pq_res = pqmap & residue
        stray = pqmap - holdouts - residue
        assert not stray, ("provenqh_map machine outside holdouts+residue",
                           len(stray), sorted(stray)[:3])
        assert not (pq_hold & proven), "provenqh holdout overlaps proven drop"
        assert not (STAY & pqmap), "a stay-QH machine boarded the R_QH tier"
        new_holdouts = sorted(holdouts - proven - pq_hold)
        new_residue = sorted(residue - pq_res)
        newset = set(new_holdouts) | set(new_residue)
        assert newset == old - proven - pqmap, "new set != old minus drops"
        assert STAY <= newset, "stay-QH machine lost"
        print(f"[provenqh] {len(new_holdouts)} holdouts + {len(new_residue)} "
              f"residue = {len(newset)} (dropped {len(proven)} proven + "
              f"{len(pq_hold)} provenqh-holdout + {len(pq_res)} provenqh-residue "
              f"= {len(proven) + len(pqmap)} total)")
    elif "--reroot" in flags:
        # PROVEN + PROVEN-QH + RE-ROOT: everything the --provenqh mode drops
        # (identical asserts, preserved verbatim), PLUS the committed R_QH
        # RE-ROOT tier (Census/RerootQH_Data.v = reroot_qh_list): list-B 0RB
        # residue machines boarded R_QH by qh_reroot through a tiny never-QH
        # core.  Each has a committed in-Coq theorem the decider returns
        # directly, so it leaves D_census at ZERO walk cost.  The re-root drop
        # set is read from tools/reroot_boarded.txt; it lands ENTIRELY in the
        # residue and is disjoint from the proven/provenQH drops.
        proven = txt(os.path.join(HERE, "proven_dropped.txt"))
        assert len(proven) == 3670, len(proven)
        assert not (proven - holdouts), "proven_dropped not in holdouts"
        assert not (STAY & proven), "stay-QH machine in proven drop list"
        pqmap = tsv_col0(os.path.join(HERE, "provenqh_map.tsv"))
        pq_hold = pqmap & holdouts
        pq_res = pqmap & residue
        stray = pqmap - holdouts - residue
        assert not stray, ("provenqh_map machine outside holdouts+residue",
                           len(stray), sorted(stray)[:3])
        assert not (pq_hold & proven), "provenqh holdout overlaps proven drop"
        assert not (STAY & pqmap), "a stay-QH machine boarded the R_QH tier"
        # the re-root tier (new)
        reroot = txt(os.path.join(HERE, "reroot_boarded.txt"))
        rr_stray = reroot - residue
        assert not rr_stray, ("reroot machine outside residue",
                              len(rr_stray), sorted(rr_stray)[:3])
        assert not (reroot & pqmap), "reroot overlaps provenQH drop"
        assert not (reroot & proven), "reroot overlaps proven drop"
        assert not (STAY & reroot), "a stay-QH machine boarded the re-root tier"
        new_holdouts = sorted(holdouts - proven - pq_hold)
        new_residue = sorted(residue - pq_res - reroot)
        newset = set(new_holdouts) | set(new_residue)
        assert newset == old - proven - pqmap - reroot, "new set != old minus drops"
        assert STAY <= newset, "stay-QH machine lost"
        print(f"[reroot] {len(new_holdouts)} holdouts + {len(new_residue)} "
              f"residue = {len(newset)} (dropped {len(proven)} proven + "
              f"{len(pq_hold)} provenqh-holdout + {len(pq_res)} provenqh-residue "
              f"+ {len(reroot)} reroot = "
              f"{len(proven) + len(pqmap) + len(reroot)} total)")
    elif "--wave3" in flags:
        # WAVE 3 (subsumes --reroot and the REROOT_LISTC_STAGE.md --listc
        # plan): everything the --reroot mode drops (identical asserts,
        # preserved verbatim; reroot_boarded.txt now also carries the wired
        # wave-2 RRStage 1,518), PLUS
        #   - tools/proven_listc_dropped.txt -- wave-2 list-C never-QH
        #     machines wired into the proven (R_NeverQH) tier via
        #     Proven_Data.v (LCStage_*), and any wave-3 IRules never-QH
        #     additions appended to the same file/tier;
        #   - tools/iqh_boarded.txt -- wave-3 list-C state-QH machines wired
        #     into the R_QH qhmap tier via RerootQH_Data.v (IQHStage_*),
        #     boarded by irulesblkpfx_check_qh_sound (MetaBlkPfxQH.v).
        # Every dropped machine has a committed in-Coq theorem the census
        # decider returns directly, so it leaves D_census at ZERO walk cost.
        proven = txt(os.path.join(HERE, "proven_dropped.txt"))
        assert len(proven) == 3670, len(proven)
        assert not (proven - holdouts), "proven_dropped not in holdouts"
        assert not (STAY & proven), "stay-QH machine in proven drop list"
        pqmap = tsv_col0(os.path.join(HERE, "provenqh_map.tsv"))
        pq_hold = pqmap & holdouts
        pq_res = pqmap & residue
        stray = pqmap - holdouts - residue
        assert not stray, ("provenqh_map machine outside holdouts+residue",
                           len(stray), sorted(stray)[:3])
        assert not (pq_hold & proven), "provenqh holdout overlaps proven drop"
        assert not (STAY & pqmap), "a stay-QH machine boarded the R_QH tier"
        reroot = txt(os.path.join(HERE, "reroot_boarded.txt"))
        listc = txt(os.path.join(HERE, "proven_listc_dropped.txt"))
        iqh = txt(os.path.join(HERE, "iqh_boarded.txt"))
        drops = [("reroot_boarded", reroot), ("proven_listc_dropped", listc),
                 ("iqh_boarded", iqh)]
        for name, d in drops:
            assert d, (name, "empty drop list")
            stray = d - residue
            assert not stray, (name, "machine outside residue",
                               len(stray), sorted(stray)[:3])
            assert not (d & pqmap), (name, "overlaps provenQH drop")
            assert not (d & proven), (name, "overlaps proven drop")
            assert not (STAY & d), (name, "contains a stay-QH machine")
            print(f"[wave3] {name}: {len(d)} (all in residue)")
        for i in range(len(drops)):
            for j in range(i + 1, len(drops)):
                inter = drops[i][1] & drops[j][1]
                assert not inter, (drops[i][0], drops[j][0], len(inter),
                                   sorted(inter)[:3])
        new_holdouts = sorted(holdouts - proven - pq_hold)
        new_residue = sorted(residue - pq_res - reroot - listc - iqh)
        newset = set(new_holdouts) | set(new_residue)
        assert newset == old - proven - pqmap - reroot - listc - iqh, \
            "new set != old minus drops"
        assert STAY <= newset, "stay-QH machine lost"
        total = (len(proven) + len(pqmap) + len(reroot) + len(listc)
                 + len(iqh))
        print(f"[wave3] {len(new_holdouts)} holdouts + {len(new_residue)} "
              f"residue = {len(newset)} (dropped {len(proven)} proven + "
              f"{len(pqmap)} provenqh + {len(reroot)} reroot + "
              f"{len(listc)} listc-nqh + {len(iqh)} iqh = {total} total)")
    else:
        # --- stage (2): subtract the four lever drop-lists ---
        proven = txt(os.path.join(HERE, "proven_dropped.txt"))
        provenqh = txt(os.path.join(HERE, "provenqh_dropped.txt"))
        qhb2 = tsv_col0(os.path.join(HERE, "qhbound_lex2_caught.tsv"))
        rw2 = tsv_col0(os.path.join(HERE, "repwl2_caught.tsv"))

        # each drop-list is the right size and lands entirely in its parent
        # (sets => each machine appears once; subset => found in old set)
        checks = [
            ("proven_dropped", proven, 3620, holdouts),
            ("provenqh_dropped", provenqh, 16, holdouts),
            ("qhbound_lex2_caught", qhb2, 2533, residue),
            ("repwl2_caught", rw2, 592, residue),
        ]
        for name, d, n, parent in checks:
            assert len(d) == n, (name, len(d), n)
            stray = d - parent
            assert not stray, (name, "not in parent set", len(stray),
                               sorted(stray)[:3])
            print(f"[stage 2] {name}: {len(d)} (all in "
                  f"{'holdouts' if parent is holdouts else 'residue'})")

        # the four lists are pairwise disjoint: no machine dropped twice
        lists = [("proven_dropped", proven), ("provenqh_dropped", provenqh),
                 ("qhbound_lex2_caught", qhb2), ("repwl2_caught", rw2)]
        for i in range(len(lists)):
            for j in range(i + 1, len(lists)):
                inter = lists[i][1] & lists[j][1]
                assert not inter, (lists[i][0], lists[j][0], len(inter))
        alldrop = proven | provenqh | qhb2 | rw2
        assert len(alldrop) == 6761, len(alldrop)
        assert (len(proven) + len(provenqh) + len(qhb2) + len(rw2)
                == len(alldrop)), "double-drop detected"

        # the 2 stay-QH holdouts are present and NOT dropped
        assert STAY <= holdouts, "stay-QH machine missing from holdouts"
        assert not (STAY & alldrop), "stay-QH machine in a drop list"

        new_holdouts = sorted(holdouts - proven - provenqh)
        new_residue = sorted(residue - qhb2 - rw2)
        assert len(new_holdouts) == 77, len(new_holdouts)
        assert len(new_residue) == 12897, len(new_residue)

        newset = set(new_holdouts) | set(new_residue)
        assert len(newset) == 12974, len(newset)
        assert newset <= old, "new machines introduced!"           # no additions
        assert newset == old - alldrop, "new set != old minus drops"  # exact
        assert STAY <= newset, "stay-QH machine lost"
        print(f"[stage 2] shrunk set: {len(new_holdouts)} holdouts + "
              f"{len(new_residue)} residue = {len(newset)} "
              f"(dropped {len(alldrop)}; stay-QH kept)")

    # --- emit the tables via gen_deferred (union + sort + chunk) ---
    hold_path = os.path.join(HERE, "census_holdouts_kept.txt")
    res_path = os.path.join(HERE, "census_residue.txt")
    open(hold_path, "w").write("\n".join(new_holdouts) + "\n")
    open(res_path, "w").write("\n".join(new_residue) + "\n")
    subprocess.run(
        [sys.executable, os.path.join(HERE, "gen_deferred.py"),
         hold_path, res_path, outdir],
        check=True)


if __name__ == "__main__":
    main()
