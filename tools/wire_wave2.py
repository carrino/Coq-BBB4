#!/usr/bin/env python3
"""wire_wave2.py -- WIRE the wave-2 staged residue proofs into the census
and regenerate the Deferred_* tables (D_census 9,364 -> 7,255).

Run from the Coq-BBB4 repo root (the branch with the staged proofs):

    python3 tools/wire_wave2.py           # do the wiring
    python3 tools/wire_wave2.py --dry     # arithmetic + checks only, NO writes

It performs the batched FOLLOW-UP documented in docs/REROOT_LISTC_STAGE.md:

  1. reroot -> R_QH tier:  append the 1,518 RerootStage machines to
     tools/reroot_boarded.txt and extend reroot_qh_list (RerootQH_Data.v)
     with rrstage_00..15.
  2. listC  -> R_NeverQH tier:  write tools/proven_listc_dropped.txt (591)
     and extend proven_list (Proven_Data.v) with lcstage_00..11.
  3. regen Deferred_*:  reconstruct the 19,735 pre-shrink set (exactly as
     tools/regen_residue.py), subtract proven + provenQH + reroot(1,702) +
     listC(591), assert the arithmetic (=> 7,255), rewrite
     census_{holdouts_kept,residue}.txt, and emit Deferred_* via gen_deferred.py.
  4. _CoqProject:  add the RerootStage/ListCStage/corruption modules.

Everything is asserted; a stale or inconsistent input fails LOUDLY before any
census file is touched.  This script is UNTRUSTED -- the Coq kernel re-checks
every proof when you build.  Idempotent: safe to re-run.

AFTER running, on STABLE hardware (native_compute):
    make                     # base build must be green (verifies the wiring)
    make census-verify       # the walk; Print Assumptions census_decided
                             #   MUST be functional_extensionality_dep only
    python3 tools/census_cache.py --update && git add -A && git commit
"""
import os
import subprocess
import sys

DRY = "--dry" in sys.argv
# repo root: tools/wire_wave2.py -> repo root (BBB4_ROOT env overrides, for testing)
ROOT = os.environ.get("BBB4_ROOT") or os.path.dirname(
    os.path.dirname(os.path.abspath(__file__)))
T = os.path.join(ROOT, "tools")
C = os.path.join(ROOT, "theories", "Census")

# the 2 proven-QH holdouts that MUST STAY deferred (from regen_residue.py)
STAY = {
    "1RB---_1LC0LB_0RC0LD_1RD1RB",
    "1RB---_1RC0RB_0LC0RD_1LD1LB",
}


def txt(path):
    return {l.strip() for l in open(path)
            if l.strip() and not l.startswith("#")}


def tsv_col0(path):
    with open(path) as f:
        next(f)
        return {l.split("\t")[0] for l in f
                if l.strip() and not l.startswith("#")}


def manifest_machines(path):
    with open(path) as f:
        next(f)  # header
        return [l.split("\t")[0] for l in f if l.strip()]


def write(path, content):
    if DRY:
        print("  [dry] would write %s (%d bytes)" % (path, len(content)))
        return
    open(path, "w").write(content)
    print("  wrote %s" % os.path.relpath(path, ROOT))


def banner(s):
    print("\n=== %s ===" % s)


# --------------------------------------------------------------------------
banner("0. preflight: staged artifacts present")
rr_manifest = os.path.join(T, "reroot_stage_manifest.tsv")
lc_manifest = os.path.join(T, "listc_stage_manifest.tsv")
for p in (rr_manifest, lc_manifest):
    assert os.path.exists(p), "missing %s -- are you on the wave-2 branch?" % p
rr_machines = manifest_machines(rr_manifest)
lc_machines = manifest_machines(lc_manifest)
assert len(rr_machines) == 1518, len(rr_machines)
assert len(lc_machines) == 591, len(lc_machines)
for i in range(16):
    assert os.path.exists(os.path.join(
        ROOT, "theories/Machines/RerootStage/RRStage_%02d.v" % i))
for i in range(12):
    assert os.path.exists(os.path.join(
        ROOT, "theories/Machines/ListCStage/LCStage_%02d.v" % i))
print("  reroot staged: %d   listC staged: %d   all .v present" %
      (len(rr_machines), len(lc_machines)))

# --------------------------------------------------------------------------
banner("1. reconstruct pre-shrink set (mirrors regen_residue.py stage 1)")
wrap_qh = tsv_col0(os.path.join(T, "wrap_residue_caught.tsv"))
core = txt(os.path.join(T, "wrap_residue_survivors.txt"))
qhb = tsv_col0(os.path.join(T, "qhbound_caught.tsv"))
qlx = tsv_col0(os.path.join(T, "qhbound_lex_caught.tsv"))
rw = tsv_col0(os.path.join(T, "repwl_residue_caught.tsv"))
assert len(wrap_qh) == 20568 and len(core) == 31758
assert qhb <= wrap_qh and qlx <= wrap_qh and not (qhb & qlx) and rw <= core
residue = (wrap_qh - qhb - qlx) | (core - rw)
# The immutable 3,713 BBB(4) holdout set, reconstructed self-contained from the
# committed drop-lists: current-kept (27) + proven never-QH holdouts (3,670) +
# provenQH holdouts (16), pairwise disjoint.  Verified byte-equal to the
# canonical /home/user/BBB/BBB4_holdouts_3713.txt (sym-diff 0).
kept = txt(os.path.join(T, "census_holdouts_kept.txt"))
proven = txt(os.path.join(T, "proven_dropped.txt"))
provenqh_dropped = txt(os.path.join(T, "provenqh_dropped.txt"))
provenqh_map = tsv_col0(os.path.join(T, "provenqh_map.tsv"))
assert not (kept & proven) and not (kept & provenqh_dropped) \
    and not (proven & provenqh_dropped), "holdout drop-lists overlap"
holdouts_full = kept | proven | provenqh_dropped
assert len(holdouts_full) == 3713, ("holdout reconstruction", len(holdouts_full))
assert len(residue) == 16022, len(residue)
old = holdouts_full | residue
assert len(old) == 19735, len(old)
print("  pre-shrink: %d holdouts + %d residue = %d" %
      (len(holdouts_full), len(residue), len(old)))

# --------------------------------------------------------------------------
banner("2. assemble drop-lists (proven + provenQH + reroot(1,702) + listC(591))")
assert len(proven) == 3670 and proven <= holdouts_full and not (STAY & proven)
pq_hold = provenqh_map & holdouts_full
pq_res = provenqh_map & residue
assert not (provenqh_map - holdouts_full - residue), "provenqh stray"
assert not (STAY & provenqh_map), "stay-QH boarded R_QH"
# reroot: committed 184 + wave-2 1,518 = 1,702, ALL residue
reroot_old = txt(os.path.join(T, "reroot_boarded.txt"))
reroot = reroot_old | set(rr_machines)
assert len(reroot) == 1702, ("reroot union", len(reroot))
assert reroot <= residue, ("reroot not in residue", len(reroot - residue))
# listC: 591, ALL residue
listc = set(lc_machines)
assert len(listc) == 591
assert listc <= residue, ("listc not in residue", len(listc - residue))
# pairwise disjoint (no double-drop)
groups = {"proven": proven, "provenqh": provenqh_map,
          "reroot": reroot, "listc": listc}
names = list(groups)
for i in range(len(names)):
    for j in range(i + 1, len(names)):
        inter = groups[names[i]] & groups[names[j]]
        assert not inter, ("overlap", names[i], names[j], len(inter),
                           sorted(inter)[:2])
assert not (STAY & (reroot | listc)), "stay-QH boarded a residue tier"

# --------------------------------------------------------------------------
banner("3. apply drops + assert D_census = 7,255")
new_holdouts = sorted(holdouts_full - proven - pq_hold)
new_residue = sorted(residue - pq_res - reroot - listc)
newset = set(new_holdouts) | set(new_residue)
assert newset == old - proven - provenqh_map - reroot - listc, "drop mismatch"
assert STAY <= newset, "stay-QH lost"
D = len(newset)
print("  new: %d holdouts + %d residue = %d  (was 9,364; -%d)" %
      (len(new_holdouts), len(new_residue), D, 9364 - D))
assert D == 7255, ("D_census", D)

# --------------------------------------------------------------------------
banner("4. write drop-lists + regen Deferred_* via gen_deferred.py")
write(os.path.join(T, "reroot_boarded.txt"),
      "\n".join(sorted(reroot)) + "\n")
write(os.path.join(T, "proven_listc_dropped.txt"),
      "# listC never-QH residue boarded R_NeverQH (proven_list, wave 2)\n"
      + "\n".join(sorted(listc)) + "\n")
write(os.path.join(T, "census_holdouts_kept.txt"),
      "\n".join(new_holdouts) + "\n")
write(os.path.join(T, "census_residue.txt"),
      "\n".join(new_residue) + "\n")
if not DRY:
    subprocess.run(
        [sys.executable, os.path.join(T, "gen_deferred.py"),
         os.path.join(T, "census_holdouts_kept.txt"),
         os.path.join(T, "census_residue.txt"), C],
        check=True)
    print("  Deferred_* regenerated")

# --------------------------------------------------------------------------
banner("5. wire reroot_qh_list (RerootQH_Data.v) + proven_list (Proven_Data.v)")
RR = ["rerootqh_0%d" % i for i in range(5)] + ["rrstage_%02d" % i for i in range(16)]
rr_data = '''(** GENERATED by tools/gen_reroot.py + wire_wave2.py -- DO NOT EDIT.

    The census re-root quasihalting tier (R_QH): wave-1 (rerootqh_00..04,
    184 machines) + wave-2 staged (rrstage_00..15, 1,518 machines) list-B
    0RB residue machines boarded by [qh_reroot] (Census/Reroot.v). *)
From Coq Require Import List.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import TNF_QH %s.
From BBB4.Machines.RerootStage Require Import %s.
Import ListNotations.

Definition reroot_qh_list : list TM :=
  %s.

Lemma reroot_qh_all :
  Forall (fun tm => NonHalt tm /\\ QHBound 2000 tm /\\ QuasiHaltsSt tm)
         reroot_qh_list.
Proof.
  unfold reroot_qh_list.
%s
Qed.
''' % (" ".join("RerootQH_%02d" % i for i in range(5)),
       " ".join("RRStage_%02d" % i for i in range(16)),
       "\n  ++ ".join(RR),
       "\n".join("  apply Forall_app; split; [exact %s_all|]." % c
                 for c in RR[:-1]) + "\n  exact %s_all." % RR[-1])
write(os.path.join(C, "RerootQH_Data.v"), rr_data)

PV = ["proven_0%d" % i for i in range(8)] + ["lcstage_%02d" % i for i in range(12)]
pv_data = '''(** GENERATED by tools/gen_proven.py + wire_wave2.py -- do not edit.

    The census proven-machines tier (R_NeverQH): BBB(4) holdouts
    (proven_00..07) + wave-2 staged list-C residue (lcstage_00..11, 591
    machines), each with a committed in-Coq [NeverQuasiHaltsSt] theorem. *)
From Coq Require Import List.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import %s.
From BBB4.Machines.ListCStage Require Import %s.
Import ListNotations.

Definition proven_list : list TM :=
  %s.

Lemma proven_all : Forall NeverQuasiHaltsSt proven_list.
Proof.
  unfold proven_list.
%s
Qed.
''' % (" ".join("Proven_%02d" % i for i in range(8)),
       " ".join("LCStage_%02d" % i for i in range(12)),
       "\n  ++ ".join(PV),
       "\n".join("  apply Forall_app; split; [exact %s%s|]."
                 % (c, "_nqh" if c.startswith("proven") else "_nqh")
                 for c in PV[:-1]) + "\n  exact %s_nqh." % PV[-1])
write(os.path.join(C, "Proven_Data.v"), pv_data)

# --------------------------------------------------------------------------
banner("6. _CoqProject: add the staged modules (idempotent)")
cp_path = os.path.join(ROOT, "_CoqProject")
cp = open(cp_path).read()
add = (["theories/Machines/RerootStage/RRStage_%02d.v" % i for i in range(16)]
       + ["theories/Machines/ListCStage/LCStage_%02d.v" % i for i in range(12)]
       + ["theories/Tests/RerootStage_Corruption.v"])
missing = [a for a in add if a not in cp]
if missing:
    block = ("\n# --- wave-2 residue tiers (wired by wire_wave2.py) ---\n"
             + "\n".join(missing) + "\n")
    write(cp_path, cp.rstrip("\n") + "\n" + block)
else:
    print("  _CoqProject already has the staged modules")

banner("DONE -- wiring complete (D_census 9,364 -> %d)" % D)
print("""
Next, on STABLE hardware (native_compute):
  make                 # base build must be GREEN (this verifies the wiring)
  make census-verify   # the walk; then check:
                       #   Print Assumptions census_decided
                       #   == functional_extensionality_dep ONLY
  python3 tools/census_cache.py --update
  git add -A && git commit -m "wire wave-2 residue tiers -- D_census -> %d"
""" % D)
