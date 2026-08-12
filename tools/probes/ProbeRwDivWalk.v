(* M4 sizing, part E (2026-08-12): the denominator, census-weighted.

   Parts C/D size the RepWL tier internally: census-weighted over
   tools/repwl_residue_caught.tsv, diverging close is ~62% of the
   tier's time.  Turning that into a share of the WALK needs the walk's
   own total in the same units, and converting through the doc's
   native figure (421 core-min) times the measured vm/native 2.53x
   spreads the answer by 2x.

   ProbeTierCost exists for exactly this: its grp_* are sampled from
   the C mirror's classification of all 3,995,005 nodes, so timing the
   real decider on each group and weighting by the census tier counts
   gives the walk's decided-tier cost in the same vm seconds as parts
   C/D -- no cross-machine, cross-round conversion anywhere.

   Census tier counts (docs/CENSUS_RUNTIME.md, tools/census_ladder.c):
     T translated cycle  2,282,976
     C in-place cycle    1,029,749
     N n-gram              200,064
     H halt                249,692
     residue + deferred    232,523

   Per-row arithmetic (time / count = per machine) is written out in
   the notes, per the rule this document adopted after a 62-second row
   was recorded as ~0.

   Untrusted probe: not in _CoqProject, loads into no proof. *)

From Coq Require Import Arith Bool List.
From BBB4 Require Import BBB4_Statement ProbeWalkCommon ProbeTierCost.
From BBB4.Census Require Import TNF_QH Decide.
Import ListNotations.

Definition run (l : list TM) : nat :=
  List.length (filter decided (map decider0 l)).

(* group sizes, so each row's per-machine cost can be divided out *)
Eval vm_compute in (List.length grp_H, List.length grp_C,
                    List.length grp_T, List.length grp_D).
Eval vm_compute in (List.length grp_N2, List.length grp_N3,
                    List.length grp_N4, List.length grp_N6).
Eval vm_compute in List.length grp_RES.

(* warm-up, not a measurement *)
Time Eval vm_compute in run (firstn 1 grp_C).

Time Eval vm_compute in run grp_H.
Time Eval vm_compute in run grp_C.
Time Eval vm_compute in run grp_T.
Time Eval vm_compute in run grp_N2.
Time Eval vm_compute in run grp_N3.
Time Eval vm_compute in run grp_N4.
Time Eval vm_compute in run grp_N6.
Time Eval vm_compute in run grp_RES.
Time Eval vm_compute in run grp_D.
