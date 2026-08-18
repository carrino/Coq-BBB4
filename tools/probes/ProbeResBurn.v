(* Where do the ~1.6s residue-class pops go?  Ablate one tier's rungs
   at a time: the delta vs the full decider is that tier's burn.
   decide_easy takes the rung lists as arguments, so ablation = [] . *)
From Coq Require Import Arith Bool List.
From BBB4 Require Import BBB4_Statement ProbeWalkCommon ProbeTierCost.
From BBB4.Census Require Import TNF_QH Decide.
Import ListNotations.
Definition F : nat := 200000.
Definition R : nat := 512.
Definition dec (ng rk : list (nat*nat)) (qh : list (nat*nat))
    (rw : list (nat*nat*nat)) : TM -> QHResult :=
(* 999 = cut effectively OFF: this probe predates the M4 node-size
   cut and its recorded numbers are the uncut pipeline's. *)
  decide_easy Bc 130 512 F R ng rk qh rw 8192 999 pmap0 emap dmap0 hmap0.
Definition cnt (d : TM -> QHResult) (l : list TM) : nat :=
  List.length (filter (fun tm => match d tm with R_Unknown => false
                                 | _ => true end) (map (fun x => x) l)).
(* full, then minus one tier each *)
Time Eval vm_compute in cnt (dec ngr rkr qhr rwr) grp_RES.
Time Eval vm_compute in cnt (dec [] rkr qhr rwr) grp_RES.
Time Eval vm_compute in cnt (dec ngr [] qhr rwr) grp_RES.
Time Eval vm_compute in cnt (dec ngr rkr [] rwr) grp_RES.
Time Eval vm_compute in cnt (dec ngr rkr qhr []) grp_RES.
(* and the winning-tier census: which ablation loses catches *)
