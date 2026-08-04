(** Per-tier cost probe for the census pipeline (vm_compute).
    Mirrors Run.v's decider parameters exactly, with EMPTY lookup maps
    so holdout-class machines show the full ladder burn. *)

From Coq Require Import Arith Bool List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import NGram.
From BBB4.Census Require Import TNF_QH Decide RankSearch RepWLSearch.
From BBB4.Checkers Require Import Cycle TCycler NGram.
Import ListNotations.

Definition T (w : Sym) (d : Dir) (n : St) := Some (mkTrans w d n).
Definition mk8 (a0 a1 b0 b1 c0' c1 d0 d1 : option Trans) : TM :=
  fun q s => match q, s with
  | StA, S0 => a0 | StA, S1 => a1 | StB, S0 => b0 | StB, S1 => b1
  | StC, S0 => c0' | StC, S1 => c1 | StD, S0 => d0 | StD, S1 => d1 end.

(* a fast in-place cycler *)
Definition spin0 : TM := mk8 (T S0 DR StA) None None None None None None None.
(* a fast translated cycler *)
Definition run1 : TM := mk8 (T S1 DR StA) None None None None None None None.
(* holdout #1 from tools/BBB4_holdouts_3713.txt: 1RB1LA_1LC0RA_1LD0LD_0RB0LC *)
Definition hold1 : TM :=
  mk8 (T S1 DR StB) (T S1 DL StA)
      (T S1 DL StC) (T S0 DR StA)
      (T S1 DL StD) (T S0 DL StD)
      (T S0 DR StB) (T S0 DL StC).
(* the champion 1RB1LD_1RC1RB_1LC1LA_0RC0RD (quasihalts at 32.7M: every
   in-walk tier fails; deferred in the real walk) *)
Definition champ : TM :=
  mk8 (T S1 DR StB) (T S1 DL StD)
      (T S1 DR StC) (T S1 DR StB)
      (T S1 DL StC) (T S1 DL StA)
      (T S0 DR StC) (T S0 DR StD).

(* Run.v parameters, verbatim *)
Definition Bc : nat := 2000.
Definition ngr : list (nat * nat) := [(2,100);(3,200);(4,400);(6,800)].
Definition rkr : list (nat * nat) := [(3,0);(3,64);(3,256);(3,1024)].
Definition qhr : list (nat * nat) :=
  [(2,64);(2,256);(2,1024);(3,64);(3,256);(3,1024);(4,64);(4,256);(4,1024)].
Definition rwr : list (nat * nat * nat) := [(2,2,0);(3,2,0);(4,2,0);(2,3,0)].

Definition em : DeferredMap := dmap_of [].
Definition decider0 : TM -> QHResult :=
  decide_easy Bc 130 512 200000 512 ngr rkr qhr rwr 8192 em em em (hmap_of []).

(* ---- tier-by-tier on the holdout (the residue-class cost) ---- *)
Time Eval vm_compute in (find_halt hold1 130 0 c0).             (* tier H *)
Time Eval vm_compute in (scan_cycle hold1 512).                 (* tier C scan *)
Time Eval vm_compute in (scan_records hold1 512).               (* tier T scan *)
Time Eval vm_compute in (ngram_check_neverqh hold1 2 100 200000 512).
Time Eval vm_compute in (ngram_check_neverqh hold1 3 200 200000 512).
Time Eval vm_compute in (ngram_check_neverqh hold1 4 400 200000 512).
Time Eval vm_compute in (ngram_check_neverqh hold1 6 800 200000 512).
Time Eval vm_compute in (rank_tier hold1 3 0 200000 512).
Time Eval vm_compute in (rank_tier hold1 3 64 200000 512).
Time Eval vm_compute in (rank_tier hold1 3 1024 200000 512).
(* the whole pipeline on residue-class machines *)
Time Eval vm_compute in (decider0 hold1).
Time Eval vm_compute in (decider0 champ).

(* ---- the bulk classes ---- *)
Time Eval vm_compute in (decider0 spin0).   (* in-place cycle *)
Time Eval vm_compute in (decider0 run1).    (* translated cycle *)

(* verified re-check costs on the cheap classes *)
Time Eval vm_compute in (cycle_leaf_check spin0 0 1).
Time Eval vm_compute in (tcycler_leaf_check run1 1 1 0).
