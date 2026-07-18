(** Negative controls for the PARTIAL-ABSORB extension of the block
    IRules checker (RulesBlk.babsorb_partial / bpeel_rev).  The machine
    1RB0RD_1LC1LB_1RD0LB_0RD1RA is the only v3-blk holdout whose C
    verification uses a partial (symbolic-remainder) absorb: a single-cell
    run contributes only PART of its cells to complete a block copy.  Its
    honest theorem is in Machines/IRulesBlk_Batch_01.v; here a block-table
    mutant (block 7's cell sequence corrupted) makes the verified checker
    reject at rule validation -- confirming the [bstreams_eq]-gated peel is
    load-bearing and never trusts the untrusted leftover. *)
From Coq Require Import ZArith List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta RulesK
     EngineK RulesBlk MetaBlk.
Import ListNotations.
Open Scope Z_scope.
Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

Definition tm_pa : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB
  | StA, S1 => mk S0 DR StD
  | StB, S0 => mk S1 DL StC
  | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S1 DR StD
  | StC, S1 => mk S0 DL StB
  | StD, S0 => mk S0 DR StD
  | StD, S1 => mk S1 DR StA
  end.
Definition blks_bad7 :=
  [(2%nat, [S1; S0; S1; S0; S1; S0; S1; S1]);
   (3%nat, [S0; S1; S0; S1; S0; S1; S1; S1]);
   (4%nat, [S0; S1]);
   (5%nat, [S0; S1; S1; S1]);
   (6%nat, [S1; S1; S1; S0; S1; S1; S1]);
   (7%nat, [S1; S0; S1; S1; S0]);
   (8%nat, [S1; S0; S1; S1; S1; S1; S1]);
   (9%nat, [S0; S1; S1; S1; S1; S1; S1]);
   (10%nat, [S0; S1; S0; S1; S0; S1; S0]);
   (11%nat, [S1; S1; S1; S1; S1; S0; S1]);
   (12%nat, [S1; S0; S0; S1; S0; S1; S0]);
   (13%nat, [S1; S0]);
   (14%nat, [S1; S1; S1; S1; S1; S1; S0])].
Definition cert_pa_badblk : BIRCert := mkBIRCert
  9999528%nat (572) (6) (1) (2) StC S0
  blks_bad7
  []
  [(1%nat, (0), (2)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (14)); (9%nat, (1), (0)); (1%nat, (0), (5)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (7%nat, (1), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (3)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (5)); (0%nat, (0), (1)); (1%nat, (0), (1))]
  [mkBRule StB S0 [(1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (10%nat, RV (-1) (2)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (2)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (4))] [(11%nat, RV (1) (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (4)); (0%nat, RC (1)); (7%nat, RV (0) (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (3)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (5)); (0%nat, RC (1)); (1%nat, RC (1))];
   mkBRule StB S0 [(1%nat, RC (1)); (0%nat, RC (1)); (12%nat, RV (-1) (2)); (1%nat, RC (1)); (0%nat, RC (2)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (3)); (0%nat, RC (1)); (1%nat, RC (3)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (2)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (2))] [(11%nat, RV (1) (1)); (1%nat, RC (2)); (0%nat, RC (1)); (1%nat, RC (3)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (7%nat, RV (0) (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (3)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (5)); (0%nat, RC (1)); (1%nat, RC (1))];
   mkBRule StB S0 [(12%nat, RV (-1) (2)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (2)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (4))] [(9%nat, RV (1) (1)); (1%nat, RC (5)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (7%nat, RV (0) (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (3)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (5)); (0%nat, RC (1)); (1%nat, RC (1))];
   mkBRule StB S0 [(1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (10%nat, RV (-1) (2)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (3)); (0%nat, RC (1)); (1%nat, RC (3)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (2)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (2))] [(11%nat, RV (1) (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (4)); (0%nat, RC (1)); (7%nat, RV (0) (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (3)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (5)); (0%nat, RC (1)); (1%nat, RC (1))];
   mkBRule StB S0 [(1%nat, RC (1)); (0%nat, RC (1)); (12%nat, RV (-1) (2)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (2)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (4))] [(11%nat, RV (1) (1)); (1%nat, RC (2)); (0%nat, RC (1)); (1%nat, RC (3)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (7%nat, RV (0) (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (3)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (5)); (0%nat, RC (1)); (1%nat, RC (1))];
   mkBRule StB S0 [(12%nat, RV (-1) (2)); (1%nat, RC (1)); (0%nat, RC (2)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (3)); (0%nat, RC (1)); (1%nat, RC (3)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (2)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (2))] [(9%nat, RV (1) (1)); (1%nat, RC (5)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (7%nat, RV (0) (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (3)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (1)); (0%nat, RC (1)); (1%nat, RC (5)); (0%nat, RC (1)); (1%nat, RC (1))]].

(* block-7 cells corrupted: the rule replay denotes the wrong tape,
   so validation fails before the anchor re-sim -- checker rejects *)
Example blk_pa_corrupt_blocktable :
  irulesblk_check_neverqh tm_pa cert_pa_badblk 200000 300000 = false.
Proof. vm_compute. reflexivity. Qed.

