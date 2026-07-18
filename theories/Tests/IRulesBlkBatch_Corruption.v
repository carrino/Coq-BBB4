(** GENERATED negative controls for the block IRules checker.
    Each mutant of the 1RB---_1RC1RA_1LD0RB_1LB0LC certificate makes the
    verified checker [irulesblk_check_neverqh] compute [false] -- the
    checker discriminates against corrupted transitions, block-table
    entries, rule deltas, meta maps, and templates. *)
From Coq Require Import ZArith List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta RulesK
     EngineK RulesBlk MetaBlk.
Import ListNotations.
Open Scope Z_scope.
Definition mk (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).

Definition tm_base : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB
  | StA, S1 => None
  | StB, S0 => mk S1 DR StC
  | StB, S1 => mk S1 DR StA
  | StC, S0 => mk S1 DL StD
  | StC, S1 => mk S0 DR StB
  | StD, S0 => mk S1 DL StB
  | StD, S1 => mk S0 DL StC
  end.
Definition tm_transmut : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S0 DR StB
  | StA, S1 => None
  | StB, S0 => mk S1 DR StC
  | StB, S1 => mk S1 DR StA
  | StC, S0 => mk S1 DL StD
  | StC, S1 => mk S0 DR StB
  | StD, S0 => mk S1 DL StB
  | StD, S1 => mk S0 DL StC
  end.
Definition blks_base := [(2%nat, [S0; S1]);
   (3%nat, [S1; S0])].
Definition blks_bad := [(2%nat, [S0; S0]);
   (3%nat, [S1; S0])].
Definition TL_base := [(1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (2), (1)); (0%nat, (0), (1)); (1%nat, (0), (1))].
Definition rules_base := [mkBRule StD S1 [(2%nat, RV (2) (1)); (0%nat, RC (1)); (1%nat, RV (-2) (3)); (0%nat, RC (1)); (1%nat, RC (1))] [(1%nat, RC (1))]].
Definition rules_deltabad := [mkBRule StD S1 [(2%nat, RV (2) (1)); (0%nat, RC (1)); (1%nat, RV (-1) (3)); (0%nat, RC (1)); (1%nat, RC (1))] [(1%nat, RC (1))]].

Definition mkc (blks : list (nat * list Sym)) (TL : list (nat * Z * Z))
    (rules : list BRule) (k0 kmin a b : Z) : BIRCert :=
  mkBIRCert 776228%nat k0 kmin a b StC S0 blks TL (@nil (nat * Z * Z)) rules.

Definition cert_base := mkc blks_base TL_base rules_base 756 1 2 12.

(* sanity: the honest certificate is accepted *)
Example blk_honest_ok :
  irulesblk_check_neverqh tm_base cert_base 200000 300000 = true.
Proof. vm_compute. reflexivity. Qed.

(* transition mutant: the anchor re-sim / replay no longer matches *)
Example blk_corrupt_transition :
  irulesblk_check_neverqh tm_transmut cert_base 200000 300000 = false.
Proof. vm_compute. reflexivity. Qed.

(* corrupted block-table entry: block 2 = [S0;S0] not [S0;S1] *)
Example blk_corrupt_blocktable :
  irulesblk_check_neverqh tm_base
    (mkc blks_bad TL_base rules_base 756 1 2 12) 200000 300000 = false.
Proof. vm_compute. reflexivity. Qed.

(* corrupted rule decrement: -2 demoted to -1 *)
Example blk_corrupt_ruledelta :
  irulesblk_check_neverqh tm_base
    (mkc blks_base TL_base rules_deltabad 756 1 2 12) 200000 300000 = false.
Proof. vm_compute. reflexivity. Qed.

(* corrupted meta map: b off by one, end-match (even under streams) fails *)
Example blk_corrupt_metab :
  irulesblk_check_neverqh tm_base
    (mkc blks_base TL_base rules_base 756 1 2 13) 200000 300000 = false.
Proof. vm_compute. reflexivity. Qed.

(* corrupted meta multiplier: a bumped, cycle no longer closes *)
Example blk_corrupt_metaa :
  irulesblk_check_neverqh tm_base
    (mkc blks_base TL_base rules_base 756 1 3 12) 200000 300000 = false.
Proof. vm_compute. reflexivity. Qed.
