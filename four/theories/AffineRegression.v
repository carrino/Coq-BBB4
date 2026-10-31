(** Carrier and rejection checks for the four-symbol affine port. *)
From Coq Require Import NArith ZArith List.
From BBB24 Require Import Statement StatementTr IRuleCensus AffineExamples.
From BBB24.Checkers.IRules Require Import AnchorVisits AnchorVisitsTr
 EngineK MetaBlk MetaBlkPfx.
Import ListNotations.
Open Scope Z_scope.

Example fourth_symbol_mask :
  tvm_get (tvm_add tvm_empty (StB,S3)) (StB,S3) = true /\
  tvm_get (tvm_add tvm_empty (StB,S3)) (StA,S3) = false /\
  tvm_get (tvm_add tvm_empty (StB,S3)) (StB,S2) = false.
Proof. repeat split; reflexivity. Qed.

Example raw_symbols_cannot_be_overridden :
  mk_tbl [(3%nat,[S0]); (4%nat,[S2;S3])] 3%nat = [S3] /\
  mk_tbl [(3%nat,[S0]); (4%nat,[S2;S3])] 4%nat = [S2;S3].
Proof. split; reflexivity. Qed.

Definition wrong_anchor : BIRCertP :=
  let c := cert_0LB1LB2RA0RB_3RA3RB1LA2LB in
  mkBIRCertP 0 (cp_k0 c) (cp_kmin c) (cp_a c) (cp_b c)
    (cp_st c) (cp_hs c) (cp_blks c) (cp_TL c) (cp_TR c) (cp_rules c).

Example reject_wrong_anchor :
  ir_check 4096%N 4096%N tm_0LB1LB2RA0RB_3RA3RB1LA2LB
    wrong_anchor 200000 300000 = false.
Proof. vm_compute. reflexivity. Qed.

Example reject_insufficient_prefix_bound :
  ir_check 0%N 0%N tm_0LB1LB2RA0RB_3RA3RB1LA2LB
    cert_0LB1LB2RA0RB_3RA3RB1LA2LB 200000 300000 = false.
Proof. vm_compute. reflexivity. Qed.

Example reject_no_replay_fuel :
  ir_check 4096%N 4096%N tm_0LB2RA3RB2LA_1RA2RA3LB2RB
    cert_0LB2RA3RB2LA_1RA2RA3LB2RB 0 0 = false.
Proof. vm_compute. reflexivity. Qed.
