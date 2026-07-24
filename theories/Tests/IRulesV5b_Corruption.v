(** Negative controls for the gap-2 cell re-blocking extension
    ([Reblock.breblock_side] / [MetaBlkPfxV5b.irulesblkpfx_check_neverqh_v5b])
    -- the ONE new trust surface of the v5-gap gap-2 boards
    (theories/Machines/ListCV5Stage/LCV5B_NN).

    All [vm_compute]-closed:

    1. The re-block is LOAD-BEARING: the gap-2 donor
       (1RB0LB_0LB0RC_1LD1RC_1LA0RD, boarded as LCV5B_00.v
       [nqh_v5b_00000]) is ACCEPTED by the v5b checker but REFUSED by the
       landed [MetaBlkPfxV5.irulesblkpfx_check_neverqh_v5] (no re-block):
       without re-encoding the near-head cells, its rule validation /
       meta replay stalls.
    2. Every single-field cert mutation is REJECTED (block cells, meta
       map).  The re-block only re-encodes cells the certificate's block
       table declares; a mutated block table denotes a different tape and
       the [bstreams_eq]-guarded [breblock_side] cannot paper over it.
    3. A first-step halter and a mutant machine under the genuine cert
       are REJECTED (the anchor re-simulation / coverage stay
       load-bearing under the re-blocking replay).

    Fuel 3000 (as in IRulesBlkPfxBatch_Corruption / IRulesV5_Corruption):
    the honest cycle closes and mutants fail at the SAME fuel. *)

From Coq Require Import ZArith List Bool.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta RulesK
     EngineK RulesBlk MetaBlk EngineKS RulesBlkPfx MetaBlkPfx StreamEq
     MetaBlkPfxV5 Reblock MetaBlkPfxV5b.
Import ListNotations.
Open Scope Z_scope.
Definition mkc (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

Definition tmb : TM := fun q s =>
  match q, s with
  | StA, S0 => mkc S1 DR StB
  | StA, S1 => mkc S0 DL StB
  | StB, S0 => mkc S0 DL StB
  | StB, S1 => mkc S0 DR StC
  | StC, S0 => mkc S1 DL StD
  | StC, S1 => mkc S1 DR StC
  | StD, S0 => mkc S1 DL StA
  | StD, S1 => mkc S0 DR StD
  end.

Definition certb : BIRCertP := mkBIRCertP
  198293%nat (107) (6) (1) (1) StA S0
  [(2%nat, [S1; S0; S0; S0; S0; S1]);
   (3%nat, [S0; S0; S1; S1; S0; S0]);
   (4%nat, [S1; S1; S0; S0; S0; S0]);
   (5%nat, [S0; S0; S0; S0; S1; S1]);
   (6%nat, [S0; S1; S1; S0; S0; S0])]
  []
  [(1%nat, (0), (2)); (3%nat, (1), (0)); (0%nat, (0), (2)); (1%nat, (0), (2))]
  [mkBRuleP StA S0 [(5%nat, BV (1) (1)); (0%nat, BC (2)); (1%nat, BC (1))] [(1%nat, BC (3)); (0%nat, BC (2)); (3%nat, BV (-1) (2)); (0%nat, BC (2)); (1%nat, BC (2))] (true, true)].

(** ** 1. The re-block is load-bearing *)

(** Honest control: the v5b (re-blocking) checker ACCEPTS the donor. *)
Example honest_v5b :
  irulesblkpfx_check_neverqh_v5b tmb certb 200000 3000 = true.
Proof. vm_compute. reflexivity. Qed.

(** The landed v5 checker (no re-block) REFUSES the SAME machine+cert:
    without re-encoding the near-head cells into the block a rule
    expects, the replay stalls.  The re-block is doing real work. *)
Example v5_refuses_donor :
  irulesblkpfx_check_neverqh_v5 tmb certb 200000 3000 = false.
Proof. vm_compute. reflexivity. Qed.

(** ** 2. Cert mutations rejected *)

(** Block 5's cells [S0;S0;S0;S0;S1;S1] -> [S0;S0;S0;S0;S1;S0]: the block
    the drain rule works over denotes a different tape; the re-block
    candidate can no longer be [bstreams_eq]-verified into place and the
    cycle cannot close.  MUST be rejected. *)
Definition certb_blk : BIRCertP := mkBIRCertP
  198293%nat (107) (6) (1) (1) StA S0
  [(2%nat, [S1; S0; S0; S0; S0; S1]);
   (3%nat, [S0; S0; S1; S1; S0; S0]);
   (4%nat, [S1; S1; S0; S0; S0; S0]);
   (5%nat, [S0; S0; S0; S0; S1; S0]);
   (6%nat, [S0; S1; S1; S0; S0; S0])]
  []
  [(1%nat, (0), (2)); (3%nat, (1), (0)); (0%nat, (0), (2)); (1%nat, (0), (2))]
  [mkBRuleP StA S0 [(5%nat, BV (1) (1)); (0%nat, BC (2)); (1%nat, BC (1))] [(1%nat, BC (3)); (0%nat, BC (2)); (3%nat, BV (-1) (2)); (0%nat, BC (2)); (1%nat, BC (2))] (true, true)].

Example corrupt_v5b_blk :
  irulesblkpfx_check_neverqh_v5b tmb certb_blk 200000 3000 = false.
Proof. vm_compute. reflexivity. Qed.

(** Meta map a: 1 -> 2 (preconditions still hold): the shifted
    want-template is wrong; no reachable configuration matches.  MUST be
    rejected. *)
Definition certb_meta : BIRCertP := mkBIRCertP
  198293%nat (107) (6) (2) (1) StA S0
  [(2%nat, [S1; S0; S0; S0; S0; S1]);
   (3%nat, [S0; S0; S1; S1; S0; S0]);
   (4%nat, [S1; S1; S0; S0; S0; S0]);
   (5%nat, [S0; S0; S0; S0; S1; S1]);
   (6%nat, [S0; S1; S1; S0; S0; S0])]
  []
  [(1%nat, (0), (2)); (3%nat, (1), (0)); (0%nat, (0), (2)); (1%nat, (0), (2))]
  [mkBRuleP StA S0 [(5%nat, BV (1) (1)); (0%nat, BC (2)); (1%nat, BC (1))] [(1%nat, BC (3)); (0%nat, BC (2)); (3%nat, BV (-1) (2)); (0%nat, BC (2)); (1%nat, BC (2))] (true, true)].

Example corrupt_v5b_meta :
  irulesblkpfx_check_neverqh_v5b tmb certb_meta 200000 3000 = false.
Proof. vm_compute. reflexivity. Qed.

(** ** 3. Halter and mutant machine under the genuine cert *)

Definition tmb_halt : TM := fun q s =>
  match q, s with
  | StA, S0 => None
  | StA, S1 => mkc S0 DL StB
  | StB, S0 => mkc S0 DL StB
  | StB, S1 => mkc S0 DR StC
  | StC, S0 => mkc S1 DL StD
  | StC, S1 => mkc S1 DR StC
  | StD, S0 => mkc S1 DL StA
  | StD, S1 => mkc S0 DR StD
  end.

Example corrupt_v5b_halter :
  irulesblkpfx_check_neverqh_v5b tmb_halt certb 200000 3000 = false.
Proof. vm_compute. reflexivity. Qed.

Definition tmb_mut : TM := fun q s =>
  match q, s with
  | StA, S0 => mkc S1 DR StB
  | StA, S1 => mkc S0 DL StB
  | StB, S0 => mkc S0 DL StB
  | StB, S1 => mkc S0 DR StC
  | StC, S0 => mkc S1 DL StD
  | StC, S1 => mkc S1 DR StC
  | StD, S0 => mkc S1 DL StA
  | StD, S1 => mkc S1 DR StD
  end.

Example corrupt_v5b_machine :
  irulesblkpfx_check_neverqh_v5b tmb_mut certb 200000 3000 = false.
Proof. vm_compute. reflexivity. Qed.
