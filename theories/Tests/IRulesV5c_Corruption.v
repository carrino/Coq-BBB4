(** Negative controls for the gap-3 engine extension
    ([BlkClosure.blk_closure] + [StreamEq2.cseq2] /
    [MetaBlkPfxV5c.irulesblkpfx_check_neverqh_v5c]) -- the new trust
    surface of the v5-gap gap-3 boards
    (theories/Machines/ListCV5Stage/LCV5C_NN).

    All [vm_compute]-closed:

    1. [cseq2] (the new cell-stream equality) ACCEPTS a genuine
       two-variable-run cell-equal pair that the landed one-pump [cseq]
       REFUSES, and REJECTS a single-cell mutation of it.
    2. The closure + [cseq2] are LOAD-BEARING: the gap-3 donor
       (1RB0LC_0LB1RC_1RD1LA_1LA0RC, boarded as LCV5C_00.v) is ACCEPTED
       by the v5c checker but REFUSED by the landed v5b checker (which
       has neither the block-hop closure nor the multi-run end-match).
    3. Every single-field cert mutation is REJECTED (block cells, meta
       map): the closure re-verifies each hop against [mk_tbl blks] and
       [cseq2] reduces to the denotation-preserving [cseq], so a mutated
       block table (a different tape) cannot be papered over.
    4. A first-step halter and a mutant machine under the genuine cert
       are REJECTED (anchor re-simulation / coverage stay load-bearing).

    The [cseq2] unit checks use fuel-free [vm_compute]; the checker
    controls use fuel 3000 (the honest meta cycle closes in ~137
    iterations and every mutant fails at the SAME fuel). *)

From Coq Require Import ZArith List Bool.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta RulesK
     EngineK RulesBlk MetaBlk EngineKS RulesBlkPfx MetaBlkPfx StreamEq
     MetaBlkPfxV5 Reblock MetaBlkPfxV5b BlkClosure StreamEq2 MetaBlkPfxV5c.
Import ListNotations.
Open Scope Z_scope.
Definition mkc (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** ** 1. The new cell-stream equality [cseq2] *)

(** Two sides, each with TWO variable-count runs, denoting the same
    cells [S1^(k+1) . S0 . S1^(k+1)]: *)
Definition xa : list BRun :=
  [(1%nat, mkExpr 1 [1]); (0%nat, econst 1); (1%nat, mkExpr 1 [1])].
Definition xb : list BRun :=
  [(1%nat, mkExpr 0 [1]); (1%nat, econst 1); (0%nat, econst 1);
   (1%nat, mkExpr 1 [1])].
(** ... and a single-cell mutation of [xb] (the middle [S1] -> [S0]): *)
Definition xb_mut : list BRun :=
  [(1%nat, mkExpr 0 [1]); (0%nat, econst 1); (0%nat, econst 1);
   (1%nat, mkExpr 1 [1])].

(** The landed one-pump [cseq] REFUSES the two-pump pair (exp1 fails). *)
Example cseq_refuses_two_pump :
  cseq (mk_tbl []) [0] xa xb = false.
Proof. vm_compute. reflexivity. Qed.

(** [cseq2] ACCEPTS the genuine cell-equal pair. *)
Example cseq2_accepts_genuine :
  cseq2 (mk_tbl []) [0] xa xb = true.
Proof. vm_compute. reflexivity. Qed.

(** [cseq2] REJECTS the mutated (non-cell-equal) pair. *)
Example cseq2_rejects_mutant :
  cseq2 (mk_tbl []) [0] xa xb_mut = false.
Proof. vm_compute. reflexivity. Qed.

(** ** The gap-3 donor machine + certificate *)

Definition tmc : TM := fun q s =>
  match q, s with
  | StA, S0 => mkc S1 DR StB
  | StA, S1 => mkc S0 DL StC
  | StB, S0 => mkc S0 DL StB
  | StB, S1 => mkc S1 DR StC
  | StC, S0 => mkc S1 DR StD
  | StC, S1 => mkc S1 DL StA
  | StD, S0 => mkc S1 DL StA
  | StD, S1 => mkc S0 DR StC
  end.

Definition certc : BIRCertP := mkBIRCertP
  199194%nat (117) (6) (1) (1) StD S0
  [(2%nat, [S1; S1; S1; S1; S1; S1; S0; S1]);
   (3%nat, [S1; S1; S1; S1; S1; S1; S1; S0]);
   (4%nat, [S1; S1; S1; S1; S0; S1; S1; S1]);
   (5%nat, [S1; S0; S1; S1; S1]);
   (6%nat, [S0; S1; S1; S1; S1]);
   (7%nat, [S1; S0; S1; S0; S1]);
   (8%nat, [S1; S1; S1; S0; S1]);
   (9%nat, [S1; S0; S1; S1; S0]);
   (10%nat, [S1; S1; S1; S1; S0])]
  [(1%nat, (0), (7)); (6%nat, (1), (0)); (1%nat, (0), (3)); (0%nat, (0), (1)); (1%nat, (3), (-2)); (0%nat, (0), (1)); (1%nat, (0), (3))]
  []
  [mkBRuleP StA S1 [(6%nat, BV (-1) (2)); (1%nat, BC (3)); (0%nat, BC (1)); (1%nat, BV (0) (1)); (0%nat, BC (1)); (1%nat, BC (3))] [(7%nat, BV (1) (1)); (0%nat, BC (1)); (1%nat, BC (1))] (true, true);
   mkBRuleP StC S0 [(8%nat, BV (1) (1)); (0%nat, BC (1)); (1%nat, BC (1)); (0%nat, BC (1)); (1%nat, BV (0) (1)); (0%nat, BC (1)); (1%nat, BC (3))] [(1%nat, BC (1)); (0%nat, BC (1)); (1%nat, BC (1)); (7%nat, BV (-1) (2)); (0%nat, BC (1)); (1%nat, BC (1))] (true, true)].

(** ** 2. The closure + multi-run end-match are load-bearing *)

(** Honest control: the v5c checker ACCEPTS the donor. *)
Example honest_v5c :
  irulesblkpfx_check_neverqh_v5c tmc certc 200000 3000 = true.
Proof. vm_compute. reflexivity. Qed.

(** The landed v5b checker (no closure, no [cseq2]) REFUSES the SAME
    machine+cert: without the closed block table the engine cannot cross
    the rotation block, and without [cseq2] the multi-run end config is
    not recognised.  The gap-3 additions do real work. *)
Example v5b_refuses_donor :
  irulesblkpfx_check_neverqh_v5b tmc certc 200000 3000 = false.
Proof. vm_compute. reflexivity. Qed.

(** ** 3. Cert mutations rejected *)

(** Block 6's cells [S0;S1;S1;S1;S1] -> [S0;S1;S1;S1;S0]: the block a
    rule / hop works over denotes a different tape; the closure's hop
    re-verification and [cseq2]'s denotation cannot close the cycle.
    MUST be rejected. *)
Definition certc_blk : BIRCertP := mkBIRCertP
  199194%nat (117) (6) (1) (1) StD S0
  [(2%nat, [S1; S1; S1; S1; S1; S1; S0; S1]);
   (3%nat, [S1; S1; S1; S1; S1; S1; S1; S0]);
   (4%nat, [S1; S1; S1; S1; S0; S1; S1; S1]);
   (5%nat, [S1; S0; S1; S1; S1]);
   (6%nat, [S0; S1; S1; S1; S0]);
   (7%nat, [S1; S0; S1; S0; S1]);
   (8%nat, [S1; S1; S1; S0; S1]);
   (9%nat, [S1; S0; S1; S1; S0]);
   (10%nat, [S1; S1; S1; S1; S0])]
  [(1%nat, (0), (7)); (6%nat, (1), (0)); (1%nat, (0), (3)); (0%nat, (0), (1)); (1%nat, (3), (-2)); (0%nat, (0), (1)); (1%nat, (0), (3))]
  []
  [mkBRuleP StA S1 [(6%nat, BV (-1) (2)); (1%nat, BC (3)); (0%nat, BC (1)); (1%nat, BV (0) (1)); (0%nat, BC (1)); (1%nat, BC (3))] [(7%nat, BV (1) (1)); (0%nat, BC (1)); (1%nat, BC (1))] (true, true);
   mkBRuleP StC S0 [(8%nat, BV (1) (1)); (0%nat, BC (1)); (1%nat, BC (1)); (0%nat, BC (1)); (1%nat, BV (0) (1)); (0%nat, BC (1)); (1%nat, BC (3))] [(1%nat, BC (1)); (0%nat, BC (1)); (1%nat, BC (1)); (7%nat, BV (-1) (2)); (0%nat, BC (1)); (1%nat, BC (1))] (true, true)].

Example corrupt_v5c_blk :
  irulesblkpfx_check_neverqh_v5c tmc certc_blk 200000 3000 = false.
Proof. vm_compute. reflexivity. Qed.

(** Meta map a: 1 -> 2 (preconditions still hold): the shifted
    want-template is wrong; no reachable configuration matches.  MUST be
    rejected. *)
Definition certc_meta : BIRCertP := mkBIRCertP
  199194%nat (117) (6) (2) (1) StD S0
  [(2%nat, [S1; S1; S1; S1; S1; S1; S0; S1]);
   (3%nat, [S1; S1; S1; S1; S1; S1; S1; S0]);
   (4%nat, [S1; S1; S1; S1; S0; S1; S1; S1]);
   (5%nat, [S1; S0; S1; S1; S1]);
   (6%nat, [S0; S1; S1; S1; S1]);
   (7%nat, [S1; S0; S1; S0; S1]);
   (8%nat, [S1; S1; S1; S0; S1]);
   (9%nat, [S1; S0; S1; S1; S0]);
   (10%nat, [S1; S1; S1; S1; S0])]
  [(1%nat, (0), (7)); (6%nat, (1), (0)); (1%nat, (0), (3)); (0%nat, (0), (1)); (1%nat, (3), (-2)); (0%nat, (0), (1)); (1%nat, (0), (3))]
  []
  [mkBRuleP StA S1 [(6%nat, BV (-1) (2)); (1%nat, BC (3)); (0%nat, BC (1)); (1%nat, BV (0) (1)); (0%nat, BC (1)); (1%nat, BC (3))] [(7%nat, BV (1) (1)); (0%nat, BC (1)); (1%nat, BC (1))] (true, true);
   mkBRuleP StC S0 [(8%nat, BV (1) (1)); (0%nat, BC (1)); (1%nat, BC (1)); (0%nat, BC (1)); (1%nat, BV (0) (1)); (0%nat, BC (1)); (1%nat, BC (3))] [(1%nat, BC (1)); (0%nat, BC (1)); (1%nat, BC (1)); (7%nat, BV (-1) (2)); (0%nat, BC (1)); (1%nat, BC (1))] (true, true)].

Example corrupt_v5c_meta :
  irulesblkpfx_check_neverqh_v5c tmc certc_meta 200000 3000 = false.
Proof. vm_compute. reflexivity. Qed.

(** ** 4. Halter and mutant machine under the genuine cert *)

Definition tmc_halt : TM := fun q s =>
  match q, s with
  | StA, S0 => None
  | StA, S1 => mkc S0 DL StC
  | StB, S0 => mkc S0 DL StB
  | StB, S1 => mkc S1 DR StC
  | StC, S0 => mkc S1 DR StD
  | StC, S1 => mkc S1 DL StA
  | StD, S0 => mkc S1 DL StA
  | StD, S1 => mkc S0 DR StC
  end.

Example corrupt_v5c_halter :
  irulesblkpfx_check_neverqh_v5c tmc_halt certc 200000 3000 = false.
Proof. vm_compute. reflexivity. Qed.

Definition tmc_mut : TM := fun q s =>
  match q, s with
  | StA, S0 => mkc S1 DR StB
  | StA, S1 => mkc S0 DL StC
  | StB, S0 => mkc S0 DL StB
  | StB, S1 => mkc S1 DR StC
  | StC, S0 => mkc S1 DR StD
  | StC, S1 => mkc S1 DL StA
  | StD, S0 => mkc S1 DL StA
  | StD, S1 => mkc S1 DR StC
  end.

Example corrupt_v5c_machine :
  irulesblkpfx_check_neverqh_v5c tmc_mut certc 200000 3000 = false.
Proof. vm_compute. reflexivity. Qed.
