(** The two parity-sensitive A1 recurrence families.

    The meta-cycles preserve the even run-length phase and use a single
    decrement-by-two rule. Their early concrete anchors are checked along
    with every rule and the instruction coverage of the whole meta-cycle.

    Certificates were discovered by the untrusted C irules searcher with
    three-sample fitting (including every-other-sample fits). The usual
    five-sample search missed these rarely recurring anchors. *)
From Coq Require Import List ZArith.
From SmallBB Require Import Statement StatementTr Size Bounds IRuleCensus.
From SmallBB.Checkers.IRules Require Import Expr RLE Engine Rules RulesK
  EngineK RulesBlk MetaBlk EngineKS RulesBlkPfx MetaBlkPfx.
Import ListNotations.
Open Scope Z_scope.

(** 1LB2LB2RA_1RA2LB1RB: B0 with right tape 2^(2k)1,
    from k = 6 at step 100, with k -> 8k + 6. *)
Definition repA0_tm : TM :=
  machine_of_codes 2 3 [5%nat;9%nat;10%nat;6%nat;9%nat;7%nat].
Definition repA0_cert : BIRCertP :=
  mkBIRCertP 100 6 2 8 6 StB S0 [] [] [(2%nat,2,0);(1%nat,0,1)]
    [mkBRuleP StB S2 [(2%nat,BV (-2) 3);(1%nat,BC 1)]
       [(2%nat,BV 4 1)] (true,false)].
Lemma repA0_checked : ir_check 59 67 repA0_tm repA0_cert 1024 1024 = true.
Proof. native_compute. reflexivity. Qed.
Theorem repA0_bounds : NonHalt repA0_tm /\ Bounds 59 67 repA0_tm.
Proof. exact (ir_check_sound 59 67 repA0_tm repA0_cert 1024 1024 repA0_checked). Qed.

(** 1LB2RB2RA_1RA2LB1RB: B0 with left tape 2^(2k)1,
    from k = 5 at step 70, with k -> 8k + 9. *)
Definition repA6_tm : TM :=
  machine_of_codes 2 3 [5%nat;11%nat;10%nat;6%nat;9%nat;7%nat].
Definition repA6_cert : BIRCertP :=
  mkBIRCertP 70 5 2 8 9 StB S0 [] [(2%nat,2,0);(1%nat,0,1)] []
    [mkBRuleP StA S0 [(1%nat,BV 4 1);(2%nat,BV (-2) 3);(1%nat,BC 1)]
       [] (true,false)].
Lemma repA6_checked : ir_check 59 67 repA6_tm repA6_cert 1024 1024 = true.
Proof. native_compute. reflexivity. Qed.
Theorem repA6_bounds : NonHalt repA6_tm /\ Bounds 59 67 repA6_tm.
Proof. exact (ir_check_sound 59 67 repA6_tm repA6_cert 1024 1024 repA6_checked). Qed.

Print Assumptions repA0_bounds.
Print Assumptions repA6_bounds.
