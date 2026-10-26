(** The two rotor-sweep families among the remaining (2,3) instruction cases.
    Each certificate proves an exact symbolic loop, including all instruction
    visits. The C searcher's inferred data is rechecked by [ir_check_sound]. *)
From Coq Require Import List ZArith.
From SmallBB Require Import Statement StatementTr Size Bounds IRuleCensus.
From SmallBB.Checkers.IRules Require Import Expr RLE Engine Rules RulesK EngineK RulesBlk MetaBlk EngineKS RulesBlkPfx MetaBlkPfx.
Import ListNotations.
Open Scope Z_scope.
Definition repb_tm0:TM:=machine_of_codes 2 3 [5%nat;10%nat;4%nat;6%nat;8%nat;9%nat].
Definition repb_cert0:BIRCertP:=mkBIRCertP 34%nat (3) (1) (8) (11) StA S0 [] [] [(2%nat, (2), (1)); (1%nat, (0), (1))] [mkBRuleP StB S0 [] [(1%nat, BV (4) (1)); (2%nat, BV (-2) (3)); (1%nat, BC (1))] (false, true)].
Lemma repb_checked0 : ir_check 59 67 repb_tm0 repb_cert0 1024 1024 = true.
Proof. native_compute. reflexivity. Qed.
Lemma repb_sound0 : NonHalt repb_tm0 /\ Bounds 59 67 repb_tm0.
Proof. exact (ir_check_sound 59 67 repb_tm0 repb_cert0 1024 1024 repb_checked0). Qed.
Lemma repb_instruction_bound0 : QHBoundTr 67 repb_tm0.
Proof. exact (proj2 (proj2 repb_sound0)). Qed.
Print Assumptions repb_instruction_bound0.
Definition repb_tm1:TM:=machine_of_codes 2 3 [5%nat;10%nat;4%nat;6%nat;10%nat;9%nat].
Definition repb_cert1:BIRCertP:=mkBIRCertP 14%nat (2) (2) (8) (6) StA S0 [] [(2%nat, (2), (0)); (1%nat, (0), (1))] [] [mkBRuleP StA S2 [(2%nat, BV (4) (1))] [(2%nat, BV (-2) (3)); (1%nat, BC (1))] (false, true)].
Lemma repb_checked1 : ir_check 59 67 repb_tm1 repb_cert1 1024 1024 = true.
Proof. native_compute. reflexivity. Qed.
Lemma repb_sound1 : NonHalt repb_tm1 /\ Bounds 59 67 repb_tm1.
Proof. exact (ir_check_sound 59 67 repb_tm1 repb_cert1 1024 1024 repb_checked1). Qed.
Lemma repb_instruction_bound1 : QHBoundTr 67 repb_tm1.
Proof. exact (proj2 (proj2 repb_sound1)). Qed.
Print Assumptions repb_instruction_bound1.
