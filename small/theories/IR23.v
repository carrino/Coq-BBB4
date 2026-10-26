From Coq Require Import List ZArith.
From SmallBB Require Import Statement StatementTr Size Bounds IRuleCensus.
From SmallBB.Checkers.IRules Require Import Expr RLE Engine Rules RulesK EngineK RulesBlk MetaBlk EngineKS RulesBlkPfx MetaBlkPfx.
Import ListNotations.
Open Scope Z_scope.
Definition ir23_entries : list (list nat * BIRCertP) := [
([5%nat;3%nat;6%nat;11%nat;10%nat;0%nat], mkBIRCertP 19822%nat (52) (5) (1) (1) StA S0 [(3%nat, [S0; S1]);
   (4%nat, [S1; S0]);
   (5%nat, [S0; S2]);
   (6%nat, [S2; S0])] [(6%nat, (2), (1)); (2%nat, (0), (1))] [] [mkBRuleP StB S1 [(6%nat, BV (2) (2)); (2%nat, BC (1))] [(0%nat, BC (1)); (4%nat, BV (-2) (3)); (1%nat, BC (1))] (true, true)]);
([5%nat;5%nat;6%nat;7%nat;9%nat;2%nat], mkBIRCertP 19074%nat (47) (2) (1) (2) StA S0 [] [(1%nat, (1), (0)); (0%nat, (0), (1)); (1%nat, (0), (1))] [] [mkBRuleP StB S0 [(1%nat, BV (1) (1))] [(2%nat, BV (-1) (2)); (1%nat, BC (1))] (true, true)]);
([5%nat;6%nat;3%nat;6%nat;9%nat;0%nat], mkBIRCertP 19723%nat (57) (9) (1) (1) StB S0 [(3%nat, [S2; S1; S0]);
   (4%nat, [S1; S1; S0]);
   (5%nat, [S1; S0; S2]);
   (6%nat, [S1; S0; S1])] [] [(3%nat, (1), (0)); (1%nat, (0), (1))] [mkBRuleP StB S2 [(0%nat, BC (1)); (1%nat, BC (2)); (6%nat, BV (-1) (2)); (1%nat, BC (1))] [(3%nat, BV (1) (1)); (1%nat, BC (1))] (true, true)]);
([7%nat;1%nat;4%nat;9%nat;8%nat;2%nat], mkBIRCertP 19822%nat (52) (5) (1) (1) StA S0 [(3%nat, [S0; S1]);
   (4%nat, [S1; S0]);
   (5%nat, [S0; S2]);
   (6%nat, [S2; S0])] [] [(6%nat, (2), (1)); (2%nat, (0), (1))] [mkBRuleP StB S1 [(0%nat, BC (1)); (4%nat, BV (-2) (3)); (1%nat, BC (1))] [(6%nat, BV (2) (2)); (2%nat, BC (1))] (true, true)]);
([7%nat;4%nat;1%nat;4%nat;11%nat;2%nat], mkBIRCertP 19723%nat (57) (9) (1) (1) StB S0 [(3%nat, [S2; S1; S0]);
   (4%nat, [S1; S1; S0]);
   (5%nat, [S1; S0; S2]);
   (6%nat, [S1; S0; S1])] [(3%nat, (1), (0)); (1%nat, (0), (1))] [] [mkBRuleP StB S2 [(3%nat, BV (1) (1)); (1%nat, BC (1))] [(0%nat, BC (1)); (1%nat, BC (2)); (6%nat, BV (-1) (2)); (1%nat, BC (1))] (true, true)]);
([7%nat;7%nat;4%nat;5%nat;11%nat;0%nat], mkBIRCertP 19074%nat (47) (2) (1) (2) StA S0 [] [] [(1%nat, (1), (0)); (0%nat, (0), (1)); (1%nat, (0), (1))] [mkBRuleP StB S0 [(2%nat, BV (-1) (2)); (1%nat, BC (1))] [(1%nat, BV (1) (1))] (true, true)]);
([9%nat;3%nat;10%nat;10%nat;0%nat;5%nat], mkBIRCertP 19723%nat (57) (9) (1) (1) StB S0 [(3%nat, [S1; S2; S0]);
   (4%nat, [S2; S2; S0]);
   (5%nat, [S2; S0; S1]);
   (6%nat, [S2; S0; S2])] [] [(3%nat, (1), (0)); (2%nat, (0), (1))] [mkBRuleP StB S1 [(0%nat, BC (1)); (2%nat, BC (2)); (6%nat, BV (-1) (2)); (2%nat, BC (1))] [(3%nat, BV (1) (1)); (2%nat, BC (1))] (true, true)]);
([9%nat;10%nat;3%nat;7%nat;0%nat;6%nat], mkBIRCertP 19822%nat (52) (5) (1) (1) StA S0 [(3%nat, [S0; S2]);
   (4%nat, [S2; S0]);
   (5%nat, [S0; S1]);
   (6%nat, [S1; S0])] [(6%nat, (2), (1)); (1%nat, (0), (1))] [] [mkBRuleP StB S2 [(6%nat, BV (2) (2)); (1%nat, BC (1))] [(0%nat, BC (1)); (4%nat, BV (-2) (3)); (2%nat, BC (1))] (true, true)]);
([9%nat;10%nat;9%nat;11%nat;2%nat;5%nat], mkBIRCertP 19074%nat (47) (2) (1) (2) StA S0 [] [(2%nat, (1), (0)); (0%nat, (0), (1)); (2%nat, (0), (1))] [] [mkBRuleP StB S0 [(2%nat, BV (1) (1))] [(1%nat, BV (-1) (2)); (2%nat, BC (1))] (true, true)]);
([11%nat;1%nat;8%nat;8%nat;2%nat;7%nat], mkBIRCertP 19723%nat (57) (9) (1) (1) StB S0 [(3%nat, [S1; S2; S0]);
   (4%nat, [S2; S2; S0]);
   (5%nat, [S2; S0; S1]);
   (6%nat, [S2; S0; S2])] [(3%nat, (1), (0)); (2%nat, (0), (1))] [] [mkBRuleP StB S1 [(3%nat, BV (1) (1)); (2%nat, BC (1))] [(0%nat, BC (1)); (2%nat, BC (2)); (6%nat, BV (-1) (2)); (2%nat, BC (1))] (true, true)]);
([11%nat;8%nat;1%nat;5%nat;2%nat;4%nat], mkBIRCertP 19822%nat (52) (5) (1) (1) StA S0 [(3%nat, [S0; S2]);
   (4%nat, [S2; S0]);
   (5%nat, [S0; S1]);
   (6%nat, [S1; S0])] [] [(6%nat, (2), (1)); (1%nat, (0), (1))] [mkBRuleP StB S2 [(0%nat, BC (1)); (4%nat, BV (-2) (3)); (2%nat, BC (1))] [(6%nat, BV (2) (2)); (1%nat, BC (1))] (true, true)]);
([11%nat;8%nat;11%nat;9%nat;0%nat;7%nat], mkBIRCertP 19074%nat (47) (2) (1) (2) StA S0 [] [] [(2%nat, (1), (0)); (0%nat, (0), (1)); (2%nat, (0), (1))] [mkBRuleP StB S0 [(1%nat, BV (-1) (2)); (2%nat, BC (1))] [(2%nat, BV (1) (1))] (true, true)])].
Lemma ir23_checked:forallb(fun x=>ir_check 59 67 (machine_of_codes 2 3 (fst x))(snd x) 200000 300000)ir23_entries=true.
Proof. native_compute. reflexivity. Qed.
Lemma ir23_nth:forall i xs cert,nth_error ir23_entries i=Some(xs,cert)->NonHalt(machine_of_codes 2 3 xs) /\ Bounds 59 67(machine_of_codes 2 3 xs).
Proof.
 intros i xs cert H. pose proof(nth_error_In ir23_entries i H)as Hin.
 pose proof ir23_checked as HC;rewrite forallb_forall in HC.
 apply(ir_check_sound 59 67 (machine_of_codes 2 3 xs)cert 200000 300000);exact(HC(xs,cert)Hin).
Qed.
