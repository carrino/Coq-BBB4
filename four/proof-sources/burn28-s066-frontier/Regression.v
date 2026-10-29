From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn28S066Frontier Require Import Frontier.
Import ListNotations.
Example s66_reg_original_entry : s66_entrycheck=true.
Proof. exact s66_entry_checked. Qed.
Example s66_reg_both_contexts : forall l r,csteps s66_tm 11(StA,(s66_prefix++l,S0,r))=
 Some(s66_front StA(s66_prefix++S2::l)r).
Proof. exact s66_slide. Qed.
Example s66_reg_repeated_frontier : forall l,csteps s66_tm 77(s66_main l)=
 Some(s66_main(repeat S2 7++l)).
Proof. exact(s66_returns 7). Qed.
Example s66_reg_B_after_one : forall l,csteps s66_tm 1(s66_main l)=Some(s66_Bmain l).
Proof. exact s66_B_after_one. Qed.
Example s66_reg_prefix_guard : csteps s66_tm 11(StA,([S2;S2;S1;S2],S0,[]))<>
 Some(s66_main[S2]).
Proof. vm_compute;discriminate. Qed.
Example s66_reg_rightblank_guard : csteps s66_tm 11(StA,(s66_prefix,S0,[S1]))<>
 Some(s66_main[S2]).
Proof. vm_compute;discriminate. Qed.
Example s66_reg_A_recurs : forall N,exists k,N<=k /\VisitsAt s66_tm StA k.
Proof. exact s66_A_late. Qed.
Example s66_reg_B_recurs : forall N,exists k,N<=k /\VisitsAt s66_tm StB k.
Proof. exact s66_B_late. Qed.
