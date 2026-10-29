From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn18CutSiblings Require Import CutSiblings.
Import ListNotations.

Example actual_entry_zero : csteps(cs_tm false)1 c0=Some(cs_back StB[][S1]).
Proof. reflexivity. Qed.
Example actual_entry_one : csteps(cs_tm true)1 c0=Some(cs_back StB[][S1]).
Proof. reflexivity. Qed.
Example zero_direct_context :
 csteps(cs_tm false)3(cs_back StB[S0;S3;S2][S1;S2])=
 Some(cs_back StB[S3;S2][S2;S1;S2]).
Proof. reflexivity. Qed.
Example zero_sweep_context :
 csteps(cs_tm true)6(cs_back StB[S0;S3;S1][S2;S2;S2;S1;S3])=
 Some(cs_back StB[S0;S0;S3;S3;S1][S1;S1;S3]).
Proof. reflexivity. Qed.
Example three_zero_sweep_context :
 csteps(cs_tm false)6(cs_back StB[S3;S1][S2;S2;S2;S1;S0])=
 Some(cs_back StB[S0;S0;S3;S1][S1;S2;S0]).
Proof. reflexivity. Qed.
Example three_one_sweep_context :
 csteps(cs_tm true)9(cs_back StB[S3;S1][S2;S2;S2;S1;S0])=
 Some(cs_back StB[S1][S2;S2;S2;S2;S2;S0]).
Proof. reflexivity. Qed.
Example strict_surplus_is_essential : ~cs_valid[S3][S1].
Proof. intros[_[_ H]];cbn in H;lia. Qed.
Example equality_exposes_an_unmarked_B_suffix : forall bit,
 csteps(cs_tm bit)3(cs_back StB[S3][S1])=Some(cs_back StB[][S2;S2]).
Proof. reflexivity. Qed.
Example missing_one_passes_beyond_the_finite_word : forall bit,
 csteps(cs_tm bit)3(cs_back StB[][S2;S2])=Some(StB,([S0;S0;S3],S0,[])).
Proof. reflexivity. Qed.
Example changed_first_two_invalidates_one_macro :
 csteps(cs_tm true)7(cs_back StB[S3][S2;S3;S1])<>
 Some(cs_back StB[][S2;S2;S2;S2;S1]).
Proof. discriminate. Qed.
