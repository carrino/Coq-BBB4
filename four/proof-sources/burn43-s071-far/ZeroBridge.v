(** Flattened concrete all-zero right stacks imply the FAR summary zero flag.
    The decoding condition is needed only for words which occur on Push edges.
    No certificate validity or state classification is asserted here. *)
From Coq Require Import List Bool.
From BBB24 Require Import Statement CTape.
From BBB24Burn43S071FAR Require Import FARForward.
Import ListNotations.
Set Implicit Arguments.

Section ConcreteZero.
Context (d : FARData).
Context (cells : W d -> list Sym).

Definition c53_flat (xs : list (W d)) : list Sym := flat_map cells xs.

Lemma c53_all_blank_app : forall a b,
 all_blank (a ++ b) = (all_blank a && all_blank b).
Proof.
 induction a as [|h a IH]; intro b; cbn [all_blank app].
 - reflexivity.
 - rewrite IH. now destruct (sym_eqb h S0).
Qed.

Context (push_blank_decode : forall w r rn,
 Push d w r rn -> all_blank (cells w) = true -> w = blank d).

Lemma c53_summ_flat_blank_words : forall xs r,
 Summ d xs r -> all_blank (c53_flat xs) = true ->
 Forall (fun w => w = blank d) xs.
Proof.
 intros xs r H; induction H as [|w xs r rn HS IH HP]; intro Hb; [constructor|].
 unfold c53_flat in Hb; cbn [flat_map] in Hb.
 rewrite c53_all_blank_app in Hb. apply andb_true_iff in Hb as [Hw Ht].
 constructor.
 - eapply push_blank_decode; eauto.
 - apply IH. exact Ht.
Qed.

Lemma c53_summ_flat_blank_zero : Closed d -> forall xs r,
 Summ d xs r -> all_blank (c53_flat xs) = true -> Zero d r.
Proof.
 intros HC xs r HS HB. eapply summ_blank; eauto.
 eapply c53_summ_flat_blank_words; eauto.
Qed.

Lemma c53_summ_flat_right_ok : Closed d -> forall xs r,
 Summ d xs r -> all_blank (c53_flat xs) = true -> zflag d r = true.
Proof.
 intros HC xs r HS HB. eapply zero_flag; [exact HC|].
 eapply c53_summ_flat_blank_zero; eauto.
Qed.
End ConcreteZero.

Print Assumptions c53_summ_flat_blank_words.
Print Assumptions c53_summ_flat_blank_zero.
Print Assumptions c53_summ_flat_right_ok.
