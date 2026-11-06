(** Closed n-gram certificates control every completion of a partial table.
    A numerical window alone is insufficient: closure also proves NonHalt. *)
From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure.
From BBB4.Checkers Require Import NGram ExactClosure.
From BBB4.Census Require Import TNF_QH.
From BBBWait42 Require Import Spec Ranked Transport.
Import ListNotations.

Theorem ngram_ranked_tail_ok_nonhalt : forall tm n ls rs cc pool ranks t w,
 1 <= n -> csteps tm t c0 = Some cc ->
 ngram_ranked_tail_ok tm n ls rs cc pool ranks w = true -> NonHalt tm.
Proof.
 intros tm n ls rs cc pool ranks t w Hn HA Hgate k Hnone.
 unfold ngram_ranked_tail_ok in Hgate.
 apply andb_true_iff in Hgate as [Hgate _].
 apply andb_true_iff in Hgate as [Hgate Hcl].
 apply andb_true_iff in Hgate as [Hseed Hmem].
 assert (Hcov : ng_covers n ls rs (ng_start n cc) (lift cc)).
 { apply ng_start_covers; exact Hseed. }
 apply (mem_In cconf cconf_enc cconf_enc_inj) in Hmem.
 assert (Hsucc : forall a c, ng_covers n ls rs a c ->
   match ng_succs tm ls rs a, step tm c with
   | Some l, Some c' => exists a', In a' l /\ ng_covers n ls rs a' c'
   | Some _, None => False | None, _ => True end).
 { intros a c HC; apply ng_succs_sound; assumption. }
 destruct (closure_invariant tm cconf cconf_enc (ng_succs tm ls rs)
   (ng_covers n ls rs) cconf_enc_inj Hsucc pool Hcl (ng_start n cc)
   (lift cc) Hmem Hcov k) as (c'&a'&HK&_).
 assert (HF : stepn tm (t+k) InitES = Some c').
 { rewrite stepn_add, <- lift_c0, (csteps_lift tm t c0 cc HA); exact HK. }
 replace (t+k) with (k+t) in HF by lia.
 rewrite stepn_add, Hnone in HF; discriminate.
Qed.

Theorem ngram_ranked_search_nonhalt : forall tm n t fuel rounds w,
 ngram_ranked_search tm n t fuel rounds w = true -> NonHalt tm.
Proof.
 intros tm n t fuel rounds w H.
 unfold ngram_ranked_search in H; apply andb_true_iff in H as [Hn H].
 apply Nat.leb_le in Hn.
 destruct (csteps tm t c0) as [[q [[l h] r]]|] eqn:Et; [|discriminate].
 cbv beta iota zeta in H.
 match type of H with
 | (let '(_, _) := ?G in _) = true => destruct G as [ls rs] eqn:Eg
 end.
 cbv beta iota zeta in H.
 match type of H with
 | (match ?G with Some _ => _ | None => _ end) = true =>
     destruct G as [pool|]; [|discriminate]
 end.
 eapply ngram_ranked_tail_ok_nonhalt; eauto.
Qed.

Theorem ngram_ranked_tail_ok_completion : forall tm n ls rs cc pool ranks t w B,
 1 <= n -> t <= B -> csteps tm t c0 = Some cc ->
 ngram_ranked_tail_ok tm n ls rs cc pool ranks w = true ->
 forall tm', TM_le tm tm' -> NonHalt tm' /\ WindowBound tm' B w.
Proof.
 intros tm n ls rs cc pool ranks t w B Hn Ht HA HC tm' Hle.
 pose proof (ngram_ranked_tail_ok_nonhalt tm n ls rs cc pool ranks t w Hn HA HC) as Hnh.
 split; [eapply nonhalt_le; eauto|].
 apply (proj2 (window_bound_completion tm tm' B w Hnh Hle)).
 eapply ngram_ranked_tail_ok_sound; eauto.
Qed.

Theorem ngram_ranked_search_completion : forall tm n t fuel rounds w B,
 t <= B -> ngram_ranked_search tm n t fuel rounds w = true ->
 forall tm', TM_le tm tm' -> NonHalt tm' /\ WindowBound tm' B w.
Proof.
 intros tm n t fuel rounds w B Ht HC tm' Hle.
 pose proof (ngram_ranked_search_nonhalt tm n t fuel rounds w HC) as Hnh.
 split; [eapply nonhalt_le; eauto|].
 apply (proj2 (window_bound_completion tm tm' B w Hnh Hle)).
 eapply ngram_ranked_search_sound; eauto.
Qed.

Module RankedCompletionRegression.
(** Six holes may be filled arbitrarily; the checked blank trace never uses them. *)
Definition partial : TM := fun q a => match q,a with
 | StA,S0 => Some (mkTrans S0 DR StB)
 | StB,S0 => Some (mkTrans S0 DR StA)
 | _,_ => None end.
Example partial_checked : ngram_ranked_search partial 1 0 16 4 1 = true.
Proof. vm_compute; reflexivity. Qed.
Theorem partial_all_completions : forall tm' B,
 TM_le partial tm' -> NonHalt tm' /\ WindowBound tm' B 1.
Proof.
 intros tm' B Hle.
 exact (ngram_ranked_search_completion partial 1 0 16 4 1 B
   (Nat.le_0_l _) partial_checked tm' Hle).
Qed.
End RankedCompletionRegression.

Print Assumptions ngram_ranked_tail_ok_nonhalt.
Print Assumptions ngram_ranked_search_completion.
