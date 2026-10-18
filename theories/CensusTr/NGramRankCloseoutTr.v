(** Closeout-only weighted NG rank producer.
    Only NG closeout batches import this module. Original DecideTr stays
    byte-for-byte unchanged, including every dynamic rank/lex call. *)
From Coq Require Import Arith Bool List ZArith PArith.
From Coq Require Import FSets.FMapPositive MSets.MSetPositive.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape GTape ClosureTr PosEnc.
From BBB4.Checkers Require Import NGram NGramTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Census Require Import RankSearch.
From BBB4.CensusTr Require Import DecideTr RankSearchWeightedTr.
Import ListNotations.
Open Scope nat_scope.

Definition rank_procedure_ng_closeout_tr (tm : TM) (lset rset : gset)
    (closure : list cconf) (tg : Instr) : list ngcomp :=
  let nodes := filter (fun a => negb (instr_eqb (cinstr a) tg)) closure in
  let g := build_adj_tr tm lset rset tg nodes in
  let Kc := S (S (length nodes)) in
  let rfuel := S (length nodes * 8 + 8) in
  match proc_rounds_weighted_tr 200 tm Kc rfuel nodes g [] with
  | Some comps => comps
  | None => []
  end.

(** Exact producer equality, including exhausted fuel. *)
Lemma rank_procedure_ng_closeout_tr_spec : forall tm lset rset closure tg,
  rank_procedure_ng_closeout_tr tm lset rset closure tg =
  DecideTr.rank_procedure_tr tm lset rset closure tg.
Proof.
  intros. unfold rank_procedure_ng_closeout_tr, DecideTr.rank_procedure_tr.
  now rewrite proc_rounds_weighted_tr_spec.
Qed.

Definition rank_tier_ng_closeout_tr (tm : TM) (n t fuel rounds : nat) : bool :=
  match csteps tm t c0 with
  | None => false
  | Some cc =>
      let '(q0, (l, h, r)) := cc in
      let lset0 := gadds (ng_seed_side n l) gempty in
      let rset0 := gadds (ng_seed_side n r) gempty in
      let a0 := ng_start n cc in
      let '(lset, rset) := ng_grow tm a0 fuel rounds lset0 rset0 in
      let closure :=
        ng_explore tm lset rset fuel [] PositiveSet.empty [a0] in
      ngram_check_neverqhtr_lex_with tm n t fuel lset rset
        (fun tg => rank_procedure_ng_closeout_tr tm lset rset closure tg)
  end.

(** Pointwise congruence avoids unfolding certificate producers while
    proving that the unchanged verified checker sees the same certificate. *)
Lemma rank_allb_ext_ng_closeout_tr : forall A (f g : A -> bool) xs,
  (forall x, f x = g x) -> allb_tr f xs = allb_tr g xs.
Proof.
  intros A f g xs H. induction xs as [|x xs IH].
  - reflexivity.
  - cbn [allb_tr]. rewrite H, IH. reflexivity.
Qed.

Lemma ngram_rank_cert_ext_ng_closeout_tr : forall tm n t fuel lset rset
    (cert1 cert2 : Instr -> list ngcomp),
  (forall tg, cert1 tg = cert2 tg) ->
  ngram_check_neverqhtr_lex_with tm n t fuel lset rset cert1 =
  ngram_check_neverqhtr_lex_with tm n t fuel lset rset cert2.
Proof.
  intros tm n t fuel lset rset cert1 cert2 Hcert.
  unfold ngram_check_neverqhtr_lex_with.
  destruct (csteps tm t c0) as [cc|] eqn:Et; [|reflexivity].
  cbv beta iota zeta.
  unfold closure_check_neverqhtr_lex. rewrite Et.
  destruct (close_tr cconf cconf_enc (ng_succs tm lset rset) fuel []
    PositiveSet.empty [ng_start n cc]); [|reflexivity].
  apply f_equal. apply f_equal.
  apply rank_allb_ext_ng_closeout_tr. intro tg. now rewrite Hcert.
Qed.

(** Exact final Boolean equality, with no extensionality axiom. *)
Lemma rank_tier_ng_closeout_tr_spec : forall tm n t fuel rounds,
  rank_tier_ng_closeout_tr tm n t fuel rounds = DecideTr.rank_tier_tr tm n t fuel rounds.
Proof.
  intros tm n t fuel rounds.
  unfold rank_tier_ng_closeout_tr, DecideTr.rank_tier_tr.
  destruct (csteps tm t c0) as [[q [[l h] r]]|] eqn:Et; [|reflexivity].
  cbv beta iota zeta.
  match goal with
  | |- (let '(_, _) := ?G in _) = _ => destruct G as [lset rset]
  end.
  cbv beta iota zeta.
  apply ngram_rank_cert_ext_ng_closeout_tr. intro tg.
  apply rank_procedure_ng_closeout_tr_spec.
Qed.

Theorem rank_tier_ng_closeout_tr_sound : forall tm n t fuel rounds,
  rank_tier_ng_closeout_tr tm n t fuel rounds = true -> NeverQuasiHaltsTr tm.
Proof.
  intros tm n t fuel rounds H.
  rewrite rank_tier_ng_closeout_tr_spec in H.
  exact (DecideTr.rank_tier_tr_sound tm n t fuel rounds H).
Qed.
