(** Advisory dispatch for instruction-census checkers.

    Every successful answer comes from an existing checker applied to the
    actual machine. Arbitrary map entries, including entries for a different
    machine, carry no logical authority. *)
From Coq Require Import Arith Lia Bool List NArith PArith.
From Coq Require Import FSets.FMapPositive MSets.MSetPositive.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape GTape.
From BBB4.Checkers Require Import NGram NGramTr WrapTr.
From BBB4.Census Require Import TNF_QH Decide RankSearch.
From BBB4.CensusTr Require Import TNF_QHTr RepWLTr DecideTr.
From BBB4.CensusTr Require Import HintTagTr.
Import ListNotations.
Open Scope nat_scope.
Set Default Goal Selector "!".

Definition TrHintMap := PositiveMap.tree TrWinner.

Definition tr_hmap_of (rows : list TrHintRow) : TrHintMap :=
  fold_right (fun '(key, tag) m => PositiveMap.add key tag m)
    (PositiveMap.empty _) rows.

(** Invalid wire codes are misses. Duplicate keys need no soundness rule;
    offline tooling should still reject conflicts for reproducibility. *)
Definition tr_hmap_of_codes (rows : list (positive * nat)) : TrHintMap :=
  fold_right (fun '(key, code) m =>
    match tr_winner_decode code with
    | Some tag => PositiveMap.add key tag m
    | None => m
    end) (PositiveMap.empty _) rows.

Definition tr_hint_lookup (hm : TrHintMap) (tm : TM) : option TrWinner :=
  PositiveMap.find (tm_enc tm) hm.

Inductive TrHintDecision := HintNeverTr | HintQHTr.

Definition tr_hint_verdict (answer : TrHintDecision) : QHResult :=
  match answer with HintNeverTr => R_NeverQH | HintQHTr => R_QH end.

Definition TrHintSound (bound : nat) (tm : TM) (answer : TrHintDecision)
    : Prop :=
  match answer with
  | HintNeverTr => NeverQuasiHaltsTr tm
  | HintQHTr => NonHalt tm /\ QHBoundTr bound tm /\ QuasiHaltsTr tm
  end.

Lemma tr_hint_sound_mono : forall small large tm answer,
  small <= large -> TrHintSound small tm answer ->
  TrHintSound large tm answer.
Proof.
  intros small large tm [|] Hle H; cbn [TrHintSound] in *.
  - exact H.
  - destruct H as [Hnh [Hqb Hqh]].
    split; [exact Hnh|]. split; [|exact Hqh].
    exact (qhboundtr_mono small large tm Hle Hqb).
Qed.

Section AdvisoryTr.
Variables B ng_fuel ng_rounds : nat.
Variables ng_rungs rank_rungs qhb_rungs qhb_lex_rungs : list (nat * nat).
Variables rw_qhb_rungs rw_rungs : list (nat * nat * nat).
Variables rw_fuel rw_cut : nat.

(** The horizon is part of the tag. A full hint has the exact original
    full candidate list, including halt/boundary behavior and ordering. *)
Definition hinted_fire_times (tm : TM) (h : TrHorizon)
    : list (Instr * nat) :=
  let prefix := qh_fire_scan_prefix qhb_rungs tm in
  match h with
  | TrShort => fire_candidates (scan_times prefix)
  | TrFull => fire_candidates (scan_times
      (resume_last_fires tm (12 * qhb_tmax_tr qhb_rungs) prefix))
  end.

Lemma hinted_fire_times_short : forall tm,
  hinted_fire_times tm TrShort = qh_last_fires_prefix qhb_rungs tm.
Proof. intros tm. apply qh_fire_scan_prefix_candidates. Qed.

Lemma hinted_fire_times_full : forall tm,
  hinted_fire_times tm TrFull = qh_last_fires qhb_rungs tm.
Proof. intros tm. apply qh_fire_scan_full_candidates. Qed.

(** Keep the same inexpensive candidate filter as the production ladder.
    This guard is not needed by the checker soundness theorem. *)
Definition hinted_qh_check (tm : TM) (h : TrHorizon)
    (check : list (Instr * nat) -> bool) : bool :=
  let lf := hinted_fire_times tm h in
  if existsb (fun p => snd p <? qhb_tmax_tr qhb_rungs) lf
  then check lf else false.

Lemma hinted_qh_check_sound : forall tm h check,
  (forall lf, check lf = true -> TrHintSound B tm HintQHTr) ->
  hinted_qh_check tm h check = true -> TrHintSound B tm HintQHTr.
Proof.
  intros tm h check Hcheck H.
  unfold hinted_qh_check in H.
  destruct (existsb (fun p => snd p <? qhb_tmax_tr qhb_rungs)
    (hinted_fire_times tm h)); [exact (Hcheck _ H)|discriminate].
Qed.

(** Small soundness projections for the three EXISTING rung functions;
    these are copied structurally from try_qhbtr_with_lf_sound. *)
Lemma hinted_plain_sound : forall tm lf nt,
  try_qhbtr_at B ng_fuel ng_rounds tm lf nt = true ->
  TrHintSound B tm HintQHTr.
Proof.
  intros tm lf [n t] H. unfold try_qhbtr_at in H.
  apply andb_prop in H as [HB H]. apply Nat.leb_le in HB.
  destruct (ngram_check_qhboundtr_sound tm (qh_pins_of lf t)
    n t ng_fuel ng_rounds H) as [Hnh [Hqb Hqh]].
  split; [exact Hnh|]. split; [|exact Hqh].
  intros tg s Hq. specialize (Hqb tg s Hq). lia.
Qed.

Lemma hinted_lex_sound : forall tm lf nt,
  try_qhbtr_lex_at B ng_fuel ng_rounds tm lf nt = true ->
  TrHintSound B tm HintQHTr.
Proof.
  intros tm lf [n t] H. unfold try_qhbtr_lex_at in H.
  apply andb_prop in H as [HB H]. apply Nat.leb_le in HB.
  destruct (csteps tm t c0) as [[q1 [[l h] r]]|] eqn:Ect;
    [|discriminate].
  match type of H with
  | (let '(_, _) := ?G in _) = true => destruct G as [lset rset]
  end.
  cbv beta iota zeta in H.
  destruct (ngram_check_qhboundtr_lex_sound tm (qh_pins_of lf t)
    n t ng_fuel ng_rounds _ H) as [Hnh [Hqb Hqh]].
  split; [exact Hnh|]. split; [|exact Hqh].
  intros tg s Hq. specialize (Hqb tg s Hq). lia.
Qed.

Lemma hinted_rw_qh_sound : forall tm lf rung,
  try_rw_qhbtr_at B rw_fuel rw_cut tm lf rung = true ->
  TrHintSound B tm HintQHTr.
Proof.
  intros tm lf [[L T] t] H. unfold try_rw_qhbtr_at in H.
  apply andb_prop in H as [HB H]. apply Nat.leb_le in HB.
  destruct (rw_tier_qhbtr_sound tm lf L T t rw_fuel rw_cut H)
    as [Hnh [Hqb Hqh]].
  split; [exact Hnh|]. split; [|exact Hqh].
  intros tg s Hq. specialize (Hqb tg s Hq). lia.
Qed.

(** nth_error rejects malformed indices BEFORE any machine simulation.
    Only the selected checker runs; no offline boolean is trusted. *)
Definition try_hint_winner_tr (tm : TM) (tag : TrWinner)
    : option TrHintDecision :=
  match tag with
  | WNGram i =>
      match nth_error ng_rungs i with
      | Some (n, t) => if ngram_check_neverqhtr tm n t ng_fuel ng_rounds
                       then Some HintNeverTr else None
      | None => None
      end
  | WRank i =>
      match nth_error rank_rungs i with
      | Some (n, t) => if rank_tier_tr tm n t ng_fuel ng_rounds
                       then Some HintNeverTr else None
      | None => None
      end
  | WQHPlain h i =>
      match nth_error qhb_rungs i with
      | Some nt => if hinted_qh_check tm h
          (fun lf => try_qhbtr_at B ng_fuel ng_rounds tm lf nt)
          then Some HintQHTr else None
      | None => None
      end
  | WQHLex h i =>
      match nth_error qhb_lex_rungs i with
      | Some nt => if hinted_qh_check tm h
          (fun lf => try_qhbtr_lex_at B ng_fuel ng_rounds tm lf nt)
          then Some HintQHTr else None
      | None => None
      end
  | WQHRW h i =>
      match nth_error rw_qhb_rungs i with
      | Some rung => if hinted_qh_check tm h
          (fun lf => try_rw_qhbtr_at B rw_fuel rw_cut tm lf rung)
          then Some HintQHTr else None
      | None => None
      end
  | WRW i =>
      match nth_error rw_rungs i with
      | Some (L, T, t) => if rw_tier_tr tm L T t rw_fuel rw_cut
                          then Some HintNeverTr else None
      | None => None
      end
  end.

Lemma try_hint_winner_tr_sound : forall tm tag answer,
  try_hint_winner_tr tm tag = Some answer -> TrHintSound B tm answer.
Proof.
  intros tm tag answer H. destruct tag as [i|i|h i|h i|h i|i];
    cbn [try_hint_winner_tr] in H.
  - destruct (nth_error ng_rungs i) as [[n t]|]; [|discriminate].
    destruct (ngram_check_neverqhtr tm n t ng_fuel ng_rounds) eqn:E;
      inversion H; subst.
    exact (ngram_check_neverqhtr_sound tm n t ng_fuel ng_rounds E).
  - destruct (nth_error rank_rungs i) as [[n t]|]; [|discriminate].
    destruct (rank_tier_tr tm n t ng_fuel ng_rounds) eqn:E;
      inversion H; subst.
    exact (rank_tier_tr_sound tm n t ng_fuel ng_rounds E).
  - destruct (nth_error qhb_rungs i) as [nt|]; [|discriminate].
    destruct (hinted_qh_check tm h
      (fun lf => try_qhbtr_at B ng_fuel ng_rounds tm lf nt)) eqn:E;
      inversion H; subst.
    eapply hinted_qh_check_sound; [|exact E].
    intros lf Hcheck. exact (hinted_plain_sound tm lf nt Hcheck).
  - destruct (nth_error qhb_lex_rungs i) as [nt|]; [|discriminate].
    destruct (hinted_qh_check tm h
      (fun lf => try_qhbtr_lex_at B ng_fuel ng_rounds tm lf nt)) eqn:E;
      inversion H; subst.
    eapply hinted_qh_check_sound; [|exact E].
    intros lf Hcheck. exact (hinted_lex_sound tm lf nt Hcheck).
  - destruct (nth_error rw_qhb_rungs i) as [rung|]; [|discriminate].
    destruct (hinted_qh_check tm h
      (fun lf => try_rw_qhbtr_at B rw_fuel rw_cut tm lf rung)) eqn:E;
      inversion H; subst.
    eapply hinted_qh_check_sound; [|exact E].
    intros lf Hcheck. exact (hinted_rw_qh_sound tm lf rung Hcheck).
  - destruct (nth_error rw_rungs i) as [[[L T] t]|]; [|discriminate].
    destruct (rw_tier_tr tm L T t rw_fuel rw_cut) eqn:E;
      inversion H; subst.
    exact (rw_tier_tr_sound tm L T t rw_fuel rw_cut E).
Qed.

Definition try_hint_tr (hm : TrHintMap) (tm : TM) : option TrHintDecision :=
  match tr_hint_lookup hm tm with
  | Some tag => try_hint_winner_tr tm tag
  | None => None
  end.

Lemma try_hint_tr_sound : forall hm tm answer,
  try_hint_tr hm tm = Some answer -> TrHintSound B tm answer.
Proof.
  intros hm tm answer H. unfold try_hint_tr in H.
  destruct (tr_hint_lookup hm tm) as [tag|]; [|discriminate].
  exact (try_hint_winner_tr_sound tm tag answer H).
Qed.

(** A generic adapter keeps all map assumptions out of soundness. eligible
    is merely a scheduling guard; fallback is the original complete decider.
    Its own parameters and interface need not change. *)
Definition advisory_decider_tr (eligible : TM -> bool)
    (fallback : QHDecider) (hm : TrHintMap) : QHDecider := fun tm =>
  if eligible tm then
    match try_hint_tr hm tm with
    | Some answer => tr_hint_verdict answer
    | None => fallback tm
    end
  else fallback tm.

Theorem advisory_decider_tr_WF_larger : forall bound D eligible fallback hm,
  B <= bound -> QHDeciderTr_WF bound D fallback ->
  QHDeciderTr_WF bound D (advisory_decider_tr eligible fallback hm).
Proof.
  intros bound D eligible fallback hm HB Hfallback tm.
  unfold advisory_decider_tr.
  destruct (eligible tm); [|exact (Hfallback tm)].
  destruct (try_hint_tr hm tm) as [answer|] eqn:E;
    [|exact (Hfallback tm)].
  pose proof (try_hint_tr_sound hm tm answer E) as Hanswer.
  pose proof (tr_hint_sound_mono B bound tm answer HB Hanswer) as Hlarge.
  destruct answer; exact Hlarge.
Qed.

Lemma advisory_decider_tr_failed : forall eligible fallback hm tm,
  try_hint_tr hm tm = None ->
  advisory_decider_tr eligible fallback hm tm = fallback tm.
Proof.
  intros eligible fallback hm tm H. unfold advisory_decider_tr.
  destruct (eligible tm); [rewrite H|]; reflexivity.
Qed.

Lemma advisory_decider_tr_miss : forall eligible fallback hm tm,
  tr_hint_lookup hm tm = None ->
  advisory_decider_tr eligible fallback hm tm = fallback tm.
Proof.
  intros eligible fallback hm tm H. apply advisory_decider_tr_failed.
  unfold try_hint_tr. rewrite H. reflexivity.
Qed.

Lemma advisory_decider_tr_empty : forall eligible fallback tm,
  advisory_decider_tr eligible fallback (PositiveMap.empty _) tm = fallback tm.
Proof.
  intros eligible fallback tm. apply advisory_decider_tr_miss.
  unfold tr_hint_lookup. apply PositiveMap.gempty.
Qed.

(** Optional guarded adapter. The production wrapper uses the generic
    adapter with constant-true eligibility, avoiding repeated halt/lookups.
    This guarded version retains halt and lookup priority. *)
Definition hint_eligible_tr (halt_gas : nat) (pm qm dm : DeferredMap)
    (tm : TM) : bool :=
  match find_halt tm halt_gas 0 c0 with
  | Some _ => false
  | None =>
      if deferred_lookup pm tm then false else
      if deferred_lookup qm tm then false else
      if deferred_lookup dm tm then false else true
  end.

Definition hinted_decide_easy_tr (halt_gas loop_gas : nat)
    (pm qm dm : DeferredMap) (hm : TrHintMap) : QHDecider :=
  advisory_decider_tr (hint_eligible_tr halt_gas pm qm dm)
    (decide_easy_tr B halt_gas loop_gas ng_fuel ng_rounds
      ng_rungs rank_rungs qhb_rungs qhb_lex_rungs rw_qhb_rungs
      rw_rungs rw_fuel rw_cut pm qm dm) hm.

(** No certificate assumptions about hm are required. The unchanged
    production WF theorem supplies the sole fallback premise. *)
Theorem hinted_decide_easy_tr_WF_larger :
  forall bound D halt_gas loop_gas pm qm dm hm,
  B <= bound ->
  QHDeciderTr_WF bound D
    (decide_easy_tr B halt_gas loop_gas ng_fuel ng_rounds
      ng_rungs rank_rungs qhb_rungs qhb_lex_rungs rw_qhb_rungs
      rw_rungs rw_fuel rw_cut pm qm dm) ->
  QHDeciderTr_WF bound D
    (hinted_decide_easy_tr halt_gas loop_gas pm qm dm hm).
Proof.
  intros bound D halt_gas loop_gas pm qm dm hm HB Hfallback.
  unfold hinted_decide_easy_tr.
  apply advisory_decider_tr_WF_larger; assumption.
Qed.
End AdvisoryTr.
