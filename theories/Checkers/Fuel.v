(** * Fuel: the neverqh_fuel checker (rule (c2)) on the n-gram abstraction.

    Instantiates the engine's combined fuel checker
    ([closure_check_neverqh_fuel], Closure.v) on the EXISTING n-gram
    abstraction ([cconf] contexts, [ng_covers]/[ng_succs]).  Every
    visited state is discharged by either a lex-rank certificate
    (rules (a)/(b), reusing the full [ng_comp_denote] measure
    vocabulary and its exactness proofs verbatim) or the runner rule
    (c2), which needs two node facts read straight off the context:

    - [fnode_moves_right]: the head symbol sits in the context, so the
      transition -- hence its direction -- is determined; the node
      "moves right" iff [tm q s] steps [DR].
    - [fnode_rfuel_ge1]: a nonblank anywhere in the right window [rw]
      witnesses a right nonblank of every covered configuration
      (`has_right_nonblank`).

    This reads the fuel from the n-gram WINDOW, so it discharges
    runner SCCs whose fuel stays within [n] cells of the head.  The
    beyond-window fuel (the capped sided-count classes of
    [FuelClass.v]) is the completeness upgrade: swap [cconf] for the
    refined [cconf * fclass * fclass] context and read [rfuel_ge1] off
    the tracked class instead of the window.  The soundness path here
    is unchanged by that swap. *)

From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement CTape PosEnc Records Closure.
From BBB4.Checkers Require Import ExactClosure NGram.
Import ListNotations.

(** ** The two runner node predicates and their covering soundness *)

Definition fnode_moves_right (tm : TM) (a : cconf) : bool :=
  let '(q, (lw, s, rw)) := a in
  match tm q s with
  | Some tr => match t_dir tr with DR => true | DL => false end
  | None => false
  end.

Definition fnode_rfuel_ge1 (a : cconf) : bool :=
  let '(q, (lw, s, rw)) := a in
  existsb (fun x => negb (sym_eqb x S0)) rw.

Lemma fnode_moves_right_sound : forall tm n lset rset a c,
  fnode_moves_right tm a = true ->
  ng_covers n lset rset a c ->
  steps_right tm c.
Proof.
  intros tm n lset rset [q [[lw s] rw]] c Hmr Hcov.
  destruct Hcov as (Hq & Hh & _).
  unfold fnode_moves_right in Hmr.
  destruct (tm q s) as [tr|] eqn:Etr; [|discriminate].
  destruct (t_dir tr) eqn:Ed; [discriminate|].
  unfold steps_right. exists tr.
  rewrite <- Hq, <- Hh in Etr. split; [exact Etr | exact Ed].
Qed.

Lemma fnode_rfuel_ge1_sound : forall n lset rset a c,
  fnode_rfuel_ge1 a = true ->
  ng_covers n lset rset a c ->
  has_right_nonblank (snd c).
Proof.
  intros n lset rset [q [[lw s] rw]] c Hrf Hcov.
  destruct Hcov as (_ & _ & _ & Hrw & _).
  unfold fnode_rfuel_ge1 in Hrf.
  apply existsb_exists in Hrf as (x & Hin & Hnb).
  (* x is a window cell; recover its tape index *)
  rewrite Hrw in Hin. unfold win in Hin.
  apply in_map_iff in Hin as (k & Hk & _).
  apply negb_true_iff in Hnb.
  exists k. intro Hcontra.
  rewrite Hk in Hcontra.
  apply (proj2 (sym_eqb_spec x S0)) in Hcontra.
  rewrite Hcontra in Hnb. discriminate.
Qed.

(** ** The checker

    Mirrors [ngram_check_neverqh_lex] (same seed / gram-set growth /
    closure), routing to [closure_check_neverqh_fuel] with the two
    runner predicates. *)

Definition ngram_check_neverqh_fuel (tm : TM) (n t fuel rounds : nat)
    (cert : St -> list ngcomp) : bool :=
  (1 <=? n) &&
  match csteps tm t c0 with
  | Some cc =>
      let '(q, (l, h, r)) := cc in
      let lset0 := gadds (ng_seed_side n l) gempty in
      let rset0 := gadds (ng_seed_side n r) gempty in
      let a0 := ng_start n cc in
      let '(lset, rset) := ng_grow tm a0 fuel rounds lset0 rset0 in
      ng_seed_ok n lset rset cc &&
      closure_check_neverqh_fuel tm cconf cconf_enc ec_state
        (ng_succs tm lset rset)
        (fnode_moves_right tm) fnode_rfuel_ge1
        t fuel a0
        (fun q => map (ng_comp_denote tm n) (cert q))
  | None => false
  end.

Theorem ngram_check_neverqh_fuel_sound : forall tm n t fuel rounds cert,
  ngram_check_neverqh_fuel tm n t fuel rounds cert = true ->
  NeverQuasiHaltsSt tm.
Proof.
  intros tm n t fuel rounds cert H.
  unfold ngram_check_neverqh_fuel in H.
  apply andb_prop in H as [Hn H].
  apply Nat.leb_le in Hn.
  destruct (csteps tm t c0) as [[q [[l h] r]]|] eqn:Et; [|discriminate].
  match type of H with
  | (let '(_, _) := ?G in _) = true => destruct G as [lset rset] eqn:Eg
  end.
  cbv beta iota zeta in H.
  apply andb_prop in H as [Hseed Hcheck].
  apply (closure_check_neverqh_fuel_sound tm cconf cconf_enc ec_state
           (ng_succs tm lset rset) (ng_covers n lset rset)) in Hcheck;
    [assumption | | | | | | |].
  - exact cconf_enc_inj.
  - intros a c Hc. eapply ng_covers_state; eauto.
  - intros a c Hc. apply ng_succs_sound; assumption.
  - intros a c Hmr Hc. eapply fnode_moves_right_sound; eauto.
  - intros a c Hrf Hc. eapply fnode_rfuel_ge1_sound; eauto.
  - intros ct' Hct'. rewrite Et in Hct'. injection Hct' as <-.
    apply ng_start_covers. exact Hseed.
  - intros q0. apply Forall_forall. intros comp Hin.
    apply in_map_iff in Hin. destruct Hin as (c & <- & _).
    destruct c as [phi | m K phi gate | phi | pp rg K phi gate]; simpl.
    + exact I.
    + intros a cc a' cc' sl Hca Hca' Hstep Es HInl.
      eapply ngm_exact; eauto.
    + exact I.
    + destruct (pm_ok n pp rg) eqn:Epm; [|exact I].
      apply andb_prop in Epm as [He Hb].
      intros a cc a' cc' sl Hca Hca' Hstep Es HInl.
      eapply pm_exact; eauto.
      * apply existsb_exists in He as (x & Hx & Hx1).
        apply sym_eqb_spec in Hx1. subst x. assumption.
      * destruct rg; apply Nat.leb_le; assumption.
Qed.
