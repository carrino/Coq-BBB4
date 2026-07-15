(** * Wrap: quiet-state quasihalting via the halt-redirect machine.

    The harness's wrapped QH certificates (wrapctl / wrapfar /
    wrapngram): to prove state [q] goes quiet after step [t],
    redirect all of [q]'s transitions to halt ([tm_wrap]) and build a
    halt-free closure of the *wrapped* machine from the *real*
    machine's step-[t] configuration.  A [q]-configuration has no
    successor in the wrapped machine, so halt-freeness says the
    wrapped run never visits [q] -- and off [q] the two machines
    agree step for step ([wrap_agree]), so neither does the real
    run.  The exact last visit [s] is read off the simulated prefix.

    No liveness argument is involved: this reuses the n-gram
    abstraction with *closedness only* ([closure_invariant]), which
    is enough to board the upstream wrapctl/wrapfar machines whose
    RepWL/DFA abstractions are not built here (measured: all 18
    close at n = 2 from t = s + 1).

    Delivered per machine:
    [NonHalt tm /\ QuietAfter tm q s /\ QuasiHaltsSt tm]. *)

From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure.
From BBB4.Checkers Require Import Cycle NGram.
Import ListNotations.

(** ** The halt-redirect machine *)

Definition tm_wrap (tm : TM) (q : St) : TM :=
  fun p s => if st_eqb p q then None else tm p s.

Lemma tm_wrap_at : forall tm q s, tm_wrap tm q q s = None.
Proof.
  intros. unfold tm_wrap.
  now rewrite (proj2 (st_eqb_spec q q) eq_refl).
Qed.

Lemma tm_wrap_off : forall tm q p s, p <> q -> tm_wrap tm q p s = tm p s.
Proof.
  intros tm q p s H. unfold tm_wrap.
  destruct (st_eqb p q) eqn:E; [|reflexivity].
  apply st_eqb_spec in E. contradiction.
Qed.

Lemma wrap_step_off : forall tm q c,
  fst c <> q -> step (tm_wrap tm q) c = step tm c.
Proof.
  intros tm q [p tp] H. unfold step; simpl in *.
  rewrite tm_wrap_off by assumption. reflexivity.
Qed.

Lemma wrap_step_at : forall tm q c,
  fst c = q -> step (tm_wrap tm q) c = None.
Proof.
  intros tm q [p tp] H. simpl in H. subst p.
  unfold step; simpl. rewrite tm_wrap_at. reflexivity.
Qed.

(** While the wrapped run survives, the two runs coincide and stay
    off [q]. *)
Lemma wrap_agree : forall tm q c,
  (forall j, stepn (tm_wrap tm q) j c <> None) ->
  forall k, stepn (tm_wrap tm q) k c = stepn tm k c /\
            (forall c', stepn tm k c = Some c' -> fst c' <> q).
Proof.
  intros tm q c Him k. induction k as [|k IH].
  - split; [reflexivity|].
    intros c' Hc' Hq. simpl in Hc'. injection Hc' as <-.
    apply (Him 1). cbn [stepn].
    rewrite wrap_step_at by assumption. reflexivity.
  - destruct IH as [IHeq IHq].
    destruct (stepn (tm_wrap tm q) k c) as [ck|] eqn:Ek;
      [| now destruct (Him k)].
    assert (Hck : stepn tm k c = Some ck) by congruence.
    assert (Hoff : fst ck <> q) by (apply (IHq ck Hck)).
    assert (Heq : stepn (tm_wrap tm q) (S k) c = stepn tm (S k) c).
    { replace (S k) with (k + 1) by lia.
      rewrite !stepn_add, Ek, Hck. cbn [stepn].
      rewrite wrap_step_off by assumption. reflexivity. }
    split; [exact Heq|].
    intros c' Hc' Hq'.
    apply (Him (S k + 1)).
    rewrite stepn_add, Heq, Hc'. cbn [stepn].
    rewrite wrap_step_at by assumption. reflexivity.
Qed.

(** ** The checker *)

(** Halt-free closure of [succs] containing [a0]: closedness plus
    membership, no liveness. *)
Definition wrap_closed (tmw : TM) (lset rset : gset)
    (fuel : nat) (a0 : cconf) : bool :=
  match close cconf cconf_enc (ng_succs tmw lset rset)
              fuel [] PositiveSet.empty [a0] with
  | Some Sl =>
      closed_b cconf cconf_enc (ng_succs tmw lset rset) Sl &&
      mem cconf cconf_enc a0 Sl
  | None => false
  end.

Definition ngram_check_quiet (tm : TM) (q : St)
    (s n t fuel rounds : nat) : bool :=
  (1 <=? n) && (s <? t) &&
  match csteps tm t c0, csteps tm s c0 with
  | Some ct, Some cs =>
      st_eqb (fst cs) q &&
      match cstep tm cs with
      | Some cs1 => negb (cvisits tm cs1 (t - s) q)
      | None => false
      end &&
      let tmw := tm_wrap tm q in
      let '(q1, (l, h, r)) := ct in
      let lset0 := gadds (ng_seed_side n l) gempty in
      let rset0 := gadds (ng_seed_side n r) gempty in
      let a0 := ng_start n ct in
      let '(lset, rset) := ng_grow tmw a0 fuel rounds lset0 rset0 in
      ng_seed_ok n lset rset ct &&
      wrap_closed tmw lset rset fuel a0
  | _, _ => false
  end.

(** ** Soundness *)

Theorem ngram_check_quiet_sound : forall tm q s n t fuel rounds,
  ngram_check_quiet tm q s n t fuel rounds = true ->
  NonHalt tm /\ QuietAfter tm q s /\ QuasiHaltsSt tm.
Proof.
  intros tm q s n t fuel rounds H.
  unfold ngram_check_quiet in H.
  apply andb_prop in H as [H Hrest].
  apply andb_prop in H as [Hn Hst].
  apply Nat.leb_le in Hn. apply Nat.ltb_lt in Hst.
  destruct (csteps tm t c0) as [ct|] eqn:Ect; [|discriminate].
  destruct (csteps tm s c0) as [cs|] eqn:Ecs; [|discriminate].
  apply andb_prop in Hrest as [H Hcl].
  apply andb_prop in H as [Hqs Hnv].
  apply st_eqb_spec in Hqs.
  destruct (cstep tm cs) as [cs1|] eqn:Ecs1; [|discriminate].
  apply negb_true_iff in Hnv.
  destruct ct as [q1 [[l h] r]] eqn:Ectc.
  match type of Hcl with
  | (let '(_, _) := ?G in _) = true => destruct G as [lset rset] eqn:Eg
  end.
  cbv beta iota zeta in Hcl.
  apply andb_prop in Hcl as [Hseed Hwc].
  rewrite <- Ectc in *.
  set (tmw := tm_wrap tm q) in *.
  (* the wrapped closure *)
  unfold wrap_closed in Hwc.
  destruct (close cconf cconf_enc (ng_succs tmw lset rset)
                  fuel [] PositiveSet.empty [ng_start n ct])
    as [Sl|] eqn:Ecl; [|discriminate].
  apply andb_prop in Hwc as [Hclb Hmem].
  apply mem_In in Hmem; [|exact cconf_enc_inj].
  assert (Hcov0 : ng_covers n lset rset (ng_start n ct) (lift ct)).
  { apply ng_start_covers. subst ct. exact Hseed. }
  (* immortality of the wrapped machine from lift ct *)
  assert (Him : forall k, stepn tmw k (lift ct) <> None).
  { intros k HN.
    destruct (closure_invariant tmw cconf cconf_enc
                (ng_succs tmw lset rset) (ng_covers n lset rset)
                cconf_enc_inj
                (fun a c Hc => ng_succs_sound tmw n lset rset a c Hn Hc)
                Sl Hclb (ng_start n ct) (lift ct) Hmem Hcov0 k)
      as (c' & a' & Hst' & _ & _).
    congruence. }
  (* prefix bookkeeping *)
  assert (Ecs1' : csteps tm (s + 1) c0 = Some cs1).
  { rewrite csteps_add, Ecs, csteps_1. exact Ecs1. }
  assert (Hstept : stepn tm t InitES = Some (lift ct)).
  { rewrite <- lift_c0. apply csteps_lift. exact Ect. }
  (* no visit of q strictly after s *)
  assert (Hquiet : forall m, s < m -> ~ VisitsAt tm q m).
  { intros m Hm (c & Hc & Hcq).
    destruct (stepn_csteps tm m c) as (cc & Hcc & Hlift); [exact Hc|].
    assert (Hccq : fst cc = q).
    { rewrite <- (lift_state cc), Hlift. exact Hcq. }
    destruct (le_lt_dec m t) as [Hle | Hgt].
    - (* inside the scanned window *)
      replace m with ((s + 1) + (m - s - 1)) in Hcc by lia.
      rewrite csteps_add, Ecs1' in Hcc.
      rewrite (cvisits_complete tm (t - s) cs1 q (m - s - 1) cc)
        in Hnv; [discriminate | lia | exact Hcc | exact Hccq].
    - (* after t: the wrapped run forbids q *)
      replace m with (t + (m - t)) in Hcc by lia.
      rewrite csteps_add, Ect in Hcc.
      apply csteps_lift in Hcc.
      destruct (wrap_agree tm q (lift ct) Him (m - t)) as [_ Hqfree].
      apply (Hqfree (lift cc)); [exact Hcc|].
      rewrite lift_state. exact Hccq. }
  assert (Hvis : VisitsAt tm q s).
  { exists (lift cs). split.
    - rewrite <- lift_c0. apply csteps_lift. exact Ecs.
    - rewrite lift_state. exact Hqs. }
  split; [|split].
  - (* NonHalt *)
    intros m HN.
    destruct (le_lt_dec m t) as [Hle | Hgt].
    + destruct (csteps_prefix tm m t c0 ct Hle Ect) as (cm & Hcm & _).
      apply csteps_lift in Hcm. rewrite lift_c0 in Hcm. congruence.
    + replace m with (t + (m - t)) in HN by lia.
      rewrite stepn_add, Hstept in HN.
      destruct (wrap_agree tm q (lift ct) Him (m - t)) as [Heq _].
      rewrite <- Heq in HN.
      exact (Him (m - t) HN).
  - split; [exact Hvis | exact Hquiet].
  - eapply quiet_after_qh. split; [exact Hvis | exact Hquiet].
Qed.
