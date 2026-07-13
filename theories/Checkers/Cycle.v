(** * Cycle: the relative-configuration cycle checker.

    First verified checker, corresponding to the BBB harness's
    [inplace] certificate (README "Certificate: inplace"): if the
    configurations after [n1] and [n1 + p] steps are equal, the
    deterministic run repeats that loop verbatim forever.

    One deliberate generalization: our [ExecState] is head-relative
    (the dynamics cannot observe absolute head position), so "equal"
    means equal state and equal tape-relative-to-head.  The C
    certificate additionally demands equal absolute position; every C
    [inplace] certificate is therefore covered, and so are pure
    translations with an exactly repeating relative tape.

    Two checkers, both closed by [vm_compute]:

    - [cycle_check_neverqh tm n1 p]: the loop exists and every state
      visited anywhere in the run is visited inside the loop window
      [n1, n1+p) => [NeverQuasiHaltsSt tm].
    - [cycle_check_qh tm n1 p q s]: the loop exists, state [q] is
      visited at configuration index [s] and never in (s, n1) nor in
      the loop window => [QuietAfter tm q s] (and hence
      [QuasiHaltsSt tm]), together with [NonHalt tm] -- a genuine
      non-halting quasihalter with an exact last-visit index. *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape.
Import ListNotations.

(** Does state [q] occur among the [len] configurations reached from
    [c] (offsets 0 .. len-1)?  Walks by [cstep]; a halt inside the
    window yields [false] for the remainder. *)
Fixpoint cvisits (tm : TM) (c : cconf) (len : nat) (q : St) : bool :=
  match len with
  | 0 => false
  | S m => st_eqb (fst c) q
           || match cstep tm c with
              | Some c' => cvisits tm c' m q
              | None => false
              end
  end.

Lemma cvisits_sound : forall tm len c q,
  cvisits tm c len q = true ->
  exists i ci, i < len /\ csteps tm i c = Some ci /\ fst ci = q.
Proof.
  induction len; intros c q H; simpl in H.
  - discriminate.
  - apply orb_prop in H as [H | H].
    + exists 0, c. split; [lia|]. split; [reflexivity|].
      apply st_eqb_spec; assumption.
    + destruct (cstep tm c) eqn:E; [|discriminate].
      destruct (IHlen _ _ H) as (i & ci & Hi & Hs & Hq).
      exists (S i), ci. split; [lia|]. split; [|assumption].
      simpl. rewrite E. assumption.
Qed.

Lemma cvisits_complete : forall tm len c q i ci,
  i < len -> csteps tm i c = Some ci -> fst ci = q ->
  cvisits tm c len q = true.
Proof.
  induction len; intros c q i ci Hi Hs Hq.
  - lia.
  - simpl. destruct i.
    + simpl in Hs. injection Hs as <-.
      apply orb_true_intro; left. apply st_eqb_spec; assumption.
    + simpl in Hs. destruct (cstep tm c) eqn:E; [|discriminate].
      apply orb_true_intro; right.
      eapply IHlen; eauto; lia.
Qed.

(** ** The loop lemmas (abstract level) *)

Lemma stepn_loop : forall tm p E,
  stepn tm p E = Some E -> forall k, stepn tm (k * p) E = Some E.
Proof.
  intros tm p E H.
  induction k.
  - reflexivity.
  - replace (S k * p) with (p + k * p) by lia.
    rewrite stepn_add, H. assumption.
Qed.

(** Any configuration index [n >= n1] folds back into the loop
    window: the run at [n] equals the run at [n1 + (n - n1) mod p]. *)
Lemma cycle_fold : forall tm n1 p E,
  0 < p ->
  stepn tm n1 InitES = Some E ->
  stepn tm p E = Some E ->
  forall n, n1 <= n ->
  exists i, i < p /\ stepn tm n InitES = stepn tm (n1 + i) InitES.
Proof.
  intros tm n1 p E Hp H1 Hloop n Hn.
  set (i := (n - n1) mod p).
  set (k := (n - n1) / p).
  pose proof (Nat.div_mod_eq (n - n1) p) as Hdm.
  assert (Hn' : n = n1 + (k * p + i)) by (unfold i, k; lia).
  exists i.
  split. { apply Nat.mod_upper_bound; lia. }
  assert (Ha : stepn tm n InitES = stepn tm (k * p + i) E).
  { rewrite Hn' at 1. rewrite (stepn_add tm n1 (k * p + i) InitES), H1.
    reflexivity. }
  assert (Hb : stepn tm (k * p + i) E = stepn tm i E).
  { rewrite (stepn_add tm (k * p) i E), (stepn_loop tm p E Hloop k).
    reflexivity. }
  assert (Hc : stepn tm (n1 + i) InitES = stepn tm i E).
  { rewrite (stepn_add tm n1 i InitES), H1. reflexivity. }
  rewrite Ha, Hb, Hc. reflexivity.
Qed.

Lemma cycle_nonhalt : forall tm n1 p E,
  0 < p ->
  stepn tm n1 InitES = Some E ->
  stepn tm p E = Some E ->
  NonHalt tm.
Proof.
  intros tm n1 p E Hp H1 Hloop n HN.
  destruct (le_lt_dec n1 n) as [Hle | Hlt].
  - destruct (cycle_fold tm n1 p E Hp H1 Hloop n Hle) as (i & Hi & Heq).
    rewrite Heq in HN.
    rewrite stepn_add, H1 in HN.
    destruct (stepn_prefix tm i p E E) as (cm & Hcm & _); [lia | assumption |].
    rewrite Hcm in HN. discriminate.
  - destruct (stepn_prefix tm n n1 InitES E) as (cm & Hcm & _);
      [lia | assumption |].
    rewrite Hcm in HN. discriminate.
Qed.

(** ** The never-quasihalting checker *)

Definition cycle_check_neverqh (tm : TM) (n1 p : nat) : bool :=
  (0 <? p) &&
  match csteps tm n1 c0 with
  | Some c1 =>
      match csteps tm p c1 with
      | Some c2 =>
          ceqb c1 c2 &&
          forallb (fun q => implb (cvisits tm c0 (n1 + p) q)
                                  (cvisits tm c1 p q)) all_St
      | None => false
      end
  | None => false
  end.

Theorem cycle_check_neverqh_sound : forall tm n1 p,
  cycle_check_neverqh tm n1 p = true -> NeverQuasiHaltsSt tm.
Proof.
  intros tm n1 p H.
  unfold cycle_check_neverqh in H.
  apply andb_prop in H as [Hp H].
  apply Nat.ltb_lt in Hp.
  destruct (csteps tm n1 c0) as [c1|] eqn:E1; [|discriminate].
  destruct (csteps tm p c1) as [c2|] eqn:E2; [|discriminate].
  apply andb_prop in H as [Heq Hsub].
  (* abstract loop facts *)
  assert (H1 : stepn tm n1 InitES = Some (lift c1)).
  { rewrite <- lift_c0. apply csteps_lift; assumption. }
  assert (Hloop : stepn tm p (lift c1) = Some (lift c1)).
  { rewrite (ceqb_lift _ _ Heq) at 2. apply csteps_lift; assumption. }
  (* the full prefix csteps run *)
  assert (E12 : csteps tm (n1 + p) c0 = Some c2).
  { rewrite csteps_add, E1. assumption. }
  intros q Hvq N.
  (* Step 1: q occurs in the loop window. *)
  assert (Hwin : exists i ci, i < p /\ csteps tm i c1 = Some ci /\ fst ci = q).
  { destruct Hvq as (n0 & cn & Hcn & Hq).
    destruct (le_lt_dec (n1 + p) n0) as [Hge | Hlt].
    - (* fold back into the window *)
      destruct (cycle_fold tm n1 p (lift c1) Hp H1 Hloop n0) as (i & Hi & Hfold);
        [lia|].
      rewrite Hfold in Hcn.
      destruct (csteps_prefix tm i p c1 c2) as (c1i & Hc1i & _);
        [lia | assumption |].
      rewrite stepn_add, H1 in Hcn.
      rewrite (csteps_lift _ _ _ _ Hc1i) in Hcn.
      injection Hcn as <-.
      exists i, c1i. auto.
    - (* inside the simulated prefix: use the subset condition *)
      destruct (csteps_prefix tm n0 (n1 + p) c0 c2) as (cn' & Hcn' & _);
        [lia | assumption |].
      assert (Hlift : stepn tm n0 InitES = Some (lift cn')).
      { rewrite <- lift_c0. apply csteps_lift; assumption. }
      rewrite Hlift in Hcn. injection Hcn as <-.
      assert (Hvis0 : cvisits tm c0 (n1 + p) q = true).
      { eapply cvisits_complete; eauto. }
      assert (Hvis1 : cvisits tm c1 p q = true).
      { rewrite forallb_forall in Hsub.
        specialize (Hsub q (all_St_complete q)).
        rewrite Hvis0 in Hsub. destruct (cvisits tm c1 p q); [reflexivity | discriminate]. }
      destruct (cvisits_sound _ _ _ _ Hvis1) as (i & ci & Hi & Hs & Hq').
      exists i, ci. auto. }
  (* Step 2: pump the window occurrence past N. *)
  destruct Hwin as (i & ci & Hi & Hs & Hq).
  exists (n1 + N * p + i).
  split. { nia. }
  exists (lift ci). split; [|assumption].
  replace (n1 + N * p + i) with (n1 + (N * p + i)) by lia.
  rewrite stepn_add, H1.
  rewrite stepn_add, stepn_loop by assumption.
  apply csteps_lift; assumption.
Qed.

Corollary cycle_check_neverqh_nonhalt : forall tm n1 p,
  cycle_check_neverqh tm n1 p = true -> NonHalt tm.
Proof.
  intros; apply never_qh_nonhalt; eapply cycle_check_neverqh_sound; eauto.
Qed.

(** ** The quasihalting checker (exact last visit) *)

Definition cycle_check_qh (tm : TM) (n1 p : nat) (q : St) (s : nat) : bool :=
  (0 <? p) && (s <? n1) &&
  match csteps tm n1 c0 with
  | Some c1 =>
      match csteps tm p c1 with
      | Some c2 =>
          ceqb c1 c2 && negb (cvisits tm c1 p q) &&
          match csteps tm s c0 with
          | Some cs =>
              st_eqb (fst cs) q &&
              match cstep tm cs with
              | Some cs1 => negb (cvisits tm cs1 (n1 - s - 1) q)
              | None => false
              end
          | None => false
          end
      | None => false
      end
  | None => false
  end.

Theorem cycle_check_qh_sound : forall tm n1 p q s,
  cycle_check_qh tm n1 p q s = true ->
  NonHalt tm /\ QuietAfter tm q s /\ QuasiHaltsSt tm.
Proof.
  intros tm n1 p q s H.
  unfold cycle_check_qh in H.
  apply andb_prop in H as [H Hrest].
  apply andb_prop in H as [Hp Hs].
  apply Nat.ltb_lt in Hp. apply Nat.ltb_lt in Hs.
  destruct (csteps tm n1 c0) as [c1|] eqn:E1; [|discriminate].
  destruct (csteps tm p c1) as [c2|] eqn:E2; [|discriminate].
  apply andb_prop in Hrest as [H Hcs].
  apply andb_prop in H as [Heq Hnw].
  destruct (csteps tm s c0) as [cs|] eqn:Es; [|discriminate].
  apply andb_prop in Hcs as [Hqs Hcs].
  apply st_eqb_spec in Hqs.
  destruct (cstep tm cs) as [cs1|] eqn:Es1; [|discriminate].
  (* abstract loop facts *)
  assert (H1 : stepn tm n1 InitES = Some (lift c1)).
  { rewrite <- lift_c0. apply csteps_lift; assumption. }
  assert (Hloop : stepn tm p (lift c1) = Some (lift c1)).
  { rewrite (ceqb_lift _ _ Heq) at 2. apply csteps_lift; assumption. }
  assert (Hnh : NonHalt tm) by (eapply cycle_nonhalt; eauto).
  (* q is never visited at indices in (s, n1) *)
  assert (Hmid : forall n, s < n -> n < n1 -> ~ VisitsAt tm q n).
  { intros n Hsn Hn1 (cn & Hcn & Hqn).
    (* csteps to n: through cs and cs1 *)
    assert (Hs1 : csteps tm (S s) c0 = Some cs1).
    { replace (S s) with (s + 1) by lia.
      rewrite csteps_add, Es, csteps_1. assumption. }
    destruct (csteps_prefix tm (S s) n1 c0 c1) as (cs1' & Hcs1' & Htail);
      [lia | assumption |].
    rewrite Hs1 in Hcs1'. injection Hcs1' as <-.
    destruct (csteps_prefix tm (n - S s) (n1 - S s) cs1 c1) as (cn' & Hcn' & _);
      [lia | assumption |].
    assert (Hliftn : stepn tm n InitES = Some (lift cn')).
    { replace n with (S s + (n - S s)) by lia.
      rewrite stepn_add.
      rewrite <- lift_c0, (csteps_lift _ _ _ _ Hs1).
      apply csteps_lift; assumption. }
    rewrite Hliftn in Hcn. injection Hcn as <-.
    assert (Hv : cvisits tm cs1 (n1 - s - 1) q = true).
    { eapply cvisits_complete; [| exact Hcn' | exact Hqn]. lia. }
    rewrite Hv in Hcs. discriminate. }
  (* q is never visited at indices >= n1 *)
  assert (Hhigh : forall n, n1 <= n -> ~ VisitsAt tm q n).
  { intros n Hn (cn & Hcn & Hqn).
    destruct (cycle_fold tm n1 p (lift c1) Hp H1 Hloop n Hn) as (i & Hi & Hfold).
    rewrite Hfold in Hcn.
    destruct (csteps_prefix tm i p c1 c2) as (c1i & Hc1i & _);
      [lia | assumption |].
    rewrite stepn_add, H1, (csteps_lift _ _ _ _ Hc1i) in Hcn.
    injection Hcn as <-.
    assert (Hv : cvisits tm c1 p q = true).
    { eapply cvisits_complete; eauto. }
    rewrite Hv in Hnw. discriminate. }
  assert (Hqa : QuietAfter tm q s).
  { split.
    - exists (lift cs). split; [|assumption].
      rewrite <- lift_c0. apply csteps_lift; assumption.
    - intros n Hn.
      destruct (le_lt_dec n1 n); [apply Hhigh; lia | apply Hmid; lia]. }
  repeat split; try assumption.
  - apply Hqa.
  - apply Hqa.
  - eapply quiet_after_qh; eauto.
Qed.
