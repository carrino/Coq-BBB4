(** * TCycler: the translated-cycler checker.

    The BBB harness's [tcycler] certificate, in head-relative form.
    Parameters [(n1, P, W)]: after [n1] steps the run reaches an
    anchor configuration; truncate its left half-tape to the top [W]
    cells and run [P] guarded steps ([GTape.gstep] -- the wall fails
    the check if the run ever needs a deeper cell).  If the guarded
    run ends in a configuration [gmatch]-ing the truncated anchor
    (same state and head, left list extending the [W]-window
    exactly, right half-tape denoting the same), then by
    [gmatch_lift] every abstract instance of the end configuration
    is again an instance of the anchor family, and the run repeats
    the lap forever ([tcycler_laps]).

    Correspondence with the C certificate: [n1] = anchor_step, [P] =
    period_steps, [W] = reach.  The soundness needs no record-event
    or frontier condition: blankness beyond the anchor's known right
    tape is what [lift] denotes, and the recurrence of the right
    half-tape is checked exactly ([lpad_eqb] in [gmatch]).  Left-
    moving translated cyclers (side L) are checked by running this
    right-handed checker on [mirror_tm tm] and transferring through
    the [Mirror] lemmas.

    Note the window constraint is two-sided in practice: [W] must be
    at least the lap's leftward excursion (or the wall fails), and at
    most excursion + net displacement (or the [W]-window comparison
    reaches into cells the lap never rewrote, which sit shifted
    relative to the anchor).  [W] = the C certificate's [reach]
    always works; the checker verifies whatever it is given, so a bad
    [W] only loses the proof, never soundness. *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape GTape Mirror.
From BBB4.Checkers Require Import Cycle.
Import ListNotations.

(** Does state [q] occur among the [len] configurations of the
    guarded run from [g] (offsets 0 .. len-1)? *)
Fixpoint gvisits (tm : TM) (g : cconf) (len : nat) (q : St) : bool :=
  match len with
  | 0 => false
  | S m => st_eqb (fst g) q
           || match gstep tm g with
              | Some g' => gvisits tm g' m q
              | None => false
              end
  end.

Lemma gvisits_sound : forall tm len g q,
  gvisits tm g len q = true ->
  exists i gi, i < len /\ gsteps tm i g = Some gi /\ fst gi = q.
Proof.
  induction len; intros g q H; simpl in H.
  - discriminate.
  - apply orb_prop in H as [H | H].
    + exists 0, g. split; [lia|]. split; [reflexivity|].
      apply st_eqb_spec; assumption.
    + destruct (gstep tm g) eqn:E; [|discriminate].
      destruct (IHlen _ _ H) as (i & gi & Hi & Hs & Hq).
      exists (S i), gi. split; [lia|]. split; [|assumption].
      simpl. rewrite E. assumption.
Qed.

Lemma gvisits_complete : forall tm len g q i gi,
  i < len -> gsteps tm i g = Some gi -> fst gi = q ->
  gvisits tm g len q = true.
Proof.
  induction len; intros g q i gi Hi Hs Hq.
  - lia.
  - simpl. destruct i.
    + simpl in Hs. injection Hs as <-.
      apply orb_true_intro; left. apply st_eqb_spec; assumption.
    + simpl in Hs. destruct (gstep tm g) eqn:E; [|discriminate].
      apply orb_true_intro; right.
      eapply IHlen; eauto; lia.
Qed.

(** ** The lap induction *)

(** From an anchor instance, every number of laps later the run is
    again at an instance of the anchor family. *)
Lemma tcycler_laps : forall tm n1 P g1 g2 rho0,
  stepn tm n1 InitES = Some (glift rho0 g1) ->
  gsteps tm P g1 = Some g2 ->
  gmatch g1 g2 = true ->
  forall k, exists rho, stepn tm (n1 + k * P) InitES = Some (glift rho g1).
Proof.
  intros tm n1 P g1 g2 rho0 HA HP Hm.
  induction k.
  - exists rho0. replace (n1 + 0 * P) with n1 by lia. exact HA.
  - destruct IHk as [rho Hrho].
    destruct (gmatch_lift _ _ Hm rho) as [rho' Hg].
    exists rho'.
    replace (n1 + S k * P) with ((n1 + k * P) + P) by lia.
    rewrite stepn_add, Hrho.
    rewrite (gsteps_lift _ _ _ _ rho HP). rewrite Hg. reflexivity.
Qed.

(** Fold an arbitrary index [n >= n1] back into lap coordinates. *)
Lemma tcycler_fold : forall tm n1 P g1 g2 rho0,
  0 < P ->
  stepn tm n1 InitES = Some (glift rho0 g1) ->
  gsteps tm P g1 = Some g2 ->
  gmatch g1 g2 = true ->
  forall n, n1 <= n ->
  exists i gi rho, i < P /\ gsteps tm i g1 = Some gi /\
    stepn tm n InitES = Some (glift rho gi).
Proof.
  intros tm n1 P g1 g2 rho0 HP0 HA HP Hm n Hn.
  set (i := (n - n1) mod P).
  set (k := (n - n1) / P).
  assert (Hi : i < P) by (apply Nat.mod_upper_bound; lia).
  pose proof (Nat.div_mod_eq (n - n1) P) as Hdm.
  assert (Hn' : n = (n1 + k * P) + i) by (unfold i, k; lia).
  destruct (tcycler_laps tm n1 P g1 g2 rho0 HA HP Hm k) as [rho Hrho].
  destruct (gsteps_prefix tm i P g1 g2) as (gi & Hgi & _);
    [lia | exact HP |].
  exists i, gi, rho.
  split; [exact Hi|]. split; [exact Hgi|].
  rewrite Hn', stepn_add, Hrho.
  apply gsteps_lift; exact Hgi.
Qed.

(** ** The checkers *)

Definition tcycler_check_neverqh (tm : TM) (n1 P W : nat) : bool :=
  (0 <? P) &&
  match csteps tm n1 c0 with
  | Some (q1, (l1, h1, r1)) =>
      let g1 : cconf := (q1, (firstn_pad W l1, h1, r1)) in
      match gsteps tm P g1 with
      | Some g2 =>
          gmatch g1 g2 &&
          forallb (fun q => implb (cvisits tm c0 (n1 + P) q)
                                  (gvisits tm g1 P q)) all_St
      | None => false
      end
  | None => false
  end.

Definition tcycler_check_qh (tm : TM) (n1 P W : nat) (q : St) (s : nat)
  : bool :=
  (0 <? P) && (s <? n1) &&
  match csteps tm n1 c0 with
  | Some (q1, (l1, h1, r1)) =>
      let g1 : cconf := (q1, (firstn_pad W l1, h1, r1)) in
      match gsteps tm P g1 with
      | Some g2 =>
          gmatch g1 g2 && negb (gvisits tm g1 P q) &&
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

(** The anchor reached from the blank tape is an instance of the
    truncated anchor family. *)
Lemma anchor_instance : forall tm n1 W q1 l1 h1 r1,
  csteps tm n1 c0 = Some (q1, (l1, h1, r1)) ->
  stepn tm n1 InitES =
  Some (glift (fun n => nthb l1 (n + W)) (q1, (firstn_pad W l1, h1, r1))).
Proof.
  intros tm n1 W q1 l1 h1 r1 H.
  rewrite <- lift_c0.
  rewrite (csteps_lift _ _ _ _ H).
  f_equal. unfold lift, glift; simpl.
  do 2 f_equal.
  apply lift_side_wall.
Qed.

Theorem tcycler_check_neverqh_sound : forall tm n1 P W,
  tcycler_check_neverqh tm n1 P W = true -> NeverQuasiHaltsSt tm.
Proof.
  intros tm n1 P W H.
  unfold tcycler_check_neverqh in H.
  apply andb_prop in H as [Hp H].
  apply Nat.ltb_lt in Hp.
  destruct (csteps tm n1 c0) as [[q1 [[l1 h1] r1]]|] eqn:E1; [|discriminate].
  destruct (gsteps tm P (q1, (firstn_pad W l1, h1, r1))) as [g2|] eqn:E2;
    [|discriminate].
  apply andb_prop in H as [Hm Hsub].
  pose proof (anchor_instance tm n1 W q1 l1 h1 r1 E1) as HA.
  set (g1 := (q1, (firstn_pad W l1, h1, r1)) : cconf) in *.
  set (rho0 := fun n => nthb l1 (n + W)) in *.
  intros q Hvq N.
  (* Step 1: q occurs in the guarded window. *)
  assert (Hwin : exists i gi, i < P /\ gsteps tm i g1 = Some gi /\ fst gi = q).
  { destruct Hvq as (n0 & cn & Hcn & Hq).
    destruct (le_lt_dec n1 n0) as [Hge | Hlt].
    - (* fold back into the window *)
      destruct (tcycler_fold tm n1 P g1 g2 rho0 Hp HA E2 Hm n0 Hge)
        as (i & gi & rho & Hi & Hgi & Hfold).
      rewrite Hfold in Hcn. injection Hcn as <-.
      exists i, gi. auto.
    - (* inside the simulated prefix: use the subset condition *)
      destruct (csteps_prefix tm n0 n1 c0 (q1, (l1, h1, r1)))
        as (cn' & Hcn' & _); [lia | exact E1 |].
      assert (Hlift : stepn tm n0 InitES = Some (lift cn')).
      { rewrite <- lift_c0. apply csteps_lift; assumption. }
      rewrite Hlift in Hcn. injection Hcn as <-.
      assert (Hvis0 : cvisits tm c0 (n1 + P) q = true).
      { eapply cvisits_complete; [| exact Hcn' | exact Hq]. lia. }
      assert (Hvis1 : gvisits tm g1 P q = true).
      { rewrite forallb_forall in Hsub.
        specialize (Hsub q (all_St_complete q)).
        rewrite Hvis0 in Hsub.
        destruct (gvisits tm g1 P q); [reflexivity | discriminate]. }
      destruct (gvisits_sound _ _ _ _ Hvis1) as (i & gi & Hi & Hs & Hq').
      exists i, gi. auto. }
  (* Step 2: pump the window occurrence past N. *)
  destruct Hwin as (i & gi & Hi & Hgi & Hq).
  destruct (tcycler_laps tm n1 P g1 g2 rho0 HA E2 Hm N) as [rho Hrho].
  exists (n1 + N * P + i).
  split. { nia. }
  exists (glift rho gi). split.
  - replace (n1 + N * P + i) with ((n1 + N * P) + i) by lia.
    rewrite stepn_add, Hrho.
    apply gsteps_lift; exact Hgi.
  - exact Hq.
Qed.

Theorem tcycler_check_qh_sound : forall tm n1 P W q s,
  tcycler_check_qh tm n1 P W q s = true ->
  NonHalt tm /\ QuietAfter tm q s /\ QuasiHaltsSt tm.
Proof.
  intros tm n1 P W q s H.
  unfold tcycler_check_qh in H.
  apply andb_prop in H as [H Hrest].
  apply andb_prop in H as [Hp Hs].
  apply Nat.ltb_lt in Hp. apply Nat.ltb_lt in Hs.
  destruct (csteps tm n1 c0) as [[q1 [[l1 h1] r1]]|] eqn:E1; [|discriminate].
  destruct (gsteps tm P (q1, (firstn_pad W l1, h1, r1))) as [g2|] eqn:E2;
    [|discriminate].
  apply andb_prop in Hrest as [H Hcs].
  apply andb_prop in H as [Hm Hnw].
  destruct (csteps tm s c0) as [cs|] eqn:Es; [|discriminate].
  apply andb_prop in Hcs as [Hqs Hcs].
  apply st_eqb_spec in Hqs.
  destruct (cstep tm cs) as [cs1|] eqn:Es1; [|discriminate].
  pose proof (anchor_instance tm n1 W q1 l1 h1 r1 E1) as HA.
  set (g1 := (q1, (firstn_pad W l1, h1, r1)) : cconf) in *.
  set (rho0 := fun n => nthb l1 (n + W)) in *.
  (* non-halting *)
  assert (Hnh : NonHalt tm).
  { intros n HN.
    destruct (le_lt_dec n1 n) as [Hge | Hlt].
    - destruct (tcycler_fold tm n1 P g1 g2 rho0 Hp HA E2 Hm n Hge)
        as (i & gi & rho & Hi & Hgi & Hfold).
      rewrite Hfold in HN. discriminate.
    - destruct (csteps_prefix tm n n1 c0 (q1, (l1, h1, r1)))
        as (cm & Hcm & _); [lia | exact E1 |].
      assert (Hl : stepn tm n InitES = Some (lift cm)).
      { rewrite <- lift_c0. apply csteps_lift; assumption. }
      rewrite Hl in HN. discriminate. }
  (* q never visited at indices in (s, n1) *)
  assert (Hmid : forall n, s < n -> n < n1 -> ~ VisitsAt tm q n).
  { intros n Hsn Hn1 (cn & Hcn & Hqn).
    assert (Hs1 : csteps tm (S s) c0 = Some cs1).
    { replace (S s) with (s + 1) by lia.
      rewrite csteps_add, Es, csteps_1. assumption. }
    destruct (csteps_prefix tm (n - S s) (n1 - S s) cs1 (q1, (l1, h1, r1)))
      as (cn' & Hcn' & _); [lia | |].
    { destruct (csteps_prefix tm (S s) n1 c0 (q1, (l1, h1, r1)))
        as (cs1' & Hcs1' & Htail); [lia | exact E1 |].
      rewrite Hs1 in Hcs1'. injection Hcs1' as <-. exact Htail. }
    assert (Hliftn : stepn tm n InitES = Some (lift cn')).
    { replace n with (S s + (n - S s)) by lia.
      rewrite stepn_add.
      rewrite <- lift_c0, (csteps_lift _ _ _ _ Hs1).
      apply csteps_lift; assumption. }
    rewrite Hliftn in Hcn. injection Hcn as <-.
    assert (Hv : cvisits tm cs1 (n1 - s - 1) q = true).
    { eapply cvisits_complete; [| exact Hcn' | exact Hqn]. lia. }
    rewrite Hv in Hcs. discriminate. }
  (* q never visited at indices >= n1 *)
  assert (Hhigh : forall n, n1 <= n -> ~ VisitsAt tm q n).
  { intros n Hn (cn & Hcn & Hqn).
    destruct (tcycler_fold tm n1 P g1 g2 rho0 Hp HA E2 Hm n Hn)
      as (i & gi & rho & Hi & Hgi & Hfold).
    rewrite Hfold in Hcn. injection Hcn as <-.
    assert (Hv : gvisits tm g1 P q = true).
    { eapply gvisits_complete; eauto. }
    rewrite Hv in Hnw. discriminate. }
  assert (Hqa : QuietAfter tm q s).
  { split.
    - exists (lift cs). split; [|exact Hqs].
      rewrite <- lift_c0. apply csteps_lift; assumption.
    - intros n Hn.
      destruct (le_lt_dec n1 n); [apply Hhigh; lia | apply Hmid; lia]. }
  split; [exact Hnh|]. split; [exact Hqa|].
  eapply quiet_after_qh; eauto.
Qed.

(** ** Mirrored (side-L) corollaries *)

Corollary tcycler_check_neverqh_sound_L : forall tm n1 P W,
  tcycler_check_neverqh (mirror_tm tm) n1 P W = true ->
  NeverQuasiHaltsSt tm.
Proof.
  intros. apply mirror_never_qh.
  eapply tcycler_check_neverqh_sound; eauto.
Qed.

Corollary tcycler_check_qh_sound_L : forall tm n1 P W q s,
  tcycler_check_qh (mirror_tm tm) n1 P W q s = true ->
  NonHalt tm /\ QuietAfter tm q s /\ QuasiHaltsSt tm.
Proof.
  intros tm n1 P W q s H.
  destruct (tcycler_check_qh_sound _ _ _ _ _ _ H) as (Hnh & Hqa & Hqh).
  split; [|split].
  - apply mirror_nonhalt; assumption.
  - apply mirror_quiet_after; assumption.
  - apply mirror_qh; assumption.
Qed.
