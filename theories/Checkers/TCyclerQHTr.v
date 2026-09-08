(** * TCyclerQHTr: translated cyclers at TRANSITION level, the
    QUASIHALTING side.

    [TCyclerTr.tcycler_check_neverqhtr] proves [NeverQuasiHaltsTr]: a
    guarded lap [g1 -> g2] of period [P] from the anchor [n1], plus the
    gate "every instruction fired in the first [n1 + P] steps fires in
    the lap".  A quiet-instruction translated cycler (SCOPING_INSTR.md
    7.3a: a LIVE-class machine whose initial transition, typically A0,
    is never taken again) fails only that gate.  This checker keeps the
    lap and drops the gate: every instruction that does not fire in the
    lap last fires before the anchor (every later configuration folds
    into the lap), so every quiet instruction's score is at most [n1];
    and an instruction fired in the prefix but absent from the lap is a
    quasihalt witness.  Conclusion: [NonHalt], the unfolded
    [QHBoundTr n1], [QuasiHaltsTr] -- the shape [provqh_tr] needs.
    [Print Assumptions tcycler_check_qhboundtr_sound] must be
    [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape GTape Mirror
  ClosureTr.
From BBB4.Checkers Require Import Cycle TCycler TCyclerTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.CensusTr Require Import TNF_QHTr.
Import ListNotations.

(** [cfires] is complete ([ClosureTr.cfires_complete]); here its
    soundness: a firing within [len] steps of [c] is a real one *)
Lemma cfires_sound : forall tm len c tg,
  cfires tm c len tg = true ->
  exists i ci, i < len /\ csteps tm i c = Some ci /\ cinstr ci = tg.
Proof.
  induction len; intros c tg H; simpl in H; [discriminate|].
  apply orb_prop in H as [H | H].
  - apply instr_eqb_spec in H. exists 0, c. split; [lia|]. split; [reflexivity|exact H].
  - destruct (cstep tm c) as [c'|] eqn:E; [|discriminate].
    destruct (IHlen c' tg H) as (i & ci & Hi & Hs & Hq).
    exists (S i), ci. split; [lia|]. split; [|exact Hq].
    simpl. rewrite E. exact Hs.
Qed.

(** ** The checker *)

Definition tcycler_check_qhboundtr (tm : TM) (n1 P W : nat) : bool :=
  (0 <? P) &&
  match csteps tm n1 c0 with
  | Some (q1, (l1, h1, r1)) =>
      let g1 : cconf := (q1, (firstn_pad W l1, h1, r1)) in
      match gsteps tm P g1 with
      | Some g2 =>
          gmatch g1 g2 &&
          existsb (fun t => cfires tm c0 n1 t && negb (gfires tm g1 P t))
                  all_Instr
      | None => false
      end
  | None => false
  end.

Theorem tcycler_check_qhboundtr_sound : forall tm n1 P W,
  tcycler_check_qhboundtr tm n1 P W = true ->
  NonHalt tm
  /\ (forall tg s, QuietAfterTr tm tg s -> S s <= n1)
  /\ QuasiHaltsTr tm.
Proof.
  intros tm n1 P W H.
  unfold tcycler_check_qhboundtr in H.
  apply andb_prop in H as [Hp H].
  apply Nat.ltb_lt in Hp.
  destruct (csteps tm n1 c0) as [[q1 [[l1 h1] r1]]|] eqn:E1; [|discriminate].
  destruct (gsteps tm P (q1, (firstn_pad W l1, h1, r1))) as [g2|] eqn:E2;
    [|discriminate].
  apply andb_prop in H as [Hm Hex].
  pose proof (anchor_instance tm n1 W q1 l1 h1 r1 E1) as HA.
  set (g1 := (q1, (firstn_pad W l1, h1, r1)) : cconf) in *.
  set (rho0 := fun n => nthb l1 (n + W)) in *.
  (* every configuration at index >= n1 is a lift of a lap configuration *)
  assert (Hfold : forall n, n1 <= n ->
            exists i gi rho, i < P /\ gsteps tm i g1 = Some gi /\
              stepn tm n InitES = Some (glift rho gi)).
  { intros n Hn. exact (tcycler_fold tm n1 P g1 g2 rho0 Hp HA E2 Hm n Hn). }
  (* non-halting *)
  assert (Hnh : NonHalt tm).
  { intros n HN.
    destruct (le_lt_dec n1 n) as [Hge | Hlt].
    - destruct (Hfold n Hge) as (i & gi & rho & Hi & Hgi & Hf).
      rewrite Hf in HN. discriminate.
    - destruct (csteps_prefix tm n n1 c0 (q1, (l1, h1, r1)))
        as (cm & Hcm & _); [lia | exact E1 |].
      assert (Hl : stepn tm n InitES = Some (lift cm)).
      { rewrite <- lift_c0. apply csteps_lift; assumption. }
      rewrite Hl in HN. discriminate. }
  (* an instruction absent from the lap never fires at index >= n1 *)
  assert (Hquiet : forall tg, gfires tm g1 P tg = false ->
            forall n, n1 <= n -> ~ FiresAt tm tg n).
  { intros tg Hg n Hn (cn & Hcn & Ht).
    destruct (Hfold n Hn) as (i & gi & rho & Hi & Hgi & Hf).
    rewrite Hf in Hcn. injection Hcn as <-.
    rewrite glift_cinstr in Ht.
    assert (Hg' : gfires tm g1 P tg = true).
    { eapply gfires_complete; eauto. }
    rewrite Hg' in Hg. discriminate. }
  (* an instruction in the lap fires again after any index *)
  assert (Hlive : forall tg, gfires tm g1 P tg = true ->
            forall N, exists n, N <= n /\ FiresAt tm tg n).
  { intros tg Hg N.
    destruct (gfires_sound _ _ _ _ Hg) as (i & gi & Hi & Hgi & Ht).
    destruct (tcycler_laps tm n1 P g1 g2 rho0 HA E2 Hm N) as [rho Hrho].
    exists (n1 + N * P + i).
    split. { nia. }
    exists (glift rho gi). split.
    - replace (n1 + N * P + i) with ((n1 + N * P) + i) by lia.
      rewrite stepn_add, Hrho.
      apply gsteps_lift; exact Hgi.
    - rewrite glift_cinstr. exact Ht. }
  split; [exact Hnh|]. split.
  - (* the bound: a quiet instruction's last fire is before the anchor *)
    intros tg s [Hs Hafter].
    destruct (gfires tm g1 P tg) eqn:Hg.
    + destruct (Hlive tg Hg (S s)) as (n & Hn & Hf).
      exfalso. apply (Hafter n); [lia | exact Hf].
    + destruct (le_lt_dec n1 s) as [Hge | Hlt]; [|lia].
      exfalso. exact (Hquiet tg Hg s Hge Hs).
  - (* the witness: a prefix-fired instruction absent from the lap *)
    apply existsb_exists in Hex as (tg & _ & Htg).
    apply andb_prop in Htg as [Hpre Hng].
    apply negb_true_iff in Hng.
    destruct (cfires_sound _ _ _ _ Hpre) as (i & ci & Hi & Hs & Hq).
    exists tg. split.
    + exists i, (lift ci). split.
      * rewrite <- lift_c0. apply csteps_lift; exact Hs.
      * rewrite cinstr_lift. exact Hq.
    + exists n1. intros n Hn. exact (Hquiet tg Hng n Hn).
Qed.

Corollary tcycler_check_qhboundtr_sound_L : forall tm n1 P W,
  tcycler_check_qhboundtr (mirror_tm tm) n1 P W = true ->
  NonHalt tm
  /\ (forall tg s, QuietAfterTr tm tg s -> S s <= n1)
  /\ QuasiHaltsTr tm.
Proof.
  intros tm n1 P W H.
  destruct (tcycler_check_qhboundtr_sound _ _ _ _ H) as [Hnh [Hb Hq]].
  split; [exact (mirror_nonhalt tm Hnh)|].
  split.
  - exact (qhboundtr_mirror n1 tm Hb).
  - destruct Hq as (t & (n & Hf) & (N & HN)).
    exists t. split.
    + exists n. apply mirror_fires; exact Hf.
    + exists N. intros m Hm Hv. apply (HN m Hm). apply mirror_fires; exact Hv.
Qed.
