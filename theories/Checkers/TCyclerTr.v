(** * TCyclerTr: the translated-cycler checker at TRANSITION level.

    [TCycler.tcycler_check_neverqh] with its target alphabet changed
    from the 4 states to the 8 instructions.  The lap induction
    ([tcycler_laps], [tcycler_fold]) is reused verbatim: it speaks
    about configurations, not targets.  Only the two scans change --
    [cfires] (ClosureTr) over the simulated prefix, [gfires] over the
    guarded lap -- and the pumped occurrence fires the same
    instruction because [glift] plants the window's head cell whatever
    the abstract far tape is ([glift_cinstr]).

    Parameters as at the state level: [(n1, P, W)] = anchor step,
    lap length, left window.  The inclusion gate is now
    [forallb (fun t => cfires .. (n1+P) t ==> gfires .. P t) all_Instr]:
    every instruction that fires in the first [n1 + P] steps fires
    inside the lap, so it recurs forever; an instruction that never
    fires needs no witness ([NeverQuasiHaltsTr] quantifies over FIRED
    instructions).  Left-moving cyclers (side L) run the right-handed
    checker on [mirror_tm tm] and transfer through [neverqhtr_mirror]. *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape GTape Mirror
  ClosureTr.
From BBB4.Checkers Require Import Cycle TCycler.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.CensusTr Require Import TNF_QHTr.
Import ListNotations.

(** the instruction a guarded configuration fires is independent of
    the abstract far tape *)
Lemma glift_cinstr : forall rho g, instr_of (glift rho g) = cinstr g.
Proof. intros rho [q [[l h] r]]. reflexivity. Qed.

(** Does instruction [tg] fire among the [len] configurations of the
    guarded run from [g] (offsets 0 .. len-1)? *)
Fixpoint gfires (tm : TM) (g : cconf) (len : nat) (tg : Instr) : bool :=
  match len with
  | 0 => false
  | S m => instr_eqb (cinstr g) tg
           || match gstep tm g with
              | Some g' => gfires tm g' m tg
              | None => false
              end
  end.

Lemma gfires_sound : forall tm len g tg,
  gfires tm g len tg = true ->
  exists i gi, i < len /\ gsteps tm i g = Some gi /\ cinstr gi = tg.
Proof.
  induction len; intros g tg H; simpl in H.
  - discriminate.
  - apply orb_prop in H as [H | H].
    + exists 0, g. split; [lia|]. split; [reflexivity|].
      apply instr_eqb_spec; assumption.
    + destruct (gstep tm g) eqn:E; [|discriminate].
      destruct (IHlen _ _ H) as (i & gi & Hi & Hs & Hq).
      exists (S i), gi. split; [lia|]. split; [|assumption].
      simpl. rewrite E. assumption.
Qed.

Lemma gfires_complete : forall tm len g tg i gi,
  i < len -> gsteps tm i g = Some gi -> cinstr gi = tg ->
  gfires tm g len tg = true.
Proof.
  induction len; intros g tg i gi Hi Hs Hq.
  - lia.
  - simpl. destruct i.
    + simpl in Hs. injection Hs as <-.
      apply orb_true_intro; left. apply instr_eqb_spec; assumption.
    + simpl in Hs. destruct (gstep tm g) eqn:E; [|discriminate].
      apply orb_true_intro; right.
      eapply IHlen; eauto; lia.
Qed.

(** ** The checker *)

Definition tcycler_check_neverqhtr (tm : TM) (n1 P W : nat) : bool :=
  (0 <? P) &&
  match csteps tm n1 c0 with
  | Some (q1, (l1, h1, r1)) =>
      let g1 : cconf := (q1, (firstn_pad W l1, h1, r1)) in
      match gsteps tm P g1 with
      | Some g2 =>
          gmatch g1 g2 &&
          forallb (fun t => implb (cfires tm c0 (n1 + P) t)
                                  (gfires tm g1 P t)) all_Instr
      | None => false
      end
  | None => false
  end.

Theorem tcycler_check_neverqhtr_sound : forall tm n1 P W,
  tcycler_check_neverqhtr tm n1 P W = true -> NeverQuasiHaltsTr tm.
Proof.
  intros tm n1 P W H.
  unfold tcycler_check_neverqhtr in H.
  apply andb_prop in H as [Hp H].
  apply Nat.ltb_lt in Hp.
  destruct (csteps tm n1 c0) as [[q1 [[l1 h1] r1]]|] eqn:E1; [|discriminate].
  destruct (gsteps tm P (q1, (firstn_pad W l1, h1, r1))) as [g2|] eqn:E2;
    [|discriminate].
  apply andb_prop in H as [Hm Hsub].
  pose proof (anchor_instance tm n1 W q1 l1 h1 r1 E1) as HA.
  set (g1 := (q1, (firstn_pad W l1, h1, r1)) : cconf) in *.
  set (rho0 := fun n => nthb l1 (n + W)) in *.
  intros t Hft N.
  (* Step 1: t fires in the guarded window. *)
  assert (Hwin : exists i gi, i < P /\ gsteps tm i g1 = Some gi /\ cinstr gi = t).
  { destruct Hft as (n0 & cn & Hcn & Ht).
    destruct (le_lt_dec n1 n0) as [Hge | Hlt].
    - (* fold back into the window *)
      destruct (tcycler_fold tm n1 P g1 g2 rho0 Hp HA E2 Hm n0 Hge)
        as (i & gi & rho & Hi & Hgi & Hfold).
      rewrite Hfold in Hcn. injection Hcn as <-.
      exists i, gi. split; [exact Hi|]. split; [exact Hgi|].
      rewrite <- Ht. symmetry. apply glift_cinstr.
    - (* inside the simulated prefix: use the inclusion gate *)
      destruct (csteps_prefix tm n0 n1 c0 (q1, (l1, h1, r1)))
        as (cn' & Hcn' & _); [lia | exact E1 |].
      assert (Hlift : stepn tm n0 InitES = Some (lift cn')).
      { rewrite <- lift_c0. apply csteps_lift; assumption. }
      rewrite Hlift in Hcn. injection Hcn as <-.
      rewrite cinstr_lift in Ht.
      assert (Hf0 : cfires tm c0 (n1 + P) t = true).
      { eapply cfires_complete; [| exact Hcn' | exact Ht]. lia. }
      assert (Hf1 : gfires tm g1 P t = true).
      { rewrite forallb_forall in Hsub.
        specialize (Hsub t (all_Instr_complete t)).
        rewrite Hf0 in Hsub.
        destruct (gfires tm g1 P t); [reflexivity | discriminate]. }
      exact (gfires_sound _ _ _ _ Hf1). }
  (* Step 2: pump the window occurrence past N. *)
  destruct Hwin as (i & gi & Hi & Hgi & Ht).
  destruct (tcycler_laps tm n1 P g1 g2 rho0 HA E2 Hm N) as [rho Hrho].
  exists (n1 + N * P + i).
  split. { nia. }
  exists (glift rho gi). split.
  - replace (n1 + N * P + i) with ((n1 + N * P) + i) by lia.
    rewrite stepn_add, Hrho.
    apply gsteps_lift; exact Hgi.
  - rewrite glift_cinstr. exact Ht.
Qed.

(** ** Mirrored (side-L) corollary *)

Corollary tcycler_check_neverqhtr_sound_L : forall tm n1 P W,
  tcycler_check_neverqhtr (mirror_tm tm) n1 P W = true ->
  NeverQuasiHaltsTr tm.
Proof.
  intros. apply neverqhtr_mirror.
  eapply tcycler_check_neverqhtr_sound; eauto.
Qed.

Corollary tcycler_check_neverqhtr_nonhalt : forall tm n1 P W,
  tcycler_check_neverqhtr tm n1 P W = true -> NonHalt tm.
Proof.
  intros. apply never_qh_tr_nonhalt.
  eapply tcycler_check_neverqhtr_sound; eauto.
Qed.
