From Coq Require Import Arith Lia Bool List NArith.
From BBB24 Require Import Statement StatementTr CTape GTape Mirror Instructions Bounds.
From BBB24.Checkers Require Import Cycle TCycler.
Import ListNotations.
Section Parameters.
Variables bs bi : N.

Fixpoint gtrace tm p g : list cconf :=
  match p with
  | 0 => []
  | S k => g :: match gstep tm g with Some g' => gtrace tm k g' | None => [] end
  end.

Lemma gtrace_spec : forall tm p g gi,
  In gi (gtrace tm p g) <-> exists i, i < p /\ gsteps tm i g = Some gi.
Proof.
  intros tm p. induction p as [|p IH]; intros g gi; simpl.
  - split; [tauto|intros (i & Hi & _); lia].
  - split.
    + intros [E|H].
      * subst gi. exists 0. split; [lia|reflexivity].
      * destruct (gstep tm g) as [g'|] eqn:E; [|contradiction].
        apply IH in H as (i & Hi & Hr). exists (S i). split; [lia|]. simpl. rewrite E. exact Hr.
    + intros ([|i] & Hi & Hr).
      * simpl in Hr. injection Hr as <-. left; reflexivity.
      * right. simpl in Hr. destruct (gstep tm g) as [g'|] eqn:E; [|discriminate].
        apply IH. exists i. split; [lia|exact Hr].
Qed.

Definition tc_tail tm t p W : option (list cconf) :=
  if 0 <? p then
    match csteps tm t c0 with
    | Some (q,(l,h,r)) =>
      let g := (q,(firstn_pad W l,h,r)) in
      match gsteps tm p g with
      | Some g' => if gmatch g g' then Some (gtrace tm p g) else None
      | None => None
      end
    | None => None
    end
  else None.

Definition Tail tm t Sl :=
  (forall s tg, t <= s -> FiresAt tm tg s -> tail_instrs Sl tg = true) /\
  (forall tg, tail_instrs Sl tg = true -> forall N,
    exists k, N <= k /\ FiresAt tm tg k).

Lemma glift_instr : forall rho g, instr_of (glift rho g) = cinstr g.
Proof. intros rho [q [[l h] r]]. reflexivity. Qed.

Theorem tc_tail_sound : forall tm t p W Sl,
  tc_tail tm t p W = Some Sl -> NonHalt tm /\ Tail tm t Sl.
Proof.
  intros tm t p W Sl H. unfold tc_tail in H.
  destruct (0 <? p) eqn:Hp; [apply Nat.ltb_lt in Hp|discriminate].
  destruct (csteps tm t c0) as [[q [[l h] r]]|] eqn:Et; [|discriminate].
  set (g := (q,(firstn_pad W l,h,r)) : cconf) in *.
  destruct (gsteps tm p g) as [g'|] eqn:Eg; [|discriminate].
  destruct (gmatch g g') eqn:Em; [|discriminate].
  injection H as <-.
  pose proof (anchor_instance tm t W q l h r Et) as Ha.
  set (rho0 := fun n => nthb l (n+W)) in *.
  assert (Hfold : forall s, t <= s -> exists i gi rho,
    i < p /\ gsteps tm i g = Some gi /\ stepn tm s InitES = Some (glift rho gi)).
  { exact (tcycler_fold tm t p g g' rho0 Hp Ha Eg Em). }
  split.
  - intros s Hnone. destruct (le_lt_dec t s).
    + destruct (Hfold s l0) as (i & gi & rho & _ & _ & Hr). congruence.
    + destruct (stepn_prefix tm s t InitES (glift rho0 g) ltac:(lia) Ha)
        as (c & Hr & _). congruence.
  - split.
    + intros s tg Hts (c & Hr & Htg).
      destruct (Hfold s Hts) as (i & gi & rho & Hi & Hgi & Hrun).
      rewrite Hrun in Hr. injection Hr as <-.
      apply existsb_exists. exists gi. split.
      * apply gtrace_spec. exists i. auto.
      * apply instr_eqb_spec. rewrite <- (glift_instr rho gi). exact Htg.
    + intros tg Htg N. apply existsb_exists in Htg as (gi & Hin & He).
      apply instr_eqb_spec in He. apply gtrace_spec in Hin as (i & Hi & Hgi).
      destruct (tcycler_laps tm t p g g' rho0 Ha Eg Em N) as (rho & Hr).
      exists (t+N*p+i). split; [nia|]. exists (glift rho gi). split.
      * rewrite stepn_add, Hr. apply gsteps_lift; exact Hgi.
      * rewrite glift_instr. exact He.
Qed.

Definition tc_check tm t p W :=
  match tc_tail tm t p W with
  | Some Sl => prefix_gate bs bi tm t (tail_states Sl) (tail_instrs Sl)
  | None => false
  end.

Theorem tc_check_sound : forall tm t p W,
  tc_check tm t p W = true -> NonHalt tm /\ Bounds bs bi tm.
Proof.
  intros tm t p W H. unfold tc_check in H.
  destruct (tc_tail tm t p W) as [Sl|] eqn:E; [|discriminate].
  destruct (tc_tail_sound tm t p W Sl E) as [Hnh [Hcov Hrec]].
  split; [exact Hnh|]. eapply (tail_bounds bs bi); eauto.
Qed.

Lemma mirror_fires : forall tm tg n,
  FiresAt (mirror_tm tm) tg n <-> FiresAt tm tg n.
Proof.
  intros tm tg n. split; intros (c & Hr & Hi).
  - rewrite mirror_stepn_init in Hr.
    destruct (stepn tm n InitES) as [c'|] eqn:E; [|discriminate].
    injection Hr as <-. exists c'. split; [exact E|exact Hi].
  - exists (mirror_es c). split; [|exact Hi]. rewrite mirror_stepn_init, Hr. reflexivity.
Qed.

Lemma mirror_bounds : forall tm, Bounds bs bi (mirror_tm tm) -> Bounds bs bi tm.
Proof.
  intros tm [Hs Hi]. split.
  - intros q s [Hv Hquiet]. apply (Hs q s). split.
    + apply mirror_visits; exact Hv.
    + intros n Hn Hv'. apply (Hquiet n Hn). apply mirror_visits; exact Hv'.
  - intros tg s [Hv Hquiet]. apply (Hi tg s). split.
    + apply mirror_fires; exact Hv.
    + intros n Hn Hv'. apply (Hquiet n Hn). apply mirror_fires; exact Hv'.
Qed.

Definition cycle_check tm (mirrored : bool) t p W :=
  tc_check (if mirrored then mirror_tm tm else tm) t p W.
Theorem cycle_check_sound : forall tm mirrored t p W,
  cycle_check tm mirrored t p W = true -> NonHalt tm /\ Bounds bs bi tm.
Proof.
  intros tm [] t p W H; apply tc_check_sound in H; [|exact H].
  destruct H as [Hnh Hb]. split; [apply mirror_nonhalt|apply mirror_bounds]; assumption.
Qed.

End Parameters.
