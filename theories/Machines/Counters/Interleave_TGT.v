(** * Interleave_TGT: first interleaved-counter board via the Jp emitter template.

    Machine 0RB---_0LC1RB_1LA1LD_1LC0RB (a wave-8 resistant counter core rep).
    Comb-free interleaved binary counter under the complemented [Jp] encoding
    (JpCounter.v).  This is the hand-authored template the auto-emitter clones
    per machine: [tm_T] table, the 6 unit windows (reflexivity), phase wrappers,
    the single-sweep lap, boot (vm_compute), the all-state-visit witnesses, and
    the [glue_neverqh] call. *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ILCounter JpCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).

Definition tm_T : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => None
  | StB, S0 => mk S0 DL StC | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S1 DL StA | StC, S1 => mk S1 DL StD
  | StD, S0 => mk S1 DL StC | StD, S1 => mk S0 DR StB end.

Definition Cc (p : positive) : cconf := (StB, (Jp p ++ [S0], S0, [])).

(* --- the 6 lap unit windows + the vis-A unit --- *)
Lemma U_P1 : wsteps true true tm_T 1 (StB,([S1],S0,[])) = Some (StC,([],S1,[S0])). Proof. reflexivity. Qed.
Lemma U_RIP: wsteps true true tm_T 2 (StC,([S0;S1],S1,[])) = Some (StC,([],S1,[S1;S1])). Proof. reflexivity. Qed.
Lemma U_STPI: wsteps true true tm_T 2 (StC,([S1;S1],S1,[])) = Some (StB,([S0;S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_STPO: wsteps false true tm_T 4 (StC,([S0],S1,[])) = Some (StB,([S0],S1,[S1;S1])). Proof. reflexivity. Qed.
Lemma U_RET: wsteps true true tm_T 1 (StB,([],S1,[S1])) = Some (StB,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FIN: wsteps true true tm_T 1 (StB,([],S1,[S0])) = Some (StB,([S1],S0,[])). Proof. reflexivity. Qed.
Lemma U_VA : wsteps false true tm_T 3 (StC,([S0],S1,[])) = Some (StA,([],S0,[S1;S1;S1])). Proof. reflexivity. Qed.

(* --- transported phases (framing = each unit's bl/br) --- *)
Lemma phP1 : forall L R, csteps tm_T 1 (StB,(S1::L,S0,R)) = Some (StC,(L,S1,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_P1). Qed.
Lemma phRIP : forall k L R, csteps tm_T (2*k) (StC,(rep [S0;S1] k ++ L,S1,R)) = Some (StC,(L,S1,rep [S1;S1] k ++ R)).
Proof. intros. pose proof (cycL _ _ _ _ _ _ _ U_RIP k L R) as H; cbn [app] in H; exact H. Qed.
Lemma phSTPI : forall L R, csteps tm_T 2 (StC,(S1::S1::L,S1,R)) = Some (StB,(S0::S1::L,S1,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STPI). Qed.
Lemma phSTPO : forall R, csteps tm_T 4 (StC,([S0],S1,R)) = Some (StB,([S0],S1,S1::S1::R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPO). Qed.
Lemma phRET : forall k L R, csteps tm_T (1*k) (StB,(L,S1,rep [S1] k ++ R)) = Some (StB,(rep [S1] k ++ L,S1,R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U_RET k L R). Qed.
Lemma phFIN : forall L R, csteps tm_T 1 (StB,(L,S1,S0::R)) = Some (StB,(S1::L,S0,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FIN). Qed.
Lemma phVA : forall R, csteps tm_T 3 (StC,([S0],S1,R)) = Some (StA,([],S0,S1::S1::S1::R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_VA). Qed.

(* EXACT lap (no lift): iterate to the next anchor with the exact config. *)
Lemma lap_exact : forall p, exists n c', csteps tm_T n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p. pose proof (Pos2Nat.is_pos p) as Hpos.
  destruct (cview p) as [j oq] eqn:Ecv. unfold Cc.
  destruct oq as [q0|].
  - destruct (cview_some_J p j q0 Ecv) as (HJp & HJs). destruct (Jp_head q0) as (iq & Hiq).
    do 2 eexists. split; [|split].
    + rewrite HJp, <- app_assoc.
      change (rep [S1;S0] j ++ (S1 :: S1 :: Jp q0) ++ [S0])
        with (rep [S1;S0] j ++ [S1] ++ (S1 :: Jp q0 ++ [S0])).
      rewrite app_assoc, pair_rot.
      eapply csteps_chain. { apply phP1. }
      eapply csteps_chain. { apply phRIP. }
      rewrite Hiq.
      eapply csteps_chain. { apply phSTPI. }
      rewrite rep_dbl.
      eapply csteps_chain. { apply (phRET (2*j)). }
      apply phFIN.
    + rewrite HJs, Hiq, rep_dbl. cbn [Nat.mul]. rewrite rep_slide, <- !app_assoc. reflexivity.
    + lia.
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_J p j' Ecv) as (HJp & HJs).
    do 2 eexists. split; [|split].
    + rewrite HJp, pair_rot.
      eapply csteps_chain. { apply phP1. }
      eapply csteps_chain. { apply phRIP. }
      eapply csteps_chain. { apply phSTPO. }
      change (S1 :: S1 :: rep [S1;S1] j' ++ [S0]) with (rep [S1;S1] (S j') ++ [S0]).
      rewrite rep_dbl.
      eapply csteps_chain. { apply (phRET (2*(S j'))). }
      apply phFIN.
    + rewrite HJs, rep_dbl. cbn [Nat.mul]. rewrite rep_slide, <- !app_assoc. reflexivity.
    + lia.
Qed.

Lemma lap_T : forall p, exists n c', csteps tm_T n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof. intro p. destruct (lap_exact p) as (n & c' & Hr & Hc & Hn). exists n, c'.
  split; [exact Hr | split; [rewrite Hc; reflexivity | exact Hn]]. Qed.

Lemma boot_T : exists t0, stepn tm_T t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 5.
  assert (H : match csteps tm_T 5 c0 with Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm_T 5 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

Lemma vis_A : forall p, exists k c, csteps tm_T k (Cc p) = Some c /\ fst c = StA.
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }
    destruct (lap_exact p) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia)) (Pos.succ p) eq_refl) as (k & c & Hk & Hq).
    exists (n + k), c. rewrite csteps_add, Hrun. exact (conj Hk Hq).
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_J p j' Ecv) as (HJp & _).
    unfold Cc. eexists. eexists. split.
    * rewrite HJp, pair_rot.
      eapply csteps_chain. { apply phP1. }
      eapply csteps_chain. { apply phRIP. }
      apply phVA.
    * reflexivity.
Qed.

(* Two steps from an anchor visit StD (phP1 into StC head-S1, then C1=1LD). *)
Lemma phBD : forall x L R, csteps tm_T 2 (StB, (S1 :: x :: L, S0, R)) = Some (StD, (L, x, [S1;S0] ++ R)).
Proof. intros. reflexivity. Qed.

Lemma vis_T : forall p q, exists k c, csteps tm_T k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q. destruct (Jp_head p) as (w & Hw). unfold Cc. destruct q.
  - apply (vis_A p).
  - exists 0. eexists. split; reflexivity.
  - exists 1. eexists. rewrite Hw. split; [apply phP1 | reflexivity].
  - rewrite Hw. destruct w as [|x w'].
    + exists 2. eexists. split; [ vm_compute; reflexivity | reflexivity ].
    + exists 2. eexists. split.
      * change ((S1 :: x :: w') ++ [S0]) with (S1 :: x :: (w' ++ [S0])). apply phBD.
      * reflexivity.
Qed.

Theorem nqh_0RB_0LC1RB_1LA1LD_1LC0RB : NeverQuasiHaltsSt tm_T.
Proof. apply (glue_neverqh tm_T Cc 1). - exact boot_T. - intros p _. apply lap_T. - intros p q _. apply vis_T. Qed.

Theorem tm_T_nonhalt : NonHalt tm_T.
Proof. apply never_qh_nonhalt, nqh_0RB_0LC1RB_1LA1LD_1LC0RB. Qed.
