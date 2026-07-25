(** * WLS_0RB0LC_1LC1RB_1RD1LA_0LB1RD: wall-lap interleaved counter, machine 0RB0LC_1LC1RB_1RD1LA_0LB1RD.

    Auto-emitted by tools/counters/emit_wall.py (UNTRUSTED emitter; the Coq
    kernel re-checks every line below).  Left-growth counter under the
    DIRECT interleave encoding [Ip], holding a fixed WALL on the far side
    (WALLLAP_NOTE.md; WAVE11_MIRROR.md section 2):

      Cc p = (StB, (Ip p ++ [S1;S0], S0, [S1;S0]))

    One lap crosses the wall, blanks it, ripples the carry, returns, and
    REBUILDS the wall:

      P1w  bounce through the wall (3 steps, right-open window);
      RIP  leftward 1-cell ripple (1 step per cell; 2j+2 cells
           interior, 2j'+3 overflow);
      STPI/TRN  pop the clear bit and turn (interior);
      STPO overflow stop at the deep edge (2 steps);
      RET  rightward rewrite [S1;S1] -> [S0;S1] (2 steps per pair;
           j+1 pairs interior, j'+1 overflow);
      FINw interior close rebuilding the wall (3 steps, EXACT) /
      FINw2 overflow close (5 steps; lands one left blank and one
           far blank short of the next anchor -- a [lift] close).

    The interior branch is EXACT, feeding the [tovf] well-founded
    induction that carries every deep visit witness to an overflow anchor.
    Derived by exact symbolic replay; validated against the raw simulator
    on BOTH cview branches (interior p = 2..199, overflow K = 1..7, step
    counts AND landings).  Axiom footprint:
    [functional_extensionality_dep] (via CTape.lift). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ILCounter JpCounter.
Import ListNotations.

Definition mk_0RB0LC_1LC1RB_1RD1LA_0LB1RD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB0LC_1LC1RB_1RD1LA_0LB1RD.

(** 0RB0LC_1LC1RB_1RD1LA_0LB1RD *)
(** 0RB0LC_1LC1RB_1RD1LA_0LB1RD -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB0LC_1LC1RB_1RD1LA_0LB1RD : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S0 DL StC
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S0 DL StB | StD, S1 => mk S1 DR StD end.

(** Its mirror 0LB0RC_1RC1LB_1LD1RA_0RB1LD: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB0LC_1LC1RB_1RD1LA_0LB1RD : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S0 DR StC
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S1 DL StD | StC, S1 => mk S1 DR StA
  | StD, S0 => mk S0 DR StB | StD, S1 => mk S1 DL StD end.
Local Notation tm := tmm_0RB0LC_1LC1RB_1RD1LA_0LB1RD.

Lemma mirror_ok_0RB0LC_1LC1RB_1RD1LA_0LB1RD : mirror_tm tm_0RB0LC_1LC1RB_1RD1LA_0LB1RD = tmm_0RB0LC_1LC1RB_1RD1LA_0LB1RD.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_0RB0LC_1LC1RB_1RD1LA_0LB1RD (p : positive) : cconf := (StB, (Ip p ++ [S1;S0], S0, [S1;S0])).
Local Notation Cc := Cc_0RB0LC_1LC1RB_1RD1LA_0LB1RD.

(** ** The window units (each closed by [reflexivity]) *)
Lemma U_P1w_0RB0LC_1LC1RB_1RD1LA_0LB1RD : wsteps true false tm 3 (StB,([],S0,[S1;S0])) = Some (StB,([S1],S1,[S0])). Proof. reflexivity. Qed.
Lemma U_RIP_0RB0LC_1LC1RB_1RD1LA_0LB1RD : wsteps true true tm 1 (StB,([S1],S1,[])) = Some (StB,([],S1,[S1])). Proof. reflexivity. Qed.
Lemma U_STPI_0RB0LC_1LC1RB_1RD1LA_0LB1RD : wsteps true true tm 1 (StB,([S0],S1,[])) = Some (StB,([],S0,[S1])). Proof. reflexivity. Qed.
Lemma U_TRN_0RB0LC_1LC1RB_1RD1LA_0LB1RD : wsteps true true tm 1 (StB,([],S0,[S1])) = Some (StC,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_RET_0RB0LC_1LC1RB_1RD1LA_0LB1RD : wsteps true true tm 2 (StC,([],S1,[S1;S1])) = Some (StC,([S0;S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FINw_0RB0LC_1LC1RB_1RD1LA_0LB1RD : wsteps true false tm 3 (StC,([S0],S1,[S0])) = Some (StB,([],S0,[S1;S0])). Proof. reflexivity. Qed.
Lemma U_STPO_0RB0LC_1LC1RB_1RD1LA_0LB1RD : wsteps false true tm 2 (StB,([S0],S1,[])) = Some (StC,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FINw2_0RB0LC_1LC1RB_1RD1LA_0LB1RD : wsteps true false tm 5 (StC,([],S1,S1::[S0])) = Some (StB,([S1],S0,[S1])). Proof. reflexivity. Qed.
Lemma U_VP1_0RB0LC_1LC1RB_1RD1LA_0LB1RD : wsteps true false tm 2 (StB,([],S0,[S1;S0])) = Some (StA,([S1;S1],S0,[])). Proof. reflexivity. Qed.
Lemma U_VP2_0RB0LC_1LC1RB_1RD1LA_0LB1RD : wsteps true false tm 1 (StB,([],S0,[S1;S0])) = Some (StC,([S1],S1,[S0])). Proof. reflexivity. Qed.
Lemma U_VF1_0RB0LC_1LC1RB_1RD1LA_0LB1RD : wsteps true false tm 3 (StC,([],S1,S1::[S0])) = Some (StD,([S1],S0,[S1])). Proof. reflexivity. Qed.

(** ** Transported phases *)
Lemma phP1w_0RB0LC_1LC1RB_1RD1LA_0LB1RD : forall L, csteps tm 3 (StB,(L,S0,[S1;S0])) = Some (StB,(S1::L,S1,[S0])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U_P1w_0RB0LC_1LC1RB_1RD1LA_0LB1RD). Qed.
Lemma phRIP_0RB0LC_1LC1RB_1RD1LA_0LB1RD : forall k L R, csteps tm (1*k) (StB,(rep [S1] k ++ L,S1,R)) = Some (StB,(L,S1,rep [S1] k ++ R)).
Proof. intros. pose proof (cycL _ _ _ _ _ _ _ U_RIP_0RB0LC_1LC1RB_1RD1LA_0LB1RD k L R) as H; cbn [app] in H; exact H. Qed.
Lemma phSTPI_0RB0LC_1LC1RB_1RD1LA_0LB1RD : forall L R, csteps tm 1 (StB,(S0::L,S1,R)) = Some (StB,(L,S0,S1::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STPI_0RB0LC_1LC1RB_1RD1LA_0LB1RD). Qed.
Lemma phTRN_0RB0LC_1LC1RB_1RD1LA_0LB1RD : forall L R, csteps tm 1 (StB,(L,S0,S1::R)) = Some (StC,(S1::L,S1,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_TRN_0RB0LC_1LC1RB_1RD1LA_0LB1RD). Qed.
Lemma phRET_0RB0LC_1LC1RB_1RD1LA_0LB1RD : forall k L R, csteps tm (2*k) (StC,(L,S1,rep [S1;S1] k ++ R)) = Some (StC,(rep [S0;S1] k ++ L,S1,R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U_RET_0RB0LC_1LC1RB_1RD1LA_0LB1RD k L R). Qed.
Lemma phFINw_0RB0LC_1LC1RB_1RD1LA_0LB1RD : forall L, csteps tm 3 (StC,(S0::L,S1,[S0])) = Some (StB,(L,S0,[S1;S0])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U_FINw_0RB0LC_1LC1RB_1RD1LA_0LB1RD). Qed.
Lemma phSTPO_0RB0LC_1LC1RB_1RD1LA_0LB1RD : forall R, csteps tm 2 (StB,([S0],S1,R)) = Some (StC,([S1],S1,R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPO_0RB0LC_1LC1RB_1RD1LA_0LB1RD). Qed.
Lemma phFINw2_0RB0LC_1LC1RB_1RD1LA_0LB1RD : forall L, csteps tm 5 (StC,(L,S1,S1::[S0])) = Some (StB,(S1::L,S0,[S1])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U_FINw2_0RB0LC_1LC1RB_1RD1LA_0LB1RD). Qed.
Lemma phVP1_0RB0LC_1LC1RB_1RD1LA_0LB1RD : forall L, csteps tm 2 (StB,(L,S0,[S1;S0])) = Some (StA,(S1::S1::L,S0,[])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U_VP1_0RB0LC_1LC1RB_1RD1LA_0LB1RD). Qed.
Lemma phVP2_0RB0LC_1LC1RB_1RD1LA_0LB1RD : forall L, csteps tm 1 (StB,(L,S0,[S1;S0])) = Some (StC,(S1::L,S1,[S0])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U_VP2_0RB0LC_1LC1RB_1RD1LA_0LB1RD). Qed.
Lemma phVF1_0RB0LC_1LC1RB_1RD1LA_0LB1RD : forall L, csteps tm 3 (StC,(L,S1,S1::[S0])) = Some (StD,(S1::L,S0,[S1])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U_VF1_0RB0LC_1LC1RB_1RD1LA_0LB1RD). Qed.

Lemma lift_lblank_0RB0LC_1LC1RB_1RD1LA_0LB1RD : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

(** ** The OUTER interior lap: EXACT *)
Lemma lap_int_0RB0LC_1LC1RB_1RD1LA_0LB1RD : forall p j q0, cview p = (j, Some q0) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p j q0 Ecv. unfold Cc_0RB0LC_1LC1RB_1RD1LA_0LB1RD.
  destruct (cview_some_I p j q0 Ecv) as (HIp & HIs).
  do 2 eexists. split; [|split].
  + rewrite HIp, <- app_assoc. cbn [app].
    rewrite rep_dbl.
    eapply csteps_chain. { apply phP1w_0RB0LC_1LC1RB_1RD1LA_0LB1RD. }
    rewrite rep_slide, <- rep_dbl, pair_fold, rep_dbl.
    replace (2 * S j) with (S (S (2 * j))) by lia.
    eapply csteps_chain. { apply (phRIP_0RB0LC_1LC1RB_1RD1LA_0LB1RD (S (S (2 * j)))). }
    eapply csteps_chain. { apply phSTPI_0RB0LC_1LC1RB_1RD1LA_0LB1RD. }
    eapply csteps_chain. { apply phTRN_0RB0LC_1LC1RB_1RD1LA_0LB1RD. }
    change (rep [S1] (S (S (2 * j))) ++ [S0])
      with (S1 :: S1 :: rep [S1] (2 * j) ++ [S0]).
    rewrite <- rep_dbl.
    change (S1 :: S1 :: rep [S1;S1] j ++ [S0])
      with (rep [S1;S1] (S j) ++ [S0]).
    eapply csteps_chain. { apply (phRET_0RB0LC_1LC1RB_1RD1LA_0LB1RD (S j)). }
    change (rep [S0;S1] (S j) ++ S1 :: (Ip q0 ++ [S1;S0]))
      with (S0 :: S1 :: rep [S0;S1] j ++ S1 :: (Ip q0 ++ [S1;S0])).
    apply phFINw_0RB0LC_1LC1RB_1RD1LA_0LB1RD.
  + rewrite HIs, <- app_assoc. cbn [app].
    change (rep [S1;S0] j ++ S1 :: S1 :: (Ip q0 ++ [S1;S0]))
      with (rep [S1;S0] j ++ [S1] ++ (S1 :: (Ip q0 ++ [S1;S0]))).
    rewrite app_assoc, pair_rot. reflexivity.
  + lia.
Qed.

(** ** The overflow lap: closes one left blank and one far blank short *)
Lemma lap_ov_0RB0LC_1LC1RB_1RD1LA_0LB1RD : forall p j', cview p = (S j', None) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j' Ecv. unfold Cc_0RB0LC_1LC1RB_1RD1LA_0LB1RD.
  destruct (cview_none_I p j' Ecv) as (HIp & HIs).
  do 2 eexists. split; [|split].
  + rewrite HIp, <- app_assoc. cbn [app].
    rewrite rep_dbl.
    eapply csteps_chain. { apply phP1w_0RB0LC_1LC1RB_1RD1LA_0LB1RD. }
    rewrite rep_slide, <- rep_dbl, pair_fold, rep_dbl.
    replace (2 * S j') with (S (S (2 * j'))) by lia.
    rewrite <- rep_slide.
    change (S1 :: rep [S1] (S (S (2 * j'))) ++ [S0])
      with (rep [S1] (S (S (S (2 * j')))) ++ [S0]).
    eapply csteps_chain. { apply (phRIP_0RB0LC_1LC1RB_1RD1LA_0LB1RD (S (S (S (2 * j'))))). }
    eapply csteps_chain. { apply phSTPO_0RB0LC_1LC1RB_1RD1LA_0LB1RD. }
    replace (S (S (S (2 * j')))) with (2 * S j' + 1) by lia.
    rewrite rep_add, <- app_assoc, <- rep_dbl. cbn [rep app].
    eapply csteps_chain. { apply (phRET_0RB0LC_1LC1RB_1RD1LA_0LB1RD (S j')). }
    apply phFINw2_0RB0LC_1LC1RB_1RD1LA_0LB1RD.
  + rewrite HIs, pair_rot.
    replace ([S1;S0]) with ([S1] ++ [S0]) by reflexivity.
    rewrite lift_app_blank. cbn [app].
    replace (S1 :: rep [S0;S1] (S j') ++ S1 :: S0 :: nil)
      with ((S1 :: rep [S0;S1] (S j') ++ [S1]) ++ [S0])
      by (cbn [app]; rewrite <- app_assoc; reflexivity).
    rewrite lift_lblank_0RB0LC_1LC1RB_1RD1LA_0LB1RD. reflexivity.
  + lia.
Qed.

Lemma lap_0RB0LC_1LC1RB_1RD1LA_0LB1RD : forall p, exists n c', csteps tm n (Cc p) = Some c' /\
  lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - destruct (lap_int_0RB0LC_1LC1RB_1RD1LA_0LB1RD p j q0 Ecv) as (n & c' & H1 & H2 & H3).
    exists n, c'. split; [exact H1|split; [rewrite H2; reflexivity|exact H3]].
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    exact (lap_ov_0RB0LC_1LC1RB_1RD1LA_0LB1RD p j' Ecv).
Qed.

Lemma boot_0RB0LC_1LC1RB_1RD1LA_0LB1RD : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 12.
  assert (H : match csteps tm 12 c0 with Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 12 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits *)

(** StA: 2 steps from the anchor, inside the P1w window (uniform in p). *)
Lemma vis_A1_0RB0LC_1LC1RB_1RD1LA_0LB1RD : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StA.
Proof.
  intro p. unfold Cc_0RB0LC_1LC1RB_1RD1LA_0LB1RD. exists 2. eexists. split.
  - apply phVP1_0RB0LC_1LC1RB_1RD1LA_0LB1RD.
  - reflexivity.
Qed.

(** StC: 1 steps from the anchor, inside the P1w window (uniform in p). *)
Lemma vis_A2_0RB0LC_1LC1RB_1RD1LA_0LB1RD : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StC.
Proof.
  intro p. unfold Cc_0RB0LC_1LC1RB_1RD1LA_0LB1RD. exists 1. eexists. split.
  - apply phVP2_0RB0LC_1LC1RB_1RD1LA_0LB1RD.
  - reflexivity.
Qed.

(** StD: reached inside the OVERFLOW lap; every p reduces to an
    all-ones anchor by well-founded induction on [tovf] (the interior
    laps close EXACTLY). *)
Lemma vis_D1_0RB0LC_1LC1RB_1RD1LA_0LB1RD : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StD.
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }
    destruct (lap_int_0RB0LC_1LC1RB_1RD1LA_0LB1RD p j q0 Ecv) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia)) (Pos.succ p) eq_refl) as (k & c & Hk & Hq).
    exists (n + k), c. rewrite csteps_add, Hrun. exact (conj Hk Hq).
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_I p j' Ecv) as (HIp & _).
    unfold Cc_0RB0LC_1LC1RB_1RD1LA_0LB1RD. eexists. eexists. split.
    + rewrite HIp, <- app_assoc. cbn [app].
      rewrite rep_dbl.
      eapply csteps_chain. { apply phP1w_0RB0LC_1LC1RB_1RD1LA_0LB1RD. }
      rewrite rep_slide, <- rep_dbl, pair_fold, rep_dbl.
      replace (2 * S j') with (S (S (2 * j'))) by lia.
      rewrite <- rep_slide.
      change (S1 :: rep [S1] (S (S (2 * j'))) ++ [S0])
        with (rep [S1] (S (S (S (2 * j')))) ++ [S0]).
      eapply csteps_chain. { apply (phRIP_0RB0LC_1LC1RB_1RD1LA_0LB1RD (S (S (S (2 * j'))))). }
      eapply csteps_chain. { apply phSTPO_0RB0LC_1LC1RB_1RD1LA_0LB1RD. }
      replace (S (S (S (2 * j')))) with (2 * S j' + 1) by lia.
      rewrite rep_add, <- app_assoc, <- rep_dbl. cbn [rep app].
      eapply csteps_chain. { apply (phRET_0RB0LC_1LC1RB_1RD1LA_0LB1RD (S j')). }
      apply phVF1_0RB0LC_1LC1RB_1RD1LA_0LB1RD.
    + reflexivity.
Qed.

Lemma vis_0RB0LC_1LC1RB_1RD1LA_0LB1RD : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q. destruct q.
  - apply vis_A1_0RB0LC_1LC1RB_1RD1LA_0LB1RD.
  - (* StB : the anchor state *)
    exists 0. eexists. split; reflexivity.
  - apply vis_A2_0RB0LC_1LC1RB_1RD1LA_0LB1RD.
  - apply vis_D1_0RB0LC_1LC1RB_1RD1LA_0LB1RD.
Qed.

Theorem nqhm_0RB0LC_1LC1RB_1RD1LA_0LB1RD : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 1). - exact boot_0RB0LC_1LC1RB_1RD1LA_0LB1RD. - intros p _. apply lap_0RB0LC_1LC1RB_1RD1LA_0LB1RD. - intros p q _. apply vis_0RB0LC_1LC1RB_1RD1LA_0LB1RD. Qed.

Theorem nqh_0RB0LC_1LC1RB_1RD1LA_0LB1RD : NeverQuasiHaltsSt tm_0RB0LC_1LC1RB_1RD1LA_0LB1RD.
Proof. apply (mirror_never_qh tm_0RB0LC_1LC1RB_1RD1LA_0LB1RD). rewrite mirror_ok_0RB0LC_1LC1RB_1RD1LA_0LB1RD. exact nqhm_0RB0LC_1LC1RB_1RD1LA_0LB1RD. Qed.

Theorem nonhalt_0RB0LC_1LC1RB_1RD1LA_0LB1RD : NonHalt tm_0RB0LC_1LC1RB_1RD1LA_0LB1RD.
Proof. apply never_qh_nonhalt, nqh_0RB0LC_1LC1RB_1RD1LA_0LB1RD. Qed.
