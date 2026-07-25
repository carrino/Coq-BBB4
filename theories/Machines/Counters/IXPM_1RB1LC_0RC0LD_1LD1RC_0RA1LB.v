(** * IXP_1RB1LC_0RC0LD_1LD1RC_0RA1LB: exponential-overflow interleaved
    counter, machine 1RB1LC_0RC0LD_1LD1RC_0RA1LB.

    Auto-emitted by tools/counters/emit_ixp.py (UNTRUSTED emitter; the Coq
    kernel re-checks every line below), cloning the hand-authored reference
    board IXP_1RB1LA_0LA1RC_0LD0RB_0LA1RD.v (WAVE11_MIRROR.md section 3).
    Interior laps are the affine flip chain (ILS4F); the OVERFLOW lap
    2^K-1 -> 2^K runs an INNER interleaved counter: anchors

      Cc p  = (StA, (Ip p ++ [S1;S0], S0, [S0]))
      Cin v = (StC, (Ip v ++ [S1], S0, [S1;S0]))

    march v = 2^(K-1) .. 2^K-1 with affine interior-only inner laps (the
    same RIP/STPI/TRN/RET units as the outer chain; only the frontier
    windows P1i/FINi differ):

      boot (affine)  :  Cc (2^K-1)  ->  Cin (2^(K-1))
      inner counting :  Cin v -> Cin (v+1), composed to the all-ones fill
                        by well-founded induction on [tovf]
      exit (affine)  :  Cin (2^K-1) ->  Cc (2^K), up to a lift close

    -- a SECOND instantiation of the lap machinery nested inside the outer
    overflow branch; [glue_neverqh] never sees the difference.  The three
    positive gadgets connecting the levels ([pow2], [fill],
    [cview_none_shape]) live in BBB4.Counters.IXPGadgets.

    Every chain was differentially validated against the raw simulator
    (interior p = 2..199, inner v = 2..299, boot j' = 0..7, exit K = 1..8,
    and the composed outer overflow step-exactly for K = 1..7).
    Axiom footprint: [functional_extensionality_dep] (via CTape.lift). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ILCounter JpCounter IXPGadgets.
Import ListNotations.

Definition mk_1RB1LC_0RC0LD_1LD1RC_0RA1LB (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1LC_0RC0LD_1LD1RC_0RA1LB.

(** 1RB1LC_0RC0LD_1LD1RC_0RA1LB *)
(** 1RB1LC_0RC0LD_1LD1RC_0RA1LB -- the real machine (its counter grows RIGHT). *)
Definition tm_1RB1LC_0RC0LD_1LD1RC_0RA1LB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StC
  | StB, S0 => mk S0 DR StC | StB, S1 => mk S0 DL StD
  | StC, S0 => mk S1 DL StD | StC, S1 => mk S1 DR StC
  | StD, S0 => mk S0 DR StA | StD, S1 => mk S1 DL StB end.

(** Its mirror 1LB1RC_0LC0RD_1RD1LC_0LA1RB: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_1RB1LC_0RC0LD_1LD1RC_0RA1LB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => mk S1 DR StC
  | StB, S0 => mk S0 DL StC | StB, S1 => mk S0 DR StD
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S1 DL StC
  | StD, S0 => mk S0 DL StA | StD, S1 => mk S1 DR StB end.
Local Notation tm := tmm_1RB1LC_0RC0LD_1LD1RC_0RA1LB.

Lemma mirror_ok_1RB1LC_0RC0LD_1LD1RC_0RA1LB : mirror_tm tm_1RB1LC_0RC0LD_1LD1RC_0RA1LB = tmm_1RB1LC_0RC0LD_1LD1RC_0RA1LB.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

(** The outer and inner anchor families. *)
Definition Cc_1RB1LC_0RC0LD_1LD1RC_0RA1LB (p : positive) : cconf := (StA, (Ip p ++ [S1;S0], S0, [S0])).
Local Notation Cc := Cc_1RB1LC_0RC0LD_1LD1RC_0RA1LB.
Definition Cin_1RB1LC_0RC0LD_1LD1RC_0RA1LB (v : positive) : cconf := (StC, (Ip v ++ [S1], S0, [S1;S0])).
Local Notation Cin := Cin_1RB1LC_0RC0LD_1LD1RC_0RA1LB.

(** ** The window units (each closed by [reflexivity]) *)
Lemma U_P1_1RB1LC_0RC0LD_1LD1RC_0RA1LB : wsteps true true tm 9 (StA,([S1],S0,[S0])) = Some (StC,([],S1,[S1;S0])). Proof. reflexivity. Qed.
Lemma U_P1i_1RB1LC_0RC0LD_1LD1RC_0RA1LB : wsteps true true tm 5 (StC,([S1],S0,[S1;S0])) = Some (StC,([],S1,[S1;S1;S0])). Proof. reflexivity. Qed.
Lemma U_RIP_1RB1LC_0RC0LD_1LD1RC_0RA1LB : wsteps true true tm 1 (StC,([S1],S1,[])) = Some (StC,([],S1,[S1])). Proof. reflexivity. Qed.
Lemma U_STPI_1RB1LC_0RC0LD_1LD1RC_0RA1LB : wsteps true true tm 1 (StC,([S0],S1,[])) = Some (StC,([],S0,[S1])). Proof. reflexivity. Qed.
Lemma U_TRN_1RB1LC_0RC0LD_1LD1RC_0RA1LB : wsteps true true tm 1 (StC,([],S0,[S1])) = Some (StD,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_RET_1RB1LC_0RC0LD_1LD1RC_0RA1LB : wsteps true true tm 2 (StD,([],S1,[S1;S1])) = Some (StD,([S0;S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FIN_1RB1LC_0RC0LD_1LD1RC_0RA1LB : wsteps true true tm 3 (StD,([],S1,[S1;S0])) = Some (StA,([S1],S0,[S0])). Proof. reflexivity. Qed.
Lemma U_FINi_1RB1LC_0RC0LD_1LD1RC_0RA1LB : wsteps true true tm 5 (StD,([],S1,[S1;S1;S0])) = Some (StC,([S1],S0,[S1;S0])). Proof. reflexivity. Qed.
Lemma U_STPO_1RB1LC_0RC0LD_1LD1RC_0RA1LB : wsteps false true tm 2 (StC,([S0],S1,[])) = Some (StD,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_STPOe_1RB1LC_0RC0LD_1LD1RC_0RA1LB : wsteps false true tm 2 (StC,([],S1,[])) = Some (StD,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FINx_1RB1LC_0RC0LD_1LD1RC_0RA1LB : wsteps true true tm 5 (StD,([],S1,[S1;S1;S0])) = Some (StC,([S1],S0,[S1;S0])). Proof. reflexivity. Qed.
Lemma U_FINe_1RB1LC_0RC0LD_1LD1RC_0RA1LB : wsteps true true tm 3 (StD,([],S1,[S1;S0])) = Some (StA,([S1],S0,[S0])). Proof. reflexivity. Qed.
Lemma U_VA1_1RB1LC_0RC0LD_1LD1RC_0RA1LB : wsteps true true tm 1 (StA,([S1],S0,[S0])) = Some (StB,([],S1,[S1;S0])). Proof. reflexivity. Qed.
Lemma U_VA2_1RB1LC_0RC0LD_1LD1RC_0RA1LB : wsteps true true tm 4 (StA,([S1],S0,[S0])) = Some (StC,([S0],S1,[S0])). Proof. reflexivity. Qed.
Lemma U_VA3_1RB1LC_0RC0LD_1LD1RC_0RA1LB : wsteps true true tm 2 (StA,([S1],S0,[S0])) = Some (StD,([S0],S1,[S0])). Proof. reflexivity. Qed.

(** ** Transported phases *)
Lemma phP1_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall L R, csteps tm 9 (StA,(S1::L,S0,S0::R)) = Some (StC,(L,S1,S1::S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_P1_1RB1LC_0RC0LD_1LD1RC_0RA1LB). Qed.
Lemma phP1i_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall L R, csteps tm 5 (StC,(S1::L,S0,S1::S0::R)) = Some (StC,(L,S1,S1::S1::S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_P1i_1RB1LC_0RC0LD_1LD1RC_0RA1LB). Qed.
Lemma phRIP_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall k L R, csteps tm (1*k) (StC,(rep [S1] k ++ L,S1,R)) = Some (StC,(L,S1,rep [S1] k ++ R)).
Proof. intros. pose proof (cycL _ _ _ _ _ _ _ U_RIP_1RB1LC_0RC0LD_1LD1RC_0RA1LB k L R) as H; cbn [app] in H; exact H. Qed.
Lemma phSTPI_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall L R, csteps tm 1 (StC,(S0::L,S1,R)) = Some (StC,(L,S0,S1::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STPI_1RB1LC_0RC0LD_1LD1RC_0RA1LB). Qed.
Lemma phTRN_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall L R, csteps tm 1 (StC,(L,S0,S1::R)) = Some (StD,(S1::L,S1,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_TRN_1RB1LC_0RC0LD_1LD1RC_0RA1LB). Qed.
Lemma phRET_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall k L R, csteps tm (2*k) (StD,(L,S1,rep [S1;S1] k ++ R)) = Some (StD,(rep [S0;S1] k ++ L,S1,R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U_RET_1RB1LC_0RC0LD_1LD1RC_0RA1LB k L R). Qed.
Lemma phFIN_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall L R, csteps tm 3 (StD,(L,S1,S1::S0::R)) = Some (StA,(S1::L,S0,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FIN_1RB1LC_0RC0LD_1LD1RC_0RA1LB). Qed.
Lemma phFINi_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall L R, csteps tm 5 (StD,(L,S1,S1::S1::S0::R)) = Some (StC,(S1::L,S0,S1::S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FINi_1RB1LC_0RC0LD_1LD1RC_0RA1LB). Qed.
Lemma phSTPO_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall R, csteps tm 2 (StC,([S0],S1,R)) = Some (StD,([S1],S1,R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPO_1RB1LC_0RC0LD_1LD1RC_0RA1LB). Qed.
Lemma phSTPOe_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall R, csteps tm 2 (StC,([],S1,R)) = Some (StD,([S1],S1,R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPOe_1RB1LC_0RC0LD_1LD1RC_0RA1LB). Qed.
Lemma phFINx_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall L R, csteps tm 5 (StD,(L,S1,S1::S1::S0::R)) = Some (StC,(S1::L,S0,S1::S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FINx_1RB1LC_0RC0LD_1LD1RC_0RA1LB). Qed.
Lemma phFINe_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall L R, csteps tm 3 (StD,(L,S1,S1::S0::R)) = Some (StA,(S1::L,S0,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FINe_1RB1LC_0RC0LD_1LD1RC_0RA1LB). Qed.
Lemma phVA1_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall L R, csteps tm 1 (StA,(S1::L,S0,S0::R)) = Some (StB,(L,S1,S1::S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_VA1_1RB1LC_0RC0LD_1LD1RC_0RA1LB). Qed.
Lemma phVA2_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall L R, csteps tm 4 (StA,(S1::L,S0,S0::R)) = Some (StC,(S0::L,S1,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_VA2_1RB1LC_0RC0LD_1LD1RC_0RA1LB). Qed.
Lemma phVA3_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall L R, csteps tm 2 (StA,(S1::L,S0,S0::R)) = Some (StD,(S0::L,S1,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_VA3_1RB1LC_0RC0LD_1LD1RC_0RA1LB). Qed.

(** ** The OUTER interior lap: EXACT (the ILS4F flip chain) *)
Lemma lap_int_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall p j q0, cview p = (j, Some q0) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p j q0 Ecv. unfold Cc_1RB1LC_0RC0LD_1LD1RC_0RA1LB.
  destruct (cview_some_I p j q0 Ecv) as (HIp & HIs).
  do 2 eexists. split; [|split].
  + rewrite HIp, <- app_assoc. cbn [app].
    rewrite rep_dbl, <- rep_slide.
    change (rep [S1] (S (2*j))) with (S1 :: rep [S1] (2*j)). cbn [app].
    eapply csteps_chain. { apply phP1_1RB1LC_0RC0LD_1LD1RC_0RA1LB. }
    eapply csteps_chain. { apply (phRIP_1RB1LC_0RC0LD_1LD1RC_0RA1LB (2*j)). }
    eapply csteps_chain. { apply phSTPI_1RB1LC_0RC0LD_1LD1RC_0RA1LB. }
    eapply csteps_chain. { apply phTRN_1RB1LC_0RC0LD_1LD1RC_0RA1LB. }
    rewrite <- rep_dbl.
    eapply csteps_chain. { apply (phRET_1RB1LC_0RC0LD_1LD1RC_0RA1LB j). }
    apply phFIN_1RB1LC_0RC0LD_1LD1RC_0RA1LB.
  + rewrite HIs, <- app_assoc. cbn [app].
    change (rep [S1;S0] j ++ S1 :: S1 :: (Ip q0 ++ [S1;S0]))
      with (rep [S1;S0] j ++ [S1] ++ (S1 :: (Ip q0 ++ [S1;S0]))).
    rewrite app_assoc, pair_rot. reflexivity.
  + lia.
Qed.

(** ** The INNER lap: EXACT, interior [cview] only (all the values the
    inner run visits below the all-ones fill are interior) *)
Lemma lap_inner_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall v j q0, cview v = (j, Some q0) ->
  exists n c', csteps tm n (Cin v) = Some c' /\ c' = Cin (Pos.succ v) /\ 0 < n.
Proof.
  intros v j q0 Ecv. unfold Cin_1RB1LC_0RC0LD_1LD1RC_0RA1LB.
  destruct (cview_some_I v j q0 Ecv) as (HIp & HIs).
  do 2 eexists. split; [|split].
  + rewrite HIp, <- app_assoc. cbn [app].
    rewrite rep_dbl, <- rep_slide.
    change (rep [S1] (S (2*j))) with (S1 :: rep [S1] (2*j)). cbn [app].
    eapply csteps_chain. { apply phP1i_1RB1LC_0RC0LD_1LD1RC_0RA1LB. }
    eapply csteps_chain. { apply (phRIP_1RB1LC_0RC0LD_1LD1RC_0RA1LB (2*j)). }
    eapply csteps_chain. { apply phSTPI_1RB1LC_0RC0LD_1LD1RC_0RA1LB. }
    eapply csteps_chain. { apply phTRN_1RB1LC_0RC0LD_1LD1RC_0RA1LB. }
    rewrite <- rep_dbl.
    eapply csteps_chain. { apply (phRET_1RB1LC_0RC0LD_1LD1RC_0RA1LB j). }
    apply phFINi_1RB1LC_0RC0LD_1LD1RC_0RA1LB.
  + rewrite HIs, <- app_assoc. cbn [app].
    change (rep [S1;S0] j ++ S1 :: S1 :: (Ip q0 ++ [S1]))
      with (rep [S1;S0] j ++ [S1] ++ (S1 :: (Ip q0 ++ [S1]))).
    rewrite app_assoc, pair_rot. reflexivity.
  + lia.
Qed.

(** Compose inner laps to the all-ones fill by well-founded induction on
    [tovf] (strictly decreasing along interior laps). *)
Lemma inner_to_fill_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall v, exists n,
  csteps tm n (Cin v) = Some (Cin (fill v)).
Proof.
  intro v; remember (tovf v) as fuel eqn:Ef; revert v Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros v Ef.
  destruct (cview v) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf v <> 0).
    { intro H0. destruct (tovf0_allones v H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }
    destruct (lap_inner_1RB1LC_0RC0LD_1LD1RC_0RA1LB v j q0 Ecv) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ v)) (ltac:(rewrite tovf_succ by lia; lia)) (Pos.succ v) eq_refl) as (k & Hk).
    exists (n + k). rewrite csteps_add, Hrun.
    rewrite (fill_succ v j q0 Ecv) in Hk. exact Hk.
  - destruct j as [|j'].
    { exfalso. destruct v; simpl in Ecv; [destruct (cview v); discriminate|discriminate|discriminate]. }
    exists 0. rewrite (fill_allones v j' Ecv). reflexivity.
Qed.

(** ** Boot: from the outer all-ones anchor into the inner family *)
Lemma boot_ov_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall n, exists m c',
  csteps tm m (StA, ((rep [S1;S1] n ++ [S1]) ++ [S1;S0], S0, [S0])) = Some c'
  /\ c' = Cin (pow2 n) /\ 0 < m.
Proof.
  intro n.
  do 2 eexists. split; [|split].
  + rewrite <- app_assoc. cbn [app].
    rewrite rep_dbl, <- !rep_slide.
    change (rep [S1] (S (S (2*n)))) with (S1 :: rep [S1] (S (2*n))). cbn [app].
    eapply csteps_chain. { apply phP1_1RB1LC_0RC0LD_1LD1RC_0RA1LB. }
    eapply csteps_chain. { apply (phRIP_1RB1LC_0RC0LD_1LD1RC_0RA1LB (S (2*n))). }
    eapply csteps_chain. { apply phSTPO_1RB1LC_0RC0LD_1LD1RC_0RA1LB. }
    change (rep [S1] (S (2*n)) ++ [S1;S0]) with (S1 :: rep [S1] (2*n) ++ [S1;S0]).
    rewrite rep_slide, <- rep_dbl.
    eapply csteps_chain. { apply (phRET_1RB1LC_0RC0LD_1LD1RC_0RA1LB n). }
    apply phFINx_1RB1LC_0RC0LD_1LD1RC_0RA1LB.
  + unfold Cin_1RB1LC_0RC0LD_1LD1RC_0RA1LB. rewrite Ip_pow2, pair_rot. reflexivity.
  + lia.
Qed.

(** ** Exit: from the inner all-ones anchor back to the outer family,
    closing under [lift] *)
Lemma exit_ov_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall n, exists m c',
  csteps tm m (StC, ((rep [S1;S1] n ++ [S1]) ++ [S1], S0, [S1;S0])) = Some c'
  /\ c' = (StA, (S1 :: rep [S0;S1] (S n) ++ [S1], S0, [S0])) /\ 0 < m.
Proof.
  intro n.
  do 2 eexists. split; [|split].
  + rewrite <- app_assoc. cbn [app].
    rewrite pair_fold, rep_dbl.
    replace (2 * S n) with (S (S (2 * n))) by lia.
    change (rep [S1] (S (S (2 * n)))) with (S1 :: rep [S1] (S (2 * n))). cbn [app].
    eapply csteps_chain. { apply phP1i_1RB1LC_0RC0LD_1LD1RC_0RA1LB. }
    eapply csteps_chain. { apply (phRIP_1RB1LC_0RC0LD_1LD1RC_0RA1LB (S (2 * n))). }
    eapply csteps_chain. { apply phSTPOe_1RB1LC_0RC0LD_1LD1RC_0RA1LB. }
    rewrite <- rep_slide.
    change (S1 :: rep [S1] (S (2 * n)) ++ S1::S0::nil) with (rep [S1] (S (S (2 * n))) ++ S1::S0::nil).
    replace (S (S (2 * n))) with (2 * S n) by lia.
    rewrite <- rep_dbl.
    eapply csteps_chain. { apply (phRET_1RB1LC_0RC0LD_1LD1RC_0RA1LB (S n)). }
    apply phFINe_1RB1LC_0RC0LD_1LD1RC_0RA1LB.
  + reflexivity.
  + lia.
Qed.

Lemma lift_lblank_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

(** ** The OUTER overflow lap: boot ; inner counting ; exit *)
Lemma lap_ov_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall p j', cview p = (S j', None) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j' Ecv.
  destruct (cview_none_I p j' Ecv) as (HIp & HIs).
  pose proof (cview_none_shape p j' Ecv) as Hp.
  destruct (boot_ov_1RB1LC_0RC0LD_1LD1RC_0RA1LB j') as (m1 & c1 & Hb & Hc1 & Hm1).
  destruct (inner_to_fill_1RB1LC_0RC0LD_1LD1RC_0RA1LB (pow2 j')) as (m2 & Hi).
  destruct (exit_ov_1RB1LC_0RC0LD_1LD1RC_0RA1LB j') as (m3 & c3 & Hx & Hc3 & _).
  exists (m1 + (m2 + m3)), c3. split; [|split].
  + unfold Cc_1RB1LC_0RC0LD_1LD1RC_0RA1LB. rewrite HIp.
    rewrite csteps_add, Hb. subst c1.
    rewrite csteps_add, Hi.
    rewrite <- Hp.
    unfold Cin_1RB1LC_0RC0LD_1LD1RC_0RA1LB. rewrite HIp. exact Hx.
  + subst c3. unfold Cc_1RB1LC_0RC0LD_1LD1RC_0RA1LB. rewrite HIs.
    rewrite <- app_assoc. cbn [app].
    change (rep [S1;S0] (S j') ++ S1 :: S1 :: S0 :: nil)
      with (rep [S1;S0] (S j') ++ [S1] ++ [S1] ++ [S0]).
    rewrite !app_assoc.
    rewrite lift_lblank_1RB1LC_0RC0LD_1LD1RC_0RA1LB.
    rewrite pair_rot.
    reflexivity.
  + lia.
Qed.

Lemma lap_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall p, exists n c', csteps tm n (Cc p) = Some c' /\
  lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - destruct (lap_int_1RB1LC_0RC0LD_1LD1RC_0RA1LB p j q0 Ecv) as (n & c' & H1 & H2 & H3).
    exists n, c'. split; [exact H1|split; [rewrite H2; reflexivity|exact H3]].
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    exact (lap_ov_1RB1LC_0RC0LD_1LD1RC_0RA1LB p j' Ecv).
Qed.

Lemma boot_1RB1LC_0RC0LD_1LD1RC_0RA1LB : exists t0, stepn tm t0 InitES = Some (lift (Cc 2)).
Proof.
  exists 30.
  assert (H : match csteps tm 30 c0 with Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 30 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits *)

(** StB: 1 steps from the anchor, inside the P1 window (uniform in p). *)
Lemma vis_A1_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StB.
Proof.
  intro p. destruct (Ip_head p) as (w & Hw). unfold Cc_1RB1LC_0RC0LD_1LD1RC_0RA1LB.
  rewrite Hw. cbn [app]. exists 1. eexists. split.
  - apply phVA1_1RB1LC_0RC0LD_1LD1RC_0RA1LB.
  - reflexivity.
Qed.

(** StC: 4 steps from the anchor, inside the P1 window (uniform in p). *)
Lemma vis_A2_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StC.
Proof.
  intro p. destruct (Ip_head p) as (w & Hw). unfold Cc_1RB1LC_0RC0LD_1LD1RC_0RA1LB.
  rewrite Hw. cbn [app]. exists 4. eexists. split.
  - apply phVA2_1RB1LC_0RC0LD_1LD1RC_0RA1LB.
  - reflexivity.
Qed.

(** StD: 2 steps from the anchor, inside the P1 window (uniform in p). *)
Lemma vis_A3_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StD.
Proof.
  intro p. destruct (Ip_head p) as (w & Hw). unfold Cc_1RB1LC_0RC0LD_1LD1RC_0RA1LB.
  rewrite Hw. cbn [app]. exists 2. eexists. split.
  - apply phVA3_1RB1LC_0RC0LD_1LD1RC_0RA1LB.
  - reflexivity.
Qed.

Lemma vis_1RB1LC_0RC0LD_1LD1RC_0RA1LB : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q. destruct q.
  - (* StA : the anchor state *)
    exists 0. eexists. split; reflexivity.
  - apply vis_A1_1RB1LC_0RC0LD_1LD1RC_0RA1LB.
  - apply vis_A2_1RB1LC_0RC0LD_1LD1RC_0RA1LB.
  - apply vis_A3_1RB1LC_0RC0LD_1LD1RC_0RA1LB.
Qed.

Theorem nqhm_1RB1LC_0RC0LD_1LD1RC_0RA1LB : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 2). - exact boot_1RB1LC_0RC0LD_1LD1RC_0RA1LB. - intros p _. apply lap_1RB1LC_0RC0LD_1LD1RC_0RA1LB. - intros p q _. apply vis_1RB1LC_0RC0LD_1LD1RC_0RA1LB. Qed.

Theorem nqh_1RB1LC_0RC0LD_1LD1RC_0RA1LB : NeverQuasiHaltsSt tm_1RB1LC_0RC0LD_1LD1RC_0RA1LB.
Proof. apply (mirror_never_qh tm_1RB1LC_0RC0LD_1LD1RC_0RA1LB). rewrite mirror_ok_1RB1LC_0RC0LD_1LD1RC_0RA1LB. exact nqhm_1RB1LC_0RC0LD_1LD1RC_0RA1LB. Qed.

Theorem nonhalt_1RB1LC_0RC0LD_1LD1RC_0RA1LB : NonHalt tm_1RB1LC_0RC0LD_1LD1RC_0RA1LB.
Proof. apply never_qh_nonhalt, nqh_1RB1LC_0RC0LD_1LD1RC_0RA1LB. Qed.
