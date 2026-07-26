(** * IXP_0RB0LC_1LC1RB_0RD1LA_0LA1LA: exponential-overflow interleaved
    counter, machine 0RB0LC_1LC1RB_0RD1LA_0LA1LA.

    Auto-emitted by tools/counters/emit_ixp.py (UNTRUSTED emitter; the Coq
    kernel re-checks every line below), cloning the hand-authored reference
    board IXP_1RB1LA_0LA1RC_0LD0RB_0LA1RD.v (WAVE11_MIRROR.md section 3).
    Interior laps are the affine flip chain (ILS4F); the OVERFLOW lap
    2^K-1 -> 2^K runs an INNER interleaved counter: anchors

      Cc p  = (StB, (Ip p ++ [S1;S0], S0, [S0]))
      Cin v = (StB, (Ip v ++ [S1], S0, [S1;S0]))

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

Definition mk_0RB0LC_1LC1RB_0RD1LA_0LA1LA (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB0LC_1LC1RB_0RD1LA_0LA1LA.

(** 0RB0LC_1LC1RB_0RD1LA_0LA1LA *)
(** 0RB0LC_1LC1RB_0RD1LA_0LA1LA -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB0LC_1LC1RB_0RD1LA_0LA1LA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S0 DL StC
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S0 DR StD | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S0 DL StA | StD, S1 => mk S1 DL StA end.

(** Its mirror 0LB0RC_1RC1LB_0LD1RA_0RA1RA: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB0LC_1LC1RB_0RD1LA_0LA1LA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S0 DR StC
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S0 DL StD | StC, S1 => mk S1 DR StA
  | StD, S0 => mk S0 DR StA | StD, S1 => mk S1 DR StA end.
Local Notation tm := tmm_0RB0LC_1LC1RB_0RD1LA_0LA1LA.

Lemma mirror_ok_0RB0LC_1LC1RB_0RD1LA_0LA1LA : mirror_tm tm_0RB0LC_1LC1RB_0RD1LA_0LA1LA = tmm_0RB0LC_1LC1RB_0RD1LA_0LA1LA.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

(** The outer and inner anchor families. *)
Definition Cc_0RB0LC_1LC1RB_0RD1LA_0LA1LA (p : positive) : cconf := (StB, (Ip p ++ [S1;S0], S0, [S0])).
Local Notation Cc := Cc_0RB0LC_1LC1RB_0RD1LA_0LA1LA.
Definition Cin_0RB0LC_1LC1RB_0RD1LA_0LA1LA (v : positive) : cconf := (StB, (Ip v ++ [S1], S0, [S1;S0])).
Local Notation Cin := Cin_0RB0LC_1LC1RB_0RD1LA_0LA1LA.

(** ** The window units (each closed by [reflexivity]) *)
Lemma U_P1_0RB0LC_1LC1RB_0RD1LA_0LA1LA : wsteps true true tm 4 (StB,([],S0,[S0])) = Some (StB,([],S1,[S0])). Proof. reflexivity. Qed.
Lemma U_P1i_0RB0LC_1LC1RB_0RD1LA_0LA1LA : wsteps true true tm 4 (StB,([],S0,[S1;S0])) = Some (StB,([],S1,[S1;S0])). Proof. reflexivity. Qed.
Lemma U_RIP_0RB0LC_1LC1RB_0RD1LA_0LA1LA : wsteps true true tm 1 (StB,([S1],S1,[])) = Some (StB,([],S1,[S1])). Proof. reflexivity. Qed.
Lemma U_STPI_0RB0LC_1LC1RB_0RD1LA_0LA1LA : wsteps true true tm 1 (StB,([S0],S1,[])) = Some (StB,([],S0,[S1])). Proof. reflexivity. Qed.
Lemma U_TRN_0RB0LC_1LC1RB_0RD1LA_0LA1LA : wsteps true true tm 1 (StB,([],S0,[S1])) = Some (StC,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_RET_0RB0LC_1LC1RB_0RD1LA_0LA1LA : wsteps true true tm 2 (StC,([],S1,[S1;S1])) = Some (StC,([S0;S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FIN_0RB0LC_1LC1RB_0RD1LA_0LA1LA : wsteps true true tm 5 (StC,([],S1,[S1;S0])) = Some (StB,([S1],S0,[S0])). Proof. reflexivity. Qed.
Lemma U_FINi_0RB0LC_1LC1RB_0RD1LA_0LA1LA : wsteps true true tm 5 (StC,([],S1,[S1;S1;S0])) = Some (StB,([S1],S0,[S1;S0])). Proof. reflexivity. Qed.
Lemma U_STPO_0RB0LC_1LC1RB_0RD1LA_0LA1LA : wsteps false true tm 2 (StB,([S0],S1,[])) = Some (StC,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_STPOe_0RB0LC_1LC1RB_0RD1LA_0LA1LA : wsteps false true tm 2 (StB,([],S1,[])) = Some (StC,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FINx_0RB0LC_1LC1RB_0RD1LA_0LA1LA : wsteps true false tm 3 (StC,([S0],S1,[S0])) = Some (StB,([],S0,[S1;S0])). Proof. reflexivity. Qed.
Lemma U_FINe_0RB0LC_1LC1RB_0RD1LA_0LA1LA : wsteps true true tm 5 (StC,([],S1,[S1;S0])) = Some (StB,([S1],S0,[S0])). Proof. reflexivity. Qed.
Lemma U_VA1_0RB0LC_1LC1RB_0RD1LA_0LA1LA : wsteps true true tm 3 (StB,([],S0,[S0])) = Some (StA,([S1],S0,[])). Proof. reflexivity. Qed.
Lemma U_VA2_0RB0LC_1LC1RB_0RD1LA_0LA1LA : wsteps true true tm 1 (StB,([],S0,[S0])) = Some (StC,([S1],S0,[])). Proof. reflexivity. Qed.
Lemma U_VA3_0RB0LC_1LC1RB_0RD1LA_0LA1LA : wsteps true true tm 2 (StB,([],S0,[S0])) = Some (StD,([],S1,[S0])). Proof. reflexivity. Qed.

(** ** Transported phases *)
Lemma phP1_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall L R, csteps tm 4 (StB,(L,S0,S0::R)) = Some (StB,(L,S1,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_P1_0RB0LC_1LC1RB_0RD1LA_0LA1LA). Qed.
Lemma phP1i_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall L R, csteps tm 4 (StB,(L,S0,S1::S0::R)) = Some (StB,(L,S1,S1::S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_P1i_0RB0LC_1LC1RB_0RD1LA_0LA1LA). Qed.
Lemma phRIP_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall k L R, csteps tm (1*k) (StB,(rep [S1] k ++ L,S1,R)) = Some (StB,(L,S1,rep [S1] k ++ R)).
Proof. intros. pose proof (cycL _ _ _ _ _ _ _ U_RIP_0RB0LC_1LC1RB_0RD1LA_0LA1LA k L R) as H; cbn [app] in H; exact H. Qed.
Lemma phSTPI_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall L R, csteps tm 1 (StB,(S0::L,S1,R)) = Some (StB,(L,S0,S1::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STPI_0RB0LC_1LC1RB_0RD1LA_0LA1LA). Qed.
Lemma phTRN_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall L R, csteps tm 1 (StB,(L,S0,S1::R)) = Some (StC,(S1::L,S1,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_TRN_0RB0LC_1LC1RB_0RD1LA_0LA1LA). Qed.
Lemma phRET_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall k L R, csteps tm (2*k) (StC,(L,S1,rep [S1;S1] k ++ R)) = Some (StC,(rep [S0;S1] k ++ L,S1,R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U_RET_0RB0LC_1LC1RB_0RD1LA_0LA1LA k L R). Qed.
Lemma phFIN_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall L R, csteps tm 5 (StC,(L,S1,S1::S0::R)) = Some (StB,(S1::L,S0,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FIN_0RB0LC_1LC1RB_0RD1LA_0LA1LA). Qed.
Lemma phFINi_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall L R, csteps tm 5 (StC,(L,S1,S1::S1::S0::R)) = Some (StB,(S1::L,S0,S1::S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FINi_0RB0LC_1LC1RB_0RD1LA_0LA1LA). Qed.
Lemma phSTPO_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall R, csteps tm 2 (StB,([S0],S1,R)) = Some (StC,([S1],S1,R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPO_0RB0LC_1LC1RB_0RD1LA_0LA1LA). Qed.
Lemma phSTPOe_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall R, csteps tm 2 (StB,([],S1,R)) = Some (StC,([S1],S1,R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPOe_0RB0LC_1LC1RB_0RD1LA_0LA1LA). Qed.
Lemma phFINx_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall L, csteps tm 3 (StC,(S0::L,S1,[S0])) = Some (StB,(L,S0,[S1;S0])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U_FINx_0RB0LC_1LC1RB_0RD1LA_0LA1LA). Qed.
Lemma phFINe_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall L R, csteps tm 5 (StC,(L,S1,S1::S0::R)) = Some (StB,(S1::L,S0,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FINe_0RB0LC_1LC1RB_0RD1LA_0LA1LA). Qed.
Lemma phVA1_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall L R, csteps tm 3 (StB,(L,S0,S0::R)) = Some (StA,(S1::L,S0,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_VA1_0RB0LC_1LC1RB_0RD1LA_0LA1LA). Qed.
Lemma phVA2_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall L R, csteps tm 1 (StB,(L,S0,S0::R)) = Some (StC,(S1::L,S0,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_VA2_0RB0LC_1LC1RB_0RD1LA_0LA1LA). Qed.
Lemma phVA3_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall L R, csteps tm 2 (StB,(L,S0,S0::R)) = Some (StD,(L,S1,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_VA3_0RB0LC_1LC1RB_0RD1LA_0LA1LA). Qed.

(** ** The OUTER interior lap: EXACT (the ILS4F flip chain) *)
Lemma lap_int_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall p j q0, cview p = (j, Some q0) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p j q0 Ecv. unfold Cc_0RB0LC_1LC1RB_0RD1LA_0LA1LA.
  destruct (cview_some_I p j q0 Ecv) as (HIp & HIs).
  do 2 eexists. split; [|split].
  + rewrite HIp, <- app_assoc. cbn [app].
    rewrite rep_dbl, <- rep_slide.
    eapply csteps_chain. { apply phP1_0RB0LC_1LC1RB_0RD1LA_0LA1LA. }
    eapply csteps_chain. { apply (phRIP_0RB0LC_1LC1RB_0RD1LA_0LA1LA (S (2*j))). }
    eapply csteps_chain. { apply phSTPI_0RB0LC_1LC1RB_0RD1LA_0LA1LA. }
    eapply csteps_chain. { apply phTRN_0RB0LC_1LC1RB_0RD1LA_0LA1LA. }
    change (rep [S1] (S (2*j)) ++ [S0]) with (S1 :: rep [S1] (2*j) ++ [S0]).
    rewrite rep_slide, <- rep_dbl.
    eapply csteps_chain. { apply (phRET_0RB0LC_1LC1RB_0RD1LA_0LA1LA j). }
    apply phFIN_0RB0LC_1LC1RB_0RD1LA_0LA1LA.
  + rewrite HIs, <- app_assoc. cbn [app].
    change (rep [S1;S0] j ++ S1 :: S1 :: (Ip q0 ++ [S1;S0]))
      with (rep [S1;S0] j ++ [S1] ++ (S1 :: (Ip q0 ++ [S1;S0]))).
    rewrite app_assoc, pair_rot. reflexivity.
  + lia.
Qed.

(** ** The INNER lap: EXACT, interior [cview] only (all the values the
    inner run visits below the all-ones fill are interior) *)
Lemma lap_inner_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall v j q0, cview v = (j, Some q0) ->
  exists n c', csteps tm n (Cin v) = Some c' /\ c' = Cin (Pos.succ v) /\ 0 < n.
Proof.
  intros v j q0 Ecv. unfold Cin_0RB0LC_1LC1RB_0RD1LA_0LA1LA.
  destruct (cview_some_I v j q0 Ecv) as (HIp & HIs).
  do 2 eexists. split; [|split].
  + rewrite HIp, <- app_assoc. cbn [app].
    rewrite rep_dbl, <- rep_slide.
    eapply csteps_chain. { apply phP1i_0RB0LC_1LC1RB_0RD1LA_0LA1LA. }
    eapply csteps_chain. { apply (phRIP_0RB0LC_1LC1RB_0RD1LA_0LA1LA (S (2*j))). }
    eapply csteps_chain. { apply phSTPI_0RB0LC_1LC1RB_0RD1LA_0LA1LA. }
    eapply csteps_chain. { apply phTRN_0RB0LC_1LC1RB_0RD1LA_0LA1LA. }
    change (rep [S1] (S (2*j)) ++ [S1;S0]) with (S1 :: rep [S1] (2*j) ++ [S1;S0]).
    rewrite rep_slide, <- rep_dbl.
    eapply csteps_chain. { apply (phRET_0RB0LC_1LC1RB_0RD1LA_0LA1LA j). }
    apply phFINi_0RB0LC_1LC1RB_0RD1LA_0LA1LA.
  + rewrite HIs, <- app_assoc. cbn [app].
    change (rep [S1;S0] j ++ S1 :: S1 :: (Ip q0 ++ [S1]))
      with (rep [S1;S0] j ++ [S1] ++ (S1 :: (Ip q0 ++ [S1]))).
    rewrite app_assoc, pair_rot. reflexivity.
  + lia.
Qed.

(** Compose inner laps to the all-ones fill by well-founded induction on
    [tovf] (strictly decreasing along interior laps). *)
Lemma inner_to_fill_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall v, exists n,
  csteps tm n (Cin v) = Some (Cin (fill v)).
Proof.
  intro v; remember (tovf v) as fuel eqn:Ef; revert v Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros v Ef.
  destruct (cview v) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf v <> 0).
    { intro H0. destruct (tovf0_allones v H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }
    destruct (lap_inner_0RB0LC_1LC1RB_0RD1LA_0LA1LA v j q0 Ecv) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ v)) (ltac:(rewrite tovf_succ by lia; lia)) (Pos.succ v) eq_refl) as (k & Hk).
    exists (n + k). rewrite csteps_add, Hrun.
    rewrite (fill_succ v j q0 Ecv) in Hk. exact Hk.
  - destruct j as [|j'].
    { exfalso. destruct v; simpl in Ecv; [destruct (cview v); discriminate|discriminate|discriminate]. }
    exists 0. rewrite (fill_allones v j' Ecv). reflexivity.
Qed.

(** ** Boot: from the outer all-ones anchor into the inner family *)
Lemma boot_ov_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall n, exists m c',
  csteps tm m (StB, ((rep [S1;S1] n ++ [S1]) ++ [S1;S0], S0, [S0])) = Some c'
  /\ c' = Cin (pow2 n) /\ 0 < m.
Proof.
  intro n.
  do 2 eexists. split; [|split].
  + rewrite <- app_assoc. cbn [app].
    rewrite rep_dbl, <- !rep_slide.
    eapply csteps_chain. { apply phP1_0RB0LC_1LC1RB_0RD1LA_0LA1LA. }
    eapply csteps_chain. { apply (phRIP_0RB0LC_1LC1RB_0RD1LA_0LA1LA (S (S (2*n)))). }
    eapply csteps_chain. { apply phSTPO_0RB0LC_1LC1RB_0RD1LA_0LA1LA. }
    change (rep [S1] (S (S (2*n))) ++ [S0]) with (S1 :: S1 :: rep [S1] (2*n) ++ [S0]).
    rewrite <- rep_dbl.
    change (S1 :: S1 :: rep [S1;S1] n ++ [S0]) with (rep [S1;S1] (S n) ++ [S0]).
    eapply csteps_chain. { apply (phRET_0RB0LC_1LC1RB_0RD1LA_0LA1LA (S n)). }
    change (rep [S0;S1] (S n) ++ [S1]) with (S0 :: S1 :: rep [S0;S1] n ++ [S1]).
    apply phFINx_0RB0LC_1LC1RB_0RD1LA_0LA1LA.
  + unfold Cin_0RB0LC_1LC1RB_0RD1LA_0LA1LA. rewrite Ip_pow2, pair_rot. reflexivity.
  + lia.
Qed.

(** ** Exit: from the inner all-ones anchor back to the outer family,
    closing under [lift] *)
Lemma exit_ov_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall n, exists m c',
  csteps tm m (StB, ((rep [S1;S1] n ++ [S1]) ++ [S1], S0, [S1;S0])) = Some c'
  /\ c' = (StB, (S1 :: rep [S0;S1] (S n) ++ [S1], S0, [S0])) /\ 0 < m.
Proof.
  intro n.
  do 2 eexists. split; [|split].
  + rewrite <- app_assoc. cbn [app].
    rewrite pair_fold, rep_dbl.
    eapply csteps_chain. { apply phP1i_0RB0LC_1LC1RB_0RD1LA_0LA1LA. }
    eapply csteps_chain. { apply (phRIP_0RB0LC_1LC1RB_0RD1LA_0LA1LA (2 * S n)). }
    eapply csteps_chain. { apply phSTPOe_0RB0LC_1LC1RB_0RD1LA_0LA1LA. }
    rewrite <- rep_dbl.
    eapply csteps_chain. { apply (phRET_0RB0LC_1LC1RB_0RD1LA_0LA1LA (S n)). }
    apply phFINe_0RB0LC_1LC1RB_0RD1LA_0LA1LA.
  + reflexivity.
  + lia.
Qed.

Lemma lift_lblank_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

(** ** The OUTER overflow lap: boot ; inner counting ; exit *)
Lemma lap_ov_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall p j', cview p = (S j', None) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j' Ecv.
  destruct (cview_none_I p j' Ecv) as (HIp & HIs).
  pose proof (cview_none_shape p j' Ecv) as Hp.
  destruct (boot_ov_0RB0LC_1LC1RB_0RD1LA_0LA1LA j') as (m1 & c1 & Hb & Hc1 & Hm1).
  destruct (inner_to_fill_0RB0LC_1LC1RB_0RD1LA_0LA1LA (pow2 j')) as (m2 & Hi).
  destruct (exit_ov_0RB0LC_1LC1RB_0RD1LA_0LA1LA j') as (m3 & c3 & Hx & Hc3 & _).
  exists (m1 + (m2 + m3)), c3. split; [|split].
  + unfold Cc_0RB0LC_1LC1RB_0RD1LA_0LA1LA. rewrite HIp.
    rewrite csteps_add, Hb. subst c1.
    rewrite csteps_add, Hi.
    rewrite <- Hp.
    unfold Cin_0RB0LC_1LC1RB_0RD1LA_0LA1LA. rewrite HIp. exact Hx.
  + subst c3. unfold Cc_0RB0LC_1LC1RB_0RD1LA_0LA1LA. rewrite HIs.
    rewrite <- app_assoc. cbn [app].
    change (rep [S1;S0] (S j') ++ S1 :: S1 :: S0 :: nil)
      with (rep [S1;S0] (S j') ++ [S1] ++ [S1] ++ [S0]).
    rewrite !app_assoc.
    rewrite lift_lblank_0RB0LC_1LC1RB_0RD1LA_0LA1LA.
    rewrite pair_rot.
    reflexivity.
  + lia.
Qed.

Lemma lap_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall p, exists n c', csteps tm n (Cc p) = Some c' /\
  lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - destruct (lap_int_0RB0LC_1LC1RB_0RD1LA_0LA1LA p j q0 Ecv) as (n & c' & H1 & H2 & H3).
    exists n, c'. split; [exact H1|split; [rewrite H2; reflexivity|exact H3]].
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    exact (lap_ov_0RB0LC_1LC1RB_0RD1LA_0LA1LA p j' Ecv).
Qed.

Lemma boot_0RB0LC_1LC1RB_0RD1LA_0LA1LA : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 17.
  assert (H : match csteps tm 17 c0 with Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 17 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits *)

(** StA: 3 steps from the anchor, inside the P1 window (uniform in p). *)
Lemma vis_A1_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StA.
Proof.
  intro p. unfold Cc_0RB0LC_1LC1RB_0RD1LA_0LA1LA. exists 3. eexists. split.
  - apply phVA1_0RB0LC_1LC1RB_0RD1LA_0LA1LA.
  - reflexivity.
Qed.

(** StC: 1 steps from the anchor, inside the P1 window (uniform in p). *)
Lemma vis_A2_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StC.
Proof.
  intro p. unfold Cc_0RB0LC_1LC1RB_0RD1LA_0LA1LA. exists 1. eexists. split.
  - apply phVA2_0RB0LC_1LC1RB_0RD1LA_0LA1LA.
  - reflexivity.
Qed.

(** StD: 2 steps from the anchor, inside the P1 window (uniform in p). *)
Lemma vis_A3_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StD.
Proof.
  intro p. unfold Cc_0RB0LC_1LC1RB_0RD1LA_0LA1LA. exists 2. eexists. split.
  - apply phVA3_0RB0LC_1LC1RB_0RD1LA_0LA1LA.
  - reflexivity.
Qed.

Lemma vis_0RB0LC_1LC1RB_0RD1LA_0LA1LA : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q. destruct q.
  - apply vis_A1_0RB0LC_1LC1RB_0RD1LA_0LA1LA.
  - (* StB : the anchor state *)
    exists 0. eexists. split; reflexivity.
  - apply vis_A2_0RB0LC_1LC1RB_0RD1LA_0LA1LA.
  - apply vis_A3_0RB0LC_1LC1RB_0RD1LA_0LA1LA.
Qed.

Theorem nqhm_0RB0LC_1LC1RB_0RD1LA_0LA1LA : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 1). - exact boot_0RB0LC_1LC1RB_0RD1LA_0LA1LA. - intros p _. apply lap_0RB0LC_1LC1RB_0RD1LA_0LA1LA. - intros p q _. apply vis_0RB0LC_1LC1RB_0RD1LA_0LA1LA. Qed.

Theorem nqh_0RB0LC_1LC1RB_0RD1LA_0LA1LA : NeverQuasiHaltsSt tm_0RB0LC_1LC1RB_0RD1LA_0LA1LA.
Proof. apply (mirror_never_qh tm_0RB0LC_1LC1RB_0RD1LA_0LA1LA). rewrite mirror_ok_0RB0LC_1LC1RB_0RD1LA_0LA1LA. exact nqhm_0RB0LC_1LC1RB_0RD1LA_0LA1LA. Qed.

Theorem nonhalt_0RB0LC_1LC1RB_0RD1LA_0LA1LA : NonHalt tm_0RB0LC_1LC1RB_0RD1LA_0LA1LA.
Proof. apply never_qh_nonhalt, nqh_0RB0LC_1LC1RB_0RD1LA_0LA1LA. Qed.
