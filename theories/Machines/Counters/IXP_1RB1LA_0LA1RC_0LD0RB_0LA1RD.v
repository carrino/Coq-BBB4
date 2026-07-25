(** * IXP_1RB1LA_0LA1RC_0LD0RB_0LA1RD: exponential-overflow interleaved
    counter, machine 1RB1LA_0LA1RC_0LD0RB_0LA1RD.

    The first board of the exponential-overflow family (WAVE11_MIRROR.md
    section 3).  Interior laps are the affine flip chain (ILS4F);
    the OVERFLOW lap 2^K-1 -> 2^K costs ~10*2^K steps because the machine
    runs an INNER interleaved counter: measured inner anchors

      Cin v = (StA, (Ip v ++ [S1], S0, [S1;S0]))

    march v = 2^(K-1) .. 2^K-1 with affine interior-only inner laps (the
    same RIP/STPI/TRN/RET units as the outer chain; only the frontier
    windows P1i/FINi differ).  The overflow is therefore

      boot (affine)  :  Cc (2^K-1)  ->  Cin (2^(K-1))
      inner counting :  Cin v -> Cin (v+1), composed to the all-ones fill
                        by well-founded induction on [tovf]
      exit (affine)  :  Cin (2^K-1) ->  Cc (2^K), one left blank short

    -- a SECOND instantiation of the lap machinery nested inside the outer
    overflow branch; [glue_neverqh] never sees the difference.  Three
    positive gadgets connect the levels: [pow2], [fill] (all-ones of the
    same width), and [cview_none_shape : cview p = (S j, None) ->
    p = fill (pow2 j)].

    Every chain was differentially validated against the raw simulator
    (interior p = 2..199, inner v = 2..299, boot j' = 0..7, exit K = 1..8,
    and the composed outer overflow step-exactly for K = 2..7).
    Axiom footprint: [functional_extensionality_dep] (via CTape.lift). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ILCounter JpCounter.
Import ListNotations.

Definition mk_IXP1 (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_IXP1.

(** 1RB1LA_0LA1RC_0LD0RB_0LA1RD *)
Definition tm_1RB1LA_0LA1RC_0LD0RB_0LA1RD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StA
  | StB, S0 => mk S0 DL StA | StB, S1 => mk S1 DR StC
  | StC, S0 => mk S0 DL StD | StC, S1 => mk S0 DR StB
  | StD, S0 => mk S0 DL StA | StD, S1 => mk S1 DR StD end.
Local Notation tm := tm_1RB1LA_0LA1RC_0LD0RB_0LA1RD.

(** The outer and inner anchor families. *)
Definition Cc_IXP1 (p : positive) : cconf := (StA, (Ip p ++ [S1;S0], S0, [S0])).
Local Notation Cc := Cc_IXP1.
Definition Cin_IXP1 (v : positive) : cconf := (StA, (Ip v ++ [S1], S0, [S1;S0])).
Local Notation Cin := Cin_IXP1.

(** ** Positive gadgets bridging the two counter levels *)

Fixpoint pow2 (n : nat) : positive :=
  match n with O => xH | S m => xO (pow2 m) end.

(** All-ones of the same width. *)
Fixpoint fill (v : positive) : positive :=
  match v with xH => xH | xO q => xI (fill q) | xI q => xI (fill q) end.

Lemma Ip_pow2 : forall n, Ip (pow2 n) = rep [S1;S0] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma fill_succ : forall v j q, cview v = (j, Some q) ->
  fill (Pos.succ v) = fill v.
Proof.
  induction v; intros j q H; simpl in H.
  - destruct (cview v) as [j' r] eqn:E. inversion H; subst.
    simpl. f_equal. exact (IHv _ _ eq_refl).
  - inversion H; subst. reflexivity.
  - discriminate.
Qed.

Lemma fill_allones : forall v j, cview v = (S j, None) -> fill v = v.
Proof.
  induction v; intros j H; simpl in H.
  - destruct (cview v) as [j' r] eqn:E. inversion H; subst j' r.
    destruct j as [|j].
    { exfalso. destruct v; simpl in E; [destruct (cview v); discriminate|discriminate|discriminate]. }
    simpl. f_equal. exact (IHv j eq_refl).
  - discriminate.
  - reflexivity.
Qed.

Lemma cview_none_shape : forall p j, cview p = (S j, None) ->
  p = fill (pow2 j).
Proof.
  induction p; intros j H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E. inversion H; subst j' r.
    destruct j as [|j].
    { exfalso. destruct p; simpl in E; [destruct (cview p); discriminate|discriminate|discriminate]. }
    simpl. f_equal. exact (IHp j eq_refl).
  - discriminate.
  - inversion H; subst. reflexivity.
Qed.

(** ** The window units (each closed by [reflexivity]) *)
Lemma U_P1_IXP1 : wsteps true true tm 2 (StA,([],S0,[S0])) = Some (StA,([],S1,[S0])). Proof. reflexivity. Qed.
Lemma U_P1i_IXP1 : wsteps true true tm 6 (StA,([],S0,[S1;S0])) = Some (StA,([],S1,[S1;S0])). Proof. reflexivity. Qed.
Lemma U_RIP_IXP1 : wsteps true true tm 1 (StA,([S1],S1,[])) = Some (StA,([],S1,[S1])). Proof. reflexivity. Qed.
Lemma U_STPI_IXP1 : wsteps true true tm 1 (StA,([S0],S1,[])) = Some (StA,([],S0,[S1])). Proof. reflexivity. Qed.
Lemma U_TRN_IXP1 : wsteps true true tm 1 (StA,([],S0,[S1])) = Some (StB,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_RET_IXP1 : wsteps true true tm 2 (StB,([],S1,[S1;S1])) = Some (StB,([S0;S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FIN_IXP1 : wsteps true true tm 3 (StB,([],S1,[S1;S0])) = Some (StA,([S1],S0,[S0])). Proof. reflexivity. Qed.
Lemma U_FINi_IXP1 : wsteps true true tm 7 (StB,([],S1,[S1;S1;S0])) = Some (StA,([S1],S0,[S1;S0])). Proof. reflexivity. Qed.
Lemma U_STPO_IXP1 : wsteps false true tm 2 (StA,([S0],S1,[])) = Some (StB,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_STPOe_IXP1 : wsteps false true tm 2 (StA,([],S1,[])) = Some (StB,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FINx_IXP1 : wsteps true false tm 5 (StB,([S0],S1,[S0])) = Some (StA,([],S0,[S1;S0])). Proof. reflexivity. Qed.
Lemma U_VB_IXP1 : wsteps true true tm 1 (StA,([],S0,[S0])) = Some (StB,([S1],S0,[])). Proof. reflexivity. Qed.
Lemma U_VD_IXP1 : wsteps true false tm 2 (StB,([S0],S1,[S0])) = Some (StD,([S0],S1,[S0])). Proof. reflexivity. Qed.

(** ** Transported phases *)
Lemma phP1_IXP1 : forall L R, csteps tm 2 (StA,(L,S0,S0::R)) = Some (StA,(L,S1,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_P1_IXP1). Qed.
Lemma phP1i_IXP1 : forall L R, csteps tm 6 (StA,(L,S0,S1::S0::R)) = Some (StA,(L,S1,S1::S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_P1i_IXP1). Qed.
Lemma phRIP_IXP1 : forall k L R, csteps tm (1*k) (StA,(rep [S1] k ++ L,S1,R)) = Some (StA,(L,S1,rep [S1] k ++ R)).
Proof. intros. pose proof (cycL _ _ _ _ _ _ _ U_RIP_IXP1 k L R) as H; cbn [app] in H; exact H. Qed.
Lemma phSTPI_IXP1 : forall L R, csteps tm 1 (StA,(S0::L,S1,R)) = Some (StA,(L,S0,S1::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STPI_IXP1). Qed.
Lemma phTRN_IXP1 : forall L R, csteps tm 1 (StA,(L,S0,S1::R)) = Some (StB,(S1::L,S1,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_TRN_IXP1). Qed.
Lemma phRET_IXP1 : forall k L R, csteps tm (2*k) (StB,(L,S1,rep [S1;S1] k ++ R)) = Some (StB,(rep [S0;S1] k ++ L,S1,R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U_RET_IXP1 k L R). Qed.
Lemma phFIN_IXP1 : forall L R, csteps tm 3 (StB,(L,S1,S1::S0::R)) = Some (StA,(S1::L,S0,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FIN_IXP1). Qed.
Lemma phFINi_IXP1 : forall L R, csteps tm 7 (StB,(L,S1,S1::S1::S0::R)) = Some (StA,(S1::L,S0,S1::S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FINi_IXP1). Qed.
Lemma phSTPO_IXP1 : forall R, csteps tm 2 (StA,([S0],S1,R)) = Some (StB,([S1],S1,R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPO_IXP1). Qed.
Lemma phSTPOe_IXP1 : forall R, csteps tm 2 (StA,([],S1,R)) = Some (StB,([S1],S1,R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPOe_IXP1). Qed.
Lemma phFINx_IXP1 : forall L, csteps tm 5 (StB,(S0::L,S1,[S0])) = Some (StA,(L,S0,[S1;S0])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U_FINx_IXP1). Qed.
Lemma phVB_IXP1 : forall L R, csteps tm 1 (StA,(L,S0,S0::R)) = Some (StB,(S1::L,S0,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_VB_IXP1). Qed.
Lemma phVC_IXP1 : forall x L R, csteps tm 1 (StB,(L,S1,x::R)) = Some (StC,(S1::L,x,R)).
Proof. intros. reflexivity. Qed.
Lemma phVD_IXP1 : forall L, csteps tm 2 (StB,(S0::L,S1,[S0])) = Some (StD,(S0::L,S1,[S0])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U_VD_IXP1). Qed.

(** ** The OUTER interior lap: EXACT (the ILS4F flip chain) *)
Lemma lap_int_IXP1 : forall p j q0, cview p = (j, Some q0) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p j q0 Ecv. unfold Cc_IXP1.
  destruct (cview_some_I p j q0 Ecv) as (HIp & HIs).
  do 2 eexists. split; [|split].
  + rewrite HIp, <- app_assoc. cbn [app].
    rewrite rep_dbl, <- rep_slide.
    eapply csteps_chain. { apply phP1_IXP1. }
    eapply csteps_chain. { apply (phRIP_IXP1 (S (2*j))). }
    eapply csteps_chain. { apply phSTPI_IXP1. }
    eapply csteps_chain. { apply phTRN_IXP1. }
    change (rep [S1] (S (2*j)) ++ [S0]) with (S1 :: rep [S1] (2*j) ++ [S0]).
    rewrite rep_slide, <- rep_dbl.
    eapply csteps_chain. { apply (phRET_IXP1 j). }
    apply phFIN_IXP1.
  + rewrite HIs, <- app_assoc. cbn [app].
    change (rep [S1;S0] j ++ S1 :: S1 :: (Ip q0 ++ [S1;S0]))
      with (rep [S1;S0] j ++ [S1] ++ (S1 :: (Ip q0 ++ [S1;S0]))).
    rewrite app_assoc, pair_rot. reflexivity.
  + lia.
Qed.

(** ** The INNER lap: EXACT, interior [cview] only (all the values the
    inner run visits below the all-ones fill are interior) *)
Lemma lap_inner_IXP1 : forall v j q0, cview v = (j, Some q0) ->
  exists n c', csteps tm n (Cin v) = Some c' /\ c' = Cin (Pos.succ v) /\ 0 < n.
Proof.
  intros v j q0 Ecv. unfold Cin_IXP1.
  destruct (cview_some_I v j q0 Ecv) as (HIp & HIs).
  do 2 eexists. split; [|split].
  + rewrite HIp, <- app_assoc. cbn [app].
    rewrite rep_dbl, <- rep_slide.
    eapply csteps_chain. { apply phP1i_IXP1. }
    eapply csteps_chain. { apply (phRIP_IXP1 (S (2*j))). }
    eapply csteps_chain. { apply phSTPI_IXP1. }
    eapply csteps_chain. { apply phTRN_IXP1. }
    change (rep [S1] (S (2*j)) ++ [S1;S0]) with (S1 :: rep [S1] (2*j) ++ [S1;S0]).
    rewrite rep_slide, <- rep_dbl.
    eapply csteps_chain. { apply (phRET_IXP1 j). }
    apply phFINi_IXP1.
  + rewrite HIs, <- app_assoc. cbn [app].
    change (rep [S1;S0] j ++ S1 :: S1 :: (Ip q0 ++ [S1]))
      with (rep [S1;S0] j ++ [S1] ++ (S1 :: (Ip q0 ++ [S1]))).
    rewrite app_assoc, pair_rot. reflexivity.
  + lia.
Qed.

(** Compose inner laps to the all-ones fill by well-founded induction on
    [tovf] (strictly decreasing along interior laps). *)
Lemma inner_to_fill_IXP1 : forall v, exists n,
  csteps tm n (Cin v) = Some (Cin (fill v)).
Proof.
  intro v; remember (tovf v) as fuel eqn:Ef; revert v Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros v Ef.
  destruct (cview v) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf v <> 0).
    { intro H0. destruct (tovf0_allones v H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }
    destruct (lap_inner_IXP1 v j q0 Ecv) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ v)) (ltac:(rewrite tovf_succ by lia; lia)) (Pos.succ v) eq_refl) as (k & Hk).
    exists (n + k). rewrite csteps_add, Hrun.
    rewrite (fill_succ v j q0 Ecv) in Hk. exact Hk.
  - destruct j as [|j'].
    { exfalso. destruct v; simpl in Ecv; [destruct (cview v); discriminate|discriminate|discriminate]. }
    exists 0. rewrite (fill_allones v j' Ecv). reflexivity.
Qed.

(** ** Boot: from the outer all-ones anchor into the inner family *)
Lemma boot_ov_IXP1 : forall n, exists m c',
  csteps tm m (StA, ((rep [S1;S1] n ++ [S1]) ++ [S1;S0], S0, [S0])) = Some c'
  /\ c' = Cin (pow2 n) /\ 0 < m.
Proof.
  intro n.
  do 2 eexists. split; [|split].
  + rewrite <- app_assoc. cbn [app].
    rewrite rep_dbl, <- !rep_slide.
    eapply csteps_chain. { apply phP1_IXP1. }
    eapply csteps_chain. { apply (phRIP_IXP1 (S (S (2*n)))). }
    eapply csteps_chain. { apply phSTPO_IXP1. }
    change (rep [S1] (S (S (2*n))) ++ [S0]) with (S1 :: S1 :: rep [S1] (2*n) ++ [S0]).
    rewrite <- rep_dbl.
    change (S1 :: S1 :: rep [S1;S1] n ++ [S0]) with (rep [S1;S1] (S n) ++ [S0]).
    eapply csteps_chain. { apply (phRET_IXP1 (S n)). }
    change (rep [S0;S1] (S n) ++ [S1]) with (S0 :: S1 :: rep [S0;S1] n ++ [S1]).
    apply phFINx_IXP1.
  + unfold Cin_IXP1. rewrite Ip_pow2, pair_rot. reflexivity.
  + lia.
Qed.

(** ** Exit: from the inner all-ones anchor back to the outer family,
    one left blank short of the anchor tail (lift close) *)
Lemma exit_ov_IXP1 : forall n, exists m c',
  csteps tm m (StA, ((rep [S1;S1] n ++ [S1]) ++ [S1], S0, [S1;S0])) = Some c'
  /\ c' = (StA, (S1 :: rep [S0;S1] (S n) ++ [S1], S0, [S0])) /\ 0 < m.
Proof.
  intro n.
  do 2 eexists. split; [|split].
  + rewrite <- app_assoc. cbn [app].
    rewrite pair_fold, rep_dbl.
    eapply csteps_chain. { apply phP1i_IXP1. }
    eapply csteps_chain. { apply (phRIP_IXP1 (2 * S n)). }
    eapply csteps_chain. { apply phSTPOe_IXP1. }
    rewrite <- rep_dbl.
    eapply csteps_chain. { apply (phRET_IXP1 (S n)). }
    apply phFIN_IXP1.
  + reflexivity.
  + lia.
Qed.

Lemma lift_lblank_IXP1 : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

(** ** The OUTER overflow lap: boot ; inner counting ; exit *)
Lemma lap_ov_IXP1 : forall p j', cview p = (S j', None) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j' Ecv.
  destruct (cview_none_I p j' Ecv) as (HIp & HIs).
  pose proof (cview_none_shape p j' Ecv) as Hp.
  destruct (boot_ov_IXP1 j') as (m1 & c1 & Hb & Hc1 & Hm1).
  destruct (inner_to_fill_IXP1 (pow2 j')) as (m2 & Hi).
  destruct (exit_ov_IXP1 j') as (m3 & c3 & Hx & Hc3 & _).
  exists (m1 + (m2 + m3)), c3. split; [|split].
  + unfold Cc_IXP1. rewrite HIp.
    rewrite csteps_add, Hb. subst c1.
    rewrite csteps_add, Hi.
    rewrite <- Hp.
    unfold Cin_IXP1. rewrite HIp. exact Hx.
  + subst c3. unfold Cc_IXP1. rewrite HIs.
    rewrite <- app_assoc. cbn [app].
    change (rep [S1;S0] (S j') ++ S1 :: S1 :: S0 :: nil)
      with (rep [S1;S0] (S j') ++ [S1] ++ [S1] ++ [S0]).
    rewrite !app_assoc.
    rewrite lift_lblank_IXP1.
    rewrite pair_rot.
    reflexivity.
  + lia.
Qed.

Lemma lap_IXP1 : forall p, exists n c', csteps tm n (Cc p) = Some c' /\
  lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - destruct (lap_int_IXP1 p j q0 Ecv) as (n & c' & H1 & H2 & H3).
    exists n, c'. split; [exact H1|split; [rewrite H2; reflexivity|exact H3]].
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    exact (lap_ov_IXP1 p j' Ecv).
Qed.

Lemma boot_IXP1 : exists t0, stepn tm t0 InitES = Some (lift (Cc 2)).
Proof.
  exists 42.
  assert (H : match csteps tm 42 c0 with Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 42 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits *)

(** StB: one step from the anchor. *)
Lemma vis_B_IXP1 : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StB.
Proof.
  intro p. unfold Cc_IXP1. exists 1. eexists. split.
  - apply phVB_IXP1.
  - reflexivity.
Qed.

(** StC: one step past the turn (interior) / past the overflow stop. *)
Lemma vis_C_IXP1 : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StC.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - destruct (cview_some_I p j q0 Ecv) as (HIp & _).
    unfold Cc_IXP1. eexists. eexists. split.
    + rewrite HIp, <- app_assoc. cbn [app].
      rewrite rep_dbl, <- rep_slide.
      eapply csteps_chain. { apply phP1_IXP1. }
      eapply csteps_chain. { apply (phRIP_IXP1 (S (2*j))). }
      eapply csteps_chain. { apply phSTPI_IXP1. }
      eapply csteps_chain. { apply phTRN_IXP1. }
      change (rep [S1] (S (2*j)) ++ [S0]) with (S1 :: rep [S1] (2*j) ++ [S0]).
      apply phVC_IXP1.
    + reflexivity.
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_I p j' Ecv) as (HIp & _).
    unfold Cc_IXP1. eexists. eexists. split.
    + rewrite HIp, <- app_assoc. cbn [app].
      rewrite rep_dbl, <- !rep_slide.
      eapply csteps_chain. { apply phP1_IXP1. }
      eapply csteps_chain. { apply (phRIP_IXP1 (S (S (2*j')))). }
      eapply csteps_chain. { apply phSTPO_IXP1. }
      change (rep [S1] (S (S (2*j'))) ++ [S0]) with (S1 :: S1 :: rep [S1] (2*j') ++ [S0]).
      apply phVC_IXP1.
    + reflexivity.
Qed.

(** StD fires only inside the OVERFLOW machinery; reach an all-ones
    counter by well-founded induction on [tovf] (the interior laps close
    EXACTLY), then run the boot prefix into its close. *)
Lemma vis_D_IXP1 : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StD.
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }
    destruct (lap_int_IXP1 p j q0 Ecv) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia)) (Pos.succ p) eq_refl) as (k & c & Hk & Hq).
    exists (n + k), c. rewrite csteps_add, Hrun. exact (conj Hk Hq).
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_I p j' Ecv) as (HIp & _).
    unfold Cc_IXP1. eexists. eexists. split.
    + rewrite HIp, <- app_assoc. cbn [app].
      rewrite rep_dbl, <- !rep_slide.
      eapply csteps_chain. { apply phP1_IXP1. }
      eapply csteps_chain. { apply (phRIP_IXP1 (S (S (2*j')))). }
      eapply csteps_chain. { apply phSTPO_IXP1. }
      change (rep [S1] (S (S (2*j'))) ++ [S0]) with (S1 :: S1 :: rep [S1] (2*j') ++ [S0]).
      rewrite <- rep_dbl.
      change (S1 :: S1 :: rep [S1;S1] j' ++ [S0]) with (rep [S1;S1] (S j') ++ [S0]).
      eapply csteps_chain. { apply (phRET_IXP1 (S j')). }
      change (rep [S0;S1] (S j') ++ [S1]) with (S0 :: S1 :: rep [S0;S1] j' ++ [S1]).
      apply phVD_IXP1.
    + reflexivity.
Qed.

Lemma vis_IXP1 : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q. destruct q.
  - exists 0. eexists. split; reflexivity.
  - apply vis_B_IXP1.
  - apply vis_C_IXP1.
  - apply vis_D_IXP1.
Qed.

Theorem nqh_1RB1LA_0LA1RC_0LD0RB_0LA1RD : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 2). - exact boot_IXP1. - intros p _. apply lap_IXP1. - intros p q _. apply vis_IXP1. Qed.

Theorem nonhalt_1RB1LA_0LA1RC_0LD0RB_0LA1RD : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_1RB1LA_0LA1RC_0LD0RB_0LA1RD. Qed.
