(** * ILCM_1RB0LD1LC1RAHHH1RD0RB1LD: 1RB0LD_1LC1RA_---1RD_0RB1LD -- right-growth interleaved counter via Mirror.

    A comb-free interleaved binary counter growing on the RIGHT, so the
    [Interleave_TGT.v] lap does not apply directly.  Its mirror
    (1LB0RD_1RC1LA_---1LD_0LB1RD) is the same counter grown LEFTward, carrying the
    [JpCounter] anchor family

        Cc p = (StD, (Jp p ++ [], S0, []))

    (the counter nearest-first on the left, the fixed cap [] parked
    below its most significant end, blank head, empty right side) and the
    template's single-sweep lap: prologue; leftward carry ripple over the low
    set pairs; interior stop, or overflow stop off the deep-left edge through
    the cap; rightward return; close at the frontier.
    [Mirror.mirror_never_qh] transfers [NeverQuasiHaltsSt] from the mirror
    back to the machine.

    Auto-emitted by tools/counters/emit_mirror.py (UNTRUSTED -- every line
    below is re-checked by the Coq kernel).  Phase lengths
    P1=1 RIP=2 STPI=2 STPO=4 RET=1 (width 1)
    FIN=1; bootstrap 9 steps to Cc 1.

    Axiom footprint: [functional_extensionality_dep] only. *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded
     FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ILCounter JpCounter.
Import ListNotations.

Definition mk_1RB0LD1LC1RAHHH1RD0RB1LD (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** The machine 1RB0LD_1LC1RA_---1RD_0RB1LD. *)
Definition tm_1RB0LD1LC1RAHHH1RD0RB1LD : TM := fun q s => match q, s with
  | StA, S0 => mk_1RB0LD1LC1RAHHH1RD0RB1LD S1 DR StB | StA, S1 => mk_1RB0LD1LC1RAHHH1RD0RB1LD S0 DL StD
  | StB, S0 => mk_1RB0LD1LC1RAHHH1RD0RB1LD S1 DL StC | StB, S1 => mk_1RB0LD1LC1RAHHH1RD0RB1LD S1 DR StA
  | StC, S0 => None | StC, S1 => mk_1RB0LD1LC1RAHHH1RD0RB1LD S1 DR StD
  | StD, S0 => mk_1RB0LD1LC1RAHHH1RD0RB1LD S0 DR StB | StD, S1 => mk_1RB0LD1LC1RAHHH1RD0RB1LD S1 DL StD end.

(** Its mirror 1LB0RD_1RC1LA_---1LD_0LB1RD: the same counter, grown leftward. *)
Definition tmm_1RB0LD1LC1RAHHH1RD0RB1LD : TM := fun q s => match q, s with
  | StA, S0 => mk_1RB0LD1LC1RAHHH1RD0RB1LD S1 DL StB | StA, S1 => mk_1RB0LD1LC1RAHHH1RD0RB1LD S0 DR StD
  | StB, S0 => mk_1RB0LD1LC1RAHHH1RD0RB1LD S1 DR StC | StB, S1 => mk_1RB0LD1LC1RAHHH1RD0RB1LD S1 DL StA
  | StC, S0 => None | StC, S1 => mk_1RB0LD1LC1RAHHH1RD0RB1LD S1 DL StD
  | StD, S0 => mk_1RB0LD1LC1RAHHH1RD0RB1LD S0 DL StB | StD, S1 => mk_1RB0LD1LC1RAHHH1RD0RB1LD S1 DR StD end.

Lemma mirror_ok_1RB0LD1LC1RAHHH1RD0RB1LD : mirror_tm tm_1RB0LD1LC1RAHHH1RD0RB1LD = tmm_1RB0LD1LC1RAHHH1RD0RB1LD.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro s; destruct q, s; reflexivity.
Qed.

Definition Cc_1RB0LD1LC1RAHHH1RD0RB1LD (p : positive) : cconf := (StD, (Jp p ++ [], S0, [])).

(* --- the two anchor-closing identities (interior / overflow) --- *)
Lemma clsI_1RB0LD1LC1RAHHH1RD0RB1LD : forall j Y,
  S1 :: rep [S1] (2*j) ++ S0 :: S1 :: (Y ++ [])
  = (rep [S1;S1] j ++ S1 :: S0 :: S1 :: Y) ++ [].
Proof. intros. rewrite rep_dbl, rep_slide, <- app_assoc. reflexivity. Qed.
Lemma clsO_1RB0LD1LC1RAHHH1RD0RB1LD : forall j',
  S1 :: rep [S1] (2*(S j')) ++ [] = (rep [S1;S1] (S j') ++ [S1]) ++ [].
Proof. intros. rewrite rep_dbl, rep_slide, <- app_assoc. reflexivity. Qed.

(* --- the lap unit windows (derived by simulation, closed by reflexivity) --- *)
Lemma U_P1_1RB0LD1LC1RAHHH1RD0RB1LD : wsteps true true tmm_1RB0LD1LC1RAHHH1RD0RB1LD 1 (StD,([S1],S0,[]))
  = Some (StB,([],S1,[S0])). Proof. reflexivity. Qed.
Lemma U_RIP_1RB0LD1LC1RAHHH1RD0RB1LD : wsteps true true tmm_1RB0LD1LC1RAHHH1RD0RB1LD 2 (StB,([S0;S1],S1,[]))
  = Some (StB,([],S1,[S1;S1])). Proof. reflexivity. Qed.
Lemma U_STPI_1RB0LD1LC1RAHHH1RD0RB1LD : wsteps true true tmm_1RB0LD1LC1RAHHH1RD0RB1LD 2 (StB,([S1;S1],S1,[]))
  = Some (StD,([S0;S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_STPO_1RB0LD1LC1RAHHH1RD0RB1LD : wsteps false true tmm_1RB0LD1LC1RAHHH1RD0RB1LD 4 (StB,([],S1,[]))
  = Some (StD,([],S1,[S1; S1])). Proof. reflexivity. Qed.
Lemma U_RET_1RB0LD1LC1RAHHH1RD0RB1LD : wsteps true true tmm_1RB0LD1LC1RAHHH1RD0RB1LD 1 (StD,([],S1,[S1]))
  = Some (StD,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FIN_1RB0LD1LC1RAHHH1RD0RB1LD : wsteps true true tmm_1RB0LD1LC1RAHHH1RD0RB1LD 1 (StD,([],S1,[S0]))
  = Some (StD,([S1],S0,[])). Proof. reflexivity. Qed.

(* --- transported phases (framing = each unit's bl/br) --- *)
Lemma phP1_1RB0LD1LC1RAHHH1RD0RB1LD : forall L R,
  csteps tmm_1RB0LD1LC1RAHHH1RD0RB1LD 1 (StD,(S1::L,S0,R)) = Some (StB,(L,S1,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_P1_1RB0LD1LC1RAHHH1RD0RB1LD). Qed.
Lemma phRIP_1RB0LD1LC1RAHHH1RD0RB1LD : forall k L R,
  csteps tmm_1RB0LD1LC1RAHHH1RD0RB1LD (2*k) (StB,(rep [S0;S1] k ++ L,S1,R))
  = Some (StB,(L,S1,rep [S1;S1] k ++ R)).
Proof. intros. pose proof (cycL _ _ _ _ _ _ _ U_RIP_1RB0LD1LC1RAHHH1RD0RB1LD k L R) as H;
  cbn [app] in H; exact H. Qed.
Lemma phSTPI_1RB0LD1LC1RAHHH1RD0RB1LD : forall L R,
  csteps tmm_1RB0LD1LC1RAHHH1RD0RB1LD 2 (StB,(S1::S1::L,S1,R)) = Some (StD,(S0::S1::L,S1,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STPI_1RB0LD1LC1RAHHH1RD0RB1LD). Qed.
Lemma phSTPO_1RB0LD1LC1RAHHH1RD0RB1LD : forall R,
  csteps tmm_1RB0LD1LC1RAHHH1RD0RB1LD 4 (StB,([],S1,R))
  = Some (StD,([],S1,S1 :: S1 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPO_1RB0LD1LC1RAHHH1RD0RB1LD). Qed.
Lemma phRET_1RB0LD1LC1RAHHH1RD0RB1LD : forall k L R,
  csteps tmm_1RB0LD1LC1RAHHH1RD0RB1LD (1*k) (StD,(L,S1,rep [S1] k ++ R))
  = Some (StD,(rep [S1] k ++ L,S1,R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U_RET_1RB0LD1LC1RAHHH1RD0RB1LD k L R). Qed.
Lemma phFIN_1RB0LD1LC1RAHHH1RD0RB1LD : forall L R,
  csteps tmm_1RB0LD1LC1RAHHH1RD0RB1LD 1 (StD,(L,S1,S0::R)) = Some (StD,(S1::L,S0,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FIN_1RB0LD1LC1RAHHH1RD0RB1LD). Qed.

(** The exact lap: from the anchor at p to the anchor at p+1. *)
Lemma lap_exact_1RB0LD1LC1RAHHH1RD0RB1LD : forall p, exists n c',
  csteps tmm_1RB0LD1LC1RAHHH1RD0RB1LD n (Cc_1RB0LD1LC1RAHHH1RD0RB1LD p) = Some c' /\ c' = Cc_1RB0LD1LC1RAHHH1RD0RB1LD (Pos.succ p) /\ 0 < n.
Proof.
  intros p. pose proof (Pos2Nat.is_pos p) as Hpos.
  destruct (cview p) as [j oq] eqn:Ecv. unfold Cc_1RB0LD1LC1RAHHH1RD0RB1LD.
  destruct oq as [q0|].
  - destruct (cview_some_J p j q0 Ecv) as (HJp & HJs).
    destruct (Jp_head q0) as (iq & Hiq).
    do 2 eexists. split; [|split].
    + rewrite HJp, <- app_assoc.
      change (rep [S1;S0] j ++ (S1 :: S1 :: Jp q0) ++ [])
        with (rep [S1;S0] j ++ [S1] ++ (S1 :: Jp q0 ++ [])).
      rewrite app_assoc, pair_rot.
      eapply csteps_chain. { apply phP1_1RB0LD1LC1RAHHH1RD0RB1LD. }
      eapply csteps_chain. { apply phRIP_1RB0LD1LC1RAHHH1RD0RB1LD. }
      rewrite Hiq.
      eapply csteps_chain. { apply phSTPI_1RB0LD1LC1RAHHH1RD0RB1LD. }
      rewrite rep_dbl.
      eapply csteps_chain. { apply (phRET_1RB0LD1LC1RAHHH1RD0RB1LD (2*j)). }
      apply phFIN_1RB0LD1LC1RAHHH1RD0RB1LD.
    + rewrite HJs, Hiq, <- clsI_1RB0LD1LC1RAHHH1RD0RB1LD. reflexivity.
    + lia.
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv;
       [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_J p j' Ecv) as (HJp & HJs).
    do 2 eexists. split; [|split].
    + rewrite HJp, pair_rot.
      eapply csteps_chain. { apply phP1_1RB0LD1LC1RAHHH1RD0RB1LD. }
      eapply csteps_chain. { apply phRIP_1RB0LD1LC1RAHHH1RD0RB1LD. }
      eapply csteps_chain. { apply phSTPO_1RB0LD1LC1RAHHH1RD0RB1LD. }
      change (S1 :: S1 :: rep [S1;S1] j' ++ [S0])
        with (rep [S1;S1] (S j') ++ [S0]).
      rewrite rep_dbl.
      eapply csteps_chain. { apply (phRET_1RB0LD1LC1RAHHH1RD0RB1LD (2*(S j'))). }
      apply phFIN_1RB0LD1LC1RAHHH1RD0RB1LD.
    + rewrite HJs, <- clsO_1RB0LD1LC1RAHHH1RD0RB1LD. reflexivity.
    + lia.
Qed.

Lemma lap_1RB0LD1LC1RAHHH1RD0RB1LD : forall p, exists n c',
  csteps tmm_1RB0LD1LC1RAHHH1RD0RB1LD n (Cc_1RB0LD1LC1RAHHH1RD0RB1LD p) = Some c' /\
  lift c' = lift (Cc_1RB0LD1LC1RAHHH1RD0RB1LD (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (lap_exact_1RB0LD1LC1RAHHH1RD0RB1LD p) as (n & c' & Hr & Hc & Hn).
  exists n, c'. split; [exact Hr | split; [rewrite Hc; reflexivity | exact Hn]].
Qed.

Lemma boot_1RB0LD1LC1RAHHH1RD0RB1LD : exists t0, stepn tmm_1RB0LD1LC1RAHHH1RD0RB1LD t0 InitES = Some (lift (Cc_1RB0LD1LC1RAHHH1RD0RB1LD 1)).
Proof.
  exists 9.
  assert (H : match csteps tmm_1RB0LD1LC1RAHHH1RD0RB1LD 9 c0 with
              | Some c => ceqb c (Cc_1RB0LD1LC1RAHHH1RD0RB1LD 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tmm_1RB0LD1LC1RAHHH1RD0RB1LD 9 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** The log-rare state StC: reached inside the overflow stop, so the anchor
    walks forward (well-founded on [tovf]) until the counter is all ones. *)
Lemma U_VAC_1RB0LD1LC1RAHHH1RD0RB1LD : wsteps false true tmm_1RB0LD1LC1RAHHH1RD0RB1LD 3 (StB,([],S1,[]))
  = Some (StC,([S1],S1,[S1])). Proof. reflexivity. Qed.
Lemma phVAC_1RB0LD1LC1RAHHH1RD0RB1LD : forall R,
  csteps tmm_1RB0LD1LC1RAHHH1RD0RB1LD 3 (StB,([],S1,R)) = Some (StC,([S1],S1,S1 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_VAC_1RB0LD1LC1RAHHH1RD0RB1LD). Qed.

Lemma visC_1RB0LD1LC1RAHHH1RD0RB1LD : forall p, exists k c,
  csteps tmm_1RB0LD1LC1RAHHH1RD0RB1LD k (Cc_1RB0LD1LC1RAHHH1RD0RB1LD p) = Some c /\ fst c = StC.
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj).
       rewrite Hjj in Ecv; discriminate. }
    destruct (lap_exact_1RB0LD1LC1RAHHH1RD0RB1LD p) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia))
                 (Pos.succ p) eq_refl) as (k & c & Hk & Hq).
    exists (n + k), c. rewrite csteps_add, Hrun. exact (conj Hk Hq).
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv;
       [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_J p j' Ecv) as (HJp & _).
    unfold Cc_1RB0LD1LC1RAHHH1RD0RB1LD. eexists. eexists. split.
    * rewrite HJp, pair_rot.
      eapply csteps_chain. { apply phP1_1RB0LD1LC1RAHHH1RD0RB1LD. }
      eapply csteps_chain. { apply phRIP_1RB0LD1LC1RAHHH1RD0RB1LD. }
      apply phVAC_1RB0LD1LC1RAHHH1RD0RB1LD.
    * reflexivity.
Qed.

(* --- determined prefixes from the anchor --- *)
Lemma phVA_1RB0LD1LC1RAHHH1RD0RB1LD : forall x L,
  csteps tmm_1RB0LD1LC1RAHHH1RD0RB1LD 2 (StD,(S1::x::L,S0,[]))
  = Some (StA,(L,x,[S1; S0])).
Proof. reflexivity. Qed.

Lemma phVB_1RB0LD1LC1RAHHH1RD0RB1LD : forall L,
  csteps tmm_1RB0LD1LC1RAHHH1RD0RB1LD 1 (StD,(S1::L,S0,[]))
  = Some (StB,(L,S1,[S0])).
Proof. reflexivity. Qed.

Lemma vis_1RB0LD1LC1RAHHH1RD0RB1LD : forall p q, exists k c,
  csteps tmm_1RB0LD1LC1RAHHH1RD0RB1LD k (Cc_1RB0LD1LC1RAHHH1RD0RB1LD p) = Some c /\ fst c = q.
Proof.
  intros p q. destruct (Jp_head p) as (w & Hw). unfold Cc_1RB0LD1LC1RAHHH1RD0RB1LD. destruct q.
  - rewrite Hw. destruct w as [|x w'].
    + exists 2. eexists. split;
      [ vm_compute; reflexivity | reflexivity ].
    + exists 2. eexists. split.
      * change ((S1 :: x :: w') ++ [])
          with (S1 :: x :: (w' ++ [])). apply phVA_1RB0LD1LC1RAHHH1RD0RB1LD.
      * reflexivity.
  - exists 1. eexists. rewrite Hw.
    split; [apply phVB_1RB0LD1LC1RAHHH1RD0RB1LD | reflexivity].
  - apply (visC_1RB0LD1LC1RAHHH1RD0RB1LD p).
  - exists 0. eexists. split; reflexivity.
Qed.

Lemma nqhm_1RB0LD1LC1RAHHH1RD0RB1LD : NeverQuasiHaltsSt tmm_1RB0LD1LC1RAHHH1RD0RB1LD.
Proof.
  apply (glue_neverqh tmm_1RB0LD1LC1RAHHH1RD0RB1LD Cc_1RB0LD1LC1RAHHH1RD0RB1LD 1).
  - exact boot_1RB0LD1LC1RAHHH1RD0RB1LD.
  - intros p _. apply lap_1RB0LD1LC1RAHHH1RD0RB1LD.
  - intros p q _. apply vis_1RB0LD1LC1RAHHH1RD0RB1LD.
Qed.

Theorem nqh_1RB0LD1LC1RAHHH1RD0RB1LD : NeverQuasiHaltsSt tm_1RB0LD1LC1RAHHH1RD0RB1LD.
Proof.
  apply (mirror_never_qh tm_1RB0LD1LC1RAHHH1RD0RB1LD). rewrite mirror_ok_1RB0LD1LC1RAHHH1RD0RB1LD. exact nqhm_1RB0LD1LC1RAHHH1RD0RB1LD.
Qed.

Theorem nonhalt_1RB0LD1LC1RAHHH1RD0RB1LD : NonHalt tm_1RB0LD1LC1RAHHH1RD0RB1LD.
Proof. apply never_qh_nonhalt, nqh_1RB0LD1LC1RAHHH1RD0RB1LD. Qed.
