(** * ILCM_0RB1LA1LC1RD1RC1LA1RB0LA: 0RB1LA_1LC1RD_1RC1LA_1RB0LA -- right-growth interleaved counter via Mirror.

    A comb-free interleaved binary counter growing on the RIGHT, so the
    [Interleave_TGT.v] lap does not apply directly.  Its mirror
    (0LB1RA_1RC1LD_1LC1RA_1LB0RA) is the same counter grown LEFTward, carrying the
    [JpCounter] anchor family

        Cc p = (StA, (Jp p ++ [], S0, []))

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

Definition mk_0RB1LA1LC1RD1RC1LA1RB0LA (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** The machine 0RB1LA_1LC1RD_1RC1LA_1RB0LA. *)
Definition tm_0RB1LA1LC1RD1RC1LA1RB0LA : TM := fun q s => match q, s with
  | StA, S0 => mk_0RB1LA1LC1RD1RC1LA1RB0LA S0 DR StB | StA, S1 => mk_0RB1LA1LC1RD1RC1LA1RB0LA S1 DL StA
  | StB, S0 => mk_0RB1LA1LC1RD1RC1LA1RB0LA S1 DL StC | StB, S1 => mk_0RB1LA1LC1RD1RC1LA1RB0LA S1 DR StD
  | StC, S0 => mk_0RB1LA1LC1RD1RC1LA1RB0LA S1 DR StC | StC, S1 => mk_0RB1LA1LC1RD1RC1LA1RB0LA S1 DL StA
  | StD, S0 => mk_0RB1LA1LC1RD1RC1LA1RB0LA S1 DR StB | StD, S1 => mk_0RB1LA1LC1RD1RC1LA1RB0LA S0 DL StA end.

(** Its mirror 0LB1RA_1RC1LD_1LC1RA_1LB0RA: the same counter, grown leftward. *)
Definition tmm_0RB1LA1LC1RD1RC1LA1RB0LA : TM := fun q s => match q, s with
  | StA, S0 => mk_0RB1LA1LC1RD1RC1LA1RB0LA S0 DL StB | StA, S1 => mk_0RB1LA1LC1RD1RC1LA1RB0LA S1 DR StA
  | StB, S0 => mk_0RB1LA1LC1RD1RC1LA1RB0LA S1 DR StC | StB, S1 => mk_0RB1LA1LC1RD1RC1LA1RB0LA S1 DL StD
  | StC, S0 => mk_0RB1LA1LC1RD1RC1LA1RB0LA S1 DL StC | StC, S1 => mk_0RB1LA1LC1RD1RC1LA1RB0LA S1 DR StA
  | StD, S0 => mk_0RB1LA1LC1RD1RC1LA1RB0LA S1 DL StB | StD, S1 => mk_0RB1LA1LC1RD1RC1LA1RB0LA S0 DR StA end.

Lemma mirror_ok_0RB1LA1LC1RD1RC1LA1RB0LA : mirror_tm tm_0RB1LA1LC1RD1RC1LA1RB0LA = tmm_0RB1LA1LC1RD1RC1LA1RB0LA.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro s; destruct q, s; reflexivity.
Qed.

Definition Cc_0RB1LA1LC1RD1RC1LA1RB0LA (p : positive) : cconf := (StA, (Jp p ++ [], S0, [])).

(* --- the two anchor-closing identities (interior / overflow) --- *)
Lemma clsI_0RB1LA1LC1RD1RC1LA1RB0LA : forall j Y,
  S1 :: rep [S1] (2*j) ++ S0 :: S1 :: (Y ++ [])
  = (rep [S1;S1] j ++ S1 :: S0 :: S1 :: Y) ++ [].
Proof. intros. rewrite rep_dbl, rep_slide, <- app_assoc. reflexivity. Qed.
Lemma clsO_0RB1LA1LC1RD1RC1LA1RB0LA : forall j',
  S1 :: rep [S1] (2*j') ++ S1 :: S1 :: [] = (rep [S1;S1] (S j') ++ [S1]) ++ [].
Proof. intros. rewrite rep_dbl, <- app_assoc.
  replace (2 * S j') with ((2*j') + 2) by lia.
  rewrite rep_add, <- app_assoc. cbn [rep app].
  rewrite rep_slide. reflexivity. Qed.

(* --- the lap unit windows (derived by simulation, closed by reflexivity) --- *)
Lemma U_P1_0RB1LA1LC1RD1RC1LA1RB0LA : wsteps true true tmm_0RB1LA1LC1RD1RC1LA1RB0LA 1 (StA,([S1],S0,[]))
  = Some (StB,([],S1,[S0])). Proof. reflexivity. Qed.
Lemma U_RIP_0RB1LA1LC1RD1RC1LA1RB0LA : wsteps true true tmm_0RB1LA1LC1RD1RC1LA1RB0LA 2 (StB,([S0;S1],S1,[]))
  = Some (StB,([],S1,[S1;S1])). Proof. reflexivity. Qed.
Lemma U_STPI_0RB1LA1LC1RD1RC1LA1RB0LA : wsteps true true tmm_0RB1LA1LC1RD1RC1LA1RB0LA 2 (StB,([S1;S1],S1,[]))
  = Some (StA,([S0;S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_STPO_0RB1LA1LC1RD1RC1LA1RB0LA : wsteps false true tmm_0RB1LA1LC1RD1RC1LA1RB0LA 4 (StB,([],S1,[]))
  = Some (StA,(S1 :: S1 :: [],S1,[])). Proof. reflexivity. Qed.
Lemma U_RET_0RB1LA1LC1RD1RC1LA1RB0LA : wsteps true true tmm_0RB1LA1LC1RD1RC1LA1RB0LA 1 (StA,([],S1,[S1]))
  = Some (StA,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FIN_0RB1LA1LC1RD1RC1LA1RB0LA : wsteps true true tmm_0RB1LA1LC1RD1RC1LA1RB0LA 1 (StA,([],S1,[S0]))
  = Some (StA,([S1],S0,[])). Proof. reflexivity. Qed.

(* --- transported phases (framing = each unit's bl/br) --- *)
Lemma phP1_0RB1LA1LC1RD1RC1LA1RB0LA : forall L R,
  csteps tmm_0RB1LA1LC1RD1RC1LA1RB0LA 1 (StA,(S1::L,S0,R)) = Some (StB,(L,S1,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_P1_0RB1LA1LC1RD1RC1LA1RB0LA). Qed.
Lemma phRIP_0RB1LA1LC1RD1RC1LA1RB0LA : forall k L R,
  csteps tmm_0RB1LA1LC1RD1RC1LA1RB0LA (2*k) (StB,(rep [S0;S1] k ++ L,S1,R))
  = Some (StB,(L,S1,rep [S1;S1] k ++ R)).
Proof. intros. pose proof (cycL _ _ _ _ _ _ _ U_RIP_0RB1LA1LC1RD1RC1LA1RB0LA k L R) as H;
  cbn [app] in H; exact H. Qed.
Lemma phSTPI_0RB1LA1LC1RD1RC1LA1RB0LA : forall L R,
  csteps tmm_0RB1LA1LC1RD1RC1LA1RB0LA 2 (StB,(S1::S1::L,S1,R)) = Some (StA,(S0::S1::L,S1,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STPI_0RB1LA1LC1RD1RC1LA1RB0LA). Qed.
Lemma phSTPO_0RB1LA1LC1RD1RC1LA1RB0LA : forall R,
  csteps tmm_0RB1LA1LC1RD1RC1LA1RB0LA 4 (StB,([],S1,R))
  = Some (StA,(S1 :: S1 :: [],S1,R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPO_0RB1LA1LC1RD1RC1LA1RB0LA). Qed.
Lemma phRET_0RB1LA1LC1RD1RC1LA1RB0LA : forall k L R,
  csteps tmm_0RB1LA1LC1RD1RC1LA1RB0LA (1*k) (StA,(L,S1,rep [S1] k ++ R))
  = Some (StA,(rep [S1] k ++ L,S1,R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U_RET_0RB1LA1LC1RD1RC1LA1RB0LA k L R). Qed.
Lemma phFIN_0RB1LA1LC1RD1RC1LA1RB0LA : forall L R,
  csteps tmm_0RB1LA1LC1RD1RC1LA1RB0LA 1 (StA,(L,S1,S0::R)) = Some (StA,(S1::L,S0,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FIN_0RB1LA1LC1RD1RC1LA1RB0LA). Qed.

(** The exact lap: from the anchor at p to the anchor at p+1. *)
Lemma lap_exact_0RB1LA1LC1RD1RC1LA1RB0LA : forall p, exists n c',
  csteps tmm_0RB1LA1LC1RD1RC1LA1RB0LA n (Cc_0RB1LA1LC1RD1RC1LA1RB0LA p) = Some c' /\ c' = Cc_0RB1LA1LC1RD1RC1LA1RB0LA (Pos.succ p) /\ 0 < n.
Proof.
  intros p. pose proof (Pos2Nat.is_pos p) as Hpos.
  destruct (cview p) as [j oq] eqn:Ecv. unfold Cc_0RB1LA1LC1RD1RC1LA1RB0LA.
  destruct oq as [q0|].
  - destruct (cview_some_J p j q0 Ecv) as (HJp & HJs).
    destruct (Jp_head q0) as (iq & Hiq).
    do 2 eexists. split; [|split].
    + rewrite HJp, <- app_assoc.
      change (rep [S1;S0] j ++ (S1 :: S1 :: Jp q0) ++ [])
        with (rep [S1;S0] j ++ [S1] ++ (S1 :: Jp q0 ++ [])).
      rewrite app_assoc, pair_rot.
      eapply csteps_chain. { apply phP1_0RB1LA1LC1RD1RC1LA1RB0LA. }
      eapply csteps_chain. { apply phRIP_0RB1LA1LC1RD1RC1LA1RB0LA. }
      rewrite Hiq.
      eapply csteps_chain. { apply phSTPI_0RB1LA1LC1RD1RC1LA1RB0LA. }
      rewrite rep_dbl.
      eapply csteps_chain. { apply (phRET_0RB1LA1LC1RD1RC1LA1RB0LA (2*j)). }
      apply phFIN_0RB1LA1LC1RD1RC1LA1RB0LA.
    + rewrite HJs, Hiq, <- clsI_0RB1LA1LC1RD1RC1LA1RB0LA. reflexivity.
    + lia.
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv;
       [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_J p j' Ecv) as (HJp & HJs).
    do 2 eexists. split; [|split].
    + rewrite HJp, pair_rot.
      eapply csteps_chain. { apply phP1_0RB1LA1LC1RD1RC1LA1RB0LA. }
      eapply csteps_chain. { apply phRIP_0RB1LA1LC1RD1RC1LA1RB0LA. }
      eapply csteps_chain. { apply phSTPO_0RB1LA1LC1RD1RC1LA1RB0LA. }
      rewrite rep_dbl.
      eapply csteps_chain. { apply (phRET_0RB1LA1LC1RD1RC1LA1RB0LA (2*j')). }
      apply phFIN_0RB1LA1LC1RD1RC1LA1RB0LA.
    + rewrite HJs, <- clsO_0RB1LA1LC1RD1RC1LA1RB0LA. reflexivity.
    + lia.
Qed.

Lemma lap_0RB1LA1LC1RD1RC1LA1RB0LA : forall p, exists n c',
  csteps tmm_0RB1LA1LC1RD1RC1LA1RB0LA n (Cc_0RB1LA1LC1RD1RC1LA1RB0LA p) = Some c' /\
  lift c' = lift (Cc_0RB1LA1LC1RD1RC1LA1RB0LA (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (lap_exact_0RB1LA1LC1RD1RC1LA1RB0LA p) as (n & c' & Hr & Hc & Hn).
  exists n, c'. split; [exact Hr | split; [rewrite Hc; reflexivity | exact Hn]].
Qed.

Lemma boot_0RB1LA1LC1RD1RC1LA1RB0LA : exists t0, stepn tmm_0RB1LA1LC1RD1RC1LA1RB0LA t0 InitES = Some (lift (Cc_0RB1LA1LC1RD1RC1LA1RB0LA 1)).
Proof.
  exists 9.
  assert (H : match csteps tmm_0RB1LA1LC1RD1RC1LA1RB0LA 9 c0 with
              | Some c => ceqb c (Cc_0RB1LA1LC1RD1RC1LA1RB0LA 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tmm_0RB1LA1LC1RD1RC1LA1RB0LA 9 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** The log-rare state StC: reached inside the overflow stop, so the anchor
    walks forward (well-founded on [tovf]) until the counter is all ones. *)
Lemma U_VAC_0RB1LA1LC1RD1RC1LA1RB0LA : wsteps false true tmm_0RB1LA1LC1RD1RC1LA1RB0LA 3 (StB,([],S1,[]))
  = Some (StC,([S1],S1,[S1])). Proof. reflexivity. Qed.
Lemma phVAC_0RB1LA1LC1RD1RC1LA1RB0LA : forall R,
  csteps tmm_0RB1LA1LC1RD1RC1LA1RB0LA 3 (StB,([],S1,R)) = Some (StC,([S1],S1,S1 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_VAC_0RB1LA1LC1RD1RC1LA1RB0LA). Qed.

Lemma visC_0RB1LA1LC1RD1RC1LA1RB0LA : forall p, exists k c,
  csteps tmm_0RB1LA1LC1RD1RC1LA1RB0LA k (Cc_0RB1LA1LC1RD1RC1LA1RB0LA p) = Some c /\ fst c = StC.
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj).
       rewrite Hjj in Ecv; discriminate. }
    destruct (lap_exact_0RB1LA1LC1RD1RC1LA1RB0LA p) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia))
                 (Pos.succ p) eq_refl) as (k & c & Hk & Hq).
    exists (n + k), c. rewrite csteps_add, Hrun. exact (conj Hk Hq).
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv;
       [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_J p j' Ecv) as (HJp & _).
    unfold Cc_0RB1LA1LC1RD1RC1LA1RB0LA. eexists. eexists. split.
    * rewrite HJp, pair_rot.
      eapply csteps_chain. { apply phP1_0RB1LA1LC1RD1RC1LA1RB0LA. }
      eapply csteps_chain. { apply phRIP_0RB1LA1LC1RD1RC1LA1RB0LA. }
      apply phVAC_0RB1LA1LC1RD1RC1LA1RB0LA.
    * reflexivity.
Qed.

(* --- determined prefixes from the anchor --- *)
Lemma phVB_0RB1LA1LC1RD1RC1LA1RB0LA : forall L,
  csteps tmm_0RB1LA1LC1RD1RC1LA1RB0LA 1 (StA,(S1::L,S0,[]))
  = Some (StB,(L,S1,[S0])).
Proof. reflexivity. Qed.

Lemma phVD_0RB1LA1LC1RD1RC1LA1RB0LA : forall x L,
  csteps tmm_0RB1LA1LC1RD1RC1LA1RB0LA 2 (StA,(S1::x::L,S0,[]))
  = Some (StD,(L,x,[S1; S0])).
Proof. reflexivity. Qed.

Lemma vis_0RB1LA1LC1RD1RC1LA1RB0LA : forall p q, exists k c,
  csteps tmm_0RB1LA1LC1RD1RC1LA1RB0LA k (Cc_0RB1LA1LC1RD1RC1LA1RB0LA p) = Some c /\ fst c = q.
Proof.
  intros p q. destruct (Jp_head p) as (w & Hw). unfold Cc_0RB1LA1LC1RD1RC1LA1RB0LA. destruct q.
  - exists 0. eexists. split; reflexivity.
  - exists 1. eexists. rewrite Hw.
    split; [apply phVB_0RB1LA1LC1RD1RC1LA1RB0LA | reflexivity].
  - apply (visC_0RB1LA1LC1RD1RC1LA1RB0LA p).
  - rewrite Hw. destruct w as [|x w'].
    + exists 2. eexists. split;
      [ vm_compute; reflexivity | reflexivity ].
    + exists 2. eexists. split.
      * change ((S1 :: x :: w') ++ [])
          with (S1 :: x :: (w' ++ [])). apply phVD_0RB1LA1LC1RD1RC1LA1RB0LA.
      * reflexivity.
Qed.

Lemma nqhm_0RB1LA1LC1RD1RC1LA1RB0LA : NeverQuasiHaltsSt tmm_0RB1LA1LC1RD1RC1LA1RB0LA.
Proof.
  apply (glue_neverqh tmm_0RB1LA1LC1RD1RC1LA1RB0LA Cc_0RB1LA1LC1RD1RC1LA1RB0LA 1).
  - exact boot_0RB1LA1LC1RD1RC1LA1RB0LA.
  - intros p _. apply lap_0RB1LA1LC1RD1RC1LA1RB0LA.
  - intros p q _. apply vis_0RB1LA1LC1RD1RC1LA1RB0LA.
Qed.

Theorem nqh_0RB1LA1LC1RD1RC1LA1RB0LA : NeverQuasiHaltsSt tm_0RB1LA1LC1RD1RC1LA1RB0LA.
Proof.
  apply (mirror_never_qh tm_0RB1LA1LC1RD1RC1LA1RB0LA). rewrite mirror_ok_0RB1LA1LC1RD1RC1LA1RB0LA. exact nqhm_0RB1LA1LC1RD1RC1LA1RB0LA.
Qed.

Theorem nonhalt_0RB1LA1LC1RD1RC1LA1RB0LA : NonHalt tm_0RB1LA1LC1RD1RC1LA1RB0LA.
Proof. apply never_qh_nonhalt, nqh_0RB1LA1LC1RD1RC1LA1RB0LA. Qed.
