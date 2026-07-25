(** * ILCM_1RB1RC1LA1RD0RB1LC1RB0LC: 1RB1RC_1LA1RD_0RB1LC_1RB0LC -- right-growth interleaved counter via Mirror.

    A comb-free interleaved binary counter growing on the RIGHT, so the
    [Interleave_TGT.v] lap does not apply directly.  Its mirror
    (1LB1LC_1RA1LD_0LB1RC_1LB0RC) is the same counter grown LEFTward, carrying the
    [JpCounter] anchor family

        Cc p = (StC, (Jp p ++ [], S0, []))

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

Definition mk_1RB1RC1LA1RD0RB1LC1RB0LC (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** The machine 1RB1RC_1LA1RD_0RB1LC_1RB0LC. *)
Definition tm_1RB1RC1LA1RD0RB1LC1RB0LC : TM := fun q s => match q, s with
  | StA, S0 => mk_1RB1RC1LA1RD0RB1LC1RB0LC S1 DR StB | StA, S1 => mk_1RB1RC1LA1RD0RB1LC1RB0LC S1 DR StC
  | StB, S0 => mk_1RB1RC1LA1RD0RB1LC1RB0LC S1 DL StA | StB, S1 => mk_1RB1RC1LA1RD0RB1LC1RB0LC S1 DR StD
  | StC, S0 => mk_1RB1RC1LA1RD0RB1LC1RB0LC S0 DR StB | StC, S1 => mk_1RB1RC1LA1RD0RB1LC1RB0LC S1 DL StC
  | StD, S0 => mk_1RB1RC1LA1RD0RB1LC1RB0LC S1 DR StB | StD, S1 => mk_1RB1RC1LA1RD0RB1LC1RB0LC S0 DL StC end.

(** Its mirror 1LB1LC_1RA1LD_0LB1RC_1LB0RC: the same counter, grown leftward. *)
Definition tmm_1RB1RC1LA1RD0RB1LC1RB0LC : TM := fun q s => match q, s with
  | StA, S0 => mk_1RB1RC1LA1RD0RB1LC1RB0LC S1 DL StB | StA, S1 => mk_1RB1RC1LA1RD0RB1LC1RB0LC S1 DL StC
  | StB, S0 => mk_1RB1RC1LA1RD0RB1LC1RB0LC S1 DR StA | StB, S1 => mk_1RB1RC1LA1RD0RB1LC1RB0LC S1 DL StD
  | StC, S0 => mk_1RB1RC1LA1RD0RB1LC1RB0LC S0 DL StB | StC, S1 => mk_1RB1RC1LA1RD0RB1LC1RB0LC S1 DR StC
  | StD, S0 => mk_1RB1RC1LA1RD0RB1LC1RB0LC S1 DL StB | StD, S1 => mk_1RB1RC1LA1RD0RB1LC1RB0LC S0 DR StC end.

Lemma mirror_ok_1RB1RC1LA1RD0RB1LC1RB0LC : mirror_tm tm_1RB1RC1LA1RD0RB1LC1RB0LC = tmm_1RB1RC1LA1RD0RB1LC1RB0LC.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro s; destruct q, s; reflexivity.
Qed.

Definition Cc_1RB1RC1LA1RD0RB1LC1RB0LC (p : positive) : cconf := (StC, (Jp p ++ [], S0, [])).

(* --- the two anchor-closing identities (interior / overflow) --- *)
Lemma clsI_1RB1RC1LA1RD0RB1LC1RB0LC : forall j Y,
  S1 :: rep [S1] (2*j) ++ S0 :: S1 :: (Y ++ [])
  = (rep [S1;S1] j ++ S1 :: S0 :: S1 :: Y) ++ [].
Proof. intros. rewrite rep_dbl, rep_slide, <- app_assoc. reflexivity. Qed.
Lemma clsO_1RB1RC1LA1RD0RB1LC1RB0LC : forall j',
  S1 :: rep [S1] (2*(S j')) ++ [] = (rep [S1;S1] (S j') ++ [S1]) ++ [].
Proof. intros. rewrite rep_dbl, rep_slide, <- app_assoc. reflexivity. Qed.

(* --- the lap unit windows (derived by simulation, closed by reflexivity) --- *)
Lemma U_P1_1RB1RC1LA1RD0RB1LC1RB0LC : wsteps true true tmm_1RB1RC1LA1RD0RB1LC1RB0LC 1 (StC,([S1],S0,[]))
  = Some (StB,([],S1,[S0])). Proof. reflexivity. Qed.
Lemma U_RIP_1RB1RC1LA1RD0RB1LC1RB0LC : wsteps true true tmm_1RB1RC1LA1RD0RB1LC1RB0LC 2 (StB,([S0;S1],S1,[]))
  = Some (StB,([],S1,[S1;S1])). Proof. reflexivity. Qed.
Lemma U_STPI_1RB1RC1LA1RD0RB1LC1RB0LC : wsteps true true tmm_1RB1RC1LA1RD0RB1LC1RB0LC 2 (StB,([S1;S1],S1,[]))
  = Some (StC,([S0;S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_STPO_1RB1RC1LA1RD0RB1LC1RB0LC : wsteps false true tmm_1RB1RC1LA1RD0RB1LC1RB0LC 4 (StB,([],S1,[]))
  = Some (StC,([],S1,[S1; S1])). Proof. reflexivity. Qed.
Lemma U_RET_1RB1RC1LA1RD0RB1LC1RB0LC : wsteps true true tmm_1RB1RC1LA1RD0RB1LC1RB0LC 1 (StC,([],S1,[S1]))
  = Some (StC,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FIN_1RB1RC1LA1RD0RB1LC1RB0LC : wsteps true true tmm_1RB1RC1LA1RD0RB1LC1RB0LC 1 (StC,([],S1,[S0]))
  = Some (StC,([S1],S0,[])). Proof. reflexivity. Qed.

(* --- transported phases (framing = each unit's bl/br) --- *)
Lemma phP1_1RB1RC1LA1RD0RB1LC1RB0LC : forall L R,
  csteps tmm_1RB1RC1LA1RD0RB1LC1RB0LC 1 (StC,(S1::L,S0,R)) = Some (StB,(L,S1,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_P1_1RB1RC1LA1RD0RB1LC1RB0LC). Qed.
Lemma phRIP_1RB1RC1LA1RD0RB1LC1RB0LC : forall k L R,
  csteps tmm_1RB1RC1LA1RD0RB1LC1RB0LC (2*k) (StB,(rep [S0;S1] k ++ L,S1,R))
  = Some (StB,(L,S1,rep [S1;S1] k ++ R)).
Proof. intros. pose proof (cycL _ _ _ _ _ _ _ U_RIP_1RB1RC1LA1RD0RB1LC1RB0LC k L R) as H;
  cbn [app] in H; exact H. Qed.
Lemma phSTPI_1RB1RC1LA1RD0RB1LC1RB0LC : forall L R,
  csteps tmm_1RB1RC1LA1RD0RB1LC1RB0LC 2 (StB,(S1::S1::L,S1,R)) = Some (StC,(S0::S1::L,S1,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STPI_1RB1RC1LA1RD0RB1LC1RB0LC). Qed.
Lemma phSTPO_1RB1RC1LA1RD0RB1LC1RB0LC : forall R,
  csteps tmm_1RB1RC1LA1RD0RB1LC1RB0LC 4 (StB,([],S1,R))
  = Some (StC,([],S1,S1 :: S1 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPO_1RB1RC1LA1RD0RB1LC1RB0LC). Qed.
Lemma phRET_1RB1RC1LA1RD0RB1LC1RB0LC : forall k L R,
  csteps tmm_1RB1RC1LA1RD0RB1LC1RB0LC (1*k) (StC,(L,S1,rep [S1] k ++ R))
  = Some (StC,(rep [S1] k ++ L,S1,R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U_RET_1RB1RC1LA1RD0RB1LC1RB0LC k L R). Qed.
Lemma phFIN_1RB1RC1LA1RD0RB1LC1RB0LC : forall L R,
  csteps tmm_1RB1RC1LA1RD0RB1LC1RB0LC 1 (StC,(L,S1,S0::R)) = Some (StC,(S1::L,S0,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FIN_1RB1RC1LA1RD0RB1LC1RB0LC). Qed.

(** The exact lap: from the anchor at p to the anchor at p+1. *)
Lemma lap_exact_1RB1RC1LA1RD0RB1LC1RB0LC : forall p, exists n c',
  csteps tmm_1RB1RC1LA1RD0RB1LC1RB0LC n (Cc_1RB1RC1LA1RD0RB1LC1RB0LC p) = Some c' /\ c' = Cc_1RB1RC1LA1RD0RB1LC1RB0LC (Pos.succ p) /\ 0 < n.
Proof.
  intros p. pose proof (Pos2Nat.is_pos p) as Hpos.
  destruct (cview p) as [j oq] eqn:Ecv. unfold Cc_1RB1RC1LA1RD0RB1LC1RB0LC.
  destruct oq as [q0|].
  - destruct (cview_some_J p j q0 Ecv) as (HJp & HJs).
    destruct (Jp_head q0) as (iq & Hiq).
    do 2 eexists. split; [|split].
    + rewrite HJp, <- app_assoc.
      change (rep [S1;S0] j ++ (S1 :: S1 :: Jp q0) ++ [])
        with (rep [S1;S0] j ++ [S1] ++ (S1 :: Jp q0 ++ [])).
      rewrite app_assoc, pair_rot.
      eapply csteps_chain. { apply phP1_1RB1RC1LA1RD0RB1LC1RB0LC. }
      eapply csteps_chain. { apply phRIP_1RB1RC1LA1RD0RB1LC1RB0LC. }
      rewrite Hiq.
      eapply csteps_chain. { apply phSTPI_1RB1RC1LA1RD0RB1LC1RB0LC. }
      rewrite rep_dbl.
      eapply csteps_chain. { apply (phRET_1RB1RC1LA1RD0RB1LC1RB0LC (2*j)). }
      apply phFIN_1RB1RC1LA1RD0RB1LC1RB0LC.
    + rewrite HJs, Hiq, <- clsI_1RB1RC1LA1RD0RB1LC1RB0LC. reflexivity.
    + lia.
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv;
       [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_J p j' Ecv) as (HJp & HJs).
    do 2 eexists. split; [|split].
    + rewrite HJp, pair_rot.
      eapply csteps_chain. { apply phP1_1RB1RC1LA1RD0RB1LC1RB0LC. }
      eapply csteps_chain. { apply phRIP_1RB1RC1LA1RD0RB1LC1RB0LC. }
      eapply csteps_chain. { apply phSTPO_1RB1RC1LA1RD0RB1LC1RB0LC. }
      change (S1 :: S1 :: rep [S1;S1] j' ++ [S0])
        with (rep [S1;S1] (S j') ++ [S0]).
      rewrite rep_dbl.
      eapply csteps_chain. { apply (phRET_1RB1RC1LA1RD0RB1LC1RB0LC (2*(S j'))). }
      apply phFIN_1RB1RC1LA1RD0RB1LC1RB0LC.
    + rewrite HJs, <- clsO_1RB1RC1LA1RD0RB1LC1RB0LC. reflexivity.
    + lia.
Qed.

Lemma lap_1RB1RC1LA1RD0RB1LC1RB0LC : forall p, exists n c',
  csteps tmm_1RB1RC1LA1RD0RB1LC1RB0LC n (Cc_1RB1RC1LA1RD0RB1LC1RB0LC p) = Some c' /\
  lift c' = lift (Cc_1RB1RC1LA1RD0RB1LC1RB0LC (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (lap_exact_1RB1RC1LA1RD0RB1LC1RB0LC p) as (n & c' & Hr & Hc & Hn).
  exists n, c'. split; [exact Hr | split; [rewrite Hc; reflexivity | exact Hn]].
Qed.

Lemma boot_1RB1RC1LA1RD0RB1LC1RB0LC : exists t0, stepn tmm_1RB1RC1LA1RD0RB1LC1RB0LC t0 InitES = Some (lift (Cc_1RB1RC1LA1RD0RB1LC1RB0LC 1)).
Proof.
  exists 9.
  assert (H : match csteps tmm_1RB1RC1LA1RD0RB1LC1RB0LC 9 c0 with
              | Some c => ceqb c (Cc_1RB1RC1LA1RD0RB1LC1RB0LC 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tmm_1RB1RC1LA1RD0RB1LC1RB0LC 9 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** The log-rare state StA: reached inside the overflow stop, so the anchor
    walks forward (well-founded on [tovf]) until the counter is all ones. *)
Lemma U_VAA_1RB1RC1LA1RD0RB1LC1RB0LC : wsteps false true tmm_1RB1RC1LA1RD0RB1LC1RB0LC 3 (StB,([],S1,[]))
  = Some (StA,([S1],S1,[S1])). Proof. reflexivity. Qed.
Lemma phVAA_1RB1RC1LA1RD0RB1LC1RB0LC : forall R,
  csteps tmm_1RB1RC1LA1RD0RB1LC1RB0LC 3 (StB,([],S1,R)) = Some (StA,([S1],S1,S1 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_VAA_1RB1RC1LA1RD0RB1LC1RB0LC). Qed.

Lemma visA_1RB1RC1LA1RD0RB1LC1RB0LC : forall p, exists k c,
  csteps tmm_1RB1RC1LA1RD0RB1LC1RB0LC k (Cc_1RB1RC1LA1RD0RB1LC1RB0LC p) = Some c /\ fst c = StA.
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj).
       rewrite Hjj in Ecv; discriminate. }
    destruct (lap_exact_1RB1RC1LA1RD0RB1LC1RB0LC p) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia))
                 (Pos.succ p) eq_refl) as (k & c & Hk & Hq).
    exists (n + k), c. rewrite csteps_add, Hrun. exact (conj Hk Hq).
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv;
       [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_J p j' Ecv) as (HJp & _).
    unfold Cc_1RB1RC1LA1RD0RB1LC1RB0LC. eexists. eexists. split.
    * rewrite HJp, pair_rot.
      eapply csteps_chain. { apply phP1_1RB1RC1LA1RD0RB1LC1RB0LC. }
      eapply csteps_chain. { apply phRIP_1RB1RC1LA1RD0RB1LC1RB0LC. }
      apply phVAA_1RB1RC1LA1RD0RB1LC1RB0LC.
    * reflexivity.
Qed.

(* --- determined prefixes from the anchor --- *)
Lemma phVB_1RB1RC1LA1RD0RB1LC1RB0LC : forall L,
  csteps tmm_1RB1RC1LA1RD0RB1LC1RB0LC 1 (StC,(S1::L,S0,[]))
  = Some (StB,(L,S1,[S0])).
Proof. reflexivity. Qed.

Lemma phVD_1RB1RC1LA1RD0RB1LC1RB0LC : forall x L,
  csteps tmm_1RB1RC1LA1RD0RB1LC1RB0LC 2 (StC,(S1::x::L,S0,[]))
  = Some (StD,(L,x,[S1; S0])).
Proof. reflexivity. Qed.

Lemma vis_1RB1RC1LA1RD0RB1LC1RB0LC : forall p q, exists k c,
  csteps tmm_1RB1RC1LA1RD0RB1LC1RB0LC k (Cc_1RB1RC1LA1RD0RB1LC1RB0LC p) = Some c /\ fst c = q.
Proof.
  intros p q. destruct (Jp_head p) as (w & Hw). unfold Cc_1RB1RC1LA1RD0RB1LC1RB0LC. destruct q.
  - apply (visA_1RB1RC1LA1RD0RB1LC1RB0LC p).
  - exists 1. eexists. rewrite Hw.
    split; [apply phVB_1RB1RC1LA1RD0RB1LC1RB0LC | reflexivity].
  - exists 0. eexists. split; reflexivity.
  - rewrite Hw. destruct w as [|x w'].
    + exists 2. eexists. split;
      [ vm_compute; reflexivity | reflexivity ].
    + exists 2. eexists. split.
      * change ((S1 :: x :: w') ++ [])
          with (S1 :: x :: (w' ++ [])). apply phVD_1RB1RC1LA1RD0RB1LC1RB0LC.
      * reflexivity.
Qed.

Lemma nqhm_1RB1RC1LA1RD0RB1LC1RB0LC : NeverQuasiHaltsSt tmm_1RB1RC1LA1RD0RB1LC1RB0LC.
Proof.
  apply (glue_neverqh tmm_1RB1RC1LA1RD0RB1LC1RB0LC Cc_1RB1RC1LA1RD0RB1LC1RB0LC 1).
  - exact boot_1RB1RC1LA1RD0RB1LC1RB0LC.
  - intros p _. apply lap_1RB1RC1LA1RD0RB1LC1RB0LC.
  - intros p q _. apply vis_1RB1RC1LA1RD0RB1LC1RB0LC.
Qed.

Theorem nqh_1RB1RC1LA1RD0RB1LC1RB0LC : NeverQuasiHaltsSt tm_1RB1RC1LA1RD0RB1LC1RB0LC.
Proof.
  apply (mirror_never_qh tm_1RB1RC1LA1RD0RB1LC1RB0LC). rewrite mirror_ok_1RB1RC1LA1RD0RB1LC1RB0LC. exact nqhm_1RB1RC1LA1RD0RB1LC1RB0LC.
Qed.

Theorem nonhalt_1RB1RC1LA1RD0RB1LC1RB0LC : NonHalt tm_1RB1RC1LA1RD0RB1LC1RB0LC.
Proof. apply never_qh_nonhalt, nqh_1RB1RC1LA1RD0RB1LC1RB0LC. Qed.
