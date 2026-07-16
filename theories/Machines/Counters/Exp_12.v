(** * Exp_12: the exp_counter machine #12, 1RB0RA_1LC1RD_1LD0LC_1RA1LB.

    Third machine of the BBB harness's [exp_counter] family
    (certificate results/counter12.cert: sym 1, side R, edge state A,
    bootstrap v0 = 1).  The SYMMETRIC marker counter: stride-3
    markers of v on BOTH sides of a 4-cell anchor,

      C(v) = (StA, (1 :: 0 :: 0 :: Gp v, 1, 0 :: 1 :: Tp v)),

    zeros-first groups (Tp) on the right, marker-first groups (Gp)
    on the left.  Both sides carry the same run j = trailing_ones(v).
    One lap: rightward marker +1 (2-step entry through the anchor
    pair, 3-step strides over set markers, 4-step stop setting the
    clear/fresh marker, 1-step C-run zeroing back), then leftward
    marker +1 (4-step launch, 3-step strides, 2-step stop, 1-step
    A-return zeroing, 6-step anchor rebuild).  Laps end exactly at
    C(v+1).  Validated differentially for v = 1..300
    (tools/counters/lap12.py). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ExpCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB0RA_1LC1RD_1LD0LC_1RA1LB *)
Definition tm_12 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DR StA
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S1 DL StD | StC, S1 => mk S0 DL StC
  | StD, S0 => mk S1 DR StA | StD, S1 => mk S1 DL StB
  end.

Definition Cc (p : positive) : cconf :=
  (StA, (S1 :: S0 :: S0 :: Gp p, S1, S0 :: S1 :: Tp p)).

(** ** The unit runs *)

(** U1: entry through the anchor pair. *)
Lemma U1 : wsteps true true tm_12 2 (StA, ([], S1, [S0; S1]))
           = Some (StB, ([S1; S0], S1, [])).
Proof. reflexivity. Qed.

(** URs: rightward stride over a set marker (3 steps). *)
Lemma URs : wsteps true true tm_12 3 (StB, ([], S1, [S0; S0; S1]))
            = Some (StB, ([S1; S1; S1], S1, [])).
Proof. reflexivity. Qed.

(** URi: interior right stop -- set the clear marker. *)
Lemma URi : wsteps true true tm_12 4 (StB, ([], S1, [S0; S0; S0]))
            = Some (StC, ([S1; S1], S1, [S1])).
Proof. reflexivity. Qed.

(** URo: right overflow stop -- a fresh marker past the edge. *)
Lemma URo : wsteps true false tm_12 4 (StB, ([], S1, []))
            = Some (StC, ([S1; S1], S1, [S1])).
Proof. reflexivity. Qed.

(** UCr: the C-run zeroing the right trail (1 step/cell). *)
Lemma UCr : wsteps true true tm_12 1 (StC, ([S1], S1, []))
            = Some (StC, ([], S1, [S0])).
Proof. reflexivity. Qed.

(** UL: the leftward launch through the anchor pair. *)
Lemma UL : wsteps true true tm_12 4 (StC, ([S0; S1; S0; S0], S1, []))
           = Some (StC, ([], S0, [S1; S1; S1; S0])).
Proof. reflexivity. Qed.

(** ULs: leftward stride over a set marker (3 steps). *)
Lemma ULs : wsteps true true tm_12 3 (StC, ([S1; S0; S0], S0, []))
            = Some (StC, ([], S0, [S1; S1; S1])).
Proof. reflexivity. Qed.

(** ULi: interior left stop -- set the clear marker. *)
Lemma ULi : wsteps true true tm_12 2 (StC, ([S0], S0, []))
            = Some (StA, ([S1], S1, [])).
Proof. reflexivity. Qed.

(** ULsE: the overflow stride across the last marker (left edge). *)
Lemma ULsE : wsteps false true tm_12 3 (StC, ([S1], S0, []))
             = Some (StC, ([], S0, [S1; S1; S1])).
Proof. reflexivity. Qed.

(** ULo: left overflow stop -- a fresh marker in blank territory. *)
Lemma ULo : wsteps false true tm_12 2 (StC, ([], S0, []))
            = Some (StA, ([S1], S1, [])).
Proof. reflexivity. Qed.

(** UAr: the A-return zeroing the left trail (1 step/cell). *)
Lemma UAr : wsteps true true tm_12 1 (StA, ([], S1, [S1]))
            = Some (StA, ([S0], S1, [])).
Proof. reflexivity. Qed.

(** UEnd: rebuild the anchor. *)
Lemma UEnd : wsteps true true tm_12 6 (StA, ([S0], S1, [S0; S0]))
             = Some (StA, ([S1], S1, [S0; S1])).
Proof. reflexivity. Qed.

(** Visit witness: D three steps in. *)
Lemma UVD : wsteps true true tm_12 3 (StA, ([], S1, [S0; S1; S0]))
            = Some (StD, ([S1; S1; S0], S0, [])).
Proof. reflexivity. Qed.

(** ** Transported phases *)

Lemma phU1 : forall L R,
  csteps tm_12 2 (StA, (L, S1, S0 :: S1 :: R))
  = Some (StB, (S1 :: S0 :: L, S1, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U1). Qed.

Lemma phURs : forall k L R,
  csteps tm_12 (3 * k) (StB, (L, S1, rep [S0; S0; S1] k ++ R))
  = Some (StB, (rep [S1; S1; S1] k ++ L, S1, R)).
Proof. intros. exact (cycR _ _ _ _ _ _ URs k L R). Qed.

Lemma phURi : forall L R,
  csteps tm_12 4 (StB, (L, S1, S0 :: S0 :: S0 :: R))
  = Some (StC, (S1 :: S1 :: L, S1, S1 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R URi). Qed.

Lemma phURo : forall L,
  csteps tm_12 4 (StB, (L, S1, []))
  = Some (StC, (S1 :: S1 :: L, S1, [S1])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L URo). Qed.

Lemma phUCr : forall k L R,
  csteps tm_12 k (StC, (rep [S1] k ++ L, S1, R))
  = Some (StC, (L, S1, rep [S0] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ UCr k L R) as H.
  rewrite Nat.mul_1_l in H; cbn [app] in H.
  exact H.
Qed.

Lemma phUL : forall L R,
  csteps tm_12 4 (StC, (S0 :: S1 :: S0 :: S0 :: L, S1, R))
  = Some (StC, (L, S0, S1 :: S1 :: S1 :: S0 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UL). Qed.

Lemma phULs : forall k L R,
  csteps tm_12 (3 * k) (StC, (rep [S1; S0; S0] k ++ L, S0, R))
  = Some (StC, (L, S0, rep [S1; S1; S1] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ ULs k L R) as H; cbn [app] in H.
  exact H.
Qed.

Lemma phULi : forall L R,
  csteps tm_12 2 (StC, (S0 :: L, S0, R))
  = Some (StA, (S1 :: L, S1, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R ULi). Qed.

Lemma phULsE : forall R,
  csteps tm_12 3 (StC, ([S1], S0, R))
  = Some (StC, ([], S0, S1 :: S1 :: S1 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R ULsE). Qed.

Lemma phULo : forall R,
  csteps tm_12 2 (StC, ([], S0, R))
  = Some (StA, ([S1], S1, R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R ULo). Qed.

Lemma phUAr : forall k L R,
  csteps tm_12 k (StA, (L, S1, rep [S1] k ++ R))
  = Some (StA, (rep [S0] k ++ L, S1, R)).
Proof.
  intros.
  pose proof (cycR _ _ _ _ _ _ UAr k L R) as H.
  rewrite Nat.mul_1_l in H.
  exact H.
Qed.

Lemma phUEnd : forall L R,
  csteps tm_12 6 (StA, (S0 :: L, S1, S0 :: S0 :: R))
  = Some (StA, (S1 :: L, S1, S0 :: S1 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UEnd). Qed.

Lemma phUVD : forall L R,
  csteps tm_12 3 (StA, (L, S1, S0 :: S1 :: S0 :: R))
  = Some (StD, (S1 :: S1 :: S0 :: L, S0, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UVD). Qed.

(** ** The lap *)

Lemma lap_12 : forall p,
  exists n c', csteps tm_12 n (Cc p) = Some c' /\
               lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p.
  destruct (cview p) as [j o] eqn:Ep.
  unfold Cc.
  destruct o as [q|].
  - (* interior carry on both sides *)
    destruct (cview_some_T p j q Ep) as (HTp & HTs).
    destruct (cview_some_G p j q Ep) as (HGp & HGs).
    do 2 eexists. split; [|split].
    + rewrite HTp, HGp.
      eapply csteps_chain. { apply phU1. }
      eapply csteps_chain. { apply phURs. }
      eapply csteps_chain. { apply phURi. }
      rewrite rep_tpl, rep1_fold.
      change (S1 :: S1 :: rep [S1] (S (3 * j)) ++
                S0 :: S1 :: S0 :: S0 :: rep [S1; S0; S0] j ++
                S0 :: S0 :: S0 :: Gp q)
        with (rep [S1] (S (S (S (3 * j)))) ++
                S0 :: S1 :: S0 :: S0 :: rep [S1; S0; S0] j ++
                S0 :: S0 :: S0 :: Gp q).
      eapply csteps_chain. { apply phUCr. }
      eapply csteps_chain. { apply phUL. }
      eapply csteps_chain. { apply phULs. }
      eapply csteps_chain. { apply phULi. }
      rewrite rep_tpl, rep1_fold, rep1_fold, rep1_fold.
      change (rep [S0] (S (S (S (3 * j)))))
        with (S0 :: rep [S0] (S (S (3 * j)))).
      eapply csteps_chain. { apply phUAr. }
      apply phUEnd.
    + rewrite HGs, HTs, !rep1_fold.
      reflexivity.
    + lia.
  - (* overflow on both sides: p = 2^j - 1 *)
    destruct j as [|j'].
    { exfalso.
      destruct p; simpl in Ep;
        [destruct (cview p); discriminate | discriminate | discriminate]. }
    destruct (cview_none_T p (S j') Ep) as (HTp & HTs).
    destruct (cview_none_G p j' Ep) as (HGp & HGs).
    do 2 eexists. split; [|split].
    + rewrite HTp, <- (app_nil_r (rep [S0; S0; S1] (S j'))), HGp.
      eapply csteps_chain. { apply phU1. }
      eapply csteps_chain. { apply phURs. }
      eapply csteps_chain. { apply phURo. }
      rewrite rep_tpl, rep1_fold.
      change (S1 :: S1 :: rep [S1] (S (3 * S j')) ++
                S0 :: S1 :: S0 :: S0 :: rep [S1; S0; S0] j' ++ [S1])
        with (rep [S1] (S (S (S (3 * S j')))) ++
                S0 :: S1 :: S0 :: S0 :: rep [S1; S0; S0] j' ++ [S1]).
      eapply csteps_chain. { apply phUCr. }
      eapply csteps_chain. { apply phUL. }
      eapply csteps_chain. { apply phULs. }
      eapply csteps_chain. { apply phULsE. }
      eapply csteps_chain. { apply phULo. }
      change (S1 :: S1 :: S1 :: rep [S1; S1; S1] j' ++
                S1 :: S1 :: S1 :: S0 :: rep [S0] (S (S (S (3 * S j')))) ++ [S1])
        with (rep [S1; S1; S1] (S j') ++
                S1 :: S1 :: S1 :: S0 :: rep [S0] (S (S (S (3 * S j')))) ++ [S1]).
      rewrite rep_tpl, rep1_fold, rep1_fold, rep1_fold.
      change (rep [S0] (S (S (S (3 * S j')))))
        with (S0 :: rep [S0] (S (S (3 * S j')))).
      eapply csteps_chain. { apply phUAr. }
      apply phUEnd.
    + rewrite HGs, HTs, !rep1_fold.
      reflexivity.
    + lia.
Qed.

(** ** Bootstrap, visits, and the theorem *)

Lemma boot_12 : exists t0, stepn tm_12 t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 29.
  assert (H : match csteps tm_12 29 c0 with
              | Some c => ceqb c (Cc 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_12 29 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

Lemma vis_12 : forall p q,
  exists k c, csteps tm_12 k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q.
  unfold Cc.
  destruct q.
  - exists 0. eexists. split; reflexivity.
  - exists 2. eexists. split; [apply phU1 | reflexivity].
  - (* StC: the right stop's exit state *)
    destruct (cview p) as [j o] eqn:Ep.
    destruct o as [q0|].
    + destruct (cview_some_T p j q0 Ep) as (HTp & _).
      do 2 eexists. split.
      * rewrite HTp.
        eapply csteps_chain. { apply phU1. }
        eapply csteps_chain. { apply phURs. }
        apply phURi.
      * reflexivity.
    + destruct (cview_none_T p j Ep) as (HTp & _).
      do 2 eexists. split.
      * rewrite HTp, <- (app_nil_r (rep [S0; S0; S1] j)).
        eapply csteps_chain. { apply phU1. }
        eapply csteps_chain. { apply phURs. }
        apply phURo.
      * reflexivity.
  - (* StD after 3 steps *)
    destruct (Tp_head p) as (w & Hw).
    exists 3. eexists. split.
    + rewrite Hw. apply phUVD.
    + reflexivity.
Qed.

(** #12 never quasihalts: bbchallenge 1RB0RA_1LC1RD_1LD0LC_1RA1LB. *)
Theorem nqh_1RB0RA_1LC1RD_1LD0LC_1RA1LB : NeverQuasiHaltsSt tm_12.
Proof.
  apply (glue_neverqh tm_12 Cc 1).
  - exact boot_12.
  - intros p _. apply lap_12.
  - intros p q _. apply vis_12.
Qed.

Theorem tm_12_nonhalt : NonHalt tm_12.
Proof. apply never_qh_nonhalt, nqh_1RB0RA_1LC1RD_1LD0LC_1RA1LB. Qed.
