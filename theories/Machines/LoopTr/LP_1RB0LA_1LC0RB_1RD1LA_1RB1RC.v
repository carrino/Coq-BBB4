(** * LP_1RB0LA_1LC0RB_1RD1LA_1RB1RC (SCOPING_INSTR 7.4.LE10)

    The binary / base-3 mirror counter of [LP_1RB0LA_1LC0RB_1RD1LA_1RA1RC]
    with 4-cell base-3 digits ([0000] / [0011] / [0001]).  [D0] here goes
    right in state [B], so a 2-digit takes a 6-step loop.  The carry from
    a low digit 1 does not fire [D0], so [fires_g] looks one increment
    ahead there.

    Hand-stated, kernel-checked.  Axiom footprint: [functional_extensionality_dep]. *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr LoopMirrorTr.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Definition tm_1RB0LA_1LC0RB_1RD1LA_1RB1RC : TM := fun q s => match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB) | StA, S1 => Some (mkTrans S0 DL StA)
  | StB, S0 => Some (mkTrans S1 DL StC) | StB, S1 => Some (mkTrans S0 DR StB)
  | StC, S0 => Some (mkTrans S1 DR StD) | StC, S1 => Some (mkTrans S1 DL StA)
  | StD, S0 => Some (mkTrans S1 DR StB) | StD, S1 => Some (mkTrans S1 DR StC)
  end.
Local Notation tm := (tm_wrap_trs tm_1RB0LA_1LC0RB_1RD1LA_1RB1RC []).
Local Notation ZL := [S0; S0].
Local Notation OL := [S1; S0].
Local Notation V := [S1; S1; S1; S1].

(** base-3 digits, least significant first, four cells each; [t0] is blank *)
Inductive trit := t0 | t1 | t2.

Definition tdig (d : trit) : list Sym :=
  match d with
  | t0 => [S0; S0; S0; S0]
  | t1 => [S0; S0; S1; S1]
  | t2 => [S0; S0; S0; S1]
  end.

Definition tcells (y : list trit) : list Sym := flat_map tdig y.

Fixpoint tinc (y : list trit) : list trit :=
  match y with
  | [] => [t1]
  | t0 :: r => t1 :: r
  | t1 :: r => t2 :: r
  | t2 :: r => t0 :: tinc r
  end.

Lemma tcells_app : forall x y, tcells (x ++ y) = tcells x ++ tcells y.
Proof. intros. apply flat_map_app. Qed.

Lemma tcells_rep : forall d k, tcells (repeat d k) = rep (tdig d) k.
Proof. intros d k. induction k as [|k IH]; [reflexivity|]. cbn [repeat]. cbn [tcells flat_map]. fold (tcells (repeat d k)). rewrite IH. reflexivity. Qed.

Lemma tsplit : forall y, (exists k d r, y = repeat t2 k ++ d :: r /\ d <> t2) \/ (exists k, y = repeat t2 k).
Proof.
  induction y as [|d y IH]; [right; exists 0; reflexivity|].
  destruct d.
  - left. exists 0, t0, y. split; [reflexivity | discriminate].
  - left. exists 0, t1, y. split; [reflexivity | discriminate].
  - destruct IH as [(k & d & r & -> & Hd) | (k & ->)].
    + left. exists (S k), d, r. split; [reflexivity | exact Hd].
    + right. exists (S k). reflexivity.
Qed.

Lemma tinc_int : forall k d r, d <> t2 ->
  tinc (repeat t2 k ++ d :: r) = repeat t0 k ++ (match d with t0 => t1 | _ => t2 end) :: r.
Proof.
  induction k as [|k IH]; intros d r Hd.
  - destruct d; [reflexivity | reflexivity | congruence].
  - cbn [repeat app tinc]. rewrite IH by exact Hd. reflexivity.
Qed.

Lemma tinc_top : forall k, tinc (repeat t2 k) = repeat t0 k ++ [t1].
Proof. induction k as [|k IH]; [reflexivity|]. cbn [repeat app tinc]. rewrite IH. reflexivity. Qed.

Lemma bsplit : forall x : list bool, (exists k r, x = repeat true k ++ false :: r) \/ (exists k, x = repeat true k).
Proof.
  induction x as [|b x IH]; [right; exists 0; reflexivity|].
  destruct b.
  - destruct IH as [(k & r & ->) | (k & ->)].
    + left. exists (S k), r. reflexivity.
    + right. exists (S k). reflexivity.
  - left. exists 0, x. reflexivity.
Qed.

Lemma rep4 : forall a k, rep [a; a; a; a] k = rep [a] (4 * k).
Proof.
  intros a k. induction k as [|k IH]; [reflexivity|].
  replace (4 * S k) with (S (S (S (S (4 * k))))) by lia.
  cbn [rep app]. rewrite IH. reflexivity.
Qed.

Definition mk1 (L R : list Sym) : cconf := (StA, (L, S0, S0 :: R)).
Definition mk2 (L R : list Sym) : cconf := cR StB (S0 :: S0 :: L) R.
Definition F (L R : list Sym) : cconf := cR StB (S0 :: L) R.

(** the left (binary) carry *)
Lemma aloop : forall n L R, Reach0 tm (cL StA (rep OL n ++ L) R) (cL StA L (rep [S1; S1] n ++ R)).
Proof. apply sweepL. intros L R. rr 4. r0. Qed.

Lemma bsweep : forall n L R, Reach0 tm (cR StB L (rep [S1] n ++ R)) (cR StB (rep [S0] n ++ L) R).
Proof. apply sweepR. intros L R. rr 1. r0. Qed.

Lemma armL : forall k X R,
  Reach0 tm (mk1 (rep OL k ++ ZL ++ X) R) (mk2 (rep ZL k ++ OL ++ X) R).
Proof.
  intros k X R. unfold mk1, mk2. rr 3.
  change (StA, (ctl (rep OL k ++ ZL ++ X), chd (rep OL k ++ ZL ++ X), S1 :: S1 :: R))
    with (cL StA (rep OL k ++ ZL ++ X) (S1 :: S1 :: R)).
  rt (aloop k (ZL ++ X) (S1 :: S1 :: R)). unfold cL; cbn [chd ctl app]. rr 1.
  rewrite (rep_snoc [S1; S1] k R : rep [S1; S1] k ++ S1 :: S1 :: R = S1 :: S1 :: rep [S1; S1] k ++ R), rep_pair.
  change (StB, (S1 :: S0 :: X, chd (S1 :: S1 :: rep [S1] (k + k) ++ R), ctl (S1 :: S1 :: rep [S1] (k + k) ++ R)))
    with (cR StB (OL ++ X) (rep [S1] (S (S (k + k))) ++ R)).
  rt (bsweep (S (S (k + k))) (OL ++ X) R). rewrite rep_pair. r0.
Qed.

(** the right (ternary) carry *)
Lemma tloop : forall n L R, Reach0 tm (F L (rep (tdig t2) n ++ R)) (F (rep V n ++ L) R).
Proof. apply (sweepFR tm F). intros L R. unfold F. rr 6. r0. Qed.

Lemma asweep : forall n L R, Reach0 tm (cL StA (rep [S1] n ++ L) R) (cL StA L (rep [S0] n ++ R)).
Proof. apply sweepL. intros L R. rr 1. r0. Qed.

Lemma zeros3 : forall k Z, rep [S0] (S (S (S (4 * k)))) ++ Z = S0 :: rep (tdig t0) k ++ [S0; S0] ++ Z.
Proof.
  intros k Z. cbn [tdig]. rewrite rep4.
  replace (S (S (S (4 * k)))) with (S (4 * k + 2)) by lia.
  cbn [rep]. rewrite rep_add, <- !app_assoc. reflexivity.
Qed.

Lemma zeros4 : forall k Z, rep [S0] (S (S (S (S (4 * k))))) ++ Z = S0 :: rep (tdig t0) k ++ [S0; S0; S0] ++ Z.
Proof.
  intros k Z. cbn [tdig]. rewrite rep4.
  replace (S (S (S (S (4 * k))))) with (S (4 * k + 3)) by lia.
  cbn [rep]. rewrite rep_add, <- !app_assoc. reflexivity.
Qed.

Lemma armR : forall k d r L R', d <> t2 ->
  Reach1 tm (mk2 L (tcells (repeat t2 k ++ d :: r) ++ R'))
            (mk1 L (tcells (repeat t0 k ++ (match d with t0 => t1 | _ => t2 end) :: r) ++ R')).
Proof.
  intros k d r L R' Hd. unfold mk2, mk1. rewrite !tcells_app, !tcells_rep, <- !app_assoc.
  change (cR StB (S0 :: S0 :: L) (rep (tdig t2) k ++ tcells (d :: r) ++ R')) with (F (S0 :: L) (rep (tdig t2) k ++ tcells (d :: r) ++ R')).
  eapply reach01; [apply tloop|]. unfold F.
  rewrite rep4. cbn [tcells flat_map]. fold (tcells r).
  destruct d; [| | congruence]; cbn [tdig app].
  - rr 7.
    change (StA, (S1 :: S1 :: rep [S1] (4 * k) ++ S0 :: L, S1, S1 :: S1 :: tcells r ++ R'))
      with (cL StA (rep [S1] (S (S (S (4 * k)))) ++ S0 :: L) (S1 :: S1 :: tcells r ++ R')).
    rt (asweep (S (S (S (4 * k)))) (S0 :: L) (S1 :: S1 :: tcells r ++ R')).
    unfold cL; cbn [chd ctl]. rewrite zeros3. r0.
  - rr 6.
    change (StA, (S1 :: S1 :: S1 :: rep [S1] (4 * k) ++ S0 :: L, S1, S1 :: tcells r ++ R'))
      with (cL StA (rep [S1] (S (S (S (S (4 * k))))) ++ S0 :: L) (S1 :: tcells r ++ R')).
    rt (asweep (S (S (S (S (4 * k))))) (S0 :: L) (S1 :: tcells r ++ R')).
    unfold cL; cbn [chd ctl]. rewrite zeros4. r0.
Qed.

(** blank tape is the digit zero on both sides *)
Lemma padL : forall L R, lift (mk1 (L ++ ZL) R) = lift (mk1 L R).
Proof. intros L R. unfold mk1. change ZL with (rep [S0] 2). apply lift_padL. Qed.

Lemma padR : forall L R, lift (mk2 L (R ++ tdig t0)) = lift (mk2 L R).
Proof.
  intros L R. unfold mk2, cR. change (tdig t0) with (rep [S0] 4).
  destruct R as [|a R].
  - cbn. exact (lift_padR 3 StB (S0 :: S0 :: L) S0 []).
  - cbn [chd ctl app]. apply lift_padR.
Qed.

Lemma stepL : forall x R, Reach0 tm (mk1 (bcells ZL OL x) R) (mk2 (bcells ZL OL (binc x)) R).
Proof.
  intros x R. destruct (bsplit x) as [(k & r & ->) | (k & ->)].
  - rewrite binc_int, bcells_tt, bcells_ff, bcells_f, bcells_t. apply armL.
  - rewrite binc_top, bcells_alltrue, bcells_ff. cbn [bcells flat_map]. rewrite app_nil_r.
    eapply reach0_lift_l; [symmetry; apply padL|].
    pose proof (armL k [] R) as H. rewrite app_nil_r in H. exact H.
Qed.

Lemma stepR : forall L y, Reach1 tm (mk2 L (tcells y)) (mk1 L (tcells (tinc y))).
Proof.
  intros L y. destruct (tsplit y) as [(k & d & r & -> & Hd) | (k & ->)].
  - rewrite tinc_int by exact Hd. pose proof (armR k d r L [] Hd) as H. rewrite !app_nil_r in H. exact H.
  - rewrite tinc_top. pose proof (armR k t0 [] L [] ltac:(discriminate)) as H.
    rewrite !app_nil_r in H. eapply reach1_lift_l; [|exact H].
    rewrite tcells_app. symmetry. apply padR.
Qed.

Lemma inc : forall x y, Reach1 tm (mk1 (bcells ZL OL x) (tcells y)) (mk1 (bcells ZL OL (binc x)) (tcells (tinc y))).
Proof. intros x y. eapply reach01; [apply stepL|]. apply stepR. Qed.

Definition Cf (i : nat) : cconf :=
  mk1 (bcells ZL OL (Nat.iter i binc [])) (tcells (Nat.iter i tinc [])).

Lemma lap : forall i, Reach1 tm (Cf i) (Cf (S i)).
Proof. intros i. unfold Cf. cbn [Nat.iter nat_rect]. apply inc. Qed.

Lemma fire_b1 : forall x R, Fires tm (mk1 (bcells ZL OL x) R) (StB, S1).
Proof.
  intros x R. destruct (bsplit x) as [(k & r & ->) | (k & ->)].
  - rewrite bcells_tt, bcells_f. unfold mk1. eapply fire_back.
    { rr 3. change (StA, (ctl (rep OL k ++ ZL ++ bcells ZL OL r), chd (rep OL k ++ ZL ++ bcells ZL OL r), S1 :: S1 :: R))
        with (cL StA (rep OL k ++ ZL ++ bcells ZL OL r) (S1 :: S1 :: R)).
      rt (aloop k (ZL ++ bcells ZL OL r) (S1 :: S1 :: R)). r0. }
    rewrite (rep_snoc [S1; S1] k R : rep [S1; S1] k ++ S1 :: S1 :: R = S1 :: S1 :: rep [S1; S1] k ++ R). unfold cL. cbn [chd ctl app]. fire_find.
  - rewrite bcells_alltrue. unfold mk1. eapply fire_back.
    { rr 3. rewrite <- (app_nil_r (rep OL k)).
      change (StA, (ctl (rep OL k ++ []), chd (rep OL k ++ []), S1 :: S1 :: R))
        with (cL StA (rep OL k ++ []) (S1 :: S1 :: R)).
      rt (aloop k [] (S1 :: S1 :: R)). r0. }
    rewrite (rep_snoc [S1; S1] k R : rep [S1; S1] k ++ S1 :: S1 :: R = S1 :: S1 :: rep [S1; S1] k ++ R). unfold cL. cbn [chd ctl app]. fire_find.
Qed.

Lemma fire_r : forall L y t,
  t = (StA, S1) \/ t = (StC, S0) \/ t = (StD, S1) -> Fires tm (mk2 L (tcells y)) t.
Proof.
  intros L y t Ht. destruct (tsplit y) as [(k & d & r & -> & Hd) | (k & ->)].
  - rewrite tcells_app, tcells_rep. unfold mk2.
    change (cR StB (S0 :: S0 :: L) (rep (tdig t2) k ++ tcells (d :: r))) with (F (S0 :: L) (rep (tdig t2) k ++ tcells (d :: r))).
    eapply fire_back; [apply tloop|]. unfold F. cbn [tcells flat_map].
    destruct d; [| | congruence]; cbn [tdig app]; destruct Ht as [ -> | [ -> | -> ]]; fire_find.
  - rewrite tcells_rep. unfold mk2. rewrite <- (app_nil_r (rep (tdig t2) k)).
    change (cR StB (S0 :: S0 :: L) (rep (tdig t2) k ++ [])) with (F (S0 :: L) (rep (tdig t2) k ++ [])).
    eapply fire_back; [apply tloop|]. unfold F. destruct Ht as [ -> | [ -> | -> ]]; fire_find.
Qed.

(** [D0] fires in every right carry but the one from a low digit 1 *)
Lemma fire_d0 : forall L y, (forall r, y <> t1 :: r) -> Fires tm (mk2 L (tcells y)) (StD, S0).
Proof.
  intros L y Hy. destruct (tsplit y) as [(k & d & r & -> & Hd) | (k & ->)].
  - rewrite tcells_app, tcells_rep. unfold mk2.
    change (cR StB (S0 :: S0 :: L) (rep (tdig t2) k ++ tcells (d :: r))) with (F (S0 :: L) (rep (tdig t2) k ++ tcells (d :: r))).
    destruct k as [|k].
    + destruct d; [| exfalso; exact (Hy r eq_refl) | congruence]. unfold F. cbn. fire_find.
    + cbn [rep]. rewrite <- app_assoc. unfold F. cbn [tdig app]. fire_find.
  - rewrite tcells_rep. unfold mk2. destruct k as [|k]; [cbn; fire_find|].
    cbn [rep tdig app]. fire_find.
Qed.

Lemma fires_g : forall x y t, Fires tm (mk1 (bcells ZL OL x) (tcells y)) t.
Proof.
  intros x y [q s].
  destruct q, s;
  first [ unfold mk1; fire_find
        | apply fire_b1
        | eapply fire_back; [apply stepL | apply fire_r; tauto]
        | idtac ].
  destruct (tsplit y) as [(k & d & r & Ey & Hd) | (k & Ey)].
  - destruct k as [|k]; [destruct d; [| |congruence]|].
    + eapply fire_back; [apply stepL|]. apply fire_d0. rewrite Ey. intros r' E. discriminate.
    + eapply fire_back; [eapply reach0_trans; [apply stepL | apply reach1_0, stepR]|].
      eapply fire_back; [apply stepL|]. apply fire_d0. rewrite Ey. cbn. intros r' E. discriminate.
    + eapply fire_back; [apply stepL|]. apply fire_d0. rewrite Ey. intros r' E. discriminate.
  - eapply fire_back; [apply stepL|]. apply fire_d0. rewrite Ey. intros r' E.
    destruct k; discriminate.
Qed.

Lemma fires : forall t, ~ In t [] -> forall i, Fires tm (Cf i) t.
Proof. intros t _ i. apply fires_g. Qed.

Theorem nqhtr_1RB0LA_1LC0RB_1RD1LA_1RB1RC : NeverQuasiHaltsTr tm_1RB0LA_1LC0RB_1RD1LA_1RB1RC.
Proof.
  apply (boardS_neverqhtr _ [] Cf lap fires 0).
  apply boot_ok. vm_compute. reflexivity.
Qed.
