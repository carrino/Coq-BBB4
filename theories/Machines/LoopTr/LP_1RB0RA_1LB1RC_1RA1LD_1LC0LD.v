(** * LP_1RB0RA_1LB1RC_1RA1LD_1LC0LD (SCOPING_INSTR 7.4.LE10)

    A mirror counter, the same scheme as [LP_1RB0RA_1LC1RD_1LD0LC_1RA1LC]
    (left [01] = 1, right [100] = 1, markers as digits).  The right carry
    walks in the shape [mk1] ([A0, B1, C0] per digit) and sweeps [D] left
    to the first left cell.  The left carry walks [D0, C1] and sweeps [A]
    back.

    Hand-stated, kernel-checked.  Axiom footprint: [functional_extensionality_dep]. *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr LoopMirrorTr.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Definition tm_1RB0RA_1LB1RC_1RA1LD_1LC0LD : TM := fun q s => match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB) | StA, S1 => Some (mkTrans S0 DR StA)
  | StB, S0 => Some (mkTrans S1 DL StB) | StB, S1 => Some (mkTrans S1 DR StC)
  | StC, S0 => Some (mkTrans S1 DR StA) | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DL StC) | StD, S1 => Some (mkTrans S0 DL StD)
  end.
Local Notation tm := (tm_wrap_trs tm_1RB0RA_1LB1RC_1RA1LD_1LC0LD []).
Local Notation Z := [S0; S0; S0].
Local Notation OR := [S1; S0; S0].
Local Notation OL := [S0; S1].
Local Notation ZL := [S0; S0].

Definition mk1 (Lc Rc : list Sym) : cconf := (StA, (Lc, S0, Rc)).
Definition mk2 (Lc Rc : list Sym) : cconf := cL StD Lc (S0 :: Rc).

Lemma awalk : forall n L R, Reach0 tm (mk1 L (rep OR n ++ R)) (mk1 (rep [S1; S1; S1] n ++ L) R).
Proof. apply (sweepFR tm mk1). intros L R. unfold mk1. rr 3. r0. Qed.

Lemma dsweep : forall n L R, Reach0 tm (cL StD (rep [S1] n ++ L) R) (cL StD L (rep [S0] n ++ R)).
Proof. apply sweepL. intros L R. rr 1. r0. Qed.

Lemma dwalk : forall n L R, Reach0 tm (cL StD (rep OL n ++ L) R) (cL StD L (rep [S1; S1] n ++ R)).
Proof. apply sweepL. intros L R. rr 2. r0. Qed.

Lemma asweep : forall n L R, Reach0 tm (cR StA L (rep [S1] n ++ R)) (cR StA (rep [S0] n ++ L) R).
Proof. apply sweepR. intros L R. rr 1. r0. Qed.

Lemma armR : forall k r Lc R',
  Reach1 tm (mk1 Lc (bcells Z OR (repeat true k ++ false :: r) ++ R'))
            (mk2 Lc (bcells Z OR (repeat false k ++ true :: r) ++ R')).
Proof.
  intros k r Lc R'. rewrite bcells_tt, bcells_ff, bcells_f, bcells_t, <- !app_assoc.
  eapply reach01; [apply (awalk k Lc (Z ++ bcells Z OR r ++ R'))|]. unfold mk1, mk2. rr 4.
  change (StD, (rep [S1; S1; S1] k ++ Lc, S1, S1 :: S0 :: S0 :: bcells Z OR r ++ R'))
    with (cL StD (S1 :: rep [S1; S1; S1] k ++ Lc) (S1 :: S0 :: S0 :: bcells Z OR r ++ R')).
  rewrite !rep_triple.
  change (S1 :: rep [S1] (k + k + k) ++ Lc) with (rep [S1] (S (k + k + k)) ++ Lc).
  rt (dsweep (S (k + k + k)) Lc (S1 :: S0 :: S0 :: bcells Z OR r ++ R')). r0.
Qed.

Lemma armL : forall k r L' Rc,
  Reach0 tm (mk2 (bcells ZL OL (repeat true k ++ false :: r) ++ L') Rc)
            (mk1 (bcells ZL OL (repeat false k ++ true :: r) ++ L') Rc).
Proof.
  intros k r L' Rc. rewrite bcells_tt, bcells_ff, bcells_f, bcells_t, <- !app_assoc. unfold mk1, mk2.
  rt (dwalk k (ZL ++ bcells ZL OL r ++ L') (S0 :: Rc)). unfold cL; cbn [chd ctl app]. rr 2.
  change (StA, (S1 :: bcells ZL OL r ++ L', S1, rep [S1; S1] k ++ S0 :: Rc))
    with (cR StA (S1 :: bcells ZL OL r ++ L') (S1 :: rep [S1; S1] k ++ S0 :: Rc)).
  rewrite !rep_pair.
  change (S1 :: rep [S1] (k + k) ++ S0 :: Rc) with (rep [S1] (S (k + k)) ++ S0 :: Rc).
  rt (asweep (S (k + k)) (S1 :: bcells ZL OL r ++ L') (S0 :: Rc)).
  rewrite (rep1_snoc S0 (k + k)). r0.
Qed.
Definition Cg (m : nat) : cconf :=
  mconf mk1 ZL OL Z OR (S (S m)) (S (S m)) 0 [] [] (2 ^ m).

Lemma lap_g : forall m, Reach1 tm (Cg m) (Cg (S m)).
Proof.
  intros m. unfold Cg.
  pose proof (Nat.pow_nonzero 2 m ltac:(lia)) as Hnz.
  assert (Hp : 2 ^ S m < 2 ^ S (S m)) by (rewrite !pow2_S; lia).
  assert (Hq : 2 ^ m < 2 ^ S m) by (rewrite pow2_S; lia).
  pose proof (mirror_iter1 tm mk1 mk2 ZL OL Z OR (fun k r Lc R0 => reach1_0 _ _ _ (armR k r Lc R0)) armL (S (S m)) (S (S m)) 0 [] [] armR (2 ^ m - 1) (2 ^ m)
                ltac:(rewrite pow2_S in Hp; lia) ltac:(rewrite pow2_S in Hp; lia)) as H.
  replace (2 ^ m + S (2 ^ m - 1)) with (2 ^ S m) in H by (rewrite pow2_S; lia).
  eapply reach10; [exact H|].
  unfold mconf, mk1. rewrite !Nat.add_0_r, (nb_extend (S (S m)) (2 ^ S m)) by lia.
  unfold bcells. rewrite !flat_map_app. cbn [flat_map]. rewrite !app_nil_r.
  match goal with |- Reach0 _ ?x (StA, (?A ++ _, S0, ?B ++ _)) =>
    apply (reach0_lift_r _ _ _ x); [|r0];
    etransitivity; [exact (lift_padR 3 StA (A ++ ZL) S0 B) | exact (lift_padL 2 StA A S0 B)] end.
Qed.

Definition Cf (i : nat) : cconf := Cg (S (S i)).

Lemma lap : forall i, Reach1 tm (Cf i) (Cf (S i)).
Proof. intros i. apply lap_g. Qed.

Lemma cf_eq : forall i, Cf i = mk1 (rep ZL (S (S i)) ++ OL ++ ZL) (rep Z (S (S i)) ++ OR ++ Z).
Proof.
  intros i. unfold Cf, Cg, mconf. rewrite Nat.add_0_r.
  rewrite (nb_extend (S (S (S i)))), nb_pow by (apply Nat.pow_lt_mono_r; lia).
  rewrite <- app_assoc. unfold bcells. rewrite !flat_map_app. fold (bcells ZL OL (repeat false (S (S i)))).
  fold (bcells Z OR (repeat false (S (S i)))). rewrite !bcells_allfalse. cbn [flat_map].
  rewrite !app_nil_r. reflexivity.
Qed.

Lemma fires : forall t, ~ In t [] -> forall i, Fires tm (Cf i) t.
Proof. intros [q s] _ i. rewrite cf_eq. unfold mk1. destruct q, s; fire_find. Qed.

Theorem nqhtr_1RB0RA_1LB1RC_1RA1LD_1LC0LD : NeverQuasiHaltsTr tm_1RB0RA_1LB1RC_1RA1LD_1LC0LD.
Proof.
  apply (boardS_neverqhtr _ [] Cf lap fires 62).
  apply boot_ok. rewrite cf_eq. vm_compute. reflexivity.
Qed.

