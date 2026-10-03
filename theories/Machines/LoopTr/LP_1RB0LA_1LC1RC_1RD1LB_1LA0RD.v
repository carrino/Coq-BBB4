(** * LP_1RB0LA_1LC1RC_1RD1LB_1LA0RD (SCOPING_INSTR 7.4.LE10)

    A mirror counter.  The head works at a junction [11 | C | 00]
    between a left digit string (pairs, [10] = 1, LSB at the junction)
    and a right one (triples, [100] = 1).  Both are [m] digits wide with a
    [1] marker beyond each.  The left holds [n + 1] and the right holds
    [n].  An increment is the right carry [armR] ([C] at the junction to
    [A] back at the junction), then the left carry [armL].  So
    [LoopMirrorTr.mirror_iter] runs [n = 0 .. 2^m - 2].  Then [ovf] (left
    all ones) resets both sides one digit wider: [Cf i] has width
    [i + 2].

    Hand-stated, kernel-checked.  Axiom footprint: [functional_extensionality_dep]. *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr LoopMirrorTr.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Definition tm_1RB0LA_1LC1RC_1RD1LB_1LA0RD : TM := fun q s => match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB) | StA, S1 => Some (mkTrans S0 DL StA)
  | StB, S0 => Some (mkTrans S1 DL StC) | StB, S1 => Some (mkTrans S1 DR StC)
  | StC, S0 => Some (mkTrans S1 DR StD) | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DL StA) | StD, S1 => Some (mkTrans S0 DR StD)
  end.
Local Notation tm := (tm_wrap_trs tm_1RB0LA_1LC1RC_1RD1LB_1LA0RD []).
Local Notation ZL := [S0; S0].
Local Notation OL := [S1; S0].
Local Notation ZR := [S0; S0; S0].
Local Notation OR := [S1; S0; S0].

Definition mk1 (Lc Rc : list Sym) : cconf := (StC, ([S1; S1; S0; S0] ++ Lc, S0, Rc)).
Definition mk2 (Lc Rc : list Sym) : cconf := (StA, ([S0; S0] ++ Lc, S1, [S0; S0] ++ Rc)).

Definition FC (L R : list Sym) : cconf := (StC, (L, S0, R)).

Lemma rwalk : forall n L R, Reach0 tm (FC L (rep OR n ++ R)) (FC (rep [S1; S1; S1] n ++ L) R).
Proof. apply sweepFR. intros L R. unfold FC. rr 5. r0. Qed.

Lemma asweep : forall n L R, Reach0 tm (cL StA (rep [S1] n ++ L) R) (cL StA L (rep [S0] n ++ R)).
Proof. apply sweepL. intros L R. rr 1. r0. Qed.

Lemma lwalk : forall n L R, Reach0 tm (cL StC (rep OL n ++ L) R) (cL StC L (rep [S1; S1] n ++ R)).
Proof. apply sweepL. intros L R. rr 2. r0. Qed.

Lemma dsweep : forall n L R, Reach0 tm (cR StD L (rep [S1] n ++ R)) (cR StD (rep [S0] n ++ L) R).
Proof. apply sweepR. intros L R. rr 1. r0. Qed.

Lemma armR : forall k r Lc R',
  Reach0 tm (mk1 Lc (bcells ZR OR (repeat true k ++ false :: r) ++ R'))
            (mk2 Lc (bcells ZR OR (repeat false k ++ true :: r) ++ R')).
Proof.
  intros k r Lc R'. rewrite bcells_tt, bcells_ff, bcells_f, bcells_t, <- !app_assoc. unfold mk1, mk2.
  change (StC, ([S1; S1; S0; S0] ++ Lc, S0, rep OR k ++ ZR ++ bcells ZR OR r ++ R'))
    with (FC ([S1; S1; S0; S0] ++ Lc) (rep OR k ++ ZR ++ bcells ZR OR r ++ R')).
  rt (rwalk k ([S1; S1; S0; S0] ++ Lc) (ZR ++ bcells ZR OR r ++ R')). unfold FC. rr 2.
  rewrite !rep_triple.
  change (StA, (rep [S1] (k + k + k) ++ S1 :: S1 :: S0 :: S0 :: Lc, S1, S1 :: S0 :: S0 :: bcells ZR OR r ++ R'))
    with (cL StA (S1 :: rep [S1] (k + k + k) ++ S1 :: [S1; S0; S0] ++ Lc) (S1 :: S0 :: S0 :: bcells ZR OR r ++ R')).
  rewrite rep1_snoc.
  change (S1 :: S1 :: rep [S1] (k + k + k) ++ [S1; S0; S0] ++ Lc) with (rep [S1] (2 + (k + k + k)) ++ [S1; S0; S0] ++ Lc).
  rt (asweep (2 + (k + k + k)) ([S1; S0; S0] ++ Lc) (S1 :: S0 :: S0 :: bcells ZR OR r ++ R')).
  unfold cL. cbn [chd ctl app]. r0.
Qed.

Lemma armL : forall k r L' Rc,
  Reach0 tm (mk2 (bcells ZL OL (repeat true k ++ false :: r) ++ L') Rc)
            (mk1 (bcells ZL OL (repeat false k ++ true :: r) ++ L') Rc).
Proof.
  intros k r L' Rc. rewrite bcells_tt, bcells_ff, bcells_f, bcells_t, <- !app_assoc. unfold mk1, mk2.
  rr 5.
  change (StC, (ctl (rep OL k ++ S0 :: S0 :: bcells ZL OL r ++ L'), chd (rep OL k ++ S0 :: S0 :: bcells ZL OL r ++ L'), S1 :: S1 :: S1 :: S0 :: S0 :: Rc))
    with (cL StC (rep OL k ++ S0 :: S0 :: bcells ZL OL r ++ L') (S1 :: S1 :: S1 :: S0 :: S0 :: Rc)).
  rt (lwalk k (S0 :: S0 :: bcells ZL OL r ++ L') (S1 :: S1 :: S1 :: S0 :: S0 :: Rc)).
  unfold cL; cbn [chd ctl]. rr 1.
  rewrite rep_pair.
  change (StD, (S1 :: S0 :: bcells ZL OL r ++ L', chd ?X, ctl ?X)) with (cR StD (S1 :: S0 :: bcells ZL OL r ++ L') X).
  rewrite !rep1_snoc.
  change (S1 :: S1 :: S1 :: rep [S1] (k + k) ++ S0 :: S0 :: Rc) with (rep [S1] (3 + (k + k)) ++ S0 :: S0 :: Rc).
  rt (dsweep (3 + (k + k)) (S1 :: S0 :: bcells ZL OL r ++ L') (S0 :: S0 :: Rc)).
  unfold cR; cbn [chd ctl]. rr 3.
  rewrite rep_pair. r0.
Qed.


Definition FD (L R : list Sym) : cconf := (StD, (L, S0, R)).

Lemma dwalk : forall n L R, Reach0 tm (cR StD L (rep OR n ++ R)) (cR StD (rep [S1; S1; S1] n ++ L) R).
Proof. apply sweepR. intros L R. rr 5. r0. Qed.

Lemma ovf : forall m,
  Reach1 tm (mk2 (bcells ZL OL (repeat true m) ++ [S1]) (bcells ZR OR (repeat true m) ++ [S1]))
            (mk1 (bcells ZL OL (nb (S m) 1) ++ [S1]) (bcells ZR OR (nb (S m) 0) ++ [S1])).
Proof.
  intros m. rewrite nb_one, nb_zero, !bcells_alltrue, bcells_t, bcells_allfalse. unfold mk1, mk2.
  rewrite bcells_allfalse. rr 3.
  change (StC, (S0 :: rep OL m ++ [S1], S1, S1 :: S0 :: S0 :: rep OR m ++ [S1]))
    with (cL StC (rep OL (S m) ++ [S1]) (S1 :: S0 :: S0 :: rep OR m ++ [S1])).
  rt (lwalk (S m) [S1] (S1 :: S0 :: S0 :: rep OR m ++ [S1])). unfold cL; cbn [chd ctl]. rr 4.
  rewrite rep_pair.
  change (StD, ([S0; S1], S1, S1 :: S1 :: rep [S1] (m + m) ++ S1 :: S0 :: S0 :: rep OR m ++ [S1]))
    with (cR StD [S0; S1] (S1 :: S1 :: S1 :: rep [S1] (m + m) ++ S1 :: S0 :: S0 :: rep OR m ++ [S1])).
  rewrite rep1_snoc.
  change (S1 :: S1 :: S1 :: S1 :: rep [S1] (m + m) ++ S0 :: S0 :: rep OR m ++ [S1])
    with (rep [S1] (4 + (m + m)) ++ S0 :: S0 :: rep OR m ++ [S1]).
  rt (dsweep (4 + (m + m)) [S0; S1] (S0 :: S0 :: rep OR m ++ [S1])). unfold cR; cbn [chd ctl].
  rr 4.
  change (StD, (S1 :: S1 :: S1 :: S0 :: S0 :: S0 :: rep [S0] (m + m) ++ [S0; S1], chd (rep OR m ++ [S1]), ctl (rep OR m ++ [S1])))
    with (cR StD (S1 :: S1 :: S1 :: S0 :: S0 :: S0 :: rep [S0] (m + m) ++ [S0; S1]) (rep OR m ++ [S1])).
  rt (dwalk m (S1 :: S1 :: S1 :: S0 :: S0 :: S0 :: rep [S0] (m + m) ++ [S0; S1]) [S1]).
  unfold cR; cbn [chd ctl]. rr 6.
  rewrite rep_triple.
  change (StA, (S1 :: S1 :: rep [S1] (m + m + m) ++ S1 :: S1 :: S1 :: S0 :: S0 :: S0 :: rep [S0] (m + m) ++ [S0; S1], S1, [S1]))
    with (cL StA (S1 :: S1 :: S1 :: rep [S1] (m + m + m) ++ S1 :: S1 :: S1 :: [S0; S0; S0] ++ rep [S0] (m + m) ++ [S0; S1]) [S1]).
  rewrite !(rep1_snoc S1 (m + m + m)).
  change (S1 :: S1 :: S1 :: S1 :: S1 :: S1 :: rep [S1] (m + m + m) ++ [S0; S0; S0] ++ rep [S0] (m + m) ++ [S0; S1])
    with (rep [S1] (6 + (m + m + m)) ++ [S0; S0; S0] ++ rep [S0] (m + m) ++ [S0; S1]).
  rt (asweep (6 + (m + m + m)) ([S0; S0; S0] ++ rep [S0] (m + m) ++ [S0; S1]) [S1]).
  unfold cL; cbn [chd ctl app]. rr 11.
  rewrite rep_pair, rep_triple, (rep1_snoc S0 (m + m)), ?rep1_fold. rfix.
Qed.

Definition Cf (i : nat) : cconf :=
  mk1 (bcells ZL OL (nb (S (S i)) 1) ++ [S1]) (bcells ZR OR (nb (S (S i)) 0) ++ [S1]).

Lemma toovf : forall i, Reach0 tm (Cf i)
  (mk2 (bcells ZL OL (repeat true (S (S i))) ++ [S1]) (bcells ZR OR (repeat true (S (S i))) ++ [S1])).
Proof.
  intros i. set (m := S (S i)).
  assert (Hp : 2 <= 2 ^ m) by (unfold m; rewrite !pow2_S; pose proof (Nat.pow_nonzero 2 i ltac:(lia)); lia).
  pose proof (mirror_iter tm mk1 mk2 ZL OL ZR OR armR armL m m 1 [S1] [S1] (2 ^ m - 2) 0
                ltac:(lia) ltac:(lia)) as H.
  unfold mconf in H. cbn [Nat.add] in H. unfold Cf. fold m.
  eapply reach0_trans; [exact H|].
  replace (2 ^ m - 2 + 1) with (2 ^ m - 1) by lia. rewrite nb_full. unfold m. rewrite nb_full_m1.
  exact (armR 0 (repeat true (S i)) _ [S1]).
Qed.

Lemma lap : forall i, Reach1 tm (Cf i) (Cf (S i)).
Proof. intros i. eapply reach01; [apply toovf|]. exact (ovf (S (S i))). Qed.

Lemma fires : forall t, ~ In t [] -> forall i, Fires tm (Cf i) t.
Proof.
  intros [q s] _ i. destruct q, s;
  first [ unfold Cf, mk1; rewrite nb_one, nb_zero, bcells_t, !bcells_allfalse; fire_find
        | eapply fire_back; [apply toovf|]; unfold mk2; rewrite !bcells_alltrue; fire_find ].
Qed.

Theorem nqhtr_1RB0LA_1LC1RC_1RD1LB_1LA0RD : NeverQuasiHaltsTr tm_1RB0LA_1LC1RC_1RD1LB_1LA0RD.
Proof.
  apply (boardS_neverqhtr _ [] Cf lap fires 111).
  apply boot_ok. vm_compute. reflexivity.
Qed.
