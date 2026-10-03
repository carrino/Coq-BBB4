(** * Counters.DoubleBounceTr: a bouncer that DOUBLES its block each round
    (SCOPING_INSTR 7.4.LE9).

    Three LE9 rows ([1RB0LC_1LA1RD_1LA1LC_0RC0LD] and two others) are not
    counters: with the head on the blank left of the tape, at an anchor
    state [q],

      R(n, m) = q | 0 1^n 0 1^m        ->+     R(2n, m+1)

    The round eats [1^n] one cell at a time, writing two zeros per cell at
    the left ([S(j,k,m) = q | 0 1 (00)^j 1^k 0 1^m]):

      S(j, k+1, m)  ->+  S(j+1, k, m)          (the eat arm, one family in [j])
      S(j, 0, m)    ->+  R(2j+2, m+1)          (the turn arm: (00)^j -> (11)^j,
                                                the separator one cell left)

    and [R(n+1, m) = S(0, n, m)].  So a round is [n - 1] eat arms (an
    induction on [k]) and one turn arm, each of which a [LadderNest] arm
    family states for every [j] and every tail.  The fires are read off one
    of the two arm families per instruction.  Never-QH and QH closers.

    Nothing landed is modified.  Axiom footprint: [functional_extensionality_dep],
    via [CTape.lift]. *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr.
From BBB4.Counters Require Import WTape.
From BBB4.Checkers Require Import WrapTr LapDecider LadderKernel LadderCheckTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import NestCountTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

Section DB.

Variable tm0  : TM.
Variable pins : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).
Variable q : St.

Definition dbmk (l : list Sym) : cconf := cfgR q [] (S0 :: l).

Definition dbR (n m : nat) : cconf := dbmk (rep [S1] n ++ [S0] ++ rep [S1] m).
Definition dbS (j k m : nat) : cconf :=
  dbmk ([S1] ++ rep [S0; S0] j ++ rep [S1] k ++ [S0] ++ rep [S1] m).

Hypothesis Heat : forall n X,
  Reach1 tm (dbmk ([S1] ++ rep [S0; S0] n ++ [S1] ++ X))
            (dbmk ([S1] ++ rep [S0; S0] n ++ [S0; S0] ++ X)).
Hypothesis Hturn : forall n X,
  Reach1 tm (dbmk ([S1] ++ rep [S0; S0] n ++ [S0; S1] ++ X))
            (dbmk (rep [S1; S1] n ++ [S1; S1; S0; S1; S1] ++ X)).
(** each instruction fires from every instance of one of the two families *)
Hypothesis Hfire : forall t, ~ In t pins ->
  (forall n X, Fires tm (dbmk ([S1] ++ rep [S0; S0] n ++ [S1] ++ X)) t) \/
  (forall n X, Fires tm (dbmk ([S1] ++ rep [S0; S0] n ++ [S0; S1] ++ X)) t).

Lemma rep_S_r' : forall (u : list Sym) k, rep u (S k) = rep u k ++ u.
Proof. intros u k. replace (S k) with (k + 1) by lia. rewrite rep_add. cbn. rewrite app_nil_r. reflexivity. Qed.

Lemma rep_dbl : forall (a : Sym) j, rep [a; a] j = rep [a] (2 * j).
Proof.
  induction j as [|j IH]; [reflexivity|].
  replace (2 * S j) with (S (S (2 * j))) by lia. cbn [rep]. rewrite IH. reflexivity.
Qed.

Lemma db_eats : forall k j m, Reach0 tm (dbS j k m) (dbS (j + k) 0 m).
Proof.
  induction k as [|k IH]; intros j m.
  - rewrite Nat.add_0_r. apply reach0_refl.
  - apply (reach0_trans tm _ (dbS (S j) k m)).
    + apply reach1_0. unfold dbS.
      rewrite (rep_S_r' [S0; S0] j), <- !app_assoc.
      change (rep [S1] (S k)) with ([S1] ++ rep [S1] k). rewrite <- !app_assoc.
      apply Heat.
    + replace (j + S k) with (S j + k) by lia. apply IH.
Qed.

Lemma db_turn : forall j m, Reach1 tm (dbS j 0 (S m)) (dbR (2 * j + 2) (S (S m))).
Proof.
  intros j m. unfold dbS, dbR. cbn [rep app].
  replace (2 * j + 2) with (2 * S j) by lia. rewrite <- rep_dbl, rep_S_r', <- !app_assoc.
  exact (Hturn j (rep [S1] m)).
Qed.

Lemma db_round : forall n m, Reach1 tm (dbR (S n) (S m)) (dbR (2 * S n) (S (S m))).
Proof.
  intros n m.
  assert (E : dbR (S n) (S m) = dbS 0 n (S m)) by reflexivity.
  rewrite E. apply (reach01 tm _ (dbS n 0 (S m))); [exact (db_eats n 0 (S m))|].
  replace (2 * S n) with (2 * n + 2) by lia. apply db_turn.
Qed.

Variables n0 m0 : nat.
Hypothesis Hn0 : 2 <= n0.
Hypothesis Hm0 : 1 <= m0.

Definition dbCf (i : nat) : cconf := dbR (2 ^ i * n0) (m0 + i).

Lemma db_pow_pos : forall i, 2 <= 2 ^ i * n0.
Proof. intros i. pose proof (Nat.pow_nonzero 2 i ltac:(lia)). nia. Qed.

Lemma db_lap : forall i, Reach1 tm (dbCf i) (dbCf (S i)).
Proof.
  intros i. unfold dbCf.
  pose proof (db_pow_pos i) as Hp.
  destruct (2 ^ i * n0) as [|n] eqn:E; [lia|].
  replace (2 ^ S i * n0) with (2 * S n) by (rewrite Nat.pow_succ_r'; lia).
  destruct m0 as [|m1]; [lia|].
  replace (S m1 + S i) with (S (S (m1 + i))) by lia. replace (S m1 + i) with (S (m1 + i)) by lia.
  apply db_round.
Qed.

Lemma db_lap_n : forall i, exists k c',
  csteps tm k (dbCf i) = Some c' /\ lift c' = lift (dbCf (S i)) /\ 0 < k.
Proof.
  intros i. destruct (reach1_csteps tm _ _ (db_lap i)) as (k & c' & Hk & Hc & Hl).
  exists k, c'. split; [exact Hc | split; [exact Hl | exact Hk]].
Qed.

Lemma db_fire : forall t, ~ In t pins -> forall i, Fires tm (dbCf i) t.
Proof.
  intros t Hnp i. unfold dbCf.
  pose proof (db_pow_pos i) as Hp.
  destruct (2 ^ i * n0) as [|[|k]] eqn:E; [lia | lia|].
  destruct m0 as [|m1]; [lia|].
  replace (S m1 + i) with (S (m1 + i)) by lia.
  set (m := m1 + i).
  destruct (Hfire t Hnp) as [He | Ht].
  - assert (Ee : dbR (S (S k)) (S m) = dbmk ([S1] ++ rep [S0; S0] 0 ++ [S1] ++ (rep [S1] k ++ [S0] ++ rep [S1] (S m))))
      by reflexivity.
    rewrite Ee. apply He.
  - apply (fire_back tm _ (dbS (S k) 0 (S m))).
    + exact (db_eats (S k) 0 (S m)).
    + exact (Ht (S k) (rep [S1] m)).
Qed.

Theorem db_neverqhtr : forall t0,
  stepn tm t0 InitES = Some (lift (dbCf 0)) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros t0 Hboot.
  apply (glue_neverqhtrN tm0 pins dbCf).
  - exists t0. exact Hboot.
  - exact db_lap_n.
  - intros t Hnp N. destruct (db_fire t Hnp N) as (k & c' & Hc & Ht).
    exists N, k, c'. split; [lia | split; assumption].
Qed.

Theorem db_qhtr : forall t0 B,
  stepn tm0 t0 InitES = Some (lift (dbCf 0)) ->
  existsb (fun tg => cfires tm0 CTape.c0 t0 tg) pins = true ->
  (t0 <=? B) = true ->
  NonHalt tm0 /\ QHBoundTr B tm0 /\ QuasiHaltsTr tm0.
Proof.
  intros t0 B Hboot Hwit Hle.
  apply (lap_qh_stage tm0 pins (fun p => dbCf (Nat.pred (Pos.to_nat p)))
           1%positive t0 B).
  - exact Hboot.
  - intros p _.
    destruct (db_lap_n (Nat.pred (Pos.to_nat p))) as (k & c' & Hrun & Hl & Hk).
    exists k, c'. split; [exact Hrun | split; [|exact Hk]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (db_fire t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End DB.
