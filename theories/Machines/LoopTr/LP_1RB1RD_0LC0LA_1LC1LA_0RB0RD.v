(** * LP_1RB1RD_0LC0LA_1LC1LA_0RB0RD: a hole moving through a run of 1s, each move a binary
    count of the cells behind it (SCOPING_INSTR 7.4.LE10).

    At its anchor [A] reads the blank left of [1^n].  It turns the first
    cell into the hole: [1 0 1^(n-1)], with [A] on the leading [1].  Moving
    the hole from cell [p] to [p+1] zeroes cells [1..p-1] and counts them
    back up to ones, a binary count of width [p].  So one lap costs about
    [2^n], and it ends at [1^(n+1)] one cell wider:
    [Cf i = A [0] 1^(i+2)].

    [pp]: [A] on a 0 with [0^k 1] to its left and [1^a 0] to its right
    fills to [A] on the 1 with [1^(k+a+1) 0] to its right.  It is proved by
    strong induction on the width [k + a], then by induction on [k].
    [uu] moves a [1^c] block across a 0 one cell at a time, with a nested
    [pp] at width [b] per cell.  [tret]: [D] zeroes a run and [C] writes
    it back one longer.

    Hand-stated, kernel-checked.  Axiom footprint: [functional_extensionality_dep]. *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Definition tm_1RB1RD_0LC0LA_1LC1LA_0RB0RD : TM := fun q s => match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StA)
  | StC, S0 => Some (mkTrans S1 DL StC)
  | StC, S1 => Some (mkTrans S1 DL StA)
  | StD, S0 => Some (mkTrans S0 DR StB)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.
Local Notation tm := (tm_wrap_trs tm_1RB1RD_0LC0LA_1LC1LA_0RB0RD []).
Local Notation o := (rep [S1]).
Local Notation z := (rep [S0]).

Lemma dsweep : forall b L R, Reach0 tm (cR StD L (o b ++ R)) (cR StD (z b ++ L) R).
Proof. apply sweepR. intros L R. rr 1. r0. Qed.

Lemma csweep : forall b L R, Reach0 tm (cL StC (z b ++ L) R) (cL StC L (o b ++ R)).
Proof. apply sweepL. intros L R. rr 1. r0. Qed.

(** the return: D zeroes [a] ones, C writes [a+1] ones back *)
Lemma tret : forall a L Y,
  Reach1 tm (StA, (L, S1, o a ++ S0 :: S0 :: Y)) (cL StA L (o (S (S a)) ++ S0 :: Y)).
Proof.
  intros a L Y. rr 1. rt dsweep. rr 2.
  rt (csweep (S a) (S1 :: L) (S0 :: Y)). rr 1. r0.
Qed.

Definition PP k a := forall XL Y,
  Reach1 tm (StA, (z k ++ S1 :: XL, S0, o a ++ S0 :: Y)) (StA, (XL, S1, o (k + a + 1) ++ S0 :: Y)).

Lemma uu : forall W, (forall b', b' < W -> PP b' 0) -> forall c b, b + c <= W ->
  forall L Y, Reach0 tm (StA, (L, S1, o b ++ S0 :: o c ++ S0 :: Y)) (StA, (L, S1, o (b + c) ++ S0 :: S0 :: Y)).
Proof.
  intros W HP c. induction c as [|c IH]; intros b Hb L Y.
  - rewrite Nat.add_0_r. r0.
  - rr 1. rt (dsweep b (S1 :: L) (S0 :: S1 :: o c ++ S0 :: Y)). rr 2.
    rt ((HP b ltac:(lia) L (o c ++ S0 :: Y))).
    rt (IH (b + 0 + 1) ltac:(lia) L Y). rfix.
Qed.

Lemma pp : forall w k a, k + a = w -> PP k a.
Proof.
  intros w. induction w as [w IHw] using lt_wf_ind.
  intros k. induction k as [|k IHk]; intros a Hka XL Y.
  - destruct a as [|a].
    + rr 3. r0.
    + rr 2. rt (uu a (fun b' Hb => IHw b' ltac:(lia) b' 0 ltac:(lia)) a 0 ltac:(lia) (S1 :: XL) Y).
      rt tret. rfix.
  - destruct a as [|a].
    + rr 3. rt ((IHk 1 ltac:(lia) XL Y)). rfix.
    + rr 2. rt (uu a (fun b' Hb => IHw b' ltac:(lia) b' 0 ltac:(lia)) a 0 ltac:(lia) (z (S k) ++ S1 :: XL) Y).
      rt tret. unfold cL. cbn [chd ctl rep app].
      rt ((IHk (S (S a)) ltac:(lia) XL Y)). rfix.
Qed.

Definition Cf (i : nat) : cconf := (StA, ([], S0, o (S (S i)))).

Lemma tomid : forall i, Reach0 tm (Cf i) (StA, ([], S1, o (S i) ++ S0 :: S0 :: [])).
Proof.
  intros i. unfold Cf. rr 2.
  apply (reach0_lift_l _ _ (StA, ([], S1, (S0 :: o (S i)) ++ S0 :: []))).
  { symmetry. apply (lift_padR 1). }
  exact (uu (S i) (fun b' Hb => pp b' b' 0 ltac:(lia)) (S i) 0 ltac:(lia) [] []).
Qed.

Lemma lap : forall i, Reach1 tm (Cf i) (Cf (S i)).
Proof.
  intros i. eapply reach01; [apply tomid|]. rt1 tret.
  apply (reach0_lift_r _ _ _ (cL StA [] (o (S (S (S i))) ++ S0 :: []))); [|r0].
  unfold Cf, cL. cbn [chd ctl]. symmetry. apply (lift_padR 1).
Qed.

Lemma fires : forall t, ~ In t [] -> forall i, Fires tm (Cf i) t.
Proof.
  intros [q s] _ i. destruct q, s.
  - apply fires_here. reflexivity.
  - eapply fire_back; [apply tomid|]. apply fires_here. reflexivity.
  - eapply fire_back; [apply tomid|]. eapply fire_back; [rr 1; rt (dsweep (S i) [S1] (S0 :: S0 :: [])); rr 1; r0|].
    apply fires_here. reflexivity.
  - eapply fire_back; [unfold Cf; rr 1; r0|]. apply fires_here. reflexivity.
  - eapply fire_back; [apply tomid|]. eapply fire_back; [rr 1; rt (dsweep (S i) [S1] (S0 :: S0 :: [])); rr 2; r0|].
    apply fires_here. reflexivity.
  - eapply fire_back; [apply tomid|]. eapply fire_back; [rr 1; rt (dsweep (S i) [S1] (S0 :: S0 :: [])); rr 2;
      rt (csweep (S (S i)) [S1] (S0 :: [])); r0|].
    apply fires_here. reflexivity.
  - eapply fire_back; [apply tomid|]. eapply fire_back; [rr 1; rt (dsweep (S i) [S1] (S0 :: S0 :: [])); r0|].
    apply fires_here. reflexivity.
  - eapply fire_back; [apply tomid|]. eapply fire_back; [rr 1; r0|].
    apply fires_here. reflexivity.
Qed.

Theorem nqhtr_1RB1RD_0LC0LA_1LC1LA_0RB0RD : NeverQuasiHaltsTr tm_1RB1RD_0LC0LA_1LC1LA_0RB0RD.
Proof.
  apply (boardS_neverqhtr tm_1RB1RD_0LC0LA_1LC1LA_0RB0RD [] Cf lap fires 10).
  apply boot_ok. vm_compute. reflexivity.
Qed.
