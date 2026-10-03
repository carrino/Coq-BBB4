(** * LP_1RB0RB_1LC1LD_0LC1RA_0LD0RA: a moving one with a recursive count
    behind it (SCOPING_INSTR 7.4.LE12).

    At its anchor [B] reads the blank right of [1 0^n]; a lap writes the
    marker, sweeps back to the left [1] and erases [0^n 1] again one cell
    wider: [Cf i = B [0] | 1 0^(i+3)].

    [ee N] (the erase): [A] on the first cell of [0^N 1], a [1] somewhere
    left behind [0^c], ends in [B] just right of the erased block, every
    cell from the [1]'s right neighbour to the block's end now [0].
    It is proved by strong induction on [N]: for [N >= 3] the machine
    moves the [1] one cell in, erases [0^j 1] for [j = 1 .. N-1] in a
    [loop] (each a smaller [ee]), sweeps back in [D] (clearing the moved
    [1]) and erases [0^(N-1) 1] one cell further on, again a smaller [ee].
    So the cells left of the marker run a Hanoi-like recursive count,
    and no counter reading is needed.

    Hand-stated, kernel-checked.  Axiom footprint: [functional_extensionality_dep]. *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Definition tm_1RB0RB_1LC1LD_0LC1RA_0LD0RA : TM := fun q s => match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S0 DR StB)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StC)
  | StC, S1 => Some (mkTrans S1 DR StA)
  | StD, S0 => Some (mkTrans S0 DL StD)
  | StD, S1 => Some (mkTrans S0 DR StA)
  end.
Local Notation tm := (tm_wrap_trs tm_1RB0RB_1LC1LD_0LC1RA_0LD0RA []).
Local Notation z := (rep [S0]).

(** [rfix] after folding [S0 :: rep [S0] n ++ l] into [rep [S0] (S n) ++ l] *)
Ltac zfix := unfold cL, cR; cbn [chd ctl rep app]; repeat rewrite rep1_fold;
  match goal with |- Reach0 _ ?a ?b => replace b with a; [apply reach0_refl | feq] end.

Lemma csweep : forall b L R, Reach0 tm (cL StC (z b ++ L) R) (cL StC L (z b ++ R)).
Proof. apply sweepL. intros L R. rr 1. r0. Qed.

Lemma dsweep : forall b L R, Reach0 tm (cL StD (z b ++ L) R) (cL StD L (z b ++ R)).
Proof. apply sweepL. intros L R. rr 1. r0. Qed.

Definition EE N := forall c X R,
  Reach1 tm (cR StA (z c ++ S1 :: X) (z N ++ S1 :: R)) (cR StB (z (c + N + 1) ++ S1 :: X) R).

(** erase [0^j 1] for each [j] from the current to [j + m - 1] *)
Lemma loop : forall N, (forall j, j < N -> EE j) -> forall m j W R, j + m < N ->
  Reach0 tm (cR StB (z j ++ S1 :: W) (z m ++ S1 :: R)) (cR StB (z (j + m) ++ S1 :: W) (S1 :: R)).
Proof.
  intros N HE m. induction m as [|m IH]; intros j W R Hjm.
  - rewrite Nat.add_0_r. r0.
  - rr 1. rt (csweep j (S1 :: W) (S1 :: z m ++ S1 :: R)). rr 1.
    rt (HE j ltac:(lia) 0 W (z m ++ S1 :: R)).
    rt (IH (0 + j + 1) W R ltac:(lia)). zfix.
Qed.

Lemma ee : forall N, EE N.
Proof.
  intros N. induction N as [N IH] using lt_wf_ind.
  destruct N as [|[|[|n]]]; intros c X R.
  - rr 1. zfix.
  - rr 4. zfix.
  - rr 11. zfix.
  - rr 7.
    rt (IH 1 ltac:(lia) 0 (z c ++ S1 :: X) (z n ++ S1 :: R)).
    rt (loop (S (S (S n))) (fun j Hj => IH j ltac:(lia)) n (0 + 1 + 1) (z c ++ S1 :: X) R ltac:(lia)).
    rr 1. rt (dsweep (0 + 1 + 1 + n) (S1 :: z c ++ S1 :: X) (S1 :: R)). rr 1.
    rt (IH (S (S n)) ltac:(lia) (S c) X R). zfix.
Qed.

Definition Cf (i : nat) : cconf := (StB, (z (i + 3) ++ [S1], S0, [])).

Lemma tostart : forall i, Reach0 tm (Cf i) (cR StA [S1] (z (i + 3) ++ [S1])).
Proof.
  intros i. unfold Cf. rr 1. rt (csweep (i + 3) [S1] [S1]). rr 1. zfix.
Qed.

Lemma lap : forall i, Reach1 tm (Cf i) (Cf (S i)).
Proof.
  intros i. eapply reach01; [apply tostart|].
  rt1 (ee (i + 3) 0 [] []). unfold Cf. zfix.
Qed.

(** the first steps of the erase at [N = i + 3], up to the D sweep *)
Lemma todsweep : forall i, Reach0 tm (Cf i)
  (cL StD (z (S (S i)) ++ [S1; S1]) (S1 :: [])).
Proof.
  intros i. eapply reach0_trans; [apply tostart|].
  replace (i + 3) with (S (S (S i))) by lia. cbn [rep app]. rr 7.
  rt (ee 1 0 [S1] (z i ++ [S1])).
  rt (loop (S (S (S i))) (fun j _ => ee j) i (0 + 1 + 1) [S1] [] ltac:(lia)).
  rr 1. zfix.
Qed.

Lemma fires : forall t, ~ In t [] -> forall i, Fires tm (Cf i) t.
Proof.
  intros [q s] _ i.
  destruct q, s;
    try (eapply fire_back; [apply tostart|]; replace (i + 3) with (S (S (S i))) by lia;
         cbn [rep app]; unfold cR; cbn [chd ctl]; fire_find);
    try (eapply fire_back; [apply todsweep|];
         cbn [rep app]; unfold cL; cbn [chd ctl]; fire_find);
    try (unfold Cf; fire_find).
Qed.

Theorem nqhtr_1RB0RB_1LC1LD_0LC1RA_0LD0RA : NeverQuasiHaltsTr tm_1RB0RB_1LC1LD_0LC1RA_0LD0RA.
Proof.
  apply (boardS_neverqhtr tm_1RB0RB_1LC1LD_0LC1RA_0LD0RA [] Cf lap fires 26).
  apply boot_ok. vm_compute. reflexivity.
Qed.
