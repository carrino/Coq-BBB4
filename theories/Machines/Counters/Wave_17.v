(** * Wave_17: the wave_counter machine #17, 1RB0RD_0LB1LC_1RA1LB_1RA1RD.

    WORK IN PROGRESS (wave track).  Edge state D, side R, poff 0,
    boot_vector [1;1;2;3] (cert results/counter17.cert).  The event
    config is the block word (frontier-first, lead dropped as the
    implicit trailing 1):

      Cf(front) = (StD, (1^{B_m} 0 1^{B_{m-1}} 0 ... 0 1^{B_1} 0 1, S0, [])),

    head one cell past the frontier.  The abstract pass [nextf 0] and
    its safety invariant [WInv 0] live in [WaveCounter]; this file
    carries the machine and the per-pass CONCRETE run (P1): a frontier
    turnaround, a leftward carry wave of parity-alternating run
    crossings ([cross_run] -- the crux, DONE below), a deposit, and a
    rightward reconstruction sweep.  No axioms beyond
    [functional_extensionality_dep]. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape WaveCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).

(** 1RB0RD_0LB1LC_1RA1LB_1RA1RD *)
Definition tm_17 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DR StD
  | StB, S0 => mk S0 DL StB | StB, S1 => mk S1 DL StC
  | StC, S0 => mk S1 DR StA | StC, S1 => mk S1 DL StB
  | StD, S0 => mk S1 DR StA | StD, S1 => mk S1 DR StD
  end.

(** ** The crux: crossing a run of ones leftward.

    From the frontier-turnaround the head sits on the top one of a run
    in state B; it walks left over the run (B and C alternating), and
    the state on reaching the separator encodes the run's parity -- B
    (continue the wave) if the run length is odd, C (stop and deposit)
    if even.  The [S k] ones (head plus [k] in the left list) are
    re-deposited on the right. *)
Definition stB (k : nat) : St := if Nat.even k then StC else StB.

Lemma cross_run : forall k rest R,
  csteps tm_17 (S k) (StB, (rep [S1] k ++ S0 :: rest, S1, R))
  = Some (stB k, (rest, S0, rep [S1] (S k) ++ R)).
Proof.
  intro k. pattern k. apply (well_founded_ind lt_wf). clear k.
  intros k IH rest R. destruct k as [|[|k']].
  - reflexivity.
  - reflexivity.
  - change (rep [S1] (S (S k'))) with (S1 :: S1 :: rep [S1] k').
    eapply csteps_chain with
      (n1 := 2) (n2 := S k')
      (c1 := (StB, (rep [S1] k' ++ S0 :: rest, S1, S1 :: S1 :: R))).
    + reflexivity.
    + rewrite (IH k' ltac:(lia) rest (S1 :: S1 :: R)).
      unfold stB. rewrite Nat.even_succ, Nat.odd_succ.
      f_equal. f_equal. f_equal.
      change (S1 :: S1 :: R) with (rep [S1] 2 ++ R).
      rewrite app_assoc, <- rep_add.
      replace (S k' + 2) with (S (S (S k'))) by lia. reflexivity.
Qed.
