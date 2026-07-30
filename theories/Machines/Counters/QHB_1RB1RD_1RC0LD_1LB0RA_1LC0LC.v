(** * QHB_1RB1RD_1RC0LD_1LB0RA_1LC0LC: machine 1RB1RD_1RC0LD_1LB0RA_1LC0LC, boarded as a QUASIHALTER.

    Emitted by tools/gen_qhb_row.py (UNTRUSTED emitter; the Coq kernel re-runs
    the checker below).

    This row sat in the closeout residue through thirty-two waves of
    never-quasihalting emitters, and it is not a never-quasihalter.  John's read
    of it, 2026-07-30, is "just diverges to the right using all states but B
    after 2331 steps".  Confirmed against the raw simulator over 3,000,000
    steps: [StB] is entered for the last time at index 2331, [StA]/[StC]/[StD]
    keep firing, the head drifts right at about one cell per three steps and the
    tape never reaches further left than -13.  So [StB] is eventually quiet, the
    machine QUASIHALTS, and what it needs is a score BOUND -- which is why every
    counter emitter in tools/counters/ was always going to file it under one gate
    or another.

    Why no earlier wave found it: `tools/sweep_qhbound_residue.py` searched
    `CAND_T = (64, 256, 1024)` and this machine's last [StB] visit is at 2331,
    so every candidate [t] was below the one index that had to be exceeded.
    Nothing about the route was missing.  `tools/sweep_qhbound_deep.py` reads
    [t] off the machine instead and finds it on the first try.

    [Checkers/Wrap.ngram_check_qhbound] is the decider: it wraps [StB] to a
    halt, closes the 2-gram abstraction of the configuration at index 2400
    (4 contexts), and checks that closure is halt-free and per-state
    ACYCLIC.  Halt-free gives [NonHalt]; acyclicity of every appearing state's
    own avoiding subgraph gives liveness, so no state other than [StB] can be
    quiet; and [StB]'s last visit is exhibited concretely at 2331 < 2400.
    Together that is [QHBound 2401], well inside the closeout's [B_board] =
    66,349.

    Axiom footprint: [functional_extensionality_dep] only, inherited from the
    imports; the certificate itself is one [vm_compute]. *)
From Coq Require Import Arith Lia List ZArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import NGram Wrap.
Import ListNotations.

(** 1RB1RD_1RC0LD_1LB0RA_1LC0LC *)
Definition tm_qhb_1RB1RD_1RC0LD_1LB0RA_1LC0LC : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StB)
  | StC, S1 => Some (mkTrans S0 DR StA)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S0 DL StC)
  end.

(** The closeout's explicit-bound stage entry (kind [iqh_le]). *)
Definition iqh_le (B : nat) (tm : TM) : Prop :=
  NonHalt tm /\ QHBound B tm /\ QuasiHaltsSt tm.

Theorem iqhle_1RB1RD_1RC0LD_1LB0RA_1LC0LC : iqh_le 2401 tm_qhb_1RB1RD_1RC0LD_1LB0RA_1LC0LC.
Proof.
  unfold iqh_le, QHBound.
  apply (ngram_check_qhbound_sound _ StB 2331 2 2400 96 9).
  vm_compute. reflexivity.
Qed.

Print Assumptions iqhle_1RB1RD_1RC0LD_1LB0RA_1LC0LC.
