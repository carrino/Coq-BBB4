(** * Tests/Reroot_Corruption: negative controls for the re-root bridge.

    The re-root tier (Census/Reroot.v) boards a census 0RB machine [m]
    by transferring a decision from its re-root [TM_swap StA q* m].  The
    ONLY per-machine trust obligation is the prefix identity
    [stepn m t* InitES = Some (q*, snd InitES)], re-derived by the
    [vm_compute]-decidable gate [prefix_ok m q* t*].  If that gate were
    weakened -- accepting a wrong pivot state [q*], a wrong prefix
    length [t*], or a configuration whose tape is NOT still blank -- an
    unsound board could slip through.  Every control below is closed by
    [vm_compute]; a regression means the gate (hence [prefix_ok_sound],
    hence the [*_reroot] transfer) was loosened.

    All checks mirror the census negative-control style
    (Tests/Census_Corruption.v). *)

From Coq Require Import Arith Bool List.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import TNF_QH Deferred_Defs Reroot.
Import ListNotations.

(** ** A genuine re-root machine

    [m0 = 0RB0LA_1LC1LD_1RD0RD_1LA0RC] (a list-C never-QH census residue
    machine, drift-cert re-root).  Its blank read-0 path is one step:
    [StA] writes [S0] and moves to [StB], which then writes [S1] -- so
    the first 1-write is at [q* = StB], [t* = 1], and
    [stepn m0 1 InitES = Some (StB, snd InitES)]. *)
Definition m0 : TM := row_to_tm
  [t0RB; t0LA; t1LC; t1LD; t1RD; t0RD; t1LA; t0RC].

(** the genuine pivot/length is accepted *)
Example prefix_genuine : prefix_ok m0 StB 1 = true.
Proof. vm_compute. reflexivity. Qed.

(** and it really discharges the [stepn] identity the transfer consumes *)
Example prefix_genuine_stepn : stepn m0 1 InitES = Some (StB, snd InitES).
Proof. apply prefix_ok_sound. vm_compute. reflexivity. Qed.

(** WRONG pivot state: the config at step 1 is [StB], not [StA]/[StC]/[StD] *)
Example prefix_wrong_state_A : prefix_ok m0 StA 1 = false.
Proof. vm_compute. reflexivity. Qed.
Example prefix_wrong_state_C : prefix_ok m0 StC 1 = false.
Proof. vm_compute. reflexivity. Qed.
Example prefix_wrong_state_D : prefix_ok m0 StD 1 = false.
Proof. vm_compute. reflexivity. Qed.

(** WRONG length: [t* = 0] is still [StA]; [t* = 2] is past the first
    1-write so the tape is NO LONGER blank -- both rejected *)
Example prefix_wrong_len_0 : prefix_ok m0 StB 0 = false.
Proof. vm_compute. reflexivity. Qed.
Example prefix_wrong_len_2 : prefix_ok m0 StB 2 = false.
Proof. vm_compute. reflexivity. Qed.
(* even guessing the state right at t*=2, the tape is dirty, so it fails *)
Example prefix_len2_any_state :
  (prefix_ok m0 StA 2, prefix_ok m0 StB 2, prefix_ok m0 StC 2, prefix_ok m0 StD 2)
  = (false, false, false, false).
Proof. vm_compute. reflexivity. Qed.

(** ** The tape must be STILL BLANK, not merely the right state

    [dirty] writes a [S1] at [StA], bounces [L] into [StB], and [StB]
    returns [R] to [StA]: after 2 steps it is back in state [StA] but
    the tape carries a [S1] the head has left behind.  A gate that
    checked only the state would wrongly accept [(StA, 2)]; [prefix_ok]
    rejects it because the concrete half-tapes are not empty. *)
Definition dirty : TM :=
  row_to_tm [t1RB; tN; t1LA; tN; tN; tN; tN; tN].

(* state IS StA again at step 2 ... *)
Example dirty_state_returns :
  option_map fst (stepn dirty 2 InitES) = Some StA.
Proof. vm_compute. reflexivity. Qed.
(* ... but the tape is dirty, so the blank-prefix gate REJECTS it *)
Example dirty_rejected : prefix_ok dirty StA 2 = false.
Proof. vm_compute. reflexivity. Qed.
(* the genuine blank prefix of [dirty] is just its start (t*=0) *)
Example dirty_blank_only : prefix_ok dirty StA 0 = true.
Proof. vm_compute. reflexivity. Qed.

(** ** A machine that halts on the blank path has NO re-root pivot

    [halt0 = ---] (all-undefined): no step is possible, so no pivot at
    any positive length is accepted. *)
Definition halt0 : TM := fun _ _ => None.
Example halt0_no_pivot :
  (prefix_ok halt0 StA 1, prefix_ok halt0 StB 1, prefix_ok halt0 StB 2)
  = (false, false, false).
Proof. vm_compute. reflexivity. Qed.
(* only the trivial [t*=0] blank start is accepted *)
Example halt0_start_ok : prefix_ok halt0 StA 0 = true.
Proof. vm_compute. reflexivity. Qed.
