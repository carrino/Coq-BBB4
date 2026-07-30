(** * ReachStI_Examples: end-to-end validation of the invariant-relativised
    [ReachSt], and the corruption tests its new features must fail.

    The positive direction is [1RB---_0LB1RC_0RD0RC_1LB1LD], one of the rows
    Nick Drozd flagged as easy.  It is a [1RB---] machine, so the plain
    [ReachSt] tier cannot even be STATED for it: [StA]'s [S1] transition is
    undefined, so [ReachSt.Total] is false, and [ReachSt tm StB] is itself
    FALSE -- the configuration [(StA, ([], S1, []))] halts on the spot and
    never reaches [StB].  Relativised to [allowed = [StB;StC;StD]], which the
    orbit satisfies from index 1 onward, both defects vanish and the measure
    closes the goal-avoiding run.

    Every corruption below must evaluate to [false].  They are not decoration:
    each is a way the emitter could be wrong, and the point of a computable
    certificate is that being wrong costs a failed [vm_compute] rather than a
    false theorem. *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import ReachStI.
Import ListNotations.

Definition tm_1RB____0LB1RC_0RD0RC_1LB1LD : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB) | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StB) | StB, S1 => Some (mkTrans S1 DR StC)
  | StC, S0 => Some (mkTrans S0 DR StD) | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StB) | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Definition allowed_1RB____0LB1RC_0RD0RC_1LB1LD : list St := [StB; StC; StD].

Definition rk_1RB____0LB1RC_0RD0RC_1LB1LD (nd : mnode) : nat :=
  match nd with
  | (StB, S0, S0, S0) => 3
  | (StB, S0, S0, S1) => 3
  | (StB, S0, S1, S0) => 3
  | (StB, S0, S1, S1) => 3
  | (StB, S1, S0, S0) => 3
  | (StB, S1, S0, S1) => 3
  | (StB, S1, S1, S0) => 3
  | (StB, S1, S1, S1) => 3
  | (StC, S0, S0, S0) => 2
  | (StC, S0, S0, S1) => 2
  | (StC, S0, S1, S0) => 3
  | (StC, S0, S1, S1) => 3
  | (StC, S1, S0, S0) => 3
  | (StC, S1, S0, S1) => 3
  | (StC, S1, S1, S0) => 3
  | (StC, S1, S1, S1) => 3
  | (StD, S0, S0, S0) => 1
  | (StD, S0, S1, S0) => 2
  | (StD, S0, S1, S1) => 2
  | (StD, S1, S0, S0) => 3
  | (StD, S1, S1, S0) => 3
  | (StD, S1, S1, S1) => 3
  | _ => 0
  end.

Lemma live_1RB____0LB1RC_0RD0RC_1LB1LD :
  NonHalt tm_1RB____0LB1RC_0RD0RC_1LB1LD
  /\ forall N, exists n, N <= n /\ VisitsAt tm_1RB____0LB1RC_0RD0RC_1LB1LD StB n.
Proof.
  apply (reach_sti_recurs_b tm_1RB____0LB1RC_0RD0RC_1LB1LD allowed_1RB____0LB1RC_0RD0RC_1LB1LD StB 2 1 rk_1RB____0LB1RC_0RD0RC_1LB1LD 1);
    vm_compute; reflexivity.
Qed.

(** ** Corruption 1: the invariant may not swallow the undefined transition.

    [StA] has no [S1] transition, so no [allowed] containing it can be total,
    and [inv_ok] is exactly the check that rules this out.  Without it the
    development would be unsound on the [1RB---] rows, because the machine
    really can halt from a [StA] configuration. *)
Example corrupt_allowed_with_A :
  inv_ok tm_1RB____0LB1RC_0RD0RC_1LB1LD [StA; StB; StC; StD] = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Corruption 2: the measure constants are not free.

    [B = 2] is what the Bellman-Ford search returns; smaller values leave the
    [StD] left-sweep non-decreasing and the check must notice. *)
Example corrupt_B_zero :
  drop_ok tm_1RB____0LB1RC_0RD0RC_1LB1LD allowed_1RB____0LB1RC_0RD0RC_1LB1LD StB 0 1 rk_1RB____0LB1RC_0RD0RC_1LB1LD = false.
Proof. vm_compute. reflexivity. Qed.

Example corrupt_B_one :
  drop_ok tm_1RB____0LB1RC_0RD0RC_1LB1LD allowed_1RB____0LB1RC_0RD0RC_1LB1LD StB 1 1 rk_1RB____0LB1RC_0RD0RC_1LB1LD = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Corruption 3: the rank is not free either.

    Flattening [rk] to the constant [0] leaves the [StC] blank branch with no
    slack. *)
Example corrupt_rk_flat :
  drop_ok tm_1RB____0LB1RC_0RD0RC_1LB1LD allowed_1RB____0LB1RC_0RD0RC_1LB1LD StB 2 1 (fun _ => 0) = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Corruption 4: a goal the sub-machine does NOT reach is rejected.

    [StC] and [StD] are the two states this row is still missing (see
    docs/WAVE34_REACHSTI.md): their avoid sub-machines spin out leftward over
    a blank tape, and no measure in this family can hide that.  If the check
    accepted either it would be claiming something about a liveness question
    that is genuinely still open. *)
Example corrupt_goal_C :
  drop_ok tm_1RB____0LB1RC_0RD0RC_1LB1LD allowed_1RB____0LB1RC_0RD0RC_1LB1LD StC 2 1 rk_1RB____0LB1RC_0RD0RC_1LB1LD = false.
Proof. vm_compute. reflexivity. Qed.

Example corrupt_goal_D :
  drop_ok tm_1RB____0LB1RC_0RD0RC_1LB1LD allowed_1RB____0LB1RC_0RD0RC_1LB1LD StD 2 1 rk_1RB____0LB1RC_0RD0RC_1LB1LD = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Corruption 5: an unreachable goal is rejected.

    Nothing targets [StA], so "the run reaches [StA]" is false from every
    allowed configuration and no measure can drop forever. *)
Example corrupt_goal_A :
  drop_ok tm_1RB____0LB1RC_0RD0RC_1LB1LD allowed_1RB____0LB1RC_0RD0RC_1LB1LD StA 2 1 rk_1RB____0LB1RC_0RD0RC_1LB1LD = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Corruption 6: the prefix must land inside the invariant.

    At index 0 the machine is in [StA], which [allowed] excludes; the board
    has to run the one transient step first. *)
Example corrupt_start_zero :
  start_ok tm_1RB____0LB1RC_0RD0RC_1LB1LD allowed_1RB____0LB1RC_0RD0RC_1LB1LD 0 = false.
Proof. vm_compute. reflexivity. Qed.

Example start_one_is_right :
  start_ok tm_1RB____0LB1RC_0RD0RC_1LB1LD allowed_1RB____0LB1RC_0RD0RC_1LB1LD 1 = true.
Proof. vm_compute. reflexivity. Qed.
