(** * LapAvoid_Corruption: negative controls for the state-avoidance route.

    BBB corruption-test tradition: every computable ingredient of the
    LAPQ_* boards must REJECT inputs that do not have the claimed property.
    The avoidance route rests on three checked computations
    ([Checkers/LapAvoid.v], [Counters/LapGlueQuiet.v]):

    - [srun_avoid]: the lap chain's own trace, re-run checking that no
      window step is in the avoided state.  A chain whose trace DOES visit
      the state must evaluate to [false]; so must the same chain asked
      about a state that recurs; so must a chain that overruns its window.
    - [bootquiet_chk]: the finite bootstrap window.  Shifting the window
      one step earlier makes it contain the quiet state's last visit, and
      the check must catch that.
    - [bootvis_chk]: the last-visit witness.  A wrong index must be
      rejected.

    Everything here is decided by [vm_compute]; a regression that made any
    of these pass would be a soundness alarm, not a convenience. *)

From Coq Require Import Arith Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlueQuiet.
From BBB4.Checkers Require Import LapDecider LapAvoid.
From BBB4.Machines.Counters Require Import LAPQ_1RB0RC_1LC0RB_0LC1RD_0RB1LA.
From BBB4.Machines.Counters Require Import LAPC_1RB1LA_1LC1RD_0LB1RA_1LB0RD.
Import ListNotations.

Local Notation tmq := tmm_1RB0RC_1LC0RB_0LC1RD_0RB1LA.
Local Notation choq := cho_1RB0RC_1LC0RB_0LC1RD_0RB1LA.
Local Notation B0q := B0_1RB0RC_1LC0RB_0LC1RD_0RB1LA.
Local Notation chpq := chp_1RB0RC_1LC0RB_0LC1RD_0RB1LA.
Local Notation P0q := P0_1RB0RC_1LC0RB_0LC1RD_0RB1LA.

(** ** A chain whose trace visits the state is REJECTED

    [LAPC_1RB1LA_1LC1RD_0LB1RA_1LB0RD] is a NEVER-quasihalting board: its
    overflow chain fires every state, StA included (its own visit lemma
    reaches StA on a prefix of this very chain).  Asking [srun_avoid]
    whether that chain avoids StA must come back [false] -- this is the
    exact mutation a wrong LAPQ board would carry. *)
Example live_StA_rejected :
  srun_avoid tmm_1RB1LA_1LC1RD_0LB1RA_1LB0RD true true StA
             cho_1RB1LA_1LC1RD_0LB1RA_1LB0RD
             B0_1RB1LA_1LC1RD_0LB1RA_1LB0RD = false.
Proof. vm_compute. reflexivity. Qed.

(** ** The check is state-sensitive on a genuine LAPQ board

    The boarded quasihalter's own chains avoid StA (that is its [av_*]
    lemmas) but visit the RECURRING states; the same boolean asked about
    each of those must refuse. *)
Example avoid_StB_rejected :
  srun_avoid tmq true true StB choq B0q = false.
Proof. vm_compute. reflexivity. Qed.

Example avoid_StC_rejected :
  srun_avoid tmq true true StC choq B0q = false.
Proof. vm_compute. reflexivity. Qed.

Example avoid_StD_rejected :
  srun_avoid tmq true true StD choq B0q = false.
Proof. vm_compute. reflexivity. Qed.

Example avoid_int_StC_rejected :
  srun_avoid tmq false true StC chpq P0q = false.
Proof. vm_compute. reflexivity. Qed.

(** ** A chain that overruns its window is REJECTED, not vacuously passed

    [srun_avoid] mirrors [srun]'s failure: a garbage step that walks off
    the window makes the whole boolean [false]. *)
Example avoid_overrun_rejected :
  srun_avoid tmq true true StA (choq ++ [SWin 50]) B0q = false.
Proof. vm_compute. reflexivity. Qed.

(** ** The bootstrap window checks are load-bearing

    On the boarded machine StA's last visit is at index 4 and the board
    checks the window [5, 8).  Sliding the window to START at 4 makes it
    contain that visit -- must be caught. *)
Example bootquiet_window_shift_rejected :
  bootquiet_chk tmq StA 4 4 = false.
Proof. vm_compute. reflexivity. Qed.

(** The visit witness is exact: index 5 is not a StA visit. *)
Example bootvis_wrong_index_rejected :
  bootvis_chk tmq StA 5 = false.
Proof. vm_compute. reflexivity. Qed.

(** And the blank tape starts IN StA, so a window that includes index 0
    can never be declared StA-free. *)
Example cavoid_index0_rejected :
  cavoid tmq StA 1 c0 = false.
Proof. vm_compute. reflexivity. Qed.
