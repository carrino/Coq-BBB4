(** * Wrap_Corruption: negative controls for the quiet-state checker.

    Test subject: tm_wrap_001 = 1RB---_0LC0LC_1RC0RD_1LB1RD (quiet
    state A, last visit at configuration index 0). *)

From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import Wrap.
From BBB4.Machines Require Import TCycler_Examples.
From BBB4.Machines.Bulk Require Import Wrap_01.

(* Positive control: the genuine parameters pass. *)
Example wrap_accept_genuine :
  ngram_check_quiet tm_wrap_001 StA 0 2 1 440 11 = true.
Proof. vm_compute. reflexivity. Qed.

(* Wrong quiet state: B is visited forever, so its wrapped closure
   contains a B-context and fails halt-freeness. *)
Example wrap_reject_state :
  ngram_check_quiet tm_wrap_001 StB 0 2 1 440 11 = false.
Proof. vm_compute. reflexivity. Qed.

(* Wrong last-visit index: configuration 1 is in state B, not A. *)
Example wrap_reject_index :
  ngram_check_quiet tm_wrap_001 StA 1 2 2 440 11 = false.
Proof. vm_compute. reflexivity. Qed.

(* The window must be nonempty: s < t is enforced. *)
Example wrap_reject_window :
  ngram_check_quiet tm_wrap_001 StA 1 2 1 440 11 = false.
Proof. vm_compute. reflexivity. Qed.

(* Retargeting at a machine that visits every state forever: the
   wrapped closure hits an A-context and is rejected. *)
Example wrap_reject_retarget :
  ngram_check_quiet tm_tc_neverqh StA 0 2 1 2000 16 = false.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions qh_1RBXXX_0LC0LC_1RC0RD_1LB1RD.
