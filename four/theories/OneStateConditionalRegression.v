(** The conditional checker must never be used without its NonHalt premise. *)
From Coq Require Import Lia.
From BBB24 Require Import Statement Spec Census OneStateConditional.
Example orc_empty_checks : orc_state_check empty=true.
Proof. vm_compute. reflexivity. Qed.
Example orc_empty_halts : Halts empty.
Proof. exists 1. reflexivity. Qed.
Example orc_empty_state_zero_false : ~QHBound 0 empty.
Proof.
  intro H. assert (Hquiet : QuietAfter empty StA 0).
  { split.
    - exists InitES. split; reflexivity.
    - intros n Hn [c [Hr _]]. destruct n; [lia|]. discriminate.
  }
  specialize (H StA 0 Hquiet). lia.
Qed.
Theorem orc_check_alone_is_not_a_state_bound :
  orc_state_check empty=true /\ Halts empty /\ ~QHBound 0 empty.
Proof. split; [exact orc_empty_checks|]. split; [exact orc_empty_halts|exact orc_empty_state_zero_false]. Qed.
