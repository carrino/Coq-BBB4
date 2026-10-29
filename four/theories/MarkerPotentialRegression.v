(** The weighted-capacity mode handles balanced right/left rotors; corrupted
    inequalities fail closed. Padding is checked separately from the machine. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec CTape Pipeline StatePipeline
 MarkerState MarkerPotential.
Import ListNotations.
Definition mp_rotor := machine_of_codes[5;10;1;11;15;6;4;1].
Example mp_rotor_accepts : mp_check mp_rotor 2%N 0 0 1=true.
Proof. vm_compute;reflexivity. Qed.
Example mp_rotor_needs_capacity : ms_check mp_rotor 2%N=false.
Proof. vm_compute;reflexivity. Qed.
Example mp_missing_left_drop_rejects : mp_check mp_rotor 2%N 0 0 0=false.
Proof. vm_compute;reflexivity. Qed.
Example mp_excess_right_growth_rejects : mp_check mp_rotor 2%N 0 0 2=false.
Proof. vm_compute;reflexivity. Qed.
Example mp_excess_symbol_weight_rejects : mp_check mp_rotor 2%N 5 0 1=false.
Proof. vm_compute;reflexivity. Qed.
Example mp_blank_marker_rejects : mp_check mp_rotor 3%N 0 0 1=false.
Proof. vm_compute;reflexivity. Qed.
Example mp_missing_cell_rejects :
 mp_check(machine_of_codes[5;10;1;11;15;6;4;16])2%N 0 0 1=false.
Proof. vm_compute;reflexivity. Qed.
Example mp_unpadded_has_no_capacity :
 ~mp_capacity(mp_weights 0 0 1)(StB,([],S3,[S1])).
Proof. vm_compute;intro H;inversion H. Qed.
Example mp_two_blanks_create_capacity :
 mp_capacity(mp_weights 0 0 1)(mp_pad 2(StB,([],S3,[S1]))).
Proof. vm_compute;repeat constructor. Qed.
Example mp_padding_preserves_configuration :
 lift(mp_pad 2(StB,([],S3,[S1])))=lift(StB,([],S3,[S1])).
Proof. apply mp_pad_lift. Qed.
Example mp_rotor_state_zero : QHBound 0 mp_rotor.
Proof. exact(proj2(mp_check_sound _ _ _ _ _ mp_rotor_accepts)). Qed.
Example mp_rotor_nonhalt : NonHalt mp_rotor.
Proof. exact(proj1(mp_check_sound _ _ _ _ _ mp_rotor_accepts)). Qed.
