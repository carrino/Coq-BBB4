(** The parity bit is necessary: the otherwise similar all-max/head-one
    configuration reaches an unbounded blank B sweep. *)
From Coq Require Import List.
From BBB24 Require Import Statement CTape.
From BBB24Burn13ParityCounter Require Import ParityCounter.
Import ListNotations.
Example one_middle_digit_has_odd_checksum : pc_parity[S2;S1]=true.
Proof. reflexivity. Qed.
Example two_middle_digits_have_even_checksum : pc_parity[S2;S2]=false.
Proof. reflexivity. Qed.
Example increment_zero : csteps pc_tm 4(pc_main[S0])=Some(pc_main[S2]).
Proof. reflexivity. Qed.
Example increment_middle : csteps pc_tm 4(pc_main[S2])=Some(pc_main[S1]).
Proof. reflexivity. Qed.
Example safe_overflow : csteps pc_tm 9(pc_main[S1])=Some(pc_main[S2;S2]).
Proof. reflexivity. Qed.
Example wrong_checksum_reaches_blank_B :
 csteps pc_tm 6(StA,([S1;S1],S1,[]))=Some(StB,([S0;S1;S2],S0,[])).
Proof. reflexivity. Qed.
Example undefined_A2_is_preserved : pc_tm StA S2=None.
Proof. reflexivity. Qed.
