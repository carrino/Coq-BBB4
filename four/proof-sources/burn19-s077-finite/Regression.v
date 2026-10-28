From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn19S077Finite Require Import FiniteEscape FinitePrefix.
Import ListNotations.
Example first_step : csteps s77_tm 1 c0=Some(StB,([],S0,[S1])).
Proof. reflexivity. Qed.
Example B0_empty_right : csteps s77_tm 3(StB,([S1;S2],S0,[]))=Some(StB,([S3;S3;S3;S1;S2],S0,[])).
Proof. reflexivity. Qed.
Example B0_padded_right : csteps s77_tm 3(StB,([S2],S0,[S0;S0]))=Some(StB,([S3;S3;S3;S2],S0,[])).
Proof. reflexivity. Qed.
Example nonzero_right_prevents_drift : csteps s77_tm 2(StB,([],S0,[S1]))=Some(StA,([],S3,[S3])).
Proof. reflexivity. Qed.
Example B3_is_not_the_escape_cell : csteps s77_tm 1(StB,([S2],S3,[]))=Some(StB,([],S2,[S1])).
Proof. reflexivity. Qed.
Example checked_escape_guard : s77_endcheck 2501552%N=true.
Proof. exact s77_escape_checked. Qed.
Example checked_last_A_visit : VisitsAt s77_tm StA(s77_count 2501551%N).
Proof. apply s77_visit_Acheck_sound;exact s77_last_A_checked. Qed.
Example exact_state_score : AttainsSt s77_tm(s77_count 2501552%N).
Proof. exact s77_attains. Qed.
