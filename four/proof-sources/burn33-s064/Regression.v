From Coq Require Import List Arith Bool NArith.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn33S064 Require Import Core Binary Trace.
Import ListNotations.
Example actual_blank_entry : csteps sk_tm 3 c0=Some(sk_main 0 1 true).
Proof. reflexivity. Qed.
Example pair_preserves_arbitrary_context :
 csteps sk_tm 7(sk_back StB[S1;S0;S3][S2;S2;S3;S0;S1])=
 Some(sk_back StB[S0;S3][S2;S2;S2;S2;S0;S1]).
Proof. reflexivity. Qed.
Example quadratic_batch : csteps sk_tm 33(sk_P 5 2 4 true S0)=Some(sk_P 2 8 1 true S0).
Proof. reflexivity. Qed.
Example reset_false : csteps sk_tm 8(sk_P 0 3 4 false S2)=Some(sk_P 2 2 3 true S2).
Proof. reflexivity. Qed.
Example reset_true : csteps sk_tm 8(sk_P 0 3 4 true S2)=Some(sk_P 3 2 3 false S2).
Proof. reflexivity. Qed.
Example empty_one_false : csteps sk_tm 4(sk_P 0 2 0 false S1)=Some(sk_main 0 3 true).
Proof. reflexivity. Qed.
Example empty_one_true : csteps sk_tm 4(sk_P 0 2 0 true S1)=Some(sk_main 0 4 false).
Proof. reflexivity. Qed.
Example terminal_one_turn : csteps sk_tm 11(sk_P 2 3 0 true S1)=Some(sk_P 1 2 2 true S2).
Proof. reflexivity. Qed.
Example terminal_two_return : csteps sk_tm 5(sk_P 2 3 0 true S2)=Some(sk_main 4 2 true).
Proof. reflexivity. Qed.
Example terminal_two_false_drift : csteps sk_tm 5(sk_P 0 3 0 false S2)=Some(sk_drift[S1;S1;S1;S1;S2]).
Proof. reflexivity. Qed.
Example terminal_two_true_drift : csteps sk_tm 5(sk_P 0 3 0 true S2)=Some(sk_drift[S1;S1;S1;S1;S1]).
Proof. reflexivity. Qed.
Example phase_zero_fuel_accepts_terminal : sk_phase 0 2 3 0 true=Some(sk_PR 2 3 true 0).
Proof. reflexivity. Qed.
Example phase_zero_fuel_rejects_pending : sk_phase 0 2 3 1 true=None.
Proof. reflexivity. Qed.
Example missing_boundary_is_rejected : sk_phase 8 0 0 1 false=None.
Proof. reflexivity. Qed.
Example synthetic_seed_drifts : sk_next 16 1 3 false=Some(sk_Done 5 true 27).
Proof. vm_compute;reflexivity. Qed.
Example actual_first_main_return : sk_next 16 0 1 true=Some(sk_Next 1 1 true 5).
Proof. vm_compute;reflexivity. Qed.
Example exact_long_prefix : csteps sk_tm(sk_count sk_runtime)c0=Some(sk_DN 486158 false).
Proof. exact sk_prefix. Qed.
Example drift_stays_B : forall t l,exists l',csteps sk_tm t(sk_drift l)=Some(sk_drift l').
Proof. exact sk_B_drift. Qed.
Example positive_state_bound : NonHalt sk_tm /\ QHBound(sk_count sk_boundN)sk_tm.
Proof. exact sk_sound. Qed.
Example actual_A_quiet : QuietFrom sk_tm StA(sk_count sk_runtime).
Proof. exact sk_A_quiet. Qed.
