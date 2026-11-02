From Coq Require Import List Arith NArith.
From BBB24 Require Import Statement StatementTr CTape.
From BBB24SparseReturn Require Import BoundaryCounter.
Import ListNotations.

Example empty_scan_context:forall l r,
 csteps sp_tm 0(front(S3::l)r)=Some(front(S3::l)r).
Proof. reflexivity. Qed.
Example first_recursive_block:
 csteps sp_tm 12(at_one[S3;S1][S1;S3])=Some(at_one[][S1;S2;S1;S3]).
Proof. exact(one_block 0 [] []). Qed.
Example recursive_block_with_arbitrary_context:forall l r,
 csteps sp_tm 28(at_one(S3::S1::l)(S1::S2::S1::S3::r))=
 Some(at_one l(S1::S2::S1::S2::S1::S3::r)).
Proof. intros l r;exact(one_block 1 l r). Qed.
Example block_with_padded_context:
 csteps sp_tm 60(at_one[S3;S1;S0;S2](w12 2++[S1;S3;S0;S3]))=
 Some(at_one[S0;S2](w12 3++[S1;S3;S0;S3])).
Proof. exact(one_block 2 [S0;S2] [S0;S3]). Qed.
Example wrong_block_duration_rejected:
 csteps sp_tm 11(at_one[S3;S1][S1;S3])<>Some(at_one[][S1;S2;S1;S3]).
Proof. vm_compute;discriminate. Qed.
Example missing_delimiter_rejected:
 csteps sp_tm 7(front[S3][S1;S2])<>Some(at_one[][S1;S2]).
Proof. vm_compute;discriminate. Qed.
Example incorrect_blank_entry_rejected:csteps sp_tm 41 c0<>Some(main 1 S0).
Proof. vm_compute;discriminate. Qed.
Example first_boundary_gap:gap 1=94.
Proof. reflexivity. Qed.
Example second_boundary_gap:gap 3=382.
Proof. reflexivity. Qed.
Example next_boundary_from_actual_blank:
 csteps sp_tm 136 c0=Some(main 3 S0).
Proof. change(csteps sp_tm(42+94)c0=Some(main 3 S0));rewrite csteps_add,main_entry;exact(main_next 1). Qed.
Example A0_returns_beyond_every_horizon:forall N,exists k,N<=k/\FiresAt sp_tm(StA,S0)k.
Proof. intro N;apply all_instructions_recurrent. Qed.
Example B2_returns_beyond_every_horizon:forall N,exists k,N<=k/\FiresAt sp_tm(StB,S2)k.
Proof. intro N;apply all_instructions_recurrent. Qed.
