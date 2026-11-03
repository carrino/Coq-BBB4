From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement StatementTr Spec CTape.
From BBB24SparseTwos Require Import TwosCounter.
Import ListNotations.

Example erased_blank_halts:csteps erased 2 c0=None.
Proof. reflexivity. Qed.
Example actual_blank_survives:csteps actual 2 c0=Some(main 0 S1).
Proof. exact entry_two. Qed.
Example erased_suffix_keeps_counting:
 csteps erased 11(main 0 S1)=Some(main 1 S1).
Proof. exact(main_next None 0). Qed.
Example generic_macro_ignores_B0:forall b0 n,
 csteps(tc_tm b0)(gap n)(main n S1)=Some(main(S n)S1).
Proof. exact main_next. Qed.
Example positive_block_has_arbitrary_context:forall b0 l r,
 csteps(tc_tm b0)15(at_two(S2::S2::S1::l)r)=Some(front(S2::S2::S2::S1::l)r).
Proof. intros;exact(one_block b0 2 ltac:(lia)l r). Qed.
Example zero_block_requires_its_distinct_base_case:
 csteps actual 3(at_two[S1][])<>Some(front[S2;S1][]).
Proof. vm_compute;discriminate. Qed.
Example zero_sentinel_is_not_permitted:
 csteps erased 7(at_two[S2;S0][])=None.
Proof. vm_compute;reflexivity. Qed.
Example first_gap:gap 0=11.
Proof. reflexivity. Qed.
Example second_gap:gap 1=27.
Proof. reflexivity. Qed.
Example third_gap:gap 2=59.
Proof. reflexivity. Qed.
Example second_actual_boundary:csteps actual 40 c0=Some(main 2 S1).
Proof. change(csteps actual(13+27)c0=Some(main 2 S1));rewrite csteps_add,entry;exact(main_next actual_b0 1). Qed.
Example sparse_A1_is_recurrent:forall N,exists k,N<=k/\FiresAt actual(StA,S1)k.
Proof. intro N;apply seven_recurrent;discriminate. Qed.
Example B0_cannot_recur:~NeverQuasiHaltsTr actual.
Proof.
 intro H;destruct(H(StB,S0)ltac:(exists 1;eexists;split;reflexivity)2)as(k&Hk&Hfire).
 exact(B0_quiet k Hk Hfire).
Qed.
Example instruction_bound_one_rejected:~QHBoundTr 1 actual.
Proof.
 intro H;destruct instruction_attains as(tg&s&Hlast&HB).
 pose proof(H tg s Hlast);lia.
Qed.
Example exact_instruction_score:AttainsTr actual 2/\QHBoundTr 2 actual.
Proof. split;[exact instruction_attains|exact instruction_bound]. Qed.
Print Assumptions exact_instruction_score.
