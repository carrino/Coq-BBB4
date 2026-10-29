(** Two complete tables share a binary paired-word carry. A pair of A0
    returns adds a (31) spacer and advances the finite counter word. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census.
Import ListNotations.

Definition dp_tm (two:bool):TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StB
 |StA,S2=>mkTrans S1 DR StA
 |StA,S3=>mkTrans(if two then S2 else S0)DR StA
 |StB,S0=>mkTrans S2 DR StB |StB,S1=>mkTrans S3 DR StA
 |StB,S2=>mkTrans S2 DL StB |StB,S3=>mkTrans S1 DL StA end).
Definition dp_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition dp_back q l r:cconf := (q,(ctl l,chd l,r)).
Fixpoint dp_pairs (x y:Sym)n := match n with 0=>[]|S n=>x::y::dp_pairs x y n end.
Fixpoint dp_bits(ds:list bool) := match ds with
 |[]=>[]|d::ds=>(if d then [S3;S1] else[S1;S3])++dp_bits ds end.
Definition dp_mode (mode:bool) := if mode then S3 else S1.
Definition dp_turn (two:bool) := if two then 4 else 6.
Definition dp_stage k l:cconf := (StA,(S1::S1::(dp_pairs S3 S1 k++l),S0,[])).
Definition dp_mid k l:cconf := (StA,(S1::S1::S3::(dp_pairs S1 S3 k++S3::l),S0,[])).
Definition dp_main k mode ds := dp_stage k(S1::dp_mode mode::(dp_bits ds++[S1;S3])).

Lemma dp_repeat_shift : forall (x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma dp_pair_shift : forall x y n l,
 dp_pairs x y n++x::y::l=x::y::(dp_pairs x y n++l).
Proof. intros x y n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma dp_rotate : forall n l,S3::(dp_pairs S1 S3 n++l)=dp_pairs S3 S1 n++S3::l.
Proof. induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma dp_rotate_one : forall n l,
 dp_pairs S1 S3 n++S1::l=S1::(dp_pairs S3 S1 n++l).
Proof. induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma dp_bits_app : forall ds es,dp_bits(ds++es)=dp_bits ds++dp_bits es.
Proof. induction ds;intro es;cbn;[reflexivity|now rewrite IHds,app_assoc]. Qed.
Lemma dp_bits_repeat : forall b n,
 dp_bits(repeat b n)=if b then dp_pairs S3 S1 n else dp_pairs S1 S3 n.
Proof. intros b n;induction n;destruct b;cbn in *;[reflexivity|reflexivity|now rewrite IHn|now rewrite IHn]. Qed.

Lemma dp_start : forall b l r,
 csteps(dp_tm b)5(StA,(S1::S1::l,S0,r))=Some(dp_back StB l(S2::S1::S2::r)).
Proof. intros b l r;reflexivity. Qed.
Lemma dp_left_spacer : forall b n l r,
 csteps(dp_tm b)(2*n)(dp_back StB(dp_pairs S3 S1 n++l)r)=
 Some(dp_back StB l(dp_pairs S2 S1 n++r)).
Proof.
 intros b n;induction n;intros l r;[reflexivity|].
 replace(2*S n)with(2+2*n)by lia;rewrite csteps_add.
 change(csteps(dp_tm b)(2*n)(dp_back StB(dp_pairs S3 S1 n++l)(S2::S1::r))=
 Some(dp_back StB l(S2::S1::(dp_pairs S2 S1 n++r)))).
 rewrite IHn,dp_pair_shift;reflexivity.
Qed.
Lemma dp_left_zeros : forall b n l r,
 csteps(dp_tm b)(2*n)(dp_back StA(dp_pairs S1 S3 n++l)(S1::r))=
 Some(dp_back StA l(S1::(dp_pairs S2 S1 n++r))).
Proof.
 intros b n;induction n;intros l r;[reflexivity|].
 replace(2*S n)with(2+2*n)by lia;rewrite csteps_add.
 change(csteps(dp_tm b)(2*n)(dp_back StA(dp_pairs S1 S3 n++l)(S1::S2::S1::r))=
 Some(dp_back StA l(S1::S2::S1::(dp_pairs S2 S1 n++r)))).
 rewrite IHn,dp_pair_shift;reflexivity.
Qed.
Lemma dp_right_pairs : forall b n l r,
 csteps(dp_tm b)(4*n)(dp_front StA l(dp_pairs S2 S1 n++r))=
 Some(dp_front StA(dp_pairs S1 S3 n++l)r).
Proof.
 intros b n;induction n;intros l r;[reflexivity|].
 replace(4*S n)with(4+4*n)by lia;rewrite csteps_add.
 change(csteps(dp_tm b)(4*n)(dp_front StA(S1::S3::l)(dp_pairs S2 S1 n++r))=
 Some(dp_front StA(S1::S3::(dp_pairs S1 S3 n++l))r)).
 rewrite IHn,dp_pair_shift;reflexivity.
Qed.
Lemma dp_right_twos : forall b n l r,
 csteps(dp_tm b)n(dp_front StA l(repeat S2 n++r))=
 Some(dp_front StA(repeat S1 n++l)r).
Proof.
 intros b n;induction n;intros l r;[reflexivity|].
 cbn[repeat app dp_front csteps cstep dp_tm ctape_move chd ctl].
 change(csteps(dp_tm b)n(dp_front StA(S1::l)(repeat S2 n++r))=
 Some(dp_front StA(S1::(repeat S1 n++l))r)).
 rewrite IHn,dp_repeat_shift;reflexivity.
Qed.
Lemma dp_tail : forall b l r,
 csteps(dp_tm b)5(dp_front StA l(S2::S1::S2::r))=
 Some(dp_front StA(S1::S1::S3::l)r).
Proof. intros b l r;reflexivity. Qed.
Lemma dp_double_three : forall b l r,
 csteps(dp_tm b)(dp_turn b)(dp_back StB(S3::S3::l)r)=
 Some(dp_back StB l(S2::S2::r)).
Proof. intros b l r;destruct b;reflexivity. Qed.
Lemma dp_true_boundary : forall b l r,
 csteps(dp_tm b)(dp_turn b)(dp_back StA(S3::S1::l)(S1::r))=
 Some(dp_front StA(S3::l)(S2::S2::r)).
Proof. intros b l r;destruct b;reflexivity. Qed.
Lemma dp_empty_boundary : forall b r,
 csteps(dp_tm b)10(dp_back StA[](S1::r))=Some(dp_front StA[S1;S1;S3]r).
Proof. intros b r;reflexivity. Qed.

Theorem dp_first_cut : forall b k l,
 csteps(dp_tm b)(6*k+11)(dp_stage k(S1::l))=Some(dp_mid k l).
Proof.
 intros b k l;replace(6*k+11)with(5+(2*k+(1+(4*k+5))))by lia.
 rewrite csteps_add;unfold dp_stage;rewrite dp_start,csteps_add,dp_left_spacer,csteps_add.
 change(csteps(dp_tm b)(4*k+5)
  (dp_front StA(S3::l)(dp_pairs S2 S1 k++[S2;S1;S2]))=Some(dp_mid k l)).
 rewrite csteps_add,dp_right_pairs,dp_tail;reflexivity.
Qed.
Lemma dp_mid_prefix : forall b k l,
 csteps(dp_tm b)(5+(2*k+dp_turn b))(dp_mid k l)=
 Some(dp_back StB l(S2::S2::(dp_pairs S2 S1 k++[S2;S1;S2]))).
Proof.
 intros b k l;rewrite csteps_add;unfold dp_mid;rewrite dp_start.
 rewrite dp_rotate,csteps_add,dp_left_spacer,dp_double_three;reflexivity.
Qed.
Theorem dp_one_mid : forall b k ds,
 csteps(dp_tm b)(6*k+13+dp_turn b)(dp_mid k(S1::(dp_bits ds++[S1;S3])))=
 Some(dp_main(S k)true ds).
Proof.
 intros b k ds;replace(6*k+13+dp_turn b)with
 ((5+(2*k+dp_turn b))+(1+(2+(4*k+5))))by lia.
 rewrite csteps_add,dp_mid_prefix,csteps_add.
 change(csteps(dp_tm b)(2+(4*k+5))
  (dp_front StA(S3::(dp_bits ds++[S1;S3]))
   (repeat S2 2++(dp_pairs S2 S1 k++[S2;S1;S2])))=
 Some(dp_main(S k)true ds)).
 rewrite csteps_add,dp_right_twos,csteps_add,dp_right_pairs,dp_tail.
 unfold dp_main,dp_stage,dp_mode;cbn[repeat app].
 rewrite dp_rotate,dp_pair_shift;reflexivity.
Qed.
Theorem dp_true_mid : forall b k n tail,
 csteps(dp_tm b)(6*k+6*n+15+2*dp_turn b)
 (dp_mid k(S3::(dp_bits(repeat false n++true::tail)++[S1;S3])))=
 Some(dp_main(S k)false(repeat true n++false::tail)).
Proof.
 intros b k n tail;replace(6*k+6*n+15+2*dp_turn b)with
 ((5+(2*k+dp_turn b))+(1+(2*n+(dp_turn b+(2+(4*n+(2+(4*k+5))))))))by lia.
 rewrite csteps_add,dp_mid_prefix,csteps_add.
 change(csteps(dp_tm b)(2*n+(dp_turn b+(2+(4*n+(2+(4*k+5))))))
  (dp_back StA(dp_bits(repeat false n++true::tail)++[S1;S3])
   (S1::S2::S2::(dp_pairs S2 S1 k++[S2;S1;S2])))=
 Some(dp_main(S k)false(repeat true n++false::tail))).
 rewrite dp_bits_app,dp_bits_repeat;cbn[dp_bits].
 rewrite <-app_assoc;cbn[app].
 rewrite csteps_add,dp_left_zeros,csteps_add,dp_true_boundary.
 change(csteps(dp_tm b)(2+(4*n+(2+(4*k+5))))
  (dp_front StA(S3::(dp_bits tail++[S1;S3]))
   (repeat S2 2++(dp_pairs S2 S1 n++S2::S2::(dp_pairs S2 S1 k++[S2;S1;S2]))))=
 Some(dp_main(S k)false(repeat true n++false::tail))).
 rewrite csteps_add,dp_right_twos,csteps_add,dp_right_pairs,csteps_add.
 change(csteps(dp_tm b)(2+(4*k+5))
  (dp_front StA(dp_pairs S1 S3 n++S1::S1::S3::(dp_bits tail++[S1;S3]))
   (repeat S2 2++(dp_pairs S2 S1 k++[S2;S1;S2])))=
 Some(dp_main(S k)false(repeat true n++false::tail))).
 rewrite csteps_add,dp_right_twos,csteps_add,dp_right_pairs,dp_tail.
 unfold dp_main,dp_stage,dp_mode;rewrite dp_bits_app,dp_bits_repeat;cbn[dp_bits repeat app].
 rewrite dp_rotate,dp_pair_shift,dp_rotate_one;try rewrite <-!app_assoc;reflexivity.
Qed.
Theorem dp_zero_mid : forall b k n,
 csteps(dp_tm b)(6*k+6*n+29+dp_turn b)
 (dp_mid k(S3::(dp_bits(repeat false n)++[S1;S3])))=
 Some(dp_main(S k)false(repeat true(S n))).
Proof.
 intros b k n;replace(6*k+6*n+29+dp_turn b)with
 ((5+(2*k+dp_turn b))+(1+(2*S n+(10+(4*S n+(2+(4*k+5)))))))by lia.
 rewrite csteps_add,dp_mid_prefix,csteps_add.
 change(csteps(dp_tm b)(2*S n+(10+(4*S n+(2+(4*k+5)))))
  (dp_back StA(dp_bits(repeat false n)++[S1;S3])
   (S1::S2::S2::(dp_pairs S2 S1 k++[S2;S1;S2])))=
 Some(dp_main(S k)false(repeat true(S n)))).
 rewrite dp_bits_repeat,dp_pair_shift,app_nil_r.
 change(csteps(dp_tm b)(2*S n+(10+(4*S n+(2+(4*k+5)))))
  (dp_back StA(dp_pairs S1 S3(S n))
   (S1::S2::S2::(dp_pairs S2 S1 k++[S2;S1;S2])))=
 Some(dp_main(S k)false(repeat true(S n)))).
 rewrite <-(app_nil_r(dp_pairs S1 S3(S n)))at 1.
 rewrite csteps_add,dp_left_zeros,csteps_add,dp_empty_boundary.
 rewrite csteps_add,dp_right_pairs,csteps_add.
 change(csteps(dp_tm b)(2+(4*k+5))
  (dp_front StA(dp_pairs S1 S3(S n)++[S1;S1;S3])
   (repeat S2 2++(dp_pairs S2 S1 k++[S2;S1;S2])))=
 Some(dp_main(S k)false(repeat true(S n)))).
 rewrite csteps_add,dp_right_twos,csteps_add,dp_right_pairs,dp_tail.
 unfold dp_main,dp_stage,dp_mode;rewrite dp_bits_repeat;cbn[repeat app].
 rewrite dp_rotate,dp_pair_shift,dp_rotate_one;try rewrite <-!app_assoc;reflexivity.
Qed.

Lemma dp_decompose : forall ds,
 (exists n,ds=repeat false n) \/ (exists n tail,ds=repeat false n++true::tail).
Proof.
 induction ds as[|d ds IH].
 - left;exists 0;reflexivity.
 - destruct d.
   + right;exists 0,ds;reflexivity.
   + destruct IH as[(n&E)|(n&tail&E)];subst ds.
     * left;exists(S n);reflexivity.
     * right;exists(S n),tail;reflexivity.
Qed.
Theorem dp_main_next : forall b k mode ds,exists t ds',0<t /\
 csteps(dp_tm b)t(dp_main k mode ds)=Some(dp_main(S k)(negb mode)ds').
Proof.
 intros b k mode ds;destruct mode.
 - destruct(dp_decompose ds)as[(n&E)|(n&tail&E)];subst ds.
   + exists((6*k+11)+(6*k+6*n+29+dp_turn b)),(repeat true(S n));split;[lia|].
     rewrite csteps_add;unfold dp_main at 1;rewrite dp_first_cut;apply dp_zero_mid.
   + exists((6*k+11)+(6*k+6*n+15+2*dp_turn b)),(repeat true n++false::tail);split;[lia|].
     rewrite csteps_add;unfold dp_main at 1;rewrite dp_first_cut;apply dp_true_mid.
 - exists((6*k+11)+(6*k+13+dp_turn b)),ds;split;[lia|].
   rewrite csteps_add;unfold dp_main at 1;rewrite dp_first_cut;apply dp_one_mid.
Qed.
Definition dp_entry_steps (b:bool) := if b then 33 else 35.
Example dp_entry : forall b,
 csteps(dp_tm b)(dp_entry_steps b)c0=Some(dp_main 0 false[]).
Proof. intro b;destruct b;reflexivity. Qed.
Lemma dp_returns : forall b N,exists t k mode ds,N<=t /\
 csteps(dp_tm b)t c0=Some(dp_main k mode ds).
Proof.
 intros b N;induction N as[|N IH].
 - exists(dp_entry_steps b),0,false,[];split;[lia|apply dp_entry].
 - destruct IH as(t&k&mode&ds&Ht&E);destruct(dp_main_next b k mode ds)as(j&ds'&Hj&E').
   exists(t+j),(S k),(negb mode),ds';split;[lia|];rewrite csteps_add,E;exact E'.
Qed.
Theorem dp_nonhalt : forall b,NonHalt(dp_tm b).
Proof.
 intros b n Hnone;destruct(dp_returns b n)as(t&k&mode&ds&Ht&E).
 pose proof(csteps_lift(dp_tm b)t c0(dp_main k mode ds)E)as Hrun;rewrite lift_c0 in Hrun.
 destruct(stepn_prefix(dp_tm b)n t InitES(lift(dp_main k mode ds))Ht Hrun)as(c&Ec&_);congruence.
Qed.
Theorem dp_A_recurrent : forall b N,exists t,N<=t /\ VisitsAt(dp_tm b)StA t.
Proof.
 intros b N;destruct(dp_returns b N)as(t&k&mode&ds&Ht&E).
 exists t;split;[exact Ht|];exists(lift(dp_main k mode ds));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem dp_B_recurrent : forall b N,exists t,N<=t /\ VisitsAt(dp_tm b)StB t.
Proof.
 intros b N;destruct(dp_returns b N)as(t&k&mode&ds&Ht&E).
 exists(t+1);split;[lia|].
 exists(lift(dp_back StB(S1::S1::(dp_pairs S3 S1 k++S1::dp_mode mode::
  (dp_bits ds++[S1;S3])))[S1]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem dp_state_zero : forall b,QHBound 0(dp_tm b).
Proof.
 intros b q s[_ Hquiet];destruct q.
 - destruct(dp_A_recurrent b(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(dp_B_recurrent b(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem dp_sound : forall b,NonHalt(dp_tm b) /\ QHBound 0(dp_tm b).
Proof. intro b;split;[apply dp_nonhalt|apply dp_state_zero]. Qed.
Print Assumptions dp_sound.
