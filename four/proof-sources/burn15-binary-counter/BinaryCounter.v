(** An odd-length block counter. A recursive B sweep restores its block,
    and a linear A sweep grows the block by two symbols. *)
From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement Spec CTape Census.
Import ListNotations.

Definition bc_tm : TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StA
 |StA,S2=>mkTrans S1 DR StA |StA,S3=>mkTrans S3 DR StB
 |StB,S0=>mkTrans S0 DR StB |StB,S1=>mkTrans S3 DL StB
 |StB,S2=>mkTrans S1 DR StA |StB,S3=>mkTrans S2 DL StB end).
Definition bc_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition bc_back q l r:cconf := (q,(ctl l,chd l,r)).
Definition bc_main n h:cconf := (StA,(repeat S1(2*n+1)++[S0],h,[])).
Fixpoint bc_work n := match n with 0=>5|S n=>2*bc_work n+7 end.

Lemma bc_work_value : forall n,bc_work n+7=12*2^n.
Proof. induction n;cbn[bc_work Nat.pow];nia. Qed.

Lemma bc_repeat_shift : forall (x:Sym)n r,
 repeat x n++x::r=x::(repeat x n++r).
Proof. intros x n;induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.

Theorem bc_recursive_block : forall n l r,
 csteps bc_tm(bc_work n)(bc_back StB(repeat S1(2*n+1)++S0::l)r)=
 Some(bc_front StA(repeat S1(2*n+1)++S0::l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(2*S n+1)with(S(S(2*n+1)))by lia;cbn[repeat app].
 replace(bc_work(S n))with(2+(bc_work n+(3+(bc_work n+2))))by(cbn[bc_work];lia).
 rewrite csteps_add.
 change(csteps bc_tm(bc_work n+(3+(bc_work n+2)))
   (bc_back StB(repeat S1(2*n+1)++S0::l)(S3::S3::r))=
   Some(bc_front StA(S1::S1::(repeat S1(2*n+1)++S0::l))r)).
 rewrite csteps_add,IHn,csteps_add.
 change(csteps bc_tm(bc_work n+2)
   (bc_back StB(repeat S1(2*n+1)++S0::l)(S2::S2::r))=
   Some(bc_front StA(S1::S1::(repeat S1(2*n+1)++S0::l))r)).
 rewrite csteps_add,IHn;reflexivity.
Qed.

Lemma bc_left_ones : forall n l r,
 csteps bc_tm n(bc_back StA(repeat S1 n++l)r)=
 Some(bc_back StA l(repeat S2 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app bc_back csteps cstep bc_tm ctape_move chd ctl].
 change(csteps bc_tm n(bc_back StA(repeat S1 n++l)(S2::r))=
 Some(bc_back StA l(S2::(repeat S2 n++r)))).
 rewrite IHn,bc_repeat_shift;reflexivity.
Qed.
Lemma bc_right_twos : forall n l r,
 csteps bc_tm n(bc_front StA l(repeat S2 n++r))=
 Some(bc_front StA(repeat S1 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app bc_front csteps cstep bc_tm ctape_move chd ctl].
 change(csteps bc_tm n(bc_front StA(S1::l)(repeat S2 n++r))=
 Some(bc_front StA(S1::(repeat S1 n++l))r)).
 rewrite IHn,bc_repeat_shift;reflexivity.
Qed.
Lemma bc_reset : forall r,
 csteps bc_tm 7(StA,([],S0,r))=Some(bc_front StA[S1;S0]r).
Proof. intro r;reflexivity. Qed.

Theorem bc_start_work : forall n,
 csteps bc_tm(1+bc_work n)(bc_main n S0)=Some(bc_main n S1).
Proof.
 intro n;rewrite csteps_add.
 change(csteps bc_tm(bc_work n)
   (bc_back StB(repeat S1(2*n+1)++[S0])[S1])=
   Some(bc_front StA(repeat S1(2*n+1)++[S0])[S1])).
 apply bc_recursive_block.
Qed.
Theorem bc_grow : forall n,
 csteps bc_tm(4*n+11)(bc_main n S1)=Some(bc_main(S n)S0).
Proof.
 intro n.
 assert(E:bc_main n S1=bc_back StA(repeat S1(2*n+2)++[S0])[]).
 {replace(2*n+2)with(S(2*n+1))by lia;reflexivity. }
 rewrite E.
 replace(4*n+11)with((2*n+2)+(7+(2*n+2)))by lia.
 rewrite csteps_add,bc_left_ones.
 rewrite app_nil_r,csteps_add.
 change(match csteps bc_tm 7(StA,([],S0,repeat S2(2*n+2)))with
 |Some c=>csteps bc_tm(2*n+2)c|None=>None end=Some(bc_main(S n)S0)).
 rewrite bc_reset.
 rewrite <-(app_nil_r(repeat S2(2*n+2)))at 1.
 rewrite bc_right_twos.
 unfold bc_main,bc_front;rewrite bc_repeat_shift.
 replace(2*S n+1)with(S(2*n+2))by lia;reflexivity.
Qed.

Definition bc_gap n := 1+bc_work n+(4*n+11).
Theorem bc_main_next : forall n,
 csteps bc_tm(bc_gap n)(bc_main n S0)=Some(bc_main(S n)S0).
Proof. intro n;unfold bc_gap;rewrite csteps_add,bc_start_work;apply bc_grow. Qed.
Example bc_entry : csteps bc_tm 7 c0=Some(bc_main 0 S0).
Proof. reflexivity. Qed.
Lemma bc_returns : forall N,exists k n,
 N<=k /\ csteps bc_tm k c0=Some(bc_main n S0).
Proof.
 induction N as[|N IH].
 - exists 7,0;split;[lia|exact bc_entry].
 - destruct IH as(k&n&Hk&E).
   exists(k+bc_gap n),(S n);split.
   + unfold bc_gap;lia.
   + rewrite csteps_add,E;apply bc_main_next.
Qed.
Theorem bc_nonhalt : NonHalt bc_tm.
Proof.
 intros n Hnone;destruct(bc_returns n)as(k&d&Hk&E).
 pose proof(csteps_lift bc_tm k c0(bc_main d S0)E)as Hrun;rewrite lift_c0 in Hrun.
 destruct(stepn_prefix bc_tm n k InitES(lift(bc_main d S0))Hk Hrun)as(c&Ec&_);congruence.
Qed.
Theorem bc_A_recurrent : forall N,exists k,N<=k /\ VisitsAt bc_tm StA k.
Proof.
 intro N;destruct(bc_returns N)as(k&n&Hk&E).
 exists k;split;[exact Hk|];exists(lift(bc_main n S0));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem bc_B_recurrent : forall N,exists k,N<=k /\ VisitsAt bc_tm StB k.
Proof.
 intro N;destruct(bc_returns N)as(k&n&Hk&E).
 exists(k+1);split;[lia|].
 exists(lift(bc_back StB(repeat S1(2*n+1)++[S0])[S1]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem bc_state_zero : QHBound 0 bc_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(bc_A_recurrent(S s))as(k&Hk&Hv);exfalso;apply(Hquiet k);[lia|exact Hv].
 - destruct(bc_B_recurrent(S s))as(k&Hk&Hv);exfalso;apply(Hquiet k);[lia|exact Hv].
Qed.
Theorem bc_sound : NonHalt bc_tm /\ QHBound 0 bc_tm.
Proof. split;[exact bc_nonhalt|exact bc_state_zero]. Qed.
Print Assumptions bc_sound.
