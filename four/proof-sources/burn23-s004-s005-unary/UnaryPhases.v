(** A four-phase unary counter for both B2 writes. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census OneStateReach TotalCompletion.
Import ListNotations.
Definition pu_tm (bit:bool) : TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S0 DL StA
 |StA,S2=>mkTrans S1 DL StB |StA,S3=>mkTrans S1 DR StB
 |StB,S0=>mkTrans S3 DR StB |StB,S1=>mkTrans S3 DR StA
 |StB,S2=>mkTrans(if bit then S2 else S0)DR StB
 |StB,S3=>mkTrans S2 DL StA end).
Definition pu_X (bit:bool) := if bit then S2 else S0.
Definition pu_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition pu_P := [S0;S2;S1;S0;S0;S2;S1;S2;S1].
Definition pu_Q (bit:bool) := [S1;(if bit then S2 else S0);S3;S1;S3;S1;(if bit then S2 else S0);S3;S1].
Definition pu_R := [S0;S0;S2;S1;S2;S1;S0;S2;S1].
Definition pu_U := [S0;S2;S1].
Definition pu_T1 := [S0;S2;S1;S2;S1].
Definition pu_T2 := [S0;S2;S1;S0;S2;S1;S2;S1].
Definition pu_T3 := [S0;S2;S1;S0;S0;S2;S1;S0;S0;S2;S1;S2;S1].
Fixpoint pu_pow(w:list Sym)n := match n with 0=>[]|S n=>w++pu_pow w n end.
Definition pu_main n t:cconf := (StB,([],S0,S1::(pu_pow pu_P n++t))).
Lemma pu_forward_one : forall bit l r,
 csteps(pu_tm bit)41(pu_front StA(S3::S3::l)(pu_P++r))=
 Some(pu_front StA(S3::S3::(pu_Q bit++l))r).
Proof. intros[]l r;reflexivity. Qed.
Lemma pu_backward_one : forall bit l r,
 csteps(pu_tm bit)17(StA,(S3::S1::(pu_Q bit++l),pu_X bit,r))=
 Some(StA,(S3::S1::l,pu_X bit,pu_R++r)).
Proof. intros[]l r;reflexivity. Qed.
Lemma pu_terminal0 : forall bit l,
 csteps(pu_tm bit)16(pu_front StA(S3::S3::l)[])=
 Some(StA,(S3::S1::l,pu_X bit,[S2;S1])).
Proof. intros[]l;reflexivity. Qed.
Lemma pu_terminal1 : forall bit l,
 csteps(pu_tm bit)24(pu_front StA(S3::S3::l)pu_T1)=
 Some(StA,(S3::S1::l,pu_X bit,[S0;S2;S1;S2;S1])).
Proof. intros[]l;reflexivity. Qed.
Lemma pu_terminal2 : forall bit l,
 csteps(pu_tm bit)64(pu_front StA(S3::S3::l)pu_T2)=
 Some(StA,(S3::S1::l,pu_X bit,[S0;S0;S2;S1;S0;S0;S2;S1;S2;S1])).
Proof. intros[]l;reflexivity. Qed.
Lemma pu_terminal3 : forall bit l,
 csteps(pu_tm bit)100(pu_front StA(S3::S3::l)pu_T3)=
 Some(StA,(S3::S1::l,pu_X bit,[S0;S0;S2;S1;S2;S1;S0;S2;S1;S0;S0;S2;S1;S2;S1])).
Proof. intros[]l;reflexivity. Qed.
Lemma pu_pow_shift : forall w n l,pu_pow w n++w++l=w++pu_pow w n++l.
Proof.
 intros w n;induction n;intro l;cbn[pu_pow];[reflexivity|].
 rewrite <-!app_assoc;now rewrite IHn.
Qed.
Lemma pu_pow_add : forall w n m,pu_pow w(n+m)=pu_pow w n++pu_pow w m.
Proof. intros w n;induction n;intro m;cbn[pu_pow Nat.add];[reflexivity|now rewrite IHn,app_assoc]. Qed.
Lemma pu_forward : forall bit n l r,
 csteps(pu_tm bit)(41*n)(pu_front StA(S3::S3::l)(pu_pow pu_P n++r))=
 Some(pu_front StA(S3::S3::(pu_pow(pu_Q bit)n++l))r).
Proof.
 intros bit n;induction n;intros l r;[reflexivity|].
 replace(41*S n)with(41+41*n)by lia.
 change(csteps(pu_tm bit)(41+41*n)(pu_front StA(S3::S3::l)(pu_P++(pu_pow pu_P n++r)))=Some(pu_front StA(S3::S3::(pu_pow(pu_Q bit)(S n)++l))r)).
 rewrite csteps_add,pu_forward_one,IHn.
 rewrite pu_pow_shift;reflexivity.
Qed.
Lemma pu_backward : forall bit n l r,
 csteps(pu_tm bit)(17*n)(StA,(S3::S1::(pu_pow(pu_Q bit)n++l),pu_X bit,r))=
 Some(StA,(S3::S1::l,pu_X bit,pu_pow pu_R n++r)).
Proof.
 intros bit n;induction n;intros l r;[reflexivity|].
 replace(17*S n)with(17+17*n)by lia.
 change(csteps(pu_tm bit)(17+17*n)(StA,(S3::S1::(pu_Q bit++(pu_pow(pu_Q bit)n++l)),pu_X bit,r))=Some(StA,(S3::S1::l,pu_X bit,pu_pow pu_R(S n)++r))).
 rewrite csteps_add,pu_backward_one,IHn.
 rewrite pu_pow_shift;reflexivity.
Qed.
Lemma pu_entry : forall bit n t,csteps(pu_tm bit)2(pu_main n t)=
 Some(pu_front StA[S3;S3](pu_pow pu_P n++t)).
Proof. reflexivity. Qed.
Lemma pu_finish : forall bit r,csteps(pu_tm bit)4(StA,([S3;S1],pu_X bit,r))=
 Some(StB,([],S0,S1::S0::S2::S1::r)).
Proof. intros[]r;reflexivity. Qed.
Lemma pu_rotate : forall n,pu_U++pu_pow pu_R n=pu_pow pu_P n++pu_U.
Proof.
 induction n;[reflexivity|].
 change(pu_P++(pu_U++pu_pow pu_R n)=(pu_P++pu_pow pu_P n)++pu_U).
 rewrite IHn,app_assoc;reflexivity.
Qed.
Lemma pu_phase : forall bit n t s cost,
 (forall l,csteps(pu_tm bit)cost(pu_front StA(S3::S3::l)t)=
 Some(StA,(S3::S1::l,pu_X bit,s))) ->
 csteps(pu_tm bit)(58*n+cost+6)(pu_main n t)=Some(pu_main n(pu_U++s)).
Proof.
 intros bit n t s cost Hterminal.
 replace(58*n+cost+6)with(2+(41*n+(cost+(17*n+4))))by lia.
 rewrite csteps_add,pu_entry,csteps_add,pu_forward,csteps_add,Hterminal.
 rewrite csteps_add.
 rewrite pu_backward;cbn[app].
 rewrite pu_finish.
 assert(E:S1::S0::S2::S1::(pu_pow pu_R n++s)=S1::(pu_pow pu_P n++(pu_U++s))).
 {f_equal;change(pu_U++(pu_pow pu_R n++s)=pu_pow pu_P n++(pu_U++s)).
  rewrite app_assoc,pu_rotate,<-app_assoc;reflexivity. }
 rewrite E;reflexivity.
Qed.
Lemma pu_phase0 : forall bit n,csteps(pu_tm bit)(58*n+22)(pu_main n[])=Some(pu_main n pu_T1).
Proof. intros bit n;replace(58*n+22)with(58*n+16+6)by lia;exact(pu_phase bit n[] [S2;S1]16(pu_terminal0 bit)). Qed.
Lemma pu_phase1 : forall bit n,csteps(pu_tm bit)(58*n+30)(pu_main n pu_T1)=Some(pu_main n pu_T2).
Proof. intros bit n;replace(58*n+30)with(58*n+24+6)by lia;exact(pu_phase bit n pu_T1[S0;S2;S1;S2;S1]24(pu_terminal1 bit)). Qed.
Lemma pu_phase2 : forall bit n,csteps(pu_tm bit)(58*n+70)(pu_main n pu_T2)=Some(pu_main n pu_T3).
Proof. intros bit n;replace(58*n+70)with(58*n+64+6)by lia;exact(pu_phase bit n pu_T2[S0;S0;S2;S1;S0;S0;S2;S1;S2;S1]64(pu_terminal2 bit)). Qed.
Lemma pu_phase3 : forall bit n,csteps(pu_tm bit)(58*n+106)(pu_main n pu_T3)=Some(pu_main(n+2)[]).
Proof.
 intros bit n;pose proof(pu_phase bit n pu_T3[S0;S0;S2;S1;S2;S1;S0;S2;S1;S0;S0;S2;S1;S2;S1]100(pu_terminal3 bit))as E.
 replace(58*n+100+6)with(58*n+106)in E by lia.
 change(csteps(pu_tm bit)(58*n+106)(pu_main n pu_T3)=Some(pu_main n(pu_pow pu_P 2)))in E.
 unfold pu_main in *;rewrite pu_pow_add,app_nil_r;exact E.
Qed.
Theorem pu_cycle : forall bit n,csteps(pu_tm bit)(232*n+228)(pu_main n[])=Some(pu_main(n+2)[]).
Proof.
 intros bit n.
 replace(232*n+228)with((58*n+22)+((58*n+30)+((58*n+70)+(58*n+106))))by lia.
 rewrite csteps_add,pu_phase0,csteps_add,pu_phase1,csteps_add,pu_phase2,pu_phase3;reflexivity.
Qed.
Lemma pu_entry_blank : forall bit,csteps(pu_tm bit)1 c0=Some(pu_main 0[]).
Proof. reflexivity. Qed.
Lemma pu_returns : forall bit N,exists t n,N<=t /\csteps(pu_tm bit)t c0=Some(pu_main n[]).
Proof.
 intros bit N;induction N as[|N IH].
 - exists 1,0;split;[lia|apply pu_entry_blank].
 - destruct IH as(t&n&Ht&E);exists(t+(232*n+228)),(n+2);split;[lia|].
   rewrite csteps_add,E;apply pu_cycle.
Qed.
Theorem pu_nonhalt : forall bit,NonHalt(pu_tm bit).
Proof. intro bit;apply ore_total_nonhalt;intros q h;destruct q,h;eexists;reflexivity. Qed.
Theorem pu_B_recurrent : forall bit N,exists t,N<=t /\VisitsAt(pu_tm bit)StB t.
Proof.
 intros bit N;destruct(pu_returns bit N)as(t&n&Ht&E).
 exists t;split;[exact Ht|];exists(lift(pu_main n[]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem pu_A_recurrent : forall bit N,exists t,N<=t /\VisitsAt(pu_tm bit)StA t.
Proof.
 intros bit N;destruct(pu_returns bit N)as(t&n&Ht&E).
 exists(t+2);split;[lia|];exists(lift(pu_front StA[S3;S3](pu_pow pu_P n++[])));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;apply pu_entry.
Qed.
Theorem pu_state_zero : forall bit,QHBound 0(pu_tm bit).
Proof.
 intros bit q s[_ Hquiet];destruct q.
 - destruct(pu_A_recurrent bit(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(pu_B_recurrent bit(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem pu_sound : forall bit,NonHalt(pu_tm bit) /\QHBound 0(pu_tm bit).
Proof. intro bit;split;[apply pu_nonhalt|apply pu_state_zero]. Qed.
Print Assumptions pu_sound.
