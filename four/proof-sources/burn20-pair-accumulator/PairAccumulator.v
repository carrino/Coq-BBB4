(** Exact frozen S075. A positive 2-block and a nonempty (12)-block
    return by (a,b) -> (a+3,a+b). Every scan preserves arbitrary suffixes. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census OneStateReach.
Import ListNotations.
Definition pa_tm:TM:=fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DR StB
 |StA,S2=>mkTrans S0 DL StA |StA,S3=>mkTrans S2 DR StA
 |StB,S0=>mkTrans S1 DR StB |StB,S1=>mkTrans S3 DL StB
 |StB,S2=>mkTrans S2 DL StB |StB,S3=>mkTrans S2 DR StA end).
Definition pa_front q l r:cconf:=(q,(l,chd r,ctl r)).
Definition pa_back q l r:cconf:=(q,(ctl l,chd l,r)).
Fixpoint pa_P n:list Sym:=match n with 0=>[]|S n=>S1::S2::pa_P n end.
Fixpoint pa_Q n:list Sym:=match n with 0=>[]|S n=>S3::S2::pa_Q n end.
Fixpoint pa_R n:list Sym:=match n with 0=>[]|S n=>S2::S3::pa_R n end.
Definition pa_tag(b:bool):=if b then S1 else S2.
Definition pa_write(b:bool):=if b then S3 else S2.
Definition pa_stage a b r:cconf:=(StA,(repeat S2 a++S1::pa_P b,S0,r)).
Definition pa_G p q k:=pa_front StA(S2::S1::pa_P p)
 (repeat S3(S q)++repeat S2 k++[S1]).
Definition pa_main a b:=pa_stage(S a)(S b)[].
Lemma pa_repeat_shift : forall (z:Sym) n r,
 repeat z n++z::r=z::(repeat z n++r).
Proof. intros z n;induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma pa_Q_shift : forall n r,
 pa_Q n++S3::S2::r=S3::S2::(pa_Q n++r).
Proof. induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma pa_R_shift : forall n r,
 pa_R n++S2::S3::r=S2::S3::(pa_R n++r).
Proof. induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma pa_rotate : forall n r,S3::(pa_R n++r)=pa_Q n++S3::r.
Proof. induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma pa_A3 : forall n l r,
 csteps pa_tm n(pa_front StA l(repeat S3 n++r))=
 Some(pa_front StA(repeat S2 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(S n)with(1+n)by lia;rewrite csteps_add.
 change(csteps pa_tm n(pa_front StA(S2::l)(repeat S3 n++r))=
 Some(pa_front StA(S2::(repeat S2 n++l))r)).
 rewrite IHn,pa_repeat_shift;reflexivity.
Qed.
Lemma pa_B0 : forall n l r,
 csteps pa_tm n(pa_front StB l(repeat S0 n++r))=
 Some(pa_front StB(repeat S1 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(S n)with(1+n)by lia;rewrite csteps_add.
 change(csteps pa_tm n(pa_front StB(S1::l)(repeat S0 n++r))=
 Some(pa_front StB(S1::(repeat S1 n++l))r)).
 rewrite IHn,pa_repeat_shift;reflexivity.
Qed.
Lemma pa_A2 : forall n l r,
 csteps pa_tm n(pa_back StA(repeat S2 n++l)r)=
 Some(pa_back StA l(repeat S0 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(S n)with(1+n)by lia;rewrite csteps_add.
 change(csteps pa_tm n(pa_back StA(repeat S2 n++l)(S0::r))=
 Some(pa_back StA l(S0::(repeat S0 n++r)))).
 rewrite IHn,pa_repeat_shift;reflexivity.
Qed.
Lemma pa_B1 : forall n l r,
 csteps pa_tm n(pa_back StB(repeat S1 n++l)r)=
 Some(pa_back StB l(repeat S3 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(S n)with(1+n)by lia;rewrite csteps_add.
 change(csteps pa_tm n(pa_back StB(repeat S1 n++l)(S3::r))=
 Some(pa_back StB l(S3::(repeat S3 n++r)))).
 rewrite IHn,pa_repeat_shift;reflexivity.
Qed.
Lemma pa_B2 : forall n l r,
 csteps pa_tm n(pa_back StB(repeat S2 n++l)r)=
 Some(pa_back StB l(repeat S2 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(S n)with(1+n)by lia;rewrite csteps_add.
 change(csteps pa_tm n(pa_back StB(repeat S2 n++l)(S2::r))=
 Some(pa_back StB l(S2::(repeat S2 n++r)))).
 rewrite IHn,pa_repeat_shift;reflexivity.
Qed.
Lemma pa_Bpairs : forall n l r,
 csteps pa_tm(2*n)(pa_back StB(pa_P n++l)r)=
 Some(pa_back StB l(pa_R n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(2*S n)with(2+2*n)by lia;rewrite csteps_add.
 change(csteps pa_tm(2*n)(pa_back StB(pa_P n++l)(S2::S3::r))=
 Some(pa_back StB l(S2::S3::(pa_R n++r)))).
 rewrite IHn,pa_R_shift;reflexivity.
Qed.
Lemma pa_support : forall l r,
 csteps pa_tm 6(pa_front StA(S2::S1::l)(S2::S3::r))=
 Some(pa_front StA(S2::S1::S1::S2::l)r).
Proof. reflexivity. Qed.
Lemma pa_support_scan : forall n p r,
 csteps pa_tm(6*n)(pa_front StA(S2::S1::pa_P p)(S2::(pa_Q n++r)))=
 Some(pa_front StA(S2::S1::pa_P(p+n))(S2::r)).
Proof.
 induction n;intros p r.
 - cbn;rewrite Nat.add_0_r;reflexivity.
 - replace(6*S n)with(6+6*n)by lia;rewrite csteps_add.
   change(match csteps pa_tm 6(pa_front StA(S2::S1::pa_P p)(S2::S3::S2::(pa_Q n++r)))with
   |Some cc=>csteps pa_tm(6*n)cc|None=>None end=
   Some(pa_front StA(S2::S1::pa_P(p+S n))(S2::r))).
   rewrite pa_support.
   change(csteps pa_tm(6*n)(pa_front StA(S2::S1::pa_P(S p))(S2::(pa_Q n++r)))=
   Some(pa_front StA(S2::S1::pa_P(p+S n))(S2::r))).
   rewrite IHn;replace(S p+n)with(p+S n)by lia;reflexivity.
Qed.
Lemma pa_boundary : forall n r,
 csteps pa_tm(2*S n+5)(pa_back StB(pa_P(S n))r)=
 Some(pa_front StA[S2;S1](S2::(pa_Q n++S3::r))).
Proof.
 intros n r;replace(2*S n+5)with(2*S n+5)by lia;rewrite csteps_add.
 pose proof(pa_Bpairs(S n)[]r)as E;rewrite app_nil_r in E;rewrite E.
 change(Some(pa_front StA[S2;S1](S2::S3::(pa_R n++r)))=
 Some(pa_front StA[S2;S1](S2::(pa_Q n++S3::r)))).
 rewrite pa_rotate;reflexivity.
Qed.
Theorem pa_restore : forall n r,
 csteps pa_tm(8*S n+5)(pa_back StB(pa_P(S n))r)=
 Some(pa_front StA(S2::S1::pa_P(S n))r).
Proof.
 intros n r;replace(8*S n+5)with((2*S n+5)+(6*n+6))by lia.
 rewrite csteps_add,pa_boundary,csteps_add.
 pose proof(pa_support_scan n 0(S3::r))as E;cbn[pa_P Nat.add]in E;rewrite E.
 rewrite pa_support;reflexivity.
Qed.
Lemma pa_erase : forall n l r,
 csteps pa_tm(2*n+3)(pa_front StA(repeat S2 n++S1::l)(S2::r))=
 Some(pa_front StB(repeat S1(S n)++S2::l)r).
Proof.
 intros n l r;replace(2*n+3)with(S n+(1+S n))by lia;rewrite csteps_add.
 change(match csteps pa_tm(S n)(pa_back StA(repeat S2(S n)++S1::l)r)with
 |Some cc=>csteps pa_tm(1+S n)cc|None=>None end=
 Some(pa_front StB(repeat S1(S n)++S2::l)r)).
 rewrite pa_A2,csteps_add.
 change(csteps pa_tm(S n)(pa_front StB(S2::l)(repeat S0(S n)++r))=
 Some(pa_front StB(repeat S1(S n)++S2::l)r)).
 apply pa_B0.
Qed.
Lemma pa_tag_step : forall b l r,
 csteps pa_tm 1(pa_front StB l(pa_tag b::r))=
 Some(pa_back StB l(pa_write b::r)).
Proof. intros [];reflexivity. Qed.
Theorem pa_rebuild : forall n q b r,
 csteps pa_tm(8*S n+q+16)
 (pa_front StB(repeat S1(q+3)++S2::pa_P(S n))(pa_tag b::r))=
 Some(pa_front StA(S2::S1::pa_P(S(S n)))
 (repeat S3(q+2)++pa_write b::r)).
Proof.
 intros n q b r;replace(8*S n+q+16)with(1+((q+3)+(1+((8*S n+5)+6))))by lia.
 rewrite csteps_add,pa_tag_step,csteps_add,pa_B1,csteps_add.
 change(csteps pa_tm((8*S n+5)+6)
 (pa_back StB(pa_P(S n))(S2::(repeat S3(q+3)++pa_write b::r)))=
 Some(pa_front StA(S2::S1::pa_P(S(S n)))(repeat S3(q+2)++pa_write b::r))).
 rewrite csteps_add,pa_restore.
 replace(q+3)with(S(q+2))by lia.
 change(csteps pa_tm 6
 (pa_front StA(S2::S1::pa_P(S n))(S2::S3::(repeat S3(q+2)++pa_write b::r)))=
 Some(pa_front StA(S2::S1::pa_P(S(S n)))(repeat S3(q+2)++pa_write b::r))).
 rewrite pa_support;reflexivity.
Qed.
Theorem pa_increment : forall n q b r,
 csteps pa_tm(8*S n+4*q+24)
 (pa_front StA(S2::S1::pa_P(S n))
 (repeat S3(S q)++S2::pa_tag b::r))=
 Some(pa_front StA(S2::S1::pa_P(S(S n)))
 (repeat S3(q+2)++pa_write b::r)).
Proof.
 intros n q b r;replace(8*S n+4*q+24)with(S q+((2*(q+2)+3)+(8*S n+q+16)))by lia.
 rewrite csteps_add,pa_A3.
 replace(repeat S2(S q)++S2::S1::pa_P(S n))with
 (repeat S2(q+2)++S1::pa_P(S n)).
 2:{ replace(q+2)with(S(S q))by lia;cbn;rewrite pa_repeat_shift;reflexivity. }
 rewrite csteps_add,pa_erase.
 replace(S(q+2))with(q+3)by lia;apply pa_rebuild.
Qed.
Theorem pa_start : forall a n r,
 csteps pa_tm(a+8*S n+7)(pa_stage a(S n)r)=
 Some(pa_front StA(S2::S1::pa_P(S n))(S3::(repeat S2 a++S1::r))).
Proof.
 intros a n r;replace(a+8*S n+7)with(1+(a+(1+(8*S n+5))))by lia.
 unfold pa_stage;rewrite csteps_add.
 change(csteps pa_tm(a+(1+(8*S n+5)))
 (pa_back StB(repeat S2 a++S1::pa_P(S n))(S1::r))=
 Some(pa_front StA(S2::S1::pa_P(S n))(S3::(repeat S2 a++S1::r)))).
 rewrite csteps_add,pa_B2,csteps_add.
 change(csteps pa_tm(8*S n+5)
 (pa_back StB(pa_P(S n))(S3::(repeat S2 a++S1::r)))=
 Some(pa_front StA(S2::S1::pa_P(S n))(S3::(repeat S2 a++S1::r)))).
 apply pa_restore.
Qed.
Theorem pa_loop : forall n q k,
 csteps pa_tm(8*S n+4*q+24)(pa_G(S n)q(S(S k)))=
 Some(pa_G(S(S n))(S q)(S k)).
Proof.
 intros n q k;unfold pa_G.
 replace(S(S q))with(q+2)by lia.
 change(csteps pa_tm(8*S n+4*q+24)
 (pa_front StA(S2::S1::pa_P(S n))
 (repeat S3(S q)++S2::pa_tag false::(repeat S2 k++[S1])))=
 Some(pa_front StA(S2::S1::pa_P(S(S n)))
 (repeat S3(q+2)++pa_write false::(repeat S2 k++[S1])))).
 apply pa_increment.
Qed.
Theorem pa_finish : forall n q,
 csteps pa_tm(8*S n+5*q+27)(pa_G(S n)q 1)=
 Some(pa_stage(q+4)(S(S n))[]).
Proof.
 intros n q;replace(8*S n+5*q+27)with((8*S n+4*q+24)+(q+3))by lia.
 unfold pa_G;rewrite csteps_add.
 change(match csteps pa_tm(8*S n+4*q+24)
 (pa_front StA(S2::S1::pa_P(S n))
 (repeat S3(S q)++S2::pa_tag true::[]))with
 |Some cc=>csteps pa_tm(q+3)cc|None=>None end=
 Some(pa_stage(q+4)(S(S n))[])).
 rewrite pa_increment.
 change(csteps pa_tm(q+3)
 (pa_front StA(S2::S1::pa_P(S(S n)))(repeat S3(q+2)++[S3]))=
 Some(pa_stage(q+4)(S(S n))[])).
 replace(repeat S3(q+2)++[S3])with(repeat S3(q+3)++[]).
 2:{ replace(q+3)with(S(q+2))by lia;cbn;rewrite pa_repeat_shift;reflexivity. }
 rewrite pa_A3;unfold pa_stage,pa_front.
 replace(q+4)with(S(q+3))by lia;cbn.
 rewrite pa_repeat_shift;reflexivity.
Qed.
Fixpoint pa_drain_cost k p q:=match k with
 |0=>8*p+5*q+27
 |S k=>8*p+4*q+24+pa_drain_cost k(S p)(S q)end.
Lemma pa_drain_cost_formula : forall k p q,
 pa_drain_cost k p q=6*k*k+31*k+8*(k+1)*p+(4*k+5)*q+27.
Proof. induction k;intros p q;cbn[pa_drain_cost];[nia|rewrite IHk;nia]. Qed.
Theorem pa_drain : forall k n q,
 csteps pa_tm(pa_drain_cost k(S n)q)(pa_G(S n)q(S k))=
 Some(pa_stage(q+k+4)(S n+k+1)[]).
Proof.
 induction k;intros n q;cbn[pa_drain_cost].
 - replace(q+0+4)with(q+4)by lia.
   replace(S n+0+1)with(S(S n))by lia;apply pa_finish.
 - rewrite csteps_add,pa_loop,IHk.
   replace(S q+k+4)with(q+S k+4)by lia.
   replace(S(S n)+k+1)with(S n+S k+1)by lia;reflexivity.
Qed.
Definition pa_cost a b:=6*a*a+40*a+8*(a+2)*b+51.
Theorem pa_main_next : forall a b,
 csteps pa_tm(pa_cost a b)(pa_main a b)=Some(pa_main(a+3)(a+b+1)).
Proof.
 intros a b;replace(pa_cost a b)with((S a+8*S b+7)+pa_drain_cost a(S b)0).
 2:{ unfold pa_cost;rewrite pa_drain_cost_formula;nia. }
 unfold pa_main at 1;rewrite csteps_add,pa_start.
 change(csteps pa_tm(pa_drain_cost a(S b)0)(pa_G(S b)0(S a))=
 Some(pa_main(a+3)(a+b+1))).
 rewrite pa_drain;unfold pa_main.
 replace(0+a+4)with(S(a+3))by lia.
 replace(S b+a+1)with(S(a+b+1))by lia;reflexivity.
Qed.
Example pa_entry : csteps pa_tm 68 c0=Some(pa_main 3 1).
Proof. reflexivity. Qed.
Lemma pa_returns : forall N,exists t a b,N<=t /\csteps pa_tm t c0=Some(pa_main a b).
Proof.
 induction N as[|N IH].
 - exists 68,3,1;split;[lia|exact pa_entry].
 - destruct IH as(t&a&b&Ht&E);exists(t+pa_cost a b),(a+3),(a+b+1);split.
   + unfold pa_cost;nia.
   + rewrite csteps_add,E;apply pa_main_next.
Qed.
Theorem pa_nonhalt : NonHalt pa_tm.
Proof. apply ore_total_nonhalt;intros q h;destruct q,h;eexists;reflexivity. Qed.
Theorem pa_A_recurrent : forall N,exists t,N<=t /\VisitsAt pa_tm StA t.
Proof.
 intro N;destruct(pa_returns N)as(t&a&b&Ht&E).
 exists t;split;[exact Ht|];exists(lift(pa_main a b));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem pa_B_recurrent : forall N,exists t,N<=t /\VisitsAt pa_tm StB t.
Proof.
 intro N;destruct(pa_returns N)as(t&a&b&Ht&E).
 exists(t+1);split;[lia|];exists(lift(StB,(repeat S2 a++S1::pa_P(S b),S2,[S1])));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem pa_state_zero : QHBound 0 pa_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(pa_A_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(pa_B_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem pa_sound : NonHalt pa_tm /\QHBound 0 pa_tm.
Proof. split;[exact pa_nonhalt|exact pa_state_zero]. Qed.
Print Assumptions pa_sound.
