(** The all-token fallback distinguishes A0 resets from A1 escapes. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement CTape.
From BBB24Burn18CounterObligations Require Import CounterObligations.
From BBB24Burn24S056Counter Require Import Phase.
Import ListNotations.
Fixpoint sf_pairs(ts:list bool):nat := match ts with
 |[]=>0|b::ts=>(if b then 1 else 0)+sf_pairs ts end.
Fixpoint sf_stack(ts:list bool):list Sym := match ts with
 |[]=>[]|b::ts=>sf_stack ts++(if b then[S2;S3]else[S2])end.
Fixpoint sf_weight(w:list Sym):nat := match w with
 |[]=>0|h::w=>(match h with S3=>3|_=>1 end)+sf_weight w end.
Lemma sf_weight_app : forall a b,sf_weight(a++b)=sf_weight a+sf_weight b.
Proof. induction a;intro b;cbn;[reflexivity|rewrite IHa;lia]. Qed.
Lemma sf_stack_length : forall ts,length(sf_stack ts)=length(s56_in ts).
Proof. induction ts as[|b ts IH];[reflexivity|destruct b;cbn[sf_stack s56_in];rewrite app_length,IH;cbn;lia]. Qed.
Lemma sf_stack_weight : forall ts,sf_weight(sf_stack ts)=length(s56_in ts)+2*sf_pairs ts.
Proof.
 induction ts as[|b ts IH];[reflexivity|destruct b;cbn[sf_stack s56_in sf_pairs];rewrite sf_weight_app,IH;cbn[sf_weight length];lia].
Qed.
Lemma sf_stack_head : forall ts,0<length(s56_in ts)->exists w,sf_stack ts=S2::w.
Proof.
 induction ts as[|b ts IH];intro H;[cbn in H;lia|].
 destruct ts as[|c ts].
 - destruct b;[exists[S3]|exists[]];reflexivity.
 - destruct(IH)as(w&E);[destruct c;cbn;lia|].
   exists(w++(if b then[S2;S3]else[S2]));change(sf_stack(c::ts)++(if b then[S2;S3]else[S2])=S2::(w++(if b then[S2;S3]else[S2])));rewrite E;reflexivity.
Qed.
Lemma sf_stack_23 : forall ts,Forall(fun h=>h=S2 \/h=S3)(sf_stack ts).
Proof.
 induction ts as[|b ts IH];[constructor|].
 cbn[sf_stack];apply Forall_app;split;[exact IH|destruct b].
 - constructor;[left;reflexivity|constructor;[right;reflexivity|constructor]].
 - constructor;[left;reflexivity|constructor].
Qed.
Lemma sf_B_reduce : forall ts l r,
 csteps s56_tm(length(s56_in ts))(co_back StB(s56_in ts++l)r)=
 Some(co_back StB l(sf_stack ts++r)).
Proof.
 induction ts as[|b ts IH];intros l r;[reflexivity|destruct b].
 - cbn[s56_in length sf_stack];replace(S(S(length(s56_in ts))))with(2+length(s56_in ts))by lia.
   rewrite csteps_add.
   change(csteps s56_tm(length(s56_in ts))(co_back StB(s56_in ts++l)(S2::S3::r))=
   Some(co_back StB l((sf_stack ts++[S2;S3])++r))).
   rewrite IH,<-app_assoc;reflexivity.
 - cbn[s56_in length sf_stack].
   change(csteps s56_tm(length(s56_in ts))(co_back StB(s56_in ts++l)(S2::r))=
   Some(co_back StB l((sf_stack ts++[S2])++r))).
   rewrite IH,<-app_assoc;reflexivity.
Qed.
Lemma sf_B_sweep : forall w l r,Forall(fun h=>h=S2 \/h=S3)w->
 csteps s56_tm(sf_weight w)(co_front StB(S2::l)(w++r))=
 Some(co_front StB(repeat S2(length w)++S2::l)r).
Proof.
 induction w as[|h w IH];intros l r H;[reflexivity|].
 inversion H as[|? ? Hh Hw];subst;destruct Hh as[Hh|Hh];subst h.
 - cbn[sf_weight length app].
   change(csteps s56_tm(sf_weight w)(co_front StB(S2::S2::l)(w++r))=
   Some(co_front StB(S2::(repeat S2(length w)++S2::l))r)).
   rewrite IH by exact Hw;rewrite co_repeat_shift;reflexivity.
 - cbn[sf_weight length app].
   change(csteps s56_tm(3+sf_weight w)(co_front StB(S2::l)(S3::w++r))=
   Some(co_front StB(S2::(repeat S2(length w)++S2::l))r)).
   rewrite csteps_add.
   change(csteps s56_tm(sf_weight w)(co_front StB(S2::S2::l)(w++r))=
   Some(co_front StB(S2::(repeat S2(length w)++S2::l))r)).
   rewrite IH by exact Hw;rewrite co_repeat_shift;reflexivity.
Qed.
Lemma sf_B_stack : forall ts r,0<length(s56_in ts)->
 csteps s56_tm(sf_weight(sf_stack ts))(co_front StB[S3](sf_stack ts++r))=
 Some(co_front StB(repeat S2(length(s56_in ts))++[S3])r).
Proof.
 intros ts r H;destruct(sf_stack_head ts H)as(w&E).
 pose proof(sf_stack_23 ts)as Hw;rewrite E in Hw;inversion Hw as[|? ? _ Htail];subst.
 pose proof(sf_stack_length ts)as Hlen;rewrite E in Hlen;cbn[length]in Hlen.
 rewrite E;cbn[sf_weight app];rewrite csteps_add.
 change(csteps s56_tm(sf_weight w)(co_front StB[S2;S3](w++r))=
 Some(co_front StB(repeat S2(length(s56_in ts))++[S3])r)).
 rewrite sf_B_sweep by exact Htail;rewrite <-Hlen;cbn[repeat].
 rewrite co_repeat_shift;reflexivity.
Qed.
Theorem sf_fallback : forall ts,0<length(s56_in ts)->
 csteps s56_tm(2*length(s56_in ts)+2*sf_pairs ts+5)
 (StA,(s56_in ts,S0,[]))=Some(sf_G(length(s56_in ts)-1)).
Proof.
 intros ts H;replace(2*length(s56_in ts)+2*sf_pairs ts+5)with
 (1+(length(s56_in ts)+(1+(sf_weight(sf_stack ts)+3))))by(rewrite sf_stack_weight;lia).
 rewrite csteps_add.
 change(csteps s56_tm(length(s56_in ts)+(1+(sf_weight(sf_stack ts)+3)))
 (co_back StB(s56_in ts)[S1])=Some(sf_G(length(s56_in ts)-1))).
 pose proof(sf_B_reduce ts [] [S1])as Er;rewrite app_nil_r in Er.
 rewrite csteps_add,Er,csteps_add.
 change(csteps s56_tm(sf_weight(sf_stack ts)+3)(co_front StB[S3](sf_stack ts++[S1]))=
 Some(sf_G(length(s56_in ts)-1))).
 rewrite csteps_add,sf_B_stack by exact H.
 destruct(length(s56_in ts))as[|n]eqn:En;[lia|].
 cbn[repeat].
 change(csteps s56_tm 3(co_front StB(S2::(repeat S2 n++[S3]))[S1])=
 Some(sf_G(S n-1))).
 replace(S n-1)with n by lia;reflexivity.
Qed.
