(** Local macros and excluded synthetic seeds only. These do not classify
    either original blank orbit or register any census family. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement CTape.
Import ListNotations.
Definition co_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition co_back q l r:cconf := (q,(ctl l,chd l,r)).
Lemma co_repeat_shift : forall(x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Definition s56_tm : TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StB
 |StA,S2=>mkTrans S1 DR StA |StA,S3=>mkTrans S3 DR StA
 |StB,S0=>mkTrans S3 DR StB |StB,S1=>mkTrans S3 DL StA
 |StB,S2=>mkTrans S2 DR StB |StB,S3=>mkTrans S2 DL StB end).
Fixpoint s56_in(ts:list bool):list Sym := match ts with
 |[]=>[]|false::ts=>S3::s56_in ts|true::ts=>S1::S1::s56_in ts end.
Fixpoint s56_out(ts:list bool):list Sym := match ts with
 |[]=>[]|false::ts=>S1::s56_out ts|true::ts=>S3::S1::s56_out ts end.
Definition s56_stop x := match x with S2=>S1|_=>S3 end.
Theorem s56_local_carry : forall ts x l r,x=S2 \/ x=S3 ->
 csteps s56_tm(2*length(s56_in ts)+3)(co_back StB(s56_in ts++S1::x::l)r)=
 Some(co_front StA(s56_out ts++S3::s56_stop x::l)r).
Proof.
 induction ts as[|b ts IH];intros x l r Hx.
 - destruct Hx as[E|E];subst x;reflexivity.
 - destruct b.
   + change(csteps s56_tm(2*S(S(length(s56_in ts)))+3)
       (co_back StB(S1::S1::(s56_in ts++S1::x::l))r)=
      Some(co_front StA(S3::S1::(s56_out ts++S3::s56_stop x::l))r)).
     replace(2*S(S(length(s56_in ts)))+3)with(2+((2*length(s56_in ts)+3)+2))by lia.
     rewrite csteps_add.
     change(csteps s56_tm((2*length(s56_in ts)+3)+2)
       (co_back StB(s56_in ts++S1::x::l)(S2::S3::r))=
      Some(co_front StA(S3::S1::(s56_out ts++S3::s56_stop x::l))r)).
     rewrite csteps_add,IH by exact Hx;reflexivity.
   + change(csteps s56_tm(2*S(length(s56_in ts))+3)
       (co_back StB(S3::(s56_in ts++S1::x::l))r)=
      Some(co_front StA(S1::(s56_out ts++S3::s56_stop x::l))r)).
     replace(2*S(length(s56_in ts))+3)with(1+((2*length(s56_in ts)+3)+1))by lia.
     rewrite csteps_add.
     change(csteps s56_tm((2*length(s56_in ts)+3)+1)
       (co_back StB(s56_in ts++S1::x::l)(S2::r))=
      Some(co_front StA(S1::(s56_out ts++S3::s56_stop x::l))r)).
     rewrite csteps_add,IH by exact Hx;reflexivity.
Qed.
Theorem s56_B0_drift : forall n l,
 csteps s56_tm n(StB,(l,S0,[]))=Some(StB,(repeat S3 n++l,S0,[])).
Proof.
 induction n;intro l;[reflexivity|].
 change(csteps s56_tm n(StB,(S3::l,S0,[]))=Some(StB,(S3::(repeat S3 n++l),S0,[]))).
 rewrite IHn,co_repeat_shift;reflexivity.
Qed.
Theorem s56_B2_drift : forall n l,
 csteps s56_tm(S n)(StB,(l,S2,[]))=Some(StB,(repeat S3 n++S2::l,S0,[])).
Proof. intros n l;change(csteps s56_tm n(StB,(S2::l,S0,[]))=Some(StB,(repeat S3 n++S2::l,S0,[])));apply s56_B0_drift. Qed.
Example s56_actual_entry : csteps s56_tm 5 c0=Some(StA,([S3;S3],S0,[])).
Proof. reflexivity. Qed.
Example s56_unsafe_seed : csteps s56_tm 10(StA,([S1;S3],S0,[]))=Some(StB,([S2;S2;S3],S2,[])).
Proof. reflexivity. Qed.

Definition s59_tm : TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StB
 |StA,S2=>mkTrans S3 DR StA |StA,S3=>mkTrans S0 DR StA
 |StB,S0=>mkTrans S2 DR StB |StB,S1=>mkTrans S3 DR StA
 |StB,S2=>mkTrans S2 DL StB |StB,S3=>mkTrans S3 DL StA end).
Theorem s59_prefix33 : forall l r,
 csteps s59_tm 4(StA,(S3::S3::l,S0,r))=Some(StA,(S0::S0::l,S1,r)).
Proof. reflexivity. Qed.
Fixpoint s59_bits(ds:list bool):list Sym := match ds with
 |[]=>[]|b::ds=>(if b then S2 else S0)::s59_bits ds end.
Fixpoint s59_cost(ds:list bool):nat := match ds with
 |[]=>0|b::ds=>(if b then 1 else 3)+s59_cost ds end.
Theorem s59_left_sweep : forall ds l r,
 csteps s59_tm(s59_cost ds)(co_back StB(s59_bits ds++l)(S2::r))=
 Some(co_back StB l(repeat S2(length ds)++S2::r)).
Proof.
 induction ds as[|b ds IH];intros l r;[reflexivity|].
 destruct b.
 - change(csteps s59_tm(1+s59_cost ds)(co_back StB(S2::(s59_bits ds++l))(S2::r))=
    Some(co_back StB l(S2::(repeat S2(length ds)++S2::r)))).
   rewrite csteps_add.
   change(csteps s59_tm(s59_cost ds)(co_back StB(s59_bits ds++l)(S2::S2::r))=
    Some(co_back StB l(S2::(repeat S2(length ds)++S2::r)))).
   rewrite IH,co_repeat_shift;reflexivity.
 - change(csteps s59_tm(3+s59_cost ds)(co_back StB(S0::(s59_bits ds++l))(S2::r))=
    Some(co_back StB l(S2::(repeat S2(length ds)++S2::r)))).
   rewrite csteps_add.
   change(csteps s59_tm(s59_cost ds)(co_back StB(s59_bits ds++l)(S2::S2::r))=
    Some(co_back StB l(S2::(repeat S2(length ds)++S2::r)))).
   rewrite IH,co_repeat_shift;reflexivity.
Qed.
Definition s59_good s := s=S0 \/ s=S2.
Definition s59_guard l h r := Forall s59_good l /\(h=S2 \/(h=S0 /\chd r=S2)).
Lemma s59_guard_step : forall l h r,s59_guard l h r ->
 exists l' h' r',cstep s59_tm(StB,(l,h,r))=Some(StB,(l',h',r')) /\s59_guard l' h' r'.
Proof.
 intros l h r[Hl[Hh|[Hh Hr]]];subst h.
 - destruct l as[|x l].
   + exists[],S0,(S2::r);split;[reflexivity|];split;[constructor|right;auto].
   + inversion Hl as[|x' l' Hx Htail];subst.
     exists l,x,(S2::r);split;[reflexivity|];split;[exact Htail|].
     destruct Hx as[Hx|Hx];subst x;[right;auto|left;reflexivity].
 - destruct r as[|x r];[discriminate|];cbn[chd]in Hr;subst x.
   exists(S2::l),S2,r;split;[reflexivity|];split.
   + constructor;[right;reflexivity|exact Hl].
   + left;reflexivity.
Qed.
Theorem s59_guard_forever_B : forall n l h r,s59_guard l h r ->
 exists l' h' r',csteps s59_tm n(StB,(l,h,r))=Some(StB,(l',h',r')) /\s59_guard l' h' r'.
Proof.
 induction n;intros l h r Hg.
 - exists l,h,r;auto.
 - destruct(s59_guard_step l h r Hg)as(l1&h1&r1&E&Hg1).
   destruct(IHn l1 h1 r1 Hg1)as(l'&h'&r'&E'&Hg').
   exists l',h',r';split;[change(match cstep s59_tm(StB,(l,h,r))with Some c=>csteps s59_tm n c|None=>None end=Some(StB,(l',h',r')));now rewrite E|exact Hg'].
Qed.
Example s59_actual_entry : csteps s59_tm 18 c0=Some(StA,([S3;S3;S0;S3;S2],S0,[])).
Proof. reflexivity. Qed.
Example s59_unsafe_empty_context : csteps s59_tm 5(StA,([S3;S3],S0,[]))=Some(StB,([S0],S0,[S2])).
Proof. reflexivity. Qed.
Example s59_unsafe_ending_three : csteps s59_tm 17(StA,([S3;S3;S3;S0;S3;S3],S0,[]))=
 Some(StB,([S0],S0,[S2;S3;S2;S2;S2])).
Proof. reflexivity. Qed.
Example s59_empty_guard : s59_guard[S0]S0[S2].
Proof. split;[constructor;[left;reflexivity|constructor]|right;auto]. Qed.
Example s59_ending_guard : s59_guard[S0]S0[S2;S3;S2;S2;S2].
Proof. split;[constructor;[left;reflexivity|constructor]|right;auto]. Qed.
Print Assumptions s56_local_carry.
Print Assumptions s56_B2_drift.
Print Assumptions s59_prefix33.
Print Assumptions s59_left_sweep.
Print Assumptions s59_guard_forever_B.
