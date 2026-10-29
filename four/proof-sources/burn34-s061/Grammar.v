(** Exact frozen S061: mutually recursive binary word normalizers. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census TotalCompletion OneStateReach.
Import ListNotations.
Definition s61_tm:TM:=fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StB
 |StA,S2=>mkTrans S3 DR StA |StA,S3=>mkTrans S1 DR StA
 |StB,S0=>mkTrans S3 DR StB |StB,S1=>mkTrans S2 DL StA
 |StB,S2=>mkTrans S1 DR StA |StB,S3=>mkTrans S3 DL StB end).
Definition s61_front q l r:cconf:=(q,(l,chd r,ctl r)).
Definition s61_back q l r:cconf:=(q,(ctl l,chd l,r)).
Inductive s61_even:Set:=
 |E0:s61_even |E1:s61_even |E2:s61_odd->s61_even
 |E3:s61_even->s61_even |E4:s61_even->s61_even |E5:s61_odd->s61_even
with s61_odd:Set:=
 |O0:s61_odd |O1:s61_odd |O2:s61_even->s61_odd
 |O3:s61_even->s61_odd |O4:s61_odd->s61_odd |O5:s61_odd->s61_odd.
Scheme s61_even_ind':=Induction for s61_even Sort Prop
 with s61_odd_ind':=Induction for s61_odd Sort Prop.
Combined Scheme s61_grammar_ind from s61_even_ind',s61_odd_ind'.
Fixpoint s61_ew(e:s61_even):list Sym:=match e with
 |E0=>[S1;S3;S1] |E1=>[S1;S1;S1;S3]
 |E2 o=>S1::S1::S1::S1::S3::s61_ow o
 |E3 e=>S1::S3::S3::S3::S1::s61_ne e
 |E4 e=>S1::S1::S1::S3::S1::s61_ne e
 |E5 o=>S1::S3::S3::S1::S3::s61_ow o end
with s61_ow(o:s61_odd):list Sym:=match o with
 |O0=>[S1] |O1=>[S1;S3;S1;S3]
 |O2 e=>S1::S1::S1::S1::S3::s61_ew e
 |O3 e=>S1::S3::S1::S3::S1::s61_ne e
 |O4 o=>S1::S1::S1::S3::S3::s61_ow o
 |O5 o=>S1::S3::S1::S1::S3::s61_ow o end
with s61_ne(e:s61_even):list Sym:=match e with
 |E0=>[S3;S1;S1] |E1=>[S3;S3;S3;S1]
 |E2 o=>S3::S3::S3::S3::S1::s61_no o
 |E3 e=>S3::S1::S3::S3::S1::s61_ne e
 |E4 e=>S3::S3::S3::S1::S1::s61_ne e
 |E5 o=>S3::S1::S3::S1::S3::s61_ow o end
with s61_no(o:s61_odd):list Sym:=match o with
 |O0=>[S3;S3;S1] |O1=>[S3;S1;S1;S3]
 |O2 e=>S3::S3::S3::S3::S1::s61_ne e
 |O3 e=>S3::S1::S1::S3::S1::s61_ne e
 |O4 o=>S3::S3::S3::S1::S3::s61_ow o
 |O5 o=>S3::S1::S1::S1::S3::s61_ow o end.
Fixpoint s61_ec e:=match e with E0=>3|E1=>7|E2 o=>10+s61_oc o|E3 _=>3|E4 _=>7|E5 _=>3 end
with s61_oc o:=match o with O0=>7|O1=>3|O2 e=>10+s61_ec e|O3 _=>3|O4 _=>7|O5 _=>3 end.
Definition s61_on o:=match o with O0=>E0|O1=>E1|O2 e=>E3 e|O3 e=>E4 e|O4 o=>E5 o|O5 o=>E2 o end.
Fixpoint s61_en e:=match e with E0=>O1|E1=>O4 O0|E2 o=>O2(s61_on o)|E3 e=>O3 e|E4 e=>O4(s61_en e)|E5 o=>O5 o end.
Fixpoint s61_dc e:=match e with E0=>7|E1=>13|E2 _=>11|E3 _=>5|E4 e=>10+s61_dc e|E5 _=>5 end.
Lemma s61_ne_head : forall e,s61_ne e=S3::ctl(s61_ne e).
Proof. destruct e;reflexivity. Qed.
Lemma s61_no_head : forall o,s61_no o=S3::ctl(s61_no o).
Proof. destruct o;reflexivity. Qed.
Lemma s61_on_word : forall o,s61_ew(s61_on o)=S1::ctl(s61_no o).
Proof. destruct o;reflexivity. Qed.
Lemma s61_normalizer_wrap : forall w v c,
 (forall r,csteps s61_tm c(s61_back StB w r)=Some(s61_front StA v r))->
 forall r,csteps s61_tm(10+c)(s61_back StB(S1::S1::S1::S1::S3::w)r)=
 Some(s61_front StA(S3::S3::S3::S3::S1::v)r).
Proof.
 intros w v c H r;replace(10+c)with(5+(c+5))by lia;rewrite csteps_add.
 change(csteps s61_tm(c+5)(s61_back StB w(S3::S2::S2::S2::S2::r))=
 Some(s61_front StA(S3::S3::S3::S3::S1::v)r)).
 rewrite csteps_add,H;reflexivity.
Qed.
Theorem s61_normalizers :
 (forall e r,csteps s61_tm(s61_ec e)(s61_back StB(s61_ew e)r)=Some(s61_front StA(s61_ne e)r))/\
 (forall o r,csteps s61_tm(s61_oc o)(s61_back StB(s61_ow o)r)=Some(s61_front StA(s61_no o)r)).
Proof.
 apply s61_grammar_ind;intros;try reflexivity.
 - apply s61_normalizer_wrap;exact H.
 - apply s61_normalizer_wrap;exact H.
Qed.
Lemma s61_E_normalizer : forall e r,
 csteps s61_tm(s61_ec e)(s61_back StB(s61_ew e)r)=Some(s61_front StA(s61_ne e)r).
Proof. exact(proj1 s61_normalizers). Qed.
Lemma s61_O_normalizer : forall o r,
 csteps s61_tm(s61_oc o)(s61_back StB(s61_ow o)r)=Some(s61_front StA(s61_no o)r).
Proof. exact(proj2 s61_normalizers). Qed.
Lemma s61_313 : forall l r,
 csteps s61_tm 5(s61_back StB(S3::S1::S3::l)r)=Some(s61_front StA(S1::S3::S1::l)r).
Proof. reflexivity. Qed.
Theorem s61_double_normalizer : forall e r,
 csteps s61_tm(s61_dc e)(s61_back StB(s61_ne e)r)=Some(s61_front StA(s61_ow(s61_en e))r).
Proof.
 induction e;intro r.
 - reflexivity.
 - reflexivity.
 - cbn[s61_ne s61_en s61_dc s61_ow].
   rewrite(s61_no_head s);change(csteps s61_tm 11(s61_back StB(S3::S3::S3::S3::S1::S3::ctl(s61_no s))r)=
   Some(s61_front StA(S1::S1::S1::S1::S3::s61_ew(s61_on s))r)).
   rewrite s61_on_word;reflexivity.
 - change(csteps s61_tm 5(s61_back StB(S3::S1::S3::(S3::S1::s61_ne e))r)=
   Some(s61_front StA(S1::S3::S1::S3::S1::s61_ne e)r));apply s61_313.
 - cbn[s61_dc];replace(10+s61_dc e)with(5+(s61_dc e+5))by lia.
   rewrite csteps_add.
   change(csteps s61_tm(s61_dc e+5)(s61_back StB(s61_ne e)(S2::S2::S3::S3::S3::r))=
   Some(s61_front StA(S1::S1::S1::S3::S3::s61_ow(s61_en e))r)).
   rewrite csteps_add,IHe;reflexivity.
 - change(csteps s61_tm 5(s61_back StB(S3::S1::S3::(S1::S3::s61_ow s))r)=
   Some(s61_front StA(S1::S3::S1::S1::S3::s61_ow s)r));apply s61_313.
Qed.
Lemma s61_repeat_shift : forall (s:Sym) n (r:list Sym),repeat s n++s::r=s::(repeat s n++r).
Proof. intros s n;induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma s61_L3 : forall n l r,
 csteps s61_tm n(s61_back StB(repeat S3 n++l)r)=Some(s61_back StB l(repeat S3 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 change(csteps s61_tm(S n)(s61_back StB(S3::(repeat S3 n++l))r)=Some(s61_back StB l(S3::(repeat S3 n++r)))).
 change(csteps s61_tm n(s61_back StB(repeat S3 n++l)(S3::r))=Some(s61_back StB l(S3::(repeat S3 n++r)))).
 rewrite IHn,s61_repeat_shift;reflexivity.
Qed.
Lemma s61_R3 : forall n l r,
 csteps s61_tm n(s61_front StA l(repeat S3 n++r))=Some(s61_front StA(repeat S1 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 change(csteps s61_tm(S n)(s61_front StA l(S3::(repeat S3 n++r)))=Some(s61_front StA(S1::(repeat S1 n++l))r)).
 change(csteps s61_tm n(s61_front StA(S1::l)(repeat S3 n++r))=Some(s61_front StA(S1::(repeat S1 n++l))r)).
 rewrite IHn,s61_repeat_shift;reflexivity.
Qed.
Lemma s61_R2 : forall n l r,
 csteps s61_tm n(s61_front StA l(repeat S2 n++r))=Some(s61_front StA(repeat S3 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 change(csteps s61_tm(S n)(s61_front StA l(S2::(repeat S2 n++r)))=Some(s61_front StA(S3::(repeat S3 n++l))r)).
 change(csteps s61_tm n(s61_front StA(S3::l)(repeat S2 n++r))=Some(s61_front StA(S3::(repeat S3 n++l))r)).
 rewrite IHn,s61_repeat_shift;reflexivity.
Qed.
Lemma s61_L11 : forall l r,
 csteps s61_tm 2(s61_back StA(S1::S1::l)r)=Some(s61_back StA l(S2::S2::r)).
Proof. reflexivity. Qed.
Lemma s61_L1_even : forall n l r,
 csteps s61_tm(2*n)(s61_back StA(repeat S1(2*n)++l)r)=Some(s61_back StA l(repeat S2(2*n)++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(2*S n)with(S(S(2*n)))by lia;cbn[repeat app].
 replace(S(S(2*n)))with(2+2*n)at 1 by lia;rewrite csteps_add.
 change(match csteps s61_tm 2(s61_back StA(S1::S1::(repeat S1(2*n)++l))r)with
 |Some cc=>csteps s61_tm(2*n)cc|None=>None end=Some(s61_back StA l(S2::S2::(repeat S2(2*n)++r)))).
 rewrite s61_L11,IHn,!s61_repeat_shift;reflexivity.
Qed.
Lemma s61_L1_odd : forall n l r,
 csteps s61_tm(2*n+1)(s61_back StA(repeat S1(2*n+1)++l)r)=Some(s61_back StB l(repeat S2(2*n+1)++r)).
Proof.
 intros n l r.
 assert(E:repeat S1(2*n+1)++l=repeat S1(2*n)++S1::l).
 { replace(2*n+1)with(S(2*n))by lia;cbn[repeat app];rewrite s61_repeat_shift;reflexivity. }
 rewrite E,csteps_add,s61_L1_even.
 change(Some(s61_back StB l(S2::(repeat S2(2*n)++r)))=Some(s61_back StB l(repeat S2(2*n+1)++r))).
 replace(2*n+1)with(S(2*n))by lia;reflexivity.
Qed.
Definition s61_C k w:cconf:=(StA,(repeat S3 k++w,S0,[])).
Lemma s61_marker : forall k v,
 s61_front StA(repeat S1 k++v)[S1]=s61_back StA(repeat S1(S k)++v)[].
Proof. reflexivity. Qed.
Lemma s61_turn : forall n l r,
 csteps s61_tm(1+n)(s61_back StA(S3::l)(repeat S2 n++r))=
 Some(s61_front StA(repeat S3 n++S1::l)r).
Proof.
 intros n l r;rewrite csteps_add.
 change(csteps s61_tm n(s61_front StA(S1::l)(repeat S2 n++r))=Some(s61_front StA(repeat S3 n++S1::l)r)).
 apply s61_R2.
Qed.
Theorem s61_odd_return_generic : forall j w v c,
 (forall r,csteps s61_tm c(s61_back StB w r)=Some(s61_front StA v r))->
 v=S3::ctl v ->
 csteps s61_tm(4*(2*j+1)+c+4)(s61_C(2*j+1)w)=Some(s61_C(2*j+2)(S1::ctl v)).
Proof.
 intros j w v c H Hv;set(k:=2*j+1).
 replace(4*k+c+4)with(1+(k+(c+(k+((k+1)+(1+(k+1)))))))by(unfold k;lia).
 rewrite csteps_add.
 change(csteps s61_tm(k+(c+(k+((k+1)+(1+(k+1))))))(s61_back StB(repeat S3 k++w)[S1])=
 Some(s61_C(2*j+2)(S1::ctl v))).
 rewrite csteps_add,s61_L3,csteps_add,H,csteps_add,s61_R3,s61_marker.
 replace(S k)with(2*(j+1))by(unfold k;lia).
 replace(k+1)with(2*(j+1))at 1 by(unfold k;lia).
 rewrite csteps_add,s61_L1_even.
 replace(2*(j+1))with(k+1)by(unfold k;lia).
 rewrite Hv at 1;rewrite s61_turn.
 replace(2*j+2)with(k+1)by(unfold k;lia);reflexivity.
Qed.
Theorem s61_even_return_generic : forall j w v z c d,
 (forall r,csteps s61_tm c(s61_back StB w r)=Some(s61_front StA v r))->
 (forall r,csteps s61_tm d(s61_back StB v r)=Some(s61_front StA z r))->
 csteps s61_tm(4*(2*j+2)+c+d+3)(s61_C(2*j+2)w)=Some(s61_C(2*j+3)z).
Proof.
 intros j w v z c d H Hd;set(k:=2*j+2).
 replace(4*k+c+d+3)with(1+(k+(c+(k+((k+1)+(d+(k+1)))))))by(unfold k;lia).
 rewrite csteps_add.
 change(csteps s61_tm(k+(c+(k+((k+1)+(d+(k+1))))))(s61_back StB(repeat S3 k++w)[S1])=
 Some(s61_C(2*j+3)z)).
 rewrite csteps_add,s61_L3,csteps_add,H,csteps_add,s61_R3,s61_marker.
 replace(S k)with(2*(j+1)+1)by(unfold k;lia).
 replace(k+1)with(2*(j+1)+1)at 1 by(unfold k;lia).
 rewrite csteps_add,s61_L1_odd,csteps_add,Hd.
 replace(2*(j+1)+1)with(k+1)by(unfold k;lia);rewrite s61_R2.
 replace(2*j+3)with(k+1)by(unfold k;lia);reflexivity.
Qed.
Definition s61_odd_cost j o:=4*(2*j+1)+s61_oc o+4.
Definition s61_even_cost j e:=4*(2*j+2)+s61_ec e+s61_dc e+3.
Definition s61_main_O j o:=s61_C(2*j+1)(s61_ow o).
Definition s61_main_E j e:=s61_C(2*j+2)(s61_ew e).
Theorem s61_odd_return : forall j o,
 csteps s61_tm(s61_odd_cost j o)(s61_main_O j o)=Some(s61_main_E j(s61_on o)).
Proof.
 intros j o;unfold s61_odd_cost,s61_main_O,s61_main_E;rewrite s61_on_word.
 eapply s61_odd_return_generic;[apply s61_O_normalizer|apply s61_no_head].
Qed.
Theorem s61_even_return : forall j e,
 csteps s61_tm(s61_even_cost j e)(s61_main_E j e)=Some(s61_main_O(S j)(s61_en e)).
Proof.
 intros j e;unfold s61_even_cost,s61_main_O,s61_main_E.
 replace(2*S j+1)with(2*j+3)by lia.
 eapply s61_even_return_generic;[apply s61_E_normalizer|apply s61_double_normalizer].
Qed.
Definition s61_cost j o:=s61_odd_cost j o+s61_even_cost j(s61_on o).
Theorem s61_return : forall j o,
 csteps s61_tm(s61_cost j o)(s61_main_O j o)=Some(s61_main_O(S j)(s61_en(s61_on o))).
Proof. intros j o;unfold s61_cost;rewrite csteps_add,s61_odd_return;apply s61_even_return. Qed.
Example s61_entry : csteps s61_tm 5 c0=Some(s61_main_O 0 O0).
Proof. reflexivity. Qed.
Lemma s61_returns : forall N,exists t j o,N<=t /\csteps s61_tm t c0=Some(s61_main_O j o).
Proof.
 induction N as[|N IH].
 - exists 5,0,O0;split;[lia|exact s61_entry].
 - destruct IH as(t&j&o&Ht&E);exists(t+s61_cost j o),(S j),(s61_en(s61_on o));split.
   + unfold s61_cost,s61_odd_cost,s61_even_cost;lia.
   + rewrite csteps_add,E;apply s61_return.
Qed.
Theorem s61_nonhalt : NonHalt s61_tm.
Proof. apply ore_total_nonhalt;intros q h;destruct q,h;eexists;reflexivity. Qed.
Theorem s61_A_recurrent : forall N,exists t,N<=t /\VisitsAt s61_tm StA t.
Proof.
 intro N;destruct(s61_returns N)as(t&j&o&Ht&E).
 exists t;split;[exact Ht|];exists(lift(s61_main_O j o));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem s61_B_recurrent : forall N,exists t,N<=t /\VisitsAt s61_tm StB t.
Proof.
 intro N;destruct(s61_returns N)as(t&j&o&Ht&E).
 exists(t+1);split;[lia|];exists(lift(s61_back StB(repeat S3(2*j+1)++s61_ow o)[S1]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem s61_state_zero : QHBound 0 s61_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(s61_A_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(s61_B_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem s61_sound : NonHalt s61_tm /\QHBound 0 s61_tm.
Proof. split;[exact s61_nonhalt|exact s61_state_zero]. Qed.
Print Assumptions s61_normalizers.
Print Assumptions s61_double_normalizer.
Print Assumptions s61_return.
Print Assumptions s61_sound.
