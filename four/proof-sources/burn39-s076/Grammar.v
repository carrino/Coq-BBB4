(** A finite recursive grammar for the whole-word carry operation. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census TotalCompletion OneStateReach.
From BBB24Burn39S076 Require Import Core.
Import ListNotations.
Inductive s76_F:list Sym->list Sym->nat->list Sym->nat->Prop:=
 |F11:forall w,s76_F(S1::S0::S1::S0::w)(S1::S1::S1::S1::S0::w)0(S1::S1::S0::w)3
 |F12:forall w,s76_F(S1::S0::S1::S1::S0::w)(S1::S1::S1::S1::S1::S0::w)0(S1::S1::S1::S0::w)3
 |F51:forall w,s76_F(S1::S1::S1::S1::S1::S0::S1::S0::w)(S1::S0::S1::S0::S1::S1::S1::S1::S0::w)2(S1::S1::S0::w)11
 |Ft13:s76_F[S1;S0;S1;S1;S1](repeat S1 6)0(repeat S1 4)3
 |Ft16:s76_F(S1::S0::repeat S1 6)(repeat S1 9)0(repeat S1 7)3
 |Ft56:s76_F(S1::S1::S1::S1::S1::S0::repeat S1 6)(S1::S0::S1::S0::repeat S1 9)2(repeat S1 7)11
 |Ft3:s76_F(repeat S1 3)[S1;S0;S1;S1;S1]1[S1]7
 |Ft9:s76_F(repeat S1 9)(s76_V 4++[S1;S1;S1])4[S1]19
 |F2:forall w v a r c,s76_F w v a r c->
 s76_F(S1::S1::S0::w)(S1::S1::S0::v)0(S0::(s76_V a++S1::S1::r))(c+6*a+12)
 |F4:forall w v a r c,s76_F w v a r c->
 s76_F(S1::S1::S1::S1::S0::w)(S1::S0::S1::S1::S0::v)1(S0::(s76_V a++S1::S1::r))(c+6*a+16).
Theorem s76_F_word : forall w v a r c,s76_F w v a r c->v=s76_V a++S1::S1::r.
Proof. intros w v a r c H;induction H;try reflexivity;now rewrite IHs76_F. Qed.
Theorem s76_F_semantic : forall w v a r c,s76_F w v a r c->forall l,
 csteps s76_tm c(s76_front StB l w)=Some(s76_back StB l(s76_T a++S0::r)).
Proof.
 intros w v a r c H;induction H;intro l;try reflexivity.
 - replace(c+6*a+12)with(3+(c+(6*a+9)))by lia;rewrite csteps_add.
   change(csteps s76_tm(c+(6*a+9))(s76_front StB(S2::S2::S3::l)w)=
   Some(s76_back StB l(S0::S0::(s76_V a++S1::S1::r)))).
   rewrite csteps_add,IHs76_F,s76_Q_train;reflexivity.
 - replace(c+6*a+16)with(5+(c+((6*a+9)+2)))by lia;rewrite csteps_add.
   change(csteps s76_tm(c+((6*a+9)+2))(s76_front StB(S2::S2::S3::S2::S3::l)w)=
   Some(s76_back StB l(S2::S1::S0::S0::(s76_V a++S1::S1::r)))).
   rewrite csteps_add,IHs76_F,csteps_add,s76_Q_train;reflexivity.
Qed.
Inductive s76_tree:Set:=
 |G0:s76_tree|G1:s76_tree|G2:s76_tree|G3:s76_tree|G4:s76_tree|G5:s76_tree
 |W0:nat->s76_tree->s76_tree|W1:nat->s76_tree->s76_tree
 |W2:nat->s76_tree->s76_tree|W3:nat->s76_tree->s76_tree.
Fixpoint s76_word g:list Sym:=match g with
 |G0=>[S1;S0;S1;S0;S1;S0;S1;S1;S1]
 |G1=>[S1;S1;S1;S1;S0;S1;S0;S1;S1;S1]
 |G2=>S1::S0::S1::S1::S0::repeat S1 6
 |G3=>S1::S1::S1::S1::S1::S0::repeat S1 6
 |G4=>S1::S0::S1::S0::repeat S1 9
 |G5=>S1::S1::S1::S1::S0::repeat S1 9
 |W0 m g=>S1::S0::S1::S1::S0::S1::S0::(s76_P m++s76_word g)
 |W1 m g=>S1::S1::S1::S1::S1::S0::S1::S0::(s76_P m++s76_word g)
 |W2 m g=>S1::S0::S1::S0::S1::S1::S1::S1::S0::(s76_P m++s76_word g)
 |W3 m g=>S1::S1::S1::S1::S0::S1::S1::S1::S1::S0::(s76_P m++s76_word g)end.
Fixpoint s76_next g:=match g with
 |G0=>G1|G1=>G2|G2=>G3|G3=>G4|G4=>G5|G5=>W0 0 G0
 |W0 m g=>W1 m g|W1 m g=>W2 m g|W2 m g=>W3 m g|W3 m g=>W0(S m)(s76_next g)end.
Lemma s76_F_P : forall m w v,
 (exists a r c,s76_F w v a r c)->exists a r c,s76_F(s76_P m++w)(s76_P m++v)a r c.
Proof.
 induction m;intros w v H;[exact H|].
 destruct(IHm w v H)as(a&r&c&HF);eexists;eexists;eexists;apply F2;exact HF.
Qed.
Theorem s76_grammar_closed : forall g,exists a r c,s76_F(s76_word g)(s76_word(s76_next g))a r c.
Proof.
 induction g.
 - eexists;eexists;eexists;apply F11.
 - eexists;eexists;eexists;apply F4;apply Ft13.
 - eexists;eexists;eexists;apply F12.
 - eexists;eexists;eexists;apply Ft56.
 - eexists;eexists;eexists;apply F11.
 - eexists;eexists;eexists;apply F4;apply Ft9.
 - eexists;eexists;eexists;apply F12.
 - eexists;eexists;eexists;apply F51.
 - eexists;eexists;eexists;apply F11.
 - destruct(s76_F_P n _ _ IHg)as(a&r&c&HF).
   eexists;eexists;eexists;apply F4;apply F4;exact HF.
Qed.
Theorem s76_return : forall n g,exists d,0<d /\
 csteps s76_tm d(s76_main(S n)(s76_word g))=Some(s76_main(S(S n))(s76_word(s76_next g))).
Proof.
 intros n g;destruct(s76_grammar_closed g)as(a&r&c&HF).
 exists(12*S n+65+c+6*a);split;[lia|].
 eapply s76_main_from_normalizer;[exact(s76_F_semantic _ _ _ _ _ HF)|exact(s76_F_word _ _ _ _ _ HF)].
Qed.
Example s76_entry : csteps s76_tm 234 c0=Some(s76_main 1(s76_word G1)).
Proof. vm_compute;reflexivity. Qed.
Lemma s76_returns : forall N,exists t n g,N<=t /\csteps s76_tm t c0=Some(s76_main(S n)(s76_word g)).
Proof.
 induction N as[|N IH].
 - exists 234,0,G1;split;[lia|exact s76_entry].
 - destruct IH as(t&n&g&Ht&E);destruct(s76_return n g)as(d&Hd&Er).
   exists(t+d),(S n),(s76_next g);split;[lia|].
   rewrite csteps_add,E;exact Er.
Qed.
Theorem s76_nonhalt : NonHalt s76_tm.
Proof. apply ore_total_nonhalt;intros q h;destruct q,h;eexists;reflexivity. Qed.
Theorem s76_A_recurrent : forall N,exists t,N<=t /\VisitsAt s76_tm StA t.
Proof.
 intro N;destruct(s76_returns N)as(t&n&g&Ht&E).
 exists t;split;[exact Ht|];exists(lift(s76_main(S n)(s76_word g)));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem s76_B_recurrent : forall N,exists t,N<=t /\VisitsAt s76_tm StB t.
Proof.
 intro N;destruct(s76_returns N)as(t&n&g&Ht&E).
 exists(t+1);split;[lia|];exists(lift(StB,([],S0,S1::(s76_U++s76_P(S n)++s76_word g))));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem s76_state_zero : QHBound 0 s76_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(s76_A_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(s76_B_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem s76_sound : NonHalt s76_tm /\QHBound 0 s76_tm.
Proof. split;[exact s76_nonhalt|exact s76_state_zero]. Qed.
Print Assumptions s76_F_semantic.
Print Assumptions s76_grammar_closed.
Print Assumptions s76_return.
Print Assumptions s76_sound.
