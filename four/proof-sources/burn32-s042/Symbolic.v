(** Affine run-block checker.  Every accepted scan is valid for every
    valuation of its two natural-number variables.  Unknown zero tests
    and unknown parities are rejected. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement CTape.
From BBB24Burn32S042 Require Import Programs.
Import ListNotations.
Record s42_exp:=s42_E{e0:nat;e1:nat;e2:nat}.
Definition s42_val x y e:=e0 e+e1 e*x+e2 e*y.
Definition s42_z:=s42_E 0 0 0.
Definition s42_one:=s42_E 1 0 0.
Definition s42_plus a b:=s42_E(e0 a+e0 b)(e1 a+e1 b)(e2 a+e2 b).
Definition s42_pred a:=s42_E(Nat.pred(e0 a))(e1 a)(e2 a).
Definition s42_zero a:=Nat.eqb(e0 a)0&&Nat.eqb(e1 a)0&&Nat.eqb(e2 a)0.
Definition s42_known_even a:=Nat.even(e1 a)&&Nat.even(e2 a).
Definition s42_runs:=list(Sym*s42_exp).
Fixpoint s42_word x y(rs:s42_runs):list Sym:=match rs with
 |[]=>[]|(h,n)::rs=>repeat h(s42_val x y n)++s42_word x y rs end.
Definition s42_push h n(rs:s42_runs):s42_runs:=
 if s42_zero n then rs else match rs with
 |(h',m)::rs'=>if sym_eqb h h' then(h,s42_plus n m)::rs' else(h,n)::rs
 |[]=>[(h,n)] end.
Definition s42_pop(rs:s42_runs):option(Sym*s42_runs):=match rs with
 |[]=>Some(S0,[])
 |(h,n)::rs'=>match e0 n with
   |0=>None
   |S _=>let m:=s42_pred n in Some(h,if s42_zero m then rs' else(h,m)::rs')end end.
Definition s42_take h(rs:s42_runs):s42_exp*s42_runs:=match rs with
 |(h',n)::rs'=>if sym_eqb h h' then(n,rs')else(s42_z,rs)
 |[] =>(s42_z,[])end.
Lemma s42_val_plus : forall x y a b,s42_val x y(s42_plus a b)=s42_val x y a+s42_val x y b.
Proof. intros;unfold s42_val,s42_plus;cbn;nia. Qed.
Lemma s42_zero_val : forall a,s42_zero a=true->forall x y,s42_val x y a=0.
Proof. intros[a b c]H x y;unfold s42_zero in H;cbn in H;repeat rewrite andb_true_iff in H.
 destruct H as[[H1 H2]H3];apply Nat.eqb_eq in H1;apply Nat.eqb_eq in H2;apply Nat.eqb_eq in H3;subst;reflexivity. Qed.
Lemma s42_parity : forall a,s42_known_even a=true->forall x y,Nat.even(s42_val x y a)=Nat.even(e0 a).
Proof.
 intros[a b c]H x y;unfold s42_known_even in H;cbn in H;apply andb_true_iff in H as[Hb Hc].
 unfold s42_val;cbn;rewrite !Nat.even_add,!Nat.even_mul,Hb,Hc;cbn.
 destruct(Nat.even a),(Nat.even x),(Nat.even y);reflexivity.
Qed.
Lemma s42_push_word : forall x y h n rs,s42_word x y(s42_push h n rs)=repeat h(s42_val x y n)++s42_word x y rs.
Proof.
 intros x y h n rs;unfold s42_push;destruct(s42_zero n)eqn:Z.
 - rewrite(s42_zero_val n Z x y);reflexivity.
 - destruct rs as[|[h' m]rs];[cbn;now rewrite app_nil_r|].
   destruct(sym_eqb h h')eqn:H;[|reflexivity].
   apply sym_eqb_spec in H;subst.
   change(repeat h'(s42_val x y(s42_plus n m))++s42_word x y rs=
    repeat h'(s42_val x y n)++(repeat h'(s42_val x y m)++s42_word x y rs)).
   rewrite s42_val_plus,repeat_app,app_assoc;reflexivity.
Qed.
Lemma s42_pop_word : forall rs h rs',s42_pop rs=Some(h,rs')->forall x y,
 chd(s42_word x y rs)=h /\ctl(s42_word x y rs)=s42_word x y rs'.
Proof.
 intros[|[a[b c d]]rs]h rs' H x y;[injection H as<- <-;split;reflexivity|].
 unfold s42_pop in H;cbn in H;destruct b as[|b];[discriminate|].
 destruct(s42_zero(s42_pred(s42_E(S b)c d)))eqn:Z;injection H as<- <-;
 cbn[s42_word s42_val s42_pred e0 e1 e2 repeat app chd ctl];split;try reflexivity.
 - pose proof(s42_zero_val _ Z x y)as E;cbn[s42_val s42_pred e0 e1 e2 Nat.pred]in E.
   cbn in E;change(ctl(repeat a(S(b+c*x+d*y))++s42_word x y rs)=s42_word x y rs);rewrite E;reflexivity.
Qed.
Lemma s42_take_word : forall h rs n rs',s42_take h rs=(n,rs')->forall x y,
 s42_word x y rs=repeat h(s42_val x y n)++s42_word x y rs'.
Proof.
 intros h[|[a m]rs]n rs' H x y;cbn[s42_take]in H.
 - injection H as<- <-;reflexivity.
 - destruct(sym_eqb h a)eqn:E;injection H as<- <-;[apply sym_eqb_spec in E;subst|];reflexivity.
Qed.
Record s42_cfg:=s42_C{sq:St;sh:Sym;sl:s42_runs;sr:s42_runs}.
Definition s42_den x y c:cconf:=(sq c,(s42_word x y(sl c),sh c,s42_word x y(sr c))).
Definition s42_move d w q c:option s42_cfg:=match d with
 |DL=>match s42_pop(sl c)with None=>None|Some(h,l)=>Some(s42_C q h l(s42_push w s42_one(sr c)))end
 |DR=>match s42_pop(sr c)with None=>None|Some(h,r)=>Some(s42_C q h(s42_push w s42_one(sl c))r)end end.
Definition s42_odd c:option s42_cfg:=
 let '(n,l):=s42_take(sh c)(sl c)in
 match s42_pop l with None=>None|Some(h,l')=>Some(s42_C StA h l'(s42_push S2(s42_plus s42_one n)(sr c)))end.
Definition s42_two c:option s42_cfg:=
 let '(n,r):=s42_take S2(sr c)in let m:=s42_plus s42_one n in
 if s42_known_even m then match s42_pop r with
 |None=>None|Some(h,r')=>Some(s42_C(if Nat.even(e0 m)then sq c else s42_flip(sq c))h(s42_push S3 m(sl c))r')end else None.
Definition s42_zero_right c:option s42_cfg:=
 let '(n,r):=s42_take S0(sr c)in
 match s42_pop r with None=>None|Some(h,r')=>Some(s42_C StB h(s42_push S0(s42_plus s42_one n)(sl c))r')end.
Definition s42_sstep c:option s42_cfg:=match sq c,sh c with
 |StA,S1|StA,S3=>s42_odd c
 |_,S2=>s42_two c
 |StB,S0=>s42_zero_right c
 |StA,S0=>s42_move DL S1 StB c
 |StB,S1=>s42_move DR S2 StA c
 |StB,S3=>s42_move DL S0 StA c end.
Fixpoint s42_run fuel c:=match fuel with
 |0=>Some c|S k=>match s42_sstep c with None=>None|Some c'=>s42_run k c' end end.

Lemma s42_move_sound : forall d w q c c',
 s42_tm(sq c)(sh c)=Some(mkTrans w d q)->s42_move d w q c=Some c'->forall x y,
 csteps s42_tm 1(s42_den x y c)=Some(s42_den x y c').
Proof.
 intros d w q[q0 h0 l r]c' Htm H x y;destruct d;
 cbn[s42_move sl sr]in H.
 - destruct(s42_pop l)as[[h l']|]eqn:P;[|discriminate];injection H as<-.
   destruct(s42_pop_word _ _ _ P x y)as[Hd Ht].
   unfold s42_den;cbn[sq sh sl sr];rewrite s42_push_word.
   change(cstep s42_tm(q0,(s42_word x y l,h0,s42_word x y r))=
    Some(q,(s42_word x y l',h,w::s42_word x y r))).
   cbn[cstep];change(s42_tm q0 h0=Some(mkTrans w DL q))in Htm;rewrite Htm.
   cbn[ctape_move t_next t_dir t_write];now rewrite Hd,Ht.
 - destruct(s42_pop r)as[[h r']|]eqn:P;[|discriminate];injection H as<-.
   destruct(s42_pop_word _ _ _ P x y)as[Hd Ht].
   unfold s42_den;cbn[sq sh sl sr];rewrite s42_push_word.
   change(cstep s42_tm(q0,(s42_word x y l,h0,s42_word x y r))=
    Some(q,(w::s42_word x y l,h,s42_word x y r'))).
   cbn[cstep];change(s42_tm q0 h0=Some(mkTrans w DR q))in Htm;rewrite Htm.
   cbn[ctape_move t_next t_dir t_write];now rewrite Hd,Ht.
Qed.
Lemma s42_odd_sound : forall c c',sq c=StA->sh c=S1\/sh c=S3->
 s42_odd c=Some c'->forall x y,exists k,1<=k /\
 csteps s42_tm k(s42_den x y c)=Some(s42_den x y c').
Proof.
 intros[q h l r]c' Hq Hh H x y;cbn[sq sh]in Hq,Hh;subst q.
 unfold s42_odd in H;cbn[sh sl sr]in H.
 destruct(s42_take h l)as[n l']eqn:T.
 destruct(s42_pop l')as[h_l|]eqn:P;[destruct h_l as[h' l'']|discriminate].
 injection H as<-.
 pose proof(s42_take_word _ _ _ _ T x y)as W.
 destruct(s42_pop_word _ _ _ P x y)as[Hd Ht].
 exists(S(s42_val x y n));split;[lia|].
 unfold s42_den;cbn[sq sh sl sr];rewrite s42_push_word,s42_val_plus.
 change(csteps s42_tm(S(s42_val x y n))(StA,(s42_word x y l,h,s42_word x y r))=
  Some(StA,(s42_word x y l'',h',repeat S2(S(s42_val x y n))++s42_word x y r))).
 rewrite W;pose proof(s42_A_odd h Hh(S(s42_val x y n))(s42_word x y l')(s42_word x y r))as A.
 cbn[repeat app]in A;unfold s42_back in A;cbn[chd ctl]in A;now rewrite Hd,Ht in A.
Qed.
Lemma s42_two_sound : forall c c',sh c=S2->s42_two c=Some c'->forall x y,
 exists k,1<=k /\csteps s42_tm k(s42_den x y c)=Some(s42_den x y c').
Proof.
 intros[q h l r]c' Hh H x y;cbn[sh]in Hh;subst h.
 unfold s42_two in H;cbn[sq sl sr]in H.
 destruct(s42_take S2 r)as[n r']eqn:T.
 destruct(s42_known_even(s42_plus s42_one n))eqn:K;[|discriminate].
 destruct(s42_pop r')as[[h' r'']|]eqn:P;[|discriminate];injection H as<-.
 pose proof(s42_take_word _ _ _ _ T x y)as W.
 destruct(s42_pop_word _ _ _ P x y)as[Hd Ht].
 pose proof(s42_parity _ K x y)as E;rewrite s42_val_plus in E.
 change(Nat.even(S(s42_val x y n))=Nat.even(e0(s42_plus s42_one n)))in E.
 exists(S(s42_val x y n));split;[lia|].
 unfold s42_den;cbn[sq sh sl sr];rewrite s42_push_word,s42_val_plus.
 change(csteps s42_tm(S(s42_val x y n))(q,(s42_word x y l,S2,s42_word x y r))=
  Some((if Nat.even(e0(s42_plus s42_one n))then q else s42_flip q),
   (repeat S3(S(s42_val x y n))++s42_word x y l,h',s42_word x y r''))).
 rewrite W;pose proof(s42_twos(S(s42_val x y n))q(s42_word x y l)(s42_word x y r'))as A.
 cbn[repeat app]in A;unfold s42_front in A;cbn[chd ctl]in A;now rewrite Hd,Ht,E in A.
Qed.
Lemma s42_zero_sound : forall c c',sq c=StB->sh c=S0->s42_zero_right c=Some c'->forall x y,
 exists k,1<=k /\csteps s42_tm k(s42_den x y c)=Some(s42_den x y c').
Proof.
 intros[q h l r]c' Hq Hh H x y;cbn[sq]in Hq;cbn[sh]in Hh;subst q h.
 unfold s42_zero_right in H;cbn[sl sr]in H.
 destruct(s42_take S0 r)as[n r']eqn:T.
 destruct(s42_pop r')as[[h' r'']|]eqn:P;[|discriminate];injection H as<-.
 pose proof(s42_take_word _ _ _ _ T x y)as W.
 destruct(s42_pop_word _ _ _ P x y)as[Hd Ht].
 exists(S(s42_val x y n));split;[lia|].
 unfold s42_den;cbn[sq sh sl sr];rewrite s42_push_word,s42_val_plus.
 change(csteps s42_tm(S(s42_val x y n))(StB,(s42_word x y l,S0,s42_word x y r))=
  Some(StB,(repeat S0(S(s42_val x y n))++s42_word x y l,h',s42_word x y r''))).
 rewrite W;pose proof(s42_B_zeros(S(s42_val x y n))(s42_word x y l)(s42_word x y r'))as A.
 cbn[repeat app]in A;unfold s42_front in A;cbn[chd ctl]in A;now rewrite Hd,Ht in A.
Qed.
Theorem s42_sstep_sound : forall c c',s42_sstep c=Some c'->forall x y,
 exists k,1<=k /\csteps s42_tm k(s42_den x y c)=Some(s42_den x y c').
Proof.
 intros[q h l r]c' H x y;destruct q,h;cbn[s42_sstep sq sh]in H.
 - exists 1;split;[lia|];eapply s42_move_sound;[reflexivity|exact H].
 - eapply s42_odd_sound;[reflexivity|now left|exact H].
 - eapply s42_two_sound;[reflexivity|exact H].
 - eapply s42_odd_sound;[reflexivity|now right|exact H].
 - eapply s42_zero_sound;[reflexivity|reflexivity|exact H].
 - exists 1;split;[lia|];eapply s42_move_sound;[reflexivity|exact H].
 - eapply s42_two_sound;[reflexivity|exact H].
 - exists 1;split;[lia|];eapply s42_move_sound;[reflexivity|exact H].
Qed.
Theorem s42_run_sound : forall fuel c c',s42_run fuel c=Some c'->forall x y,
 exists k,fuel<=k /\csteps s42_tm k(s42_den x y c)=Some(s42_den x y c').
Proof.
 induction fuel;intros c c' H x y;cbn[s42_run]in H.
 - injection H as<-;exists 0;split;[lia|reflexivity].
 - destruct(s42_sstep c)as[d|]eqn:E;[|discriminate].
   destruct(s42_sstep_sound _ _ E x y)as(a&Ha&Ea).
   destruct(IHfuel _ _ H x y)as(b&Hb&Eb).
   exists(a+b);split;[lia|];now rewrite csteps_add,Ea.
Qed.
Print Assumptions s42_run_sound.

(** Substitution preserves the denotation for every valuation. *)
Definition s42_sub_exp a b e:=s42_E
 (e0 e+e1 e*e0 a+e2 e*e0 b)
 (e1 e*e1 a+e2 e*e1 b)(e1 e*e2 a+e2 e*e2 b).
Definition s42_sub_runs a b (rs:s42_runs):=map(fun hn=>(fst hn,s42_sub_exp a b(snd hn)))rs.
Definition s42_sub a b c:=s42_C(sq c)(sh c)(s42_sub_runs a b(sl c))(s42_sub_runs a b(sr c)).
Lemma s42_sub_val : forall x y a b e,
 s42_val x y(s42_sub_exp a b e)=s42_val(s42_val x y a)(s42_val x y b)e.
Proof. intros x y[a0 a1 a2][b0 b1 b2][c0 c1 c2];unfold s42_val,s42_sub_exp;cbn;nia. Qed.
Lemma s42_sub_word : forall rs x y a b,
 s42_word x y(s42_sub_runs a b rs)=s42_word(s42_val x y a)(s42_val x y b)rs.
Proof. induction rs as[|[h n]rs IH];intros;cbn[s42_sub_runs map s42_word fst snd];[reflexivity|].
 unfold s42_sub_runs in IH;rewrite s42_sub_val,IH;reflexivity. Qed.
Lemma s42_sub_den : forall c x y a b,
 s42_den x y(s42_sub a b c)=s42_den(s42_val x y a)(s42_val x y b)c.
Proof. intros[q h l r]x y a b;unfold s42_den,s42_sub;cbn[sq sh sl sr];now rewrite !s42_sub_word. Qed.
