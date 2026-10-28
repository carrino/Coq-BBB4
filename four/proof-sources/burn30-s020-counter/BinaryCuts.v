(** A closed binary-token cut grammar for S020. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census OneStateReach TotalCompletion.
Import ListNotations.
Definition s20_tm : TM := fun q h => Some (match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S0 DR StB
 |StA,S2=>mkTrans S1 DL StA |StA,S3=>mkTrans S3 DR StA
 |StB,S0=>mkTrans S1 DR StB |StB,S1=>mkTrans S3 DL StA
 |StB,S2=>mkTrans S2 DL StB |StB,S3=>mkTrans S2 DR StA end).
Definition s20_at q l h r : cconf := (q,(l,h,r)).
Definition s20_P := [S1;S3;S1;S2].
Definition s20_Q := [S2;S3;S2;S0].
Definition s20_R := [S2;S1;S3;S1].
Definition s20_D := [S2;S0;S2;S3].
Definition s20_K := [S3;S2;S0;S2].
Definition s20_Z := [S1;S1;S1;S1].
Definition s20_O := [S3;S2;S1;S3].
Definition s20_E := [S1;S3;S2;S1].
Fixpoint s20_pow (w:list Sym) n := match n with 0=>[]|S n=>w++s20_pow w n end.
Definition s20_G m := [S3;S2;S2]++s20_pow s20_P m++[S1;S3;S1;S1].
Definition s20_cut n r := s20_at StA [] S0
 ([S3;S2;S2]++s20_pow s20_P n++[S1;S1;S1]++r).
Definition s20_mid n r := s20_at StA [] S0
 ([S3;S2;S2]++s20_pow s20_P n++[S1;S3;S1;S1;S3]++r).
Definition s20_carry l r := s20_at StA (S3::l) S1 (S1::S3::r).

Lemma s20_entry : forall r, csteps s20_tm 7
 (s20_at StA [] S0 ([S3;S2;S2]++r))=
 Some(s20_at StA [S2;S0] S3 ([S1;S2]++r)).
Proof. reflexivity. Qed.
Lemma s20_forward_one : forall l r,csteps s20_tm 16
 (s20_at StA l S3 ([S1;S2]++s20_P++r))=
 Some(s20_at StA (s20_D++l) S3 ([S1;S2]++r)).
Proof. reflexivity. Qed.
Lemma s20_backward_one : forall l r,csteps s20_tm 16
 (s20_at StA ([S2;S0;S3;S2;S0]++s20_Q++l) S2 r)=
 Some(s20_at StA ([S2;S0;S3;S2;S0]++l) S2 (s20_R++r)).
Proof. reflexivity. Qed.
Lemma s20_blank_backward_one : forall l r,csteps s20_tm 6
 (s20_at StA (s20_Q++l) S0 ([S1;S1]++r))=
 Some(s20_at StA l S0 ([S1;S1]++s20_Z++r)).
Proof. reflexivity. Qed.
Lemma s20_first_terminal : forall l r,csteps s20_tm 27
 (s20_at StA ([S2;S0]++l) S3 ([S1;S2;S1;S1;S1]++r))=
 Some(s20_at StA ([S2;S0;S3;S2;S0]++l) S2 ([S1;S3]++r)).
Proof. reflexivity. Qed.
Lemma s20_finish : forall r,csteps s20_tm 12
 (s20_at StA [S2;S0;S3;S2;S0] S2 r)=
 Some(s20_at StA [] S0 ([S3;S2;S2;S1;S3;S1]++r)).
Proof. reflexivity. Qed.
Lemma s20_prepare : forall l r,csteps s20_tm 17
 (s20_at StA ([S2;S0]++l) S3 ([S1;S2;S1;S3;S1;S1;S3]++r))=
 Some(s20_carry ([S2;S0]++s20_Q++l) r).
Proof. reflexivity. Qed.
Lemma s20_carry_one : forall l r,csteps s20_tm 10
 (s20_carry l (s20_O++r))=Some(s20_carry (s20_K++l) r).
Proof. reflexivity. Qed.
Lemma s20_carry_zero : forall l r,csteps s20_tm 22
 (s20_carry l (s20_Z++r))=
 Some(s20_at StA (S2::l) S0 ([S1;S1]++s20_O++r)).
Proof. reflexivity. Qed.
Lemma s20_carry_finish : forall l r,csteps s20_tm 10
 (s20_at StA ([S2;S2;S0]++s20_Q++l) S0 ([S1;S1]++r))=
 Some(s20_at StA ([S2;S0;S3;S2;S0]++l) S2 ([S2;S1;S1;S1]++r)).
Proof. reflexivity. Qed.
Lemma s20_end_E : forall l,csteps s20_tm 21 (s20_carry l s20_E)=
 Some(s20_at StA l S2 (s20_G 0)).
Proof. reflexivity. Qed.
Lemma s20_K_backward_one : forall l r,csteps s20_tm 16
 (s20_at StA (s20_K++l) S2 ([S3;S2;S2]++r))=
 Some(s20_at StA l S2 ([S3;S2;S2]++s20_P++r)).
Proof. reflexivity. Qed.
Lemma s20_end_finish : forall r,csteps s20_tm 54
 (s20_at StA s20_Q S0 ([S1;S1]++r))=
 Some(s20_cut 0 (s20_O++r)).
Proof. reflexivity. Qed.
Lemma s20_G_entry : forall l r,csteps s20_tm 9
 (s20_carry l ([S3;S2;S2]++r))=
 Some(s20_at StA (s20_K++l) S3 ([S1;S2]++r)).
Proof. reflexivity. Qed.
Lemma s20_G_terminal : forall l,csteps s20_tm 30
 (s20_at StA l S3 [S1;S2;S1;S3;S1;S1])=
 Some(s20_at StA ([S2;S3]++l) S0 [S1;S1;S3;S2;S1]).
Proof. reflexivity. Qed.
Lemma s20_G_finish : forall l r,csteps s20_tm 21
 (s20_at StA ([S2;S3]++s20_K++l) S0 ([S1;S1]++r))=
 Some(s20_at StA (S2::l) S0 ([S1;S1]++s20_O++S1::r)).
Proof. reflexivity. Qed.

Lemma s20_pow_shift : forall w n r,
 s20_pow w n++w++r=w++s20_pow w n++r.
Proof.
 intros w n;induction n;intro r;cbn[s20_pow];[reflexivity|].
 rewrite <-!app_assoc;now rewrite IHn.
Qed.
Lemma s20_pow_end : forall w n,s20_pow w(S n)=s20_pow w n++w.
Proof. intros w n;pose proof(s20_pow_shift w n [])as H;rewrite !app_nil_r in H;exact(eq_sym H). Qed.
Lemma s20_rotate : forall n a b c r,a++b=c++a ->
 a++s20_pow b n++r=s20_pow c n++a++r.
Proof.
 intro n;induction n;intros a b c r H;cbn[s20_pow];[reflexivity|].
 rewrite <-!app_assoc,(app_assoc a b),H,<-!app_assoc.
 rewrite(IHn a b c r H);reflexivity.
Qed.
Lemma s20_DQ : forall n l,
 s20_pow s20_D n++[S2;S0]++l=[S2;S0]++s20_pow s20_Q n++l.
Proof. intros;symmetry;apply s20_rotate;reflexivity. Qed.
Lemma s20_DQ0 : forall n,
 s20_pow s20_D n++[S2;S0]=[S2;S0]++s20_pow s20_Q n.
Proof. intro n;pose proof(s20_DQ n [])as H;now rewrite !app_nil_r in H. Qed.
Lemma s20_RP : forall n r,
 [S1;S3;S1]++s20_pow s20_R n++r=s20_pow s20_P n++[S1;S3;S1]++r.
Proof. intros;apply s20_rotate;reflexivity. Qed.
Lemma s20_KQ : forall n l,
 S2::(s20_pow s20_K n++l)=s20_pow s20_Q n++S2::l.
Proof. intros;change([S2]++s20_pow s20_K n++l=s20_pow s20_Q n++[S2]++l);apply s20_rotate;reflexivity. Qed.
Lemma s20_DQ23 : forall n l,
 [S2;S3]++s20_pow s20_D n++l=s20_pow s20_Q n++[S2;S3]++l.
Proof. intros;apply s20_rotate;reflexivity. Qed.
Lemma s20_Z1 : forall n r,
 S1::(s20_pow s20_Z n++r)=s20_pow s20_Z n++S1::r.
Proof. intros;change([S1]++s20_pow s20_Z n++r=s20_pow s20_Z n++[S1]++r);apply s20_rotate;reflexivity. Qed.

Lemma s20_forward : forall n l r,csteps s20_tm (16*n)
 (s20_at StA l S3 ([S1;S2]++s20_pow s20_P n++r))=
 Some(s20_at StA (s20_pow s20_D n++l) S3 ([S1;S2]++r)).
Proof.
 intro n;induction n;intros l r;[reflexivity|].
 replace(16*S n)with(16+16*n)by lia.
 change(csteps s20_tm(16+16*n)(s20_at StA l S3([S1;S2]++s20_P++s20_pow s20_P n++r))=
 Some(s20_at StA(s20_pow s20_D(S n)++l)S3([S1;S2]++r))).
 rewrite csteps_add,s20_forward_one,IHn.
 rewrite s20_pow_shift;reflexivity.
Qed.
Lemma s20_backward : forall n l r,csteps s20_tm (16*n)
 (s20_at StA ([S2;S0;S3;S2;S0]++s20_pow s20_Q n++l) S2 r)=
 Some(s20_at StA ([S2;S0;S3;S2;S0]++l) S2 (s20_pow s20_R n++r)).
Proof.
 intro n;induction n;intros l r;[reflexivity|].
 replace(16*S n)with(16+16*n)by lia.
 change(csteps s20_tm(16+16*n)(s20_at StA([S2;S0;S3;S2;S0]++s20_Q++s20_pow s20_Q n++l)S2 r)=
 Some(s20_at StA([S2;S0;S3;S2;S0]++l)S2(s20_pow s20_R(S n)++r))).
 rewrite csteps_add,s20_backward_one,IHn,s20_pow_shift;reflexivity.
Qed.
Lemma s20_blank_backward : forall n l r,csteps s20_tm (6*n)
 (s20_at StA (s20_pow s20_Q n++l) S0 ([S1;S1]++r))=
 Some(s20_at StA l S0 ([S1;S1]++s20_pow s20_Z n++r)).
Proof.
 intro n;induction n;intros l r;[reflexivity|].
 replace(6*S n)with(6+6*n)by lia.
 change(csteps s20_tm(6+6*n)(s20_at StA(s20_Q++(s20_pow s20_Q n++l))S0([S1;S1]++r))=
 Some(s20_at StA l S0([S1;S1]++s20_pow s20_Z(S n)++r))).
 rewrite csteps_add,s20_blank_backward_one,IHn,s20_pow_shift;reflexivity.
Qed.
Lemma s20_ones_forward : forall j l r,csteps s20_tm (10*j)
 (s20_carry l (s20_pow s20_O j++r))=
 Some(s20_carry (s20_pow s20_K j++l) r).
Proof.
 intro j;induction j;intros l r;[reflexivity|].
 replace(10*S j)with(10+10*j)by lia.
 change(csteps s20_tm(10+10*j)(s20_carry l(s20_O++(s20_pow s20_O j++r)))=
 Some(s20_carry(s20_pow s20_K(S j)++l)r)).
 rewrite csteps_add,s20_carry_one,IHj,s20_pow_shift;reflexivity.
Qed.
Lemma s20_carry_lift : forall r s cost,
 (forall l,csteps s20_tm cost(s20_carry l r)=
 Some(s20_at StA(S2::l)S0([S1;S1]++s))) ->
 forall j l,csteps s20_tm(cost+16*j)(s20_carry l(s20_pow s20_O j++r))=
 Some(s20_at StA(S2::l)S0([S1;S1]++s20_pow s20_Z j++s)).
Proof.
 intros r s cost H j;induction j;intro l.
 - replace(cost+16*0)with cost by lia;apply H.
 - replace(cost+16*S j)with(10+((cost+16*j)+6))by lia.
   change(csteps s20_tm(10+((cost+16*j)+6))(s20_carry l(s20_O++(s20_pow s20_O j++r)))=
   Some(s20_at StA(S2::l)S0([S1;S1]++s20_pow s20_Z(S j)++s))).
   rewrite csteps_add,s20_carry_one,csteps_add,IHj.
   change(csteps s20_tm 6(s20_at StA(s20_Q++S2::l)S0([S1;S1]++s20_pow s20_Z j++s))=
   Some(s20_at StA(S2::l)S0([S1;S1]++s20_pow s20_Z(S j)++s))).
   rewrite s20_blank_backward_one;reflexivity.
Qed.

Lemma s20_phase : forall n t s cost,
 (forall l,csteps s20_tm cost(s20_at StA([S2;S0]++l)S3([S1;S2]++t))=
 Some(s20_at StA([S2;S0;S3;S2;S0]++l)S2 s)) ->
 csteps s20_tm(32*n+cost+19)
 (s20_at StA [] S0([S3;S2;S2]++s20_pow s20_P n++t))=
 Some(s20_at StA [] S0([S3;S2;S2]++s20_pow s20_P n++[S1;S3;S1]++s)).
Proof.
 intros n t s cost H.
 replace(32*n+cost+19)with(7+(16*n+(cost+(16*n+12))))by lia.
 rewrite csteps_add,s20_entry,csteps_add,s20_forward.
 rewrite s20_DQ0,csteps_add,H,csteps_add.
 rewrite <-(app_nil_r(s20_pow s20_Q n)) at 1.
 rewrite s20_backward;cbn[app].
 rewrite s20_finish.
 change(Some(s20_at StA[]S0([S3;S2;S2]++[S1;S3;S1]++s20_pow s20_R n++s))=
 Some(s20_at StA[]S0([S3;S2;S2]++s20_pow s20_P n++[S1;S3;S1]++s))).
 rewrite s20_RP;reflexivity.
Qed.
Lemma s20_first_phase : forall n r,
 csteps s20_tm(32*n+46)(s20_cut n r)=Some(s20_mid n r).
Proof.
 intros n r;unfold s20_cut,s20_mid.
 replace(32*n+46)with(32*n+27+19)by lia.
 apply(s20_phase n([S1;S1;S1]++r)([S1;S3]++r)27).
 intro l;exact(s20_first_terminal l r).
Qed.
Lemma s20_false_terminal : forall j l r,
 csteps s20_tm(49+16*j)
 (s20_at StA([S2;S0]++l)S3([S1;S2;S1;S3;S1;S1;S3]++s20_pow s20_O j++s20_Z++r))=
 Some(s20_at StA([S2;S0;S3;S2;S0]++l)S2([S2;S1;S1;S1]++s20_pow s20_Z j++s20_O++r)).
Proof.
 intros j l r;replace(49+16*j)with(17+((22+16*j)+10))by lia.
 rewrite csteps_add,s20_prepare,csteps_add.
 rewrite(s20_carry_lift(s20_Z++r)(s20_O++r)22(fun l=>s20_carry_zero l r)).
 apply s20_carry_finish.
Qed.
Theorem s20_increment : forall n j r,
 csteps s20_tm(64*n+114+16*j)(s20_cut n(s20_pow s20_O j++s20_Z++r))=
 Some(s20_cut(S n)(s20_pow s20_Z j++s20_O++r)).
Proof.
 intros n j r;replace(64*n+114+16*j)with((32*n+46)+(32*n+(49+16*j)+19))by lia.
 rewrite csteps_add,s20_first_phase.
 unfold s20_mid,s20_cut;rewrite s20_pow_end,<-!app_assoc.
 change(csteps s20_tm(32*n+(49+16*j)+19)
 (s20_at StA[]S0([S3;S2;S2]++s20_pow s20_P n++([S1;S3;S1;S1;S3]++s20_pow s20_O j++s20_Z++r)))=
 Some(s20_at StA[]S0([S3;S2;S2]++s20_pow s20_P n++[S1;S3;S1]++([S2;S1;S1;S1]++s20_pow s20_Z j++s20_O++r)))).
 apply s20_phase;intro l;apply s20_false_terminal.
Qed.

Lemma s20_K_backward : forall j l r,csteps s20_tm(16*j)
 (s20_at StA(s20_pow s20_K j++l)S2([S3;S2;S2]++r))=
 Some(s20_at StA l S2([S3;S2;S2]++s20_pow s20_P j++r)).
Proof.
 intro j;induction j;intros l r;[reflexivity|].
 replace(16*S j)with(16+16*j)by lia.
 change(csteps s20_tm(16+16*j)(s20_at StA(s20_K++(s20_pow s20_K j++l))S2([S3;S2;S2]++r))=
 Some(s20_at StA l S2([S3;S2;S2]++s20_pow s20_P(S j)++r))).
 rewrite csteps_add,s20_K_backward_one,IHj,s20_pow_shift;reflexivity.
Qed.
Lemma s20_G_normalize : forall m l,csteps s20_tm(22*m+60)(s20_carry l(s20_G m))=
 Some(s20_at StA(S2::l)S0([S1;S1]++s20_O++s20_pow s20_Z m++s20_E)).
Proof.
 intros m l;replace(22*m+60)with(9+(16*m+(30+(6*m+21))))by lia.
 unfold s20_G;rewrite csteps_add,s20_G_entry,csteps_add,s20_forward.
 rewrite csteps_add,s20_G_terminal.
 rewrite s20_DQ23,csteps_add.
 pose proof(s20_blank_backward m([S2;S3]++s20_K++l)[S3;S2;S1])as H.
 cbn[app]in H|-*;rewrite H.
 pose proof(s20_G_finish l(s20_pow s20_Z m++[S3;S2;S1]))as F.
 cbn[app]in F;rewrite F.
 rewrite s20_Z1;reflexivity.
Qed.
Lemma s20_G_carry_terminal : forall j m l,
 csteps s20_tm(22*m+87+16*j)
 (s20_at StA([S2;S0]++l)S3([S1;S2;S1;S3;S1;S1;S3]++s20_pow s20_O j++s20_G m))=
 Some(s20_at StA([S2;S0;S3;S2;S0]++l)S2
 ([S2;S1;S1;S1]++s20_pow s20_Z j++s20_O++s20_pow s20_Z m++s20_E)).
Proof.
 intros j m l;replace(22*m+87+16*j)with(17+(((22*m+60)+16*j)+10))by lia.
 rewrite csteps_add,s20_prepare,csteps_add.
 rewrite(s20_carry_lift(s20_G m)(s20_O++s20_pow s20_Z m++s20_E)(22*m+60)(s20_G_normalize m)).
 apply s20_carry_finish.
Qed.
Theorem s20_overflow_G : forall n j m,
 csteps s20_tm(64*n+16*j+22*m+152)(s20_cut n(s20_pow s20_O j++s20_G m))=
 Some(s20_cut(S n)(s20_pow s20_Z j++s20_O++s20_pow s20_Z m++s20_E)).
Proof.
 intros n j m;replace(64*n+16*j+22*m+152)with((32*n+46)+(32*n+(22*m+87+16*j)+19))by lia.
 rewrite csteps_add,s20_first_phase.
 unfold s20_mid,s20_cut;rewrite s20_pow_end,<-!app_assoc.
 change(csteps s20_tm(32*n+(22*m+87+16*j)+19)
 (s20_at StA[]S0([S3;S2;S2]++s20_pow s20_P n++([S1;S3;S1;S1;S3]++s20_pow s20_O j++s20_G m)))=
 Some(s20_at StA[]S0([S3;S2;S2]++s20_pow s20_P n++[S1;S3;S1]++
 ([S2;S1;S1;S1]++s20_pow s20_Z j++s20_O++s20_pow s20_Z m++s20_E)))).
 apply s20_phase;intro l;apply s20_G_carry_terminal.
Qed.

Lemma s20_end_drain : forall n r,
 csteps s20_tm(6*n+56)
 (s20_at StA([S2;S0]++s20_pow s20_Q(S n))S2 r)=
 Some(s20_cut 0(s20_O++s20_pow s20_Z n++r)).
Proof.
 intros n r;replace(6*n+56)with(2+(6*n+54))by lia.
 change(csteps s20_tm(2+(6*n+54))
 (s20_at StA([S2;S0]++s20_pow s20_Q(S n))S2 r)=
 Some(s20_cut 0(s20_O++s20_pow s20_Z n++r))).
 rewrite csteps_add.
 change(csteps s20_tm(6*n+54)(s20_at StA(s20_pow s20_Q(S n))S0([S1;S1]++r))=
 Some(s20_cut 0(s20_O++s20_pow s20_Z n++r))).
 rewrite s20_pow_end,csteps_add,s20_blank_backward.
 apply s20_end_finish.
Qed.
Theorem s20_overflow_E : forall n j,
 csteps s20_tm(54*n+26*j+147)(s20_cut n(s20_pow s20_O j++s20_E))=
 Some(s20_cut 0(s20_O++s20_pow s20_Z n++s20_G j)).
Proof.
 intros n j.
 replace(54*n+26*j+147)with((32*n+46)+(7+(16*n+(17+(10*j+(21+(16*j+(6*n+56))))))))by lia.
 rewrite csteps_add,s20_first_phase;unfold s20_mid.
 rewrite csteps_add,s20_entry,csteps_add,s20_forward,s20_DQ0.
 rewrite csteps_add.
 pose proof(s20_prepare(s20_pow s20_Q n)(s20_pow s20_O j++s20_E))as H.
 cbn[app]in H|-*;rewrite H,csteps_add,s20_ones_forward,csteps_add,s20_end_E.
 unfold s20_G at 1.
 rewrite csteps_add,s20_K_backward.
 change(csteps s20_tm(6*n+56)
 (s20_at StA([S2;S0]++s20_pow s20_Q(S n))S2(s20_G j))=
 Some(s20_cut 0(s20_O++s20_pow s20_Z n++s20_G j))).
 apply s20_end_drain.
Qed.

(** The two terminal tags and arbitrary finite binary-token words form a
    closed grammar. No relation between the binary value and [n] is needed. *)
Inductive s20_word : list Sym -> Prop :=
 |s20_word_E : s20_word s20_E
 |s20_word_G : forall m,s20_word(s20_G m)
 |s20_word_Z : forall r,s20_word r -> s20_word(s20_Z++r)
 |s20_word_O : forall r,s20_word r -> s20_word(s20_O++r).
Lemma s20_word_zeros : forall n r,s20_word r ->s20_word(s20_pow s20_Z n++r).
Proof. intro n;induction n;intros r H;[exact H|].
 change(s20_word(s20_Z++(s20_pow s20_Z n++r)));constructor;now apply IHn.
Qed.
Inductive s20_stop : list Sym -> Prop :=
 |s20_stop_E : s20_stop s20_E
 |s20_stop_G : forall m,s20_stop(s20_G m)
 |s20_stop_Z : forall r,s20_word r -> s20_stop(s20_Z++r).
Lemma s20_factor : forall w,s20_word w ->
 exists j r,w=s20_pow s20_O j++r /\ s20_stop r.
Proof.
 intros w H;induction H.
 - exists 0,s20_E;split;[reflexivity|constructor].
 - exists 0,(s20_G m);split;[reflexivity|constructor].
 - exists 0,(s20_Z++r);split;[reflexivity|now constructor].
 - destruct IHs20_word as(j&s&E&Hstop);exists(S j),s;split;[|exact Hstop].
   rewrite E;cbn[s20_pow];now rewrite app_assoc.
Qed.
Theorem s20_closed : forall n w,s20_word w ->
 exists k n' w',0<k /\ s20_word w' /\
 csteps s20_tm k(s20_cut n w)=Some(s20_cut n' w').
Proof.
 intros n w H;destruct(s20_factor w H)as(j&r&->&Hstop);destruct Hstop.
 - exists(54*n+26*j+147),0,(s20_O++s20_pow s20_Z n++s20_G j).
   split;[lia|];split;[constructor;apply s20_word_zeros;constructor|apply s20_overflow_E].
 - exists(64*n+16*j+22*m+152),(S n),(s20_pow s20_Z j++s20_O++s20_pow s20_Z m++s20_E).
   split;[lia|];split;[apply s20_word_zeros;constructor;apply s20_word_zeros;constructor|apply s20_overflow_G].
 - exists(64*n+114+16*j),(S n),(s20_pow s20_Z j++s20_O++r).
   split;[lia|];split;[apply s20_word_zeros;now constructor|apply s20_increment].
Qed.
Lemma s20_blank_entry : csteps s20_tm 176 c0=Some(s20_cut 0(s20_O++s20_E)).
Proof. reflexivity. Qed.
Theorem s20_returns : forall N,exists t n w,
 N<=t /\s20_word w /\csteps s20_tm t c0=Some(s20_cut n w).
Proof.
 intro N;induction N as[|N IH].
 - exists 176,0,(s20_O++s20_E);split;[lia|];split;[constructor;constructor|apply s20_blank_entry].
 - destruct IH as(t&n&w&Ht&Hw&E).
   destruct(s20_closed n w Hw)as(k&n'&w'&Hk&Hw'&E').
   exists(t+k),n',w';split;[lia|];split;[exact Hw'|].
   rewrite csteps_add,E;exact E'.
Qed.
Theorem s20_nonhalt : NonHalt s20_tm.
Proof. apply ore_total_nonhalt;intros q h;destruct q,h;eexists;reflexivity. Qed.
Theorem s20_A_recurrent : forall N,exists t,N<=t /\VisitsAt s20_tm StA t.
Proof.
 intro N;destruct(s20_returns N)as(t&n&w&Ht&Hw&E).
 exists t;split;[exact Ht|];exists(lift(s20_cut n w));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem s20_B_recurrent : forall N,exists t,N<=t /\VisitsAt s20_tm StB t.
Proof.
 intro N;destruct(s20_returns N)as(t&n&w&Ht&Hw&E).
 exists(t+1);split;[lia|].
 exists(lift(s20_at StB[]S0(S1::([S3;S2;S2]++s20_pow s20_P n++[S1;S1;S1]++w))));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem s20_state_zero : QHBound 0 s20_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(s20_A_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(s20_B_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem s20_sound : NonHalt s20_tm /\QHBound 0 s20_tm.
Proof. split;[apply s20_nonhalt|apply s20_state_zero]. Qed.
Print Assumptions s20_sound.
