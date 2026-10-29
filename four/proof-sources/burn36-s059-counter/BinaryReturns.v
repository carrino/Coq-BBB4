(** S059: four boundary phases implement binary increment. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census OneStateReach TotalCompletion.
Import ListNotations.
Definition s59_tm : TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StB
 |StA,S2=>mkTrans S3 DR StA |StA,S3=>mkTrans S0 DR StA
 |StB,S0=>mkTrans S2 DR StB |StB,S1=>mkTrans S3 DR StA
 |StB,S2=>mkTrans S2 DL StB |StB,S3=>mkTrans S3 DL StA end).
Definition s59_at q l h r:cconf :=(q,(l,h,r)).
Definition s59_front q l r:cconf :=(q,(l,chd r,ctl r)).
Definition s59_back q l r:cconf :=(q,(ctl l,chd l,r)).
Definition s59_P :=[S3;S3;S3;S0].
Definition s59_Q :=[S3;S2;S2;S2].
Definition s59_R :=[S3;S3;S0;S3].
Definition s59_U :=[S3;S1].
Definition s59_Z :=[S0;S0].
Definition s59_O :=[S0;S3].
Fixpoint s59_pow(w:list Sym)n :=match n with 0=>[]|S n=>w++s59_pow w n end.
Definition s59_frame n t:=s59_at StA(s59_pow s59_P n++t)S0[].
Definition s59_main n w:=s59_frame n([S3;S2]++w).
Lemma s59_forward_one : forall l r,csteps s59_tm 12
 (s59_at StA(s59_P++l)S0 r)=Some(s59_at StA l S0(s59_Q++r)).
Proof. reflexivity. Qed.
Lemma s59_backward_one : forall l r,csteps s59_tm 4
 (s59_at StA l S2(s59_Q++r))=Some(s59_at StA(s59_R++l)S2 r).
Proof. reflexivity. Qed.
Lemma s59_prefix : forall l r,csteps s59_tm 9
 (s59_at StA([S3;S2]++l)S0 r)=Some(s59_back StA l([S3;S2;S2]++r)).
Proof. reflexivity. Qed.
Lemma s59_ones_one : forall l r,csteps s59_tm 2
 (s59_back StA(s59_O++l)r)=Some(s59_back StA l(s59_U++r)).
Proof. reflexivity. Qed.
Lemma s59_zero_stop : forall l r,csteps s59_tm 3
 (s59_back StA(s59_Z++l)r)=Some(s59_front StA([S3;S2]++l)r).
Proof. reflexivity. Qed.
Lemma s59_empty_stop : forall r,csteps s59_tm 3
 (s59_back StA[]r)=Some(s59_front StA[S3;S2]r).
Proof. reflexivity. Qed.
Lemma s59_restore_first : forall l r,csteps s59_tm 10
 (s59_front StA([S3;S2]++l)(s59_U++r))=
 Some(s59_front StA([S3;S3;S0;S3]++l)r).
Proof. reflexivity. Qed.
Lemma s59_restore_one : forall l r,csteps s59_tm 10
 (s59_front StA([S3;S3]++l)(s59_U++r))=
 Some(s59_front StA([S3;S3]++s59_Z++l)r).
Proof. reflexivity. Qed.
Lemma s59_restore_finish : forall l r,csteps s59_tm 2
 (s59_front StA l([S3;S2;S2]++r))=
 Some(s59_at StA([S3;S0]++l)S2 r).
Proof. reflexivity. Qed.
Lemma s59_phase2_zero : forall l r,csteps s59_tm 20
 (s59_at StA([S3;S3;S0;S3;S2]++l)S0 r)=
 Some(s59_at StA([S3;S3;S3;S0;S3]++l)S2 r).
Proof. reflexivity. Qed.
Lemma s59_phase2_succ : forall l r,csteps s59_tm 20
 (s59_at StA([S3;S3;S0;S3;S3]++l)S0 r)=
 Some(s59_at StA([S3;S3;S3;S0;S0]++l)S2 r).
Proof. reflexivity. Qed.
Lemma s59_phase3 : forall l r,csteps s59_tm 16
 (s59_at StA([S3;S3;S3;S3]++l)S0 r)=
 Some(s59_at StA([S3;S3;S0;S0]++l)S2 r).
Proof. reflexivity. Qed.
Lemma s59_phase4 : forall l r,csteps s59_tm 18
 (s59_at StA([S3;S3;S3;S0;S0]++l)S0 r)=
 Some(s59_at StA([S3;S3;S0;S3;S2]++l)S2 r).
Proof. reflexivity. Qed.

Lemma s59_pow_shift : forall w n r,
 s59_pow w n++w++r=w++s59_pow w n++r.
Proof.
 intros w n;induction n;intro r;cbn[s59_pow];[reflexivity|].
 rewrite <-!app_assoc;now rewrite IHn.
Qed.
Lemma s59_pow_end : forall w n,s59_pow w(S n)=s59_pow w n++w.
Proof. intros w n;pose proof(s59_pow_shift w n[])as H;rewrite !app_nil_r in H;exact(eq_sym H). Qed.
Lemma s59_rotate : forall n r,S3::(s59_pow s59_R n++r)=s59_pow s59_P n++S3::r.
Proof.
 intro n;induction n;intro r;[reflexivity|].
 change(s59_P++S3::(s59_pow s59_R n++r)=(s59_P++s59_pow s59_P n)++S3::r).
 rewrite IHn,<-app_assoc;reflexivity.
Qed.
Lemma s59_forward : forall n l r,csteps s59_tm(12*n)
 (s59_at StA(s59_pow s59_P n++l)S0 r)=
 Some(s59_at StA l S0(s59_pow s59_Q n++r)).
Proof.
 intro n;induction n;intros l r;[reflexivity|].
 replace(12*S n)with(12+12*n)by lia.
 change(csteps s59_tm(12+12*n)(s59_at StA(s59_P++(s59_pow s59_P n++l))S0 r)=
 Some(s59_at StA l S0(s59_pow s59_Q(S n)++r))).
 rewrite csteps_add,s59_forward_one,IHn,s59_pow_shift;reflexivity.
Qed.
Lemma s59_backward : forall n l r,csteps s59_tm(4*n)
 (s59_at StA l S2(s59_pow s59_Q n++r))=
 Some(s59_at StA(s59_pow s59_R n++l)S2 r).
Proof.
 intro n;induction n;intros l r;[reflexivity|].
 replace(4*S n)with(4+4*n)by lia.
 change(csteps s59_tm(4+4*n)(s59_at StA l S2(s59_Q++(s59_pow s59_Q n++r)))=
 Some(s59_at StA(s59_pow s59_R(S n)++l)S2 r)).
 rewrite csteps_add,s59_backward_one,IHn,s59_pow_shift;reflexivity.
Qed.
Lemma s59_phase : forall n t s cost,
 (forall r,csteps s59_tm cost(s59_at StA t S0 r)=Some(s59_at StA s S2 r))->
 csteps s59_tm(16*n+cost+1)(s59_frame n t)=Some(s59_frame n(S3::s)).
Proof.
 intros n t s cost H;unfold s59_frame.
 replace(16*n+cost+1)with(12*n+(cost+(4*n+1)))by lia.
 rewrite csteps_add,s59_forward,csteps_add,H,csteps_add,s59_backward.
 change(Some(s59_at StA(S3::(s59_pow s59_R n++s))S0[])=
 Some(s59_at StA(s59_pow s59_P n++S3::s)S0[])).
 now rewrite s59_rotate.
Qed.
Lemma s59_ones : forall j l r,csteps s59_tm(2*j)
 (s59_back StA(s59_pow s59_O j++l)r)=
 Some(s59_back StA l(s59_pow s59_U j++r)).
Proof.
 intro j;induction j;intros l r;[reflexivity|].
 replace(2*S j)with(2+2*j)by lia.
 change(csteps s59_tm(2+2*j)(s59_back StA(s59_O++(s59_pow s59_O j++l))r)=
 Some(s59_back StA l(s59_pow s59_U(S j)++r))).
 rewrite csteps_add,s59_ones_one,IHj,s59_pow_shift;reflexivity.
Qed.
Lemma s59_restore : forall j l r,csteps s59_tm(10*j)
 (s59_front StA([S3;S3]++l)(s59_pow s59_U j++r))=
 Some(s59_front StA([S3;S3]++s59_pow s59_Z j++l)r).
Proof.
 intro j;induction j;intros l r;[reflexivity|].
 replace(10*S j)with(10+10*j)by lia.
 change(csteps s59_tm(10+10*j)(s59_front StA([S3;S3]++l)(s59_U++(s59_pow s59_U j++r)))=
 Some(s59_front StA([S3;S3]++s59_pow s59_Z(S j)++l)r)).
 rewrite csteps_add,s59_restore_one,IHj,s59_pow_shift;reflexivity.
Qed.
Definition s59_out j l :=match j with
 |0=>[S3;S0;S3;S2]++l
 |S j=>[S3;S0;S3;S3]++s59_pow s59_Z j++s59_O++l end.
Lemma s59_restore_all : forall j l r,csteps s59_tm(10*j+2)
 (s59_front StA([S3;S2]++l)(s59_pow s59_U j++[S3;S2;S2]++r))=
 Some(s59_at StA(s59_out j l)S2 r).
Proof.
 intros[|j]l r;[apply s59_restore_finish|].
 replace(10*S j+2)with(10+(10*j+2))by lia.
 change(csteps s59_tm(10+(10*j+2))
 (s59_front StA([S3;S2]++l)(s59_U++(s59_pow s59_U j++[S3;S2;S2]++r)))=
 Some(s59_at StA(s59_out(S j)l)S2 r)).
 rewrite csteps_add,s59_restore_first,csteps_add.
 pose proof(s59_restore j(s59_O++l)([S3;S2;S2]++r))as H.
 cbn[s59_O app]in H|-*;rewrite H.
 pose proof(s59_restore_finish([S3;S3]++s59_pow s59_Z j++s59_O++l)r)as F.
 cbn[s59_O app]in F;rewrite F;reflexivity.
Qed.

Inductive s59_stop : list Sym ->list Sym ->Prop :=
 |s59_stop_empty : s59_stop[][]
 |s59_stop_zero : forall l,s59_stop(s59_Z++l)l.
Lemma s59_stop_steps : forall t l,s59_stop t l ->forall r,
 csteps s59_tm 3(s59_back StA t r)=Some(s59_front StA([S3;S2]++l)r).
Proof. intros t l H;destruct H;[apply s59_empty_stop|apply s59_zero_stop]. Qed.
Lemma s59_first_terminal : forall j t l r,s59_stop t l ->
 csteps s59_tm(14+12*j)
 (s59_at StA([S3;S2]++s59_pow s59_O j++t)S0 r)=
 Some(s59_at StA(s59_out j l)S2 r).
Proof.
 intros j t l r H;replace(14+12*j)with(9+(2*j+(3+(10*j+2))))by lia.
 rewrite csteps_add,s59_prefix,csteps_add,s59_ones,csteps_add.
 rewrite(s59_stop_steps t l H),s59_restore_all;reflexivity.
Qed.
Lemma s59_second_terminal : forall j l r,csteps s59_tm 20
 (s59_at StA(S3::s59_out j l)S0 r)=
 Some(s59_at StA([S3;S3;S3]++s59_pow s59_Z j++s59_O++l)S2 r).
Proof.
 intros[|j]l r.
 - exact(s59_phase2_zero l r).
 - exact(s59_phase2_succ(s59_pow s59_Z j++s59_O++l)r).
Qed.
Theorem s59_increment : forall n j t l,s59_stop t l ->
 csteps s59_tm(64*n+72+12*j)(s59_main n(s59_pow s59_O j++t))=
 Some(s59_main(S n)(s59_pow s59_Z j++s59_O++l)).
Proof.
 intros n j t l H;unfold s59_main.
 replace(64*n+72+12*j)with((16*n+(14+12*j)+1)+((16*n+20+1)+((16*n+16+1)+(16*n+18+1))))by lia.
 rewrite csteps_add,(s59_phase n([S3;S2]++s59_pow s59_O j++t)(s59_out j l)(14+12*j)
 (fun r=>s59_first_terminal j t l r H)).
 rewrite csteps_add,(s59_phase n(S3::s59_out j l)([S3;S3;S3]++s59_pow s59_Z j++s59_O++l)20
 (s59_second_terminal j l)).
 pose proof(s59_phase n([S3;S3;S3;S3]++s59_pow s59_Z j++s59_O++l)
 ([S3;S3;S0;S0]++s59_pow s59_Z j++s59_O++l)16
 (fun r=>s59_phase3(s59_pow s59_Z j++s59_O++l)r))as H3.
 cbn[app]in H3|-*;rewrite csteps_add,H3.
 pose proof(s59_phase n([S3;S3;S3;S0;S0]++s59_pow s59_Z j++s59_O++l)
 ([S3;S3;S0;S3;S2]++s59_pow s59_Z j++s59_O++l)18
 (fun r=>s59_phase4(s59_pow s59_Z j++s59_O++l)r))as H4.
 cbn[app]in H4;rewrite H4.
 unfold s59_frame;rewrite s59_pow_end,<-app_assoc;reflexivity.
Qed.

(** The empty end acts as an implicit zero token. Every finite binary word
    is admitted, without any coupling to the unary prefix length. *)
Inductive s59_word : list Sym->Prop :=
 |s59_word_empty : s59_word[]
 |s59_word_zero : forall w,s59_word w->s59_word(s59_Z++w)
 |s59_word_one : forall w,s59_word w->s59_word(s59_O++w).
Lemma s59_word_zeros : forall j w,s59_word w->s59_word(s59_pow s59_Z j++w).
Proof.
 intro j;induction j;intros w H;[exact H|].
 change(s59_word(s59_Z++(s59_pow s59_Z j++w)));constructor;now apply IHj.
Qed.
Lemma s59_factor : forall w,s59_word w->
 exists j t l,w=s59_pow s59_O j++t /\s59_stop t l /\s59_word l.
Proof.
 intros w H;induction H.
 - exists 0,[],[];split;[reflexivity|];split;constructor.
 - exists 0,(s59_Z++w),w;split;[reflexivity|];split;[constructor|exact H].
 - destruct IHs59_word as(j&t&l&E&Hstop&Hl);exists(S j),t,l.
   split;[rewrite E;cbn[s59_pow];now rewrite app_assoc|auto].
Qed.
Theorem s59_closed : forall n w,s59_word w->
 exists k w',0<k /\s59_word w' /\csteps s59_tm k(s59_main n w)=Some(s59_main(S n)w').
Proof.
 intros n w H;destruct(s59_factor w H)as(j&t&l&->&Hstop&Hl).
 exists(64*n+72+12*j),(s59_pow s59_Z j++s59_O++l).
 split;[lia|];split;[apply s59_word_zeros;now constructor|now apply s59_increment].
Qed.
Lemma s59_blank_entry : csteps s59_tm 3 c0=Some(s59_main 0[]).
Proof. reflexivity. Qed.
Theorem s59_returns : forall N,exists t n w,
 N<=t /\s59_word w /\csteps s59_tm t c0=Some(s59_main n w).
Proof.
 intro N;induction N as[|N IH].
 - exists 3,0,[];split;[lia|];split;[constructor|apply s59_blank_entry].
 - destruct IH as(t&n&w&Ht&Hw&E);destruct(s59_closed n w Hw)as(k&w'&Hk&Hw'&E').
   exists(t+k),(S n),w';split;[lia|];split;[exact Hw'|].
   rewrite csteps_add,E;exact E'.
Qed.
Theorem s59_nonhalt : NonHalt s59_tm.
Proof. apply ore_total_nonhalt;intros q h;destruct q,h;eexists;reflexivity. Qed.
Theorem s59_A_recurrent : forall N,exists t,N<=t /\VisitsAt s59_tm StA t.
Proof.
 intro N;destruct(s59_returns N)as(t&n&w&Ht&Hw&E).
 exists t;split;[exact Ht|];exists(lift(s59_main n w));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem s59_B_recurrent : forall N,exists t,N<=t /\VisitsAt s59_tm StB t.
Proof.
 intro N;destruct(s59_returns N)as(t&n&w&Ht&Hw&E).
 exists(t+1);split;[lia|].
 exists(lift(s59_back StB(s59_pow s59_P n++[S3;S2]++w)[S1]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem s59_state_zero : QHBound 0 s59_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(s59_A_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(s59_B_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem s59_sound : NonHalt s59_tm /\QHBound 0 s59_tm.
Proof. split;[apply s59_nonhalt|apply s59_state_zero]. Qed.
Print Assumptions s59_sound.
