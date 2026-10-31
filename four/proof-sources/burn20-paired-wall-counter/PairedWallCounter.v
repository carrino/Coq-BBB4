(** Exact frozen S050. Parity phases preserve a finite wall word (30)^n0.
    Every short program below is universally quantified over its tape context. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census OneStateReach.
Import ListNotations.
Definition wc_tm:TM:=fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StB
 |StA,S2=>mkTrans S1 DL StA |StA,S3=>mkTrans S1 DR StA
 |StB,S0=>mkTrans S3 DR StB |StB,S1=>mkTrans S3 DL StA
 |StB,S2=>mkTrans S3 DL StB |StB,S3=>mkTrans S0 DR StB end).
Definition wc_front q l r:cconf:=(q,(l,chd r,ctl r)).
Fixpoint wc_pairs n:list Sym:=match n with 0=>[]|S n=>S3::S0::wc_pairs n end.
Fixpoint wc_W n:list Sym:=match n with 0=>[]|S n=>S3::S2::S1::S1::wc_W n end.
Definition wc_left n:=wc_pairs n++[S0].
Definition wc_stage a n r:cconf:=(StA,(repeat S1 a++wc_left n,S0,r)).
Definition wc_X n r:cconf:=(StA,(S1::wc_left n,S1,r)).
Definition wc_Y n r:cconf:=(StA,(S1::S1::wc_left n,S1,r)).
Definition wc_Z n r:cconf:=(StA,(S1::S1::S1::wc_left n,S1,r)).
Definition wc_main n:=wc_stage 4(4*n+2)[].
Definition wc_cost n:=416*n+577.
Lemma wc_pairs_app : forall n m,wc_pairs(n+m)=wc_pairs n++wc_pairs m.
Proof. induction n;intro m;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma wc_left_add : forall n m,wc_left(n+m)=wc_pairs n++wc_left m.
Proof. intros n m;unfold wc_left;rewrite wc_pairs_app,app_assoc;reflexivity. Qed.
Lemma wc_W_shift : forall n r,
 wc_W n++S3::S2::S1::S1::r=S3::S2::S1::S1::(wc_W n++r).
Proof. induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma wc_start_zero : forall l r,
 csteps wc_tm 2(StA,(S1::S1::S1::l,S0,r))=Some(StA,(S1::l,S1,S3::S1::r)).
Proof. reflexivity. Qed.
Lemma wc_start_one : forall l r,
 csteps wc_tm 2(StA,(S1::S1::S1::l,S1,r))=Some(StA,(S1::l,S1,S3::S2::r)).
Proof. reflexivity. Qed.
Lemma wc_L20 : forall l r,
 csteps wc_tm 20(StA,(S1::S3::S0::S3::S0::l,S1,r))=
 Some(StA,(S1::l,S1,S3::S2::S1::S1::r)).
Proof. reflexivity. Qed.
Lemma wc_odd_turn : forall r,
 csteps wc_tm 38(wc_X 1 r)=Some(wc_Y 0(S3::S2::r)).
Proof. reflexivity. Qed.
Lemma wc_even_turn : forall r,
 csteps wc_tm 35(wc_X 0(S3::S2::S1::S1::r))=
 Some(wc_Y 0(S3::S2::S1::S1::S1::r)).
Proof. reflexivity. Qed.
Lemma wc_R32 : forall p r,
 csteps wc_tm 32(wc_Y p(S3::S2::S3::S2::S1::S1::r))=
 Some(wc_Y(p+2)(S3::S2::r)).
Proof.
 intros p r;unfold wc_Y.
 replace(p+2)with(2+p)by lia;rewrite wc_left_add.
 destruct p;reflexivity.
Qed.
Lemma wc_R58 : forall p r,
 csteps wc_tm 58(wc_Y p(S3::S2::S1::S1::S1::S3::S2::S1::S1::r))=
 Some(wc_Y(p+2)(S3::S2::S1::S1::S1::r)).
Proof.
 intros p r;unfold wc_Y.
 replace(p+2)with(2+p)by lia;rewrite wc_left_add.
 destruct p;reflexivity.
Qed.
Lemma wc_odd_finish : forall p r,
 csteps wc_tm 23(wc_Y p(S3::S2::S3::S1::r))=
 Some(wc_front StA(S1::S1::S1::wc_left(p+2))r).
Proof.
 intros p r;unfold wc_Y.
 replace(p+2)with(2+p)by lia;rewrite wc_left_add.
 destruct p;reflexivity.
Qed.
Lemma wc_even_finish1 : forall p r,
 csteps wc_tm 57(wc_Y p(S3::S2::S1::S1::S1::S3::S1::r))=
 Some(wc_Z(p+2)(S3::S2::r)).
Proof.
 intros p r;unfold wc_Y,wc_Z.
 replace(p+2)with(2+p)by lia;rewrite wc_left_add.
 destruct p;reflexivity.
Qed.
Lemma wc_even_finish2 : forall p r,
 csteps wc_tm 114(wc_Y p(S3::S2::S1::S1::S1::S3::S2::S3::S2::r))=
 Some(wc_front StA(S1::S1::S1::S1::wc_left(p+4))r).
Proof.
 intros p r;unfold wc_Y.
 replace(p+4)with(4+p)by lia;rewrite wc_left_add.
 destruct p;reflexivity.
Qed.
Lemma wc_four : forall p r,
 csteps wc_tm 21(wc_stage 4 p r)=
 Some(wc_front StA(S1::S1::S1::wc_left(S p))r).
Proof. intros p r;destruct p;reflexivity. Qed.
Lemma wc_L_scan : forall n p r,
 csteps wc_tm(20*n)(wc_X(2*n+p)r)=Some(wc_X p(wc_W n++r)).
Proof.
 induction n;intros p r.
 - cbn;reflexivity.
 - replace(20*S n)with(20+20*n)by lia;rewrite csteps_add.
   replace(2*S n+p)with(S(S(2*n+p)))by lia.
   change(csteps wc_tm(20*n)(wc_X(2*n+p)(S3::S2::S1::S1::r))=
   Some(wc_X p(wc_W(S n)++r))).
   rewrite IHn,wc_W_shift;reflexivity.
Qed.
Lemma wc_R32_scan : forall n p r,
 csteps wc_tm(32*n)(wc_Y p(S3::S2::(wc_W n++r)))=
 Some(wc_Y(p+2*n)(S3::S2::r)).
Proof.
 induction n;intros p r.
 - cbn;rewrite Nat.add_0_r;reflexivity.
 - replace(32*S n)with(32+32*n)by lia;rewrite csteps_add.
   change(match csteps wc_tm 32(wc_Y p(S3::S2::S3::S2::S1::S1::(wc_W n++r)))with
   |Some cc=>csteps wc_tm(32*n)cc|None=>None end=Some(wc_Y(p+2*S n)(S3::S2::r))).
   rewrite wc_R32,IHn;replace(p+2+2*n)with(p+2*S n)by lia;reflexivity.
Qed.
Lemma wc_R58_scan : forall n p r,
 csteps wc_tm(58*n)(wc_Y p(S3::S2::S1::S1::S1::(wc_W n++r)))=
 Some(wc_Y(p+2*n)(S3::S2::S1::S1::S1::r)).
Proof.
 induction n;intros p r.
 - cbn;rewrite Nat.add_0_r;reflexivity.
 - replace(58*S n)with(58+58*n)by lia;rewrite csteps_add.
   change(match csteps wc_tm 58(wc_Y p(S3::S2::S1::S1::S1::S3::S2::S1::S1::(wc_W n++r)))with
   |Some cc=>csteps wc_tm(58*n)cc|None=>None end=Some(wc_Y(p+2*S n)(S3::S2::S1::S1::S1::r))).
   rewrite wc_R58,IHn;replace(p+2+2*n)with(p+2*S n)by lia;reflexivity.
Qed.
Theorem wc_odd_phase : forall n r,
 csteps wc_tm(52*n+63)(wc_stage 3(S(2*n))r)=
 Some(wc_front StA(S1::S1::S1::wc_left(2*n+2))r).
Proof.
 intros n r;replace(52*n+63)with(2+(20*n+(38+(32*n+23))))by lia;rewrite csteps_add.
 change(csteps wc_tm(20*n+(38+(32*n+23)))(wc_X(S(2*n))(S3::S1::r))=
 Some(wc_front StA(S1::S1::S1::wc_left(2*n+2))r)).
 replace(S(2*n))with(2*n+1)by lia.
 rewrite csteps_add,wc_L_scan,csteps_add,wc_odd_turn,csteps_add,wc_R32_scan,wc_odd_finish;reflexivity.
Qed.
Lemma wc_even_phase1 : forall n r,
 csteps wc_tm(78*n+114)(wc_stage 3(2*S n)r)=Some(wc_Z(2*S n)(S3::S2::r)).
Proof.
 intros n r;replace(78*n+114)with(2+(20*S n+(35+(58*n+57))))by lia;rewrite csteps_add.
 change(csteps wc_tm(20*S n+(35+(58*n+57)))(wc_X(2*S n)(S3::S1::r))=
 Some(wc_Z(2*S n)(S3::S2::r))).
 pose proof(wc_L_scan(S n)0(S3::S1::r))as EL;rewrite Nat.add_0_r in EL.
 rewrite csteps_add,EL,csteps_add.
 change(csteps wc_tm(58*n+57)(wc_Y 0(S3::S2::S1::S1::S1::(wc_W n++S3::S1::r)))=
 Some(wc_Z(2*S n)(S3::S2::r))).
 rewrite csteps_add,wc_R58_scan,wc_even_finish1.
 replace(0+2*n+2)with(2*S n)by lia;reflexivity.
Qed.
Lemma wc_even_phase2 : forall n r,
 csteps wc_tm(78*n+171)(wc_Z(2*S n)(S3::S2::r))=
 Some(wc_front StA(S1::S1::S1::S1::wc_left(2*n+4))r).
Proof.
 intros n r;replace(78*n+171)with(2+(20*S n+(35+(58*n+114))))by lia;rewrite csteps_add.
 change(csteps wc_tm(20*S n+(35+(58*n+114)))(wc_X(2*S n)(S3::S2::S3::S2::r))=
 Some(wc_front StA(S1::S1::S1::S1::wc_left(2*n+4))r)).
 pose proof(wc_L_scan(S n)0(S3::S2::S3::S2::r))as EL;rewrite Nat.add_0_r in EL.
 rewrite csteps_add,EL,csteps_add.
 change(csteps wc_tm(58*n+114)(wc_Y 0(S3::S2::S1::S1::S1::(wc_W n++S3::S2::S3::S2::r)))=
 Some(wc_front StA(S1::S1::S1::S1::wc_left(2*n+4))r)).
 rewrite csteps_add,wc_R58_scan,wc_even_finish2;reflexivity.
Qed.
Theorem wc_even_phase : forall n r,
 csteps wc_tm(156*n+285)(wc_stage 3(2*S n)r)=
 Some(wc_front StA(S1::S1::S1::S1::wc_left(2*n+4))r).
Proof.
 intros n r;replace(156*n+285)with((78*n+114)+(78*n+171))by lia.
 rewrite csteps_add,wc_even_phase1;apply wc_even_phase2.
Qed.
Theorem wc_main_next : forall n,
 csteps wc_tm(wc_cost n)(wc_main n)=Some(wc_main(S n)).
Proof.
 intro n;replace(wc_cost n)with(21+((52*(2*n+1)+63)+(156*(2*n+1)+285)))by(unfold wc_cost;lia).
 unfold wc_main at 1;rewrite csteps_add,wc_four.
 change(csteps wc_tm((52*(2*n+1)+63)+(156*(2*n+1)+285))
 (wc_stage 3(S(4*n+2))[])=Some(wc_main(S n))).
 replace(S(4*n+2))with(S(2*(2*n+1)))by lia.
 rewrite csteps_add,wc_odd_phase.
 change(csteps wc_tm(156*(2*n+1)+285)(wc_stage 3(2*(2*n+1)+2)[])=Some(wc_main(S n))).
 replace(2*(2*n+1)+2)with(2*S(2*n+1))by lia;rewrite wc_even_phase.
 unfold wc_main,wc_stage;replace(2*(2*n+1)+4)with(4*S n+2)by lia;reflexivity.
Qed.
Example wc_entry : csteps wc_tm 149 c0=Some(wc_main 0).
Proof. reflexivity. Qed.
Lemma wc_returns : forall N,exists t n,N<=t /\csteps wc_tm t c0=Some(wc_main n).
Proof.
 induction N as[|N IH].
 - exists 149,0;split;[lia|exact wc_entry].
 - destruct IH as(t&n&Ht&E);exists(t+wc_cost n),(S n);split.
   + unfold wc_cost;lia.
   + rewrite csteps_add,E;apply wc_main_next.
Qed.
Theorem wc_nonhalt : NonHalt wc_tm.
Proof. apply ore_total_nonhalt;intros q h;destruct q,h;eexists;reflexivity. Qed.
Theorem wc_A_recurrent : forall N,exists t,N<=t /\VisitsAt wc_tm StA t.
Proof.
 intro N;destruct(wc_returns N)as(t&n&Ht&E).
 exists t;split;[exact Ht|];exists(lift(wc_main n));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem wc_B_recurrent : forall N,exists t,N<=t /\VisitsAt wc_tm StB t.
Proof.
 intro N;destruct(wc_returns N)as(t&n&Ht&E).
 exists(t+1);split;[lia|];exists(lift(StB,(S1::S1::S1::wc_left(4*n+2),S1,[S1])));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem wc_state_zero : QHBound 0 wc_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(wc_A_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(wc_B_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem wc_sound : NonHalt wc_tm /\QHBound 0 wc_tm.
Proof. split;[exact wc_nonhalt|exact wc_state_zero]. Qed.
Print Assumptions wc_sound.
