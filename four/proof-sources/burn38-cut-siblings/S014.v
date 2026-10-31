(** S014: a guarded four-token grammar, closed by finitely many F passes. *)
From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement Spec CTape Census OneStateReach TotalCompletion.
From BBB24Burn39S014Normalizer Require Import Normalizer.
Import ListNotations.
Definition b38_R0:=[S3;S1;S3;S1;S0;S3;S1;S3;S1].
Definition b38_RL:=[S3;S0;S3;S1].
Definition b38_L (v:bn_variant) ts:=bn_back StB(bn_enc ts++[S3])(S0::b38_RL).
Lemma b38_R0_step : forall v l,csteps(bn_tm v)75
 (bn_at StA l S3 b38_R0)=
 Some(bn_back StB l(S0::bn_Fword++bn_Jword++[S3])).
Proof. destruct v;intro l;destruct l;reflexivity. Qed.
Lemma b38_pair_finish : forall v l,csteps(bn_tm v)3
 (bn_at StA l S3[S3;S1])=Some(bn_cut(bn_code bb++l)).
Proof. destruct v;intro l;reflexivity. Qed.
Lemma b38_three_finish : forall v l,csteps(bn_tm v)2
 (bn_at StA l S3[S3])=Some(bn_cut([S1;S2]++l)).
Proof. destruct v;intro l;reflexivity. Qed.
Lemma b38_header_B : forall v l,csteps(bn_tm v)44
 (bn_cut([S1;S2]++bn_code bb++l))=
 Some(bn_back StB l(S0::bn_Fword++[S3;S1])).
Proof. destruct v;intro l;destruct l;reflexivity. Qed.
Lemma b38_cut_B : forall v l,csteps(bn_tm v)5
 (bn_cut(bn_code bb++l))=Some(bn_cut([S1;S2;S1;S2]++l)).
Proof. destruct v;intro l;reflexivity. Qed.
Lemma b38_header_twelve : forall v l,csteps(bn_tm v)5
 (bn_cut([S1;S2;S1;S2]++l))=
 Some(bn_back StB l(S0::b38_RL)).
Proof. destruct v;intro l;destruct l;reflexivity. Qed.
Lemma b38_RL_step : forall v l,csteps(bn_tm v)5
 (bn_at StA l S3 b38_RL)=Some(bn_back StB l[S0;S3;S1;S3;S1]).
Proof. destruct v;intro l;destruct l;reflexivity. Qed.
Lemma b38_last_finish : forall v l,csteps(bn_tm v)9
 (bn_at StA l S3[S3;S1;S3;S1])=Some(bn_cut(bn_code ba++l)).
Proof. destruct v;intro l;reflexivity. Qed.
Lemma b38_R0_to_L : forall ts v,
 csteps(bn_tm v)(137+bn_cost ts+bn_cost(bn_F ts))
 (bn_at StA(bn_enc ts++[S3])S3 b38_R0)=
 Some(b38_L v(bn_F(bn_F ts))).
Proof.
 intros ts v;replace(137+bn_cost ts+bn_cost(bn_F ts))with
 (75+(bn_cost ts+(3+(2+(44+(bn_cost(bn_F ts)+(3+(5+5))))))))by lia.
 rewrite csteps_add,b38_R0_step,csteps_add,bn_normalize,csteps_add,bn_right_b.
 rewrite csteps_add,b38_three_finish,csteps_add,b38_header_B,csteps_add,bn_normalize.
 rewrite csteps_add,b38_pair_finish,csteps_add,b38_cut_B,b38_header_twelve;reflexivity.
Qed.
Lemma b38_L_AA : forall ts v,
 csteps(bn_tm v)(110+bn_cost ts+bn_cost(bn_F ts))(b38_L v(ba::ba::ts))=
 Some(bn_cut(bn_code ba++bn_enc(bn_F(bn_F ts))++[S3])).
Proof.
 intros ts v;replace(110+bn_cost ts+bn_cost(bn_F ts))with
 (29+(bn_cost(ba::ts)+(5+(29+(bn_cost(bn_F ts)+9)))))by (cbn[bn_cost];lia).
 unfold b38_L.
 change(csteps(bn_tm v)(29+(bn_cost(ba::ts)+(5+(29+(bn_cost(bn_F ts)+9)))))
 (bn_back StB(bn_code ba++(bn_enc(ba::ts)++[S3]))(S0::b38_RL))=
 Some(bn_cut(bn_code ba++bn_enc(bn_F(bn_F ts))++[S3]))).
 rewrite csteps_add,bn_left_a,csteps_add,bn_normalize.
 rewrite csteps_add,b38_RL_step,csteps_add.
 change(csteps(bn_tm v)(29+(bn_cost(bn_F ts)+9))
 (bn_back StB(bn_code ba++(bn_enc(bn_F ts)++[S3]))[S0;S3;S1;S3;S1])=
 Some(bn_cut(bn_code ba++bn_enc(bn_F(bn_F ts))++[S3]))).
 pose proof(bn_left_a v(bn_enc(bn_F ts)++[S3])[S3;S1;S3;S1])as H.
 cbn[app]in H;rewrite csteps_add,H,csteps_add,bn_normalize,b38_last_finish;reflexivity.
Qed.
Lemma b38_F3_AA : forall ts,exists ys,bn_F(bn_F(bn_F ts))=ba::ba::ys.
Proof.
 intro ts;induction ts as[|t ts IH].
 - exists[ba;bc];reflexivity.
 - destruct t;cbn[bn_F].
   + destruct IH as(ys&E);rewrite E;exists(ba::ys);reflexivity.
   + exists(bb::bn_F ts);reflexivity.
   + exists(bc::bn_F ts);reflexivity.
   + exists(bd::bn_F ts);reflexivity.
Qed.

Definition b14_tm:=bn_tm bn_LeftZero.
Definition b14_RB:=[S3;S1;S3;S3;S1;S3;S1;S3;S3;S1].
Definition b14_main ts:=bn_cut(bn_enc ts++[S3]).
Lemma b14_first_A : forall l,csteps b14_tm 54(bn_cut(bn_code ba++l))=
 Some(bn_back StB l(S0::b38_R0)).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b14_header_AB : forall l,csteps b14_tm 239(bn_cut(bn_enc[ba;bb]++l))=
 Some(bn_back StB l(S0::bn_Fword++b14_RB)).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b14_finish_AB : forall l,csteps b14_tm 115(bn_at StA l S3 b14_RB)=
 Some(bn_cut(bn_enc[ba;ba;bc]++l)).
Proof. reflexivity. Qed.
Lemma b14_header_AD : forall l,csteps b14_tm 218(bn_cut(bn_enc[ba;bd]++l))=
 Some(bn_back StB l(S0::bn_Fword++b14_RB++[S3;S3])).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b14_middle_AD : forall l,csteps b14_tm 283
 (bn_at StA l S3(b14_RB++[S3;S3]))=
 Some(bn_back StB l(S0::bn_Fword++b14_RB++[S3;S1])).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b14_finish_AD : forall l,csteps b14_tm 21
 (bn_at StA l S3(b14_RB++[S3;S1]))=
 Some(bn_cut(bn_enc[ba;ba;bb]++l)).
Proof. reflexivity. Qed.
Lemma b14_AB : forall ts,csteps b14_tm(354+bn_cost ts)(b14_main(ba::bb::ts))=
 Some(b14_main(ba::ba::bc::bn_F ts)).
Proof.
 intro ts;replace(354+bn_cost ts)with(239+(bn_cost ts+115))by lia.
 unfold b14_main;change(csteps b14_tm(239+(bn_cost ts+115))
 (bn_cut(bn_enc[ba;bb]++(bn_enc ts++[S3])))=
 Some(bn_cut(bn_enc[ba;ba;bc]++(bn_enc(bn_F ts)++[S3])))).
 rewrite csteps_add,b14_header_AB,csteps_add;unfold b14_tm;rewrite bn_normalize;apply b14_finish_AB.
Qed.
Lemma b14_AD : forall ts,csteps b14_tm(522+bn_cost ts+bn_cost(bn_F ts))(b14_main(ba::bd::ts))=
 Some(b14_main(ba::ba::bb::bn_F(bn_F ts))).
Proof.
 intro ts;replace(522+bn_cost ts+bn_cost(bn_F ts))with(218+(bn_cost ts+(283+(bn_cost(bn_F ts)+21))))by lia.
 unfold b14_main;change(csteps b14_tm(218+(bn_cost ts+(283+(bn_cost(bn_F ts)+21))))
 (bn_cut(bn_enc[ba;bd]++(bn_enc ts++[S3])))=
 Some(bn_cut(bn_enc[ba;ba;bb]++(bn_enc(bn_F(bn_F ts))++[S3])))).
 rewrite csteps_add,b14_header_AD,csteps_add;unfold b14_tm;rewrite bn_normalize.
 rewrite csteps_add,b14_middle_AD,csteps_add,bn_normalize;apply b14_finish_AD.
Qed.
Lemma b14_AA_to_L : forall ts,csteps b14_tm
 (220+bn_cost ts+bn_cost(bn_F ts)+bn_cost(bn_F(bn_F ts)))(b14_main(ba::ba::ts))=
 Some(b38_L bn_LeftZero(bn_F(bn_F(bn_F ts)))).
Proof.
 intro ts;replace(220+bn_cost ts+bn_cost(bn_F ts)+bn_cost(bn_F(bn_F ts)))with
 (54+(29+(bn_cost ts+(137+bn_cost(bn_F ts)+bn_cost(bn_F(bn_F ts))))))by lia.
 unfold b14_main;change(csteps b14_tm
 (54+(29+(bn_cost ts+(137+bn_cost(bn_F ts)+bn_cost(bn_F(bn_F ts))))))
 (bn_cut(bn_code ba++(bn_code ba++(bn_enc ts++[S3]))))=
 Some(b38_L bn_LeftZero(bn_F(bn_F(bn_F ts))))).
 rewrite csteps_add,b14_first_A,csteps_add;unfold b14_tm;rewrite bn_left_a,csteps_add,bn_normalize.
 apply b38_R0_to_L.
Qed.
Lemma b14_single_A : csteps b14_tm 444(b14_main[ba])=Some(b14_main[ba;bd;ba;bb]).
Proof. reflexivity. Qed.
Inductive b14_valid : list bn_token->Prop:=
 |b14_valid_end : b14_valid[ba]
 |b14_valid_AB : forall ts,b14_valid(ba::bb::ts)
 |b14_valid_AD : forall ts,b14_valid(ba::bd::ts)
 |b14_valid_AA : forall ts,b14_valid(ba::ba::ts).
Lemma b14_F2_valid : forall ts,b14_valid(ba::bn_F(bn_F ts)).
Proof. intros[|[]ts];constructor. Qed.
Theorem b14_closed : forall ts,b14_valid ts->
 exists k ts',0<k /\b14_valid ts' /\csteps b14_tm k(b14_main ts)=Some(b14_main ts').
Proof.
 intros ts H;destruct H.
 - exists 444,[ba;bd;ba;bb];split;[lia|];split;[constructor|apply b14_single_A].
 - exists(354+bn_cost ts),(ba::ba::bc::bn_F ts);split;[lia|];split;[constructor|apply b14_AB].
 - exists(522+bn_cost ts+bn_cost(bn_F ts)),(ba::ba::bb::bn_F(bn_F ts));split;[lia|];split;[constructor|apply b14_AD].
 - destruct(b38_F3_AA ts)as(ys&E).
   exists((220+bn_cost ts+bn_cost(bn_F ts)+bn_cost(bn_F(bn_F ts)))+
   (110+bn_cost ys+bn_cost(bn_F ys))),(ba::bn_F(bn_F ys)).
   split;[lia|];split;[apply b14_F2_valid|].
   rewrite csteps_add,b14_AA_to_L,E;apply b38_L_AA.
Qed.
Lemma b14_blank_entry : csteps b14_tm 56 c0=Some(b14_main[ba;bb]).
Proof. reflexivity. Qed.
Theorem b14_returns : forall N,exists t ts,N<=t /\b14_valid ts /\csteps b14_tm t c0=Some(b14_main ts).
Proof.
 intro N;induction N as[|N IH].
 - exists 56,[ba;bb];split;[lia|];split;[constructor|apply b14_blank_entry].
 - destruct IH as(t&ts&Ht&Hv&E);destruct(b14_closed ts Hv)as(k&ts'&Hk&Hv'&E').
   exists(t+k),ts';split;[lia|];split;[exact Hv'|];rewrite csteps_add,E;exact E'.
Qed.
Theorem b14_nonhalt : NonHalt b14_tm.
Proof. apply ore_total_nonhalt;intros q h;destruct q,h;eexists;reflexivity. Qed.
Theorem b14_A_recurrent : forall N,exists t,N<=t /\VisitsAt b14_tm StA t.
Proof.
 intro N;destruct(b14_returns N)as(t&ts&Ht&Hv&E);exists t;split;[exact Ht|].
 exists(lift(b14_main ts));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem b14_B_recurrent : forall N,exists t,N<=t /\VisitsAt b14_tm StB t.
Proof.
 intro N;destruct(b14_returns N)as(t&ts&Ht&Hv&E);exists(t+1);split;[lia|].
 exists(lift(bn_back StB(bn_enc ts++[S3])[S1]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem b14_state_zero : QHBound 0 b14_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(b14_A_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(b14_B_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem b14_sound : NonHalt b14_tm /\QHBound 0 b14_tm.
Proof. split;[apply b14_nonhalt|apply b14_state_zero]. Qed.
Print Assumptions b14_sound.
