(** S016: copied generic continuations plus isolated RightOne closure. *)
From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement Spec CTape Census OneStateReach TotalCompletion.
From BBB24Burn42S016 Require Import Normalizer.
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
Definition b16_tm:=bn_tm bn_RightOne.
Definition b16_C ts:=bn_cut(bn_enc ts++[S3]).
Definition b16_C12 ts:=bn_cut([S1;S2]++bn_enc ts++[S3]).
Definition b16_A ts r:=bn_at StA(bn_enc ts++[S3])S3 r.
Definition b16_H ts:=bn_back StB(bn_enc ts++[S3])[S0;S3;S1;S3;S1].
Definition b16_L ts:=b38_L bn_RightOne ts.
Definition b16_M ts:=bn_back StB(bn_enc ts++[S3])[S0;S3;S0;S3;S1;S3;S1].
Definition b16_K ts:=bn_back StB(bn_enc ts++[S3])[S0;S3;S3;S3;S0;S3;S1].
Inductive b16_valid:list bn_token->Prop:=
 |b16_valid_A:forall ts,b16_valid(ba::ts)
 |b16_valid_D:forall ts,b16_valid(bd::ts).
Definition b16_image ts:=exists ys,ts=ba::ys \/ts=bb::ys \/ts=bd::ys.
Lemma b16_F_image : forall ts,b16_image(bn_F ts).
Proof.
 intros[|t ts];unfold b16_image;[exists[bb];auto|].
 destruct t;cbn[bn_F];eexists;auto.
Qed.
Definition b16_reaches cc:=exists k ts,b16_valid ts /\csteps b16_tm k cc=Some(b16_C ts).
Lemma b16_done : forall ts,b16_valid ts->b16_reaches(b16_C ts).
Proof. intros ts H;exists 0,ts;split;[exact H|reflexivity]. Qed.
Lemma b16_after : forall n cc cc',csteps b16_tm n cc=Some cc'->b16_reaches cc'->b16_reaches cc.
Proof. intros n cc cc' E(k&ts&Hv&Ek);exists(n+k),ts;split;[exact Hv|];rewrite csteps_add,E;exact Ek. Qed.
Lemma b16_CA : forall l,csteps b16_tm 120(bn_cut([S1;S3;S3;S1;S2]++l))=Some(bn_back StB l[S0;S3;S1;S3;S1;S3;S1;S3;S3;S0;S3;S1]).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_CD : forall l,csteps b16_tm 183(bn_cut([S1;S3;S3;S1;S3;S3;S1;S2]++l))=Some(bn_back StB l[S0;S3;S1;S3;S1;S3;S3;S1;S3;S3;S3;S3;S0;S3;S1]).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_toK : forall l,csteps b16_tm 3(bn_at StA l S3[S1;S3;S3;S0;S3;S1])=Some(bn_back StB l[S0;S3;S3;S3;S0;S3;S1]).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_KA : forall l,csteps b16_tm 29(bn_back StB([S1;S3;S3;S1;S2]++l)[S0;S3;S3;S3;S0;S3;S1])=Some(bn_back StB l[S0;S3;S1;S3;S1;S3;S3;S3;S3;S0;S3;S1]).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_KB : forall l,csteps b16_tm 37(bn_back StB([S0;S1;S2]++l)[S0;S3;S3;S3;S0;S3;S1])=Some(bn_back StB l[S0;S3;S1;S3;S1;S3;S3;S1;S3;S1]).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_KD : forall l,csteps b16_tm 98(bn_back StB([S1;S3;S3;S1;S3;S3;S1;S2]++l)[S0;S3;S3;S3;S0;S3;S1])=Some(bn_back StB l[S0;S3;S1;S3;S1;S3;S3;S1;S3;S3;S0;S3;S1;S3;S1]).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_toM : forall l,csteps b16_tm 9(bn_at StA l S3[S3;S3;S3;S0;S3;S1])=Some(bn_back StB l[S0;S3;S0;S3;S1;S3;S1]).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_MA : forall l,csteps b16_tm 29(bn_back StB([S1;S3;S3;S1;S2]++l)[S0;S3;S0;S3;S1;S3;S1])=Some(bn_back StB l[S0;S3;S1;S3;S1;S3;S3;S0;S3;S1;S3;S1]).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_MB : forall l,csteps b16_tm 69(bn_back StB([S0;S1;S2]++l)[S0;S3;S0;S3;S1;S3;S1])=Some(bn_back StB l[S0;S3;S1;S3;S1;S3;S3;S1;S3;S3]).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_MD : forall l,csteps b16_tm 94(bn_back StB([S1;S3;S3;S1;S3;S3;S1;S2]++l)[S0;S3;S0;S3;S1;S3;S1])=Some(bn_back StB l[S0;S3;S1;S3;S1;S3;S3;S1;S3;S3;S1;S3;S1;S3;S1]).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_HA : forall l,csteps b16_tm 29(bn_back StB([S1;S3;S3;S1;S2]++l)[S0;S3;S1;S3;S1])=Some(bn_back StB l[S0;S3;S1;S3;S1;S3;S3;S1;S3;S1]).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_HB : forall l,csteps b16_tm 10(bn_back StB([S0;S1;S2]++l)[S0;S3;S1;S3;S1])=Some(bn_cut([S1;S3;S3;S1;S3;S3;S1;S2]++l)).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_HD : forall l,csteps b16_tm 46(bn_back StB([S1;S3;S3;S1;S3;S3;S1;S2]++l)[S0;S3;S1;S3;S1])=Some(bn_cut([S1;S3;S3;S1;S2;S1;S3;S3;S1;S2;S3;S1;S2]++l)).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_LA : forall l,csteps b16_tm 29(bn_back StB([S1;S3;S3;S1;S2]++l)[S0;S3;S0;S3;S1])=Some(bn_back StB l[S0;S3;S1;S3;S1;S3;S3;S0;S3;S1]).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_LB : forall l,csteps b16_tm 14(bn_back StB([S0;S1;S2]++l)[S0;S3;S0;S3;S1])=Some(bn_cut([S1;S3;S3;S1;S2;S3;S1;S2]++l)).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_LD : forall l,csteps b16_tm 94(bn_back StB([S1;S3;S3;S1;S3;S3;S1;S2]++l)[S0;S3;S0;S3;S1])=Some(bn_back StB l[S0;S3;S1;S3;S1;S3;S3;S1;S3;S3;S1;S3;S1]).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_RLD : forall l,csteps b16_tm 12(bn_at StA l S3[S3;S1;S3;S3;S1;S3;S1])=Some(bn_cut([S1;S3;S3;S1;S2;S0;S1;S2]++l)).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_C12A : forall l,csteps b16_tm 32(bn_cut([S1;S2;S1;S3;S3;S1;S2]++l))=Some(bn_back StB l[S0;S3;S1;S3;S1;S3;S3;S1]).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_C12D : forall l,csteps b16_tm 43(bn_cut([S1;S2;S1;S3;S3;S1;S3;S3;S1;S2]++l))=Some(bn_cut([S0;S1;S2;S1;S3;S3;S1;S2;S3;S1;S2]++l)).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_CBL : forall l,csteps b16_tm 10(bn_cut([S0;S1;S2]++l))=Some(bn_back StB l[S0;S3;S0;S3;S1]).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_oneA : forall l,csteps b16_tm 32(bn_at StA([S1;S3;S3;S1;S2]++l)S3[S1])=Some(bn_back StB l[S0;S3;S1;S3;S1;S3;S3]).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_oneB : forall l,csteps b16_tm 6(bn_at StA([S0;S1;S2]++l)S3[S1])=Some(bn_cut([S1;S3;S3;S1;S2]++l)).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_oneD : forall l,csteps b16_tm 42(bn_at StA([S1;S3;S3;S1;S3;S3;S1;S2]++l)S3[S1])=Some(bn_cut([S1;S2;S1;S3;S3;S1;S2;S3;S1;S2]++l)).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_RB5 : forall l,csteps b16_tm 5(bn_at StA l S3[S3;S1;S3;S3])=Some(bn_cut([S1;S2;S0;S1;S2]++l)).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_RD56 : forall l,csteps b16_tm 56(bn_at StA l S3[S3;S1;S3;S3;S1;S3;S1;S3;S1])=Some(bn_cut([S1;S2;S1;S3;S3;S1;S3;S3;S1;S2]++l)).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_RC81 : forall l,csteps b16_tm 81(bn_at StA l S3[S3;S1;S3;S3;S3;S3;S0;S3;S1])=Some(bn_back StB l[S0;S3;S1;S3;S1;S3;S3;S1;S3;S3]).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_KD115 : forall l,csteps b16_tm 115
 (bn_at StA l S3[S3;S1;S3;S3;S0;S3;S1;S3;S1])=
 Some(bn_back StB l[S0;S3;S1;S3;S1;S3;S3;S1;S3;S3;S1]).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_KD6 : forall l,csteps b16_tm 6
 (bn_at StA l S3[S3;S1;S3;S3;S1])=Some(bn_cut(bn_code bb++bn_code bb++l)).
Proof. reflexivity. Qed.
Lemma b16_normalize : forall ts r,csteps b16_tm(bn_cost ts)
 (bn_back StB(bn_enc ts++[S3])(S0::S3::S1::S3::S1::S3::r))=
 Some(bn_at StA(bn_enc(bn_F ts)++[S3])S3 r).
Proof. intros ts r;apply bn_normalize. Qed.
Lemma b16_MA5 : forall l,csteps b16_tm 5(bn_at StA l S3[S3;S0;S3;S1;S3;S1])=
 Some(bn_back StB l[S0;S3;S1;S3;S1;S3;S1]).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b16_pair_finish : forall l,csteps b16_tm 3(bn_at StA l S3[S3;S1])=Some(bn_cut(bn_code bb++l)).
Proof. apply(b38_pair_finish bn_RightOne). Qed.
Lemma b16_header_B : forall l,csteps b16_tm 44(bn_cut([S1;S2]++bn_code bb++l))=
 Some(bn_back StB l[S0;S3;S1;S3;S1;S3;S3;S1]).
Proof. apply(b38_header_B bn_RightOne). Qed.
Lemma b16_H_A_reaches : forall ts,b16_reaches(b16_H(ba::ts)).
Proof.
 intro ts;eapply b16_after with(n:=38+bn_cost ts)(cc':=b16_C(ba::bn_F ts)).
 - replace(38+bn_cost ts)with(29+(bn_cost ts+9))by lia;unfold b16_H,b16_C.
   change(csteps b16_tm(29+(bn_cost ts+9))(bn_back StB(bn_code ba++(bn_enc ts++[S3]))[S0;S3;S1;S3;S1])=
   Some(bn_cut(bn_code ba++(bn_enc(bn_F ts)++[S3])))).
   rewrite csteps_add,b16_HA,csteps_add;rewrite b16_normalize;apply b38_last_finish.
 - apply b16_done;constructor.
Qed.
Lemma b16_H_B_reaches : forall ts,b16_reaches(b16_H(bb::ts)).
Proof.
 intro ts;eapply b16_after with(n:=10)(cc':=b16_C(bd::ts));[apply b16_HB|apply b16_done;constructor].
Qed.
Lemma b16_H_D_reaches : forall ts,b16_reaches(b16_H(bd::ts)).
Proof.
 intro ts;eapply b16_after with(n:=46)(cc':=b16_C(ba::ba::bc::ts));[apply b16_HD|apply b16_done;constructor].
Qed.
Lemma b16_H_F_reaches : forall ts,b16_reaches(b16_H(bn_F ts)).
Proof.
 intro ts;destruct(b16_F_image ts)as(ys&[E|[E|E]]);rewrite E;
 [apply b16_H_A_reaches|apply b16_H_B_reaches|apply b16_H_D_reaches].
Qed.
Lemma b16_L_A_header : forall ts,csteps b16_tm(34+bn_cost ts)(b16_L(ba::ts))=Some(b16_H(bn_F ts)).
Proof.
 intro ts;replace(34+bn_cost ts)with(29+(bn_cost ts+5))by lia;unfold b16_L,b38_L,b16_H.
 change(csteps b16_tm(29+(bn_cost ts+5))(bn_back StB(bn_code ba++(bn_enc ts++[S3]))(S0::b38_RL))=
 Some(bn_back StB(bn_enc(bn_F ts)++[S3])[S0;S3;S1;S3;S1])).
 rewrite csteps_add,b16_LA,csteps_add;rewrite b16_normalize;apply b38_RL_step.
Qed.
Lemma b16_L_A_reaches : forall ts,b16_reaches(b16_L(ba::ts)).
Proof. intro ts;eapply b16_after;[apply b16_L_A_header|apply b16_H_F_reaches]. Qed.
Lemma b16_L_B_reaches : forall ts,b16_reaches(b16_L(bb::ts)).
Proof.
 intro ts;eapply b16_after with(n:=14)(cc':=b16_C(ba::bc::ts));[apply b16_LB|apply b16_done;constructor].
Qed.
Lemma b16_L_D_reaches : forall ts,b16_reaches(b16_L(bd::ts)).
Proof.
 intro ts;eapply b16_after with(n:=106+bn_cost ts)(cc':=b16_C(ba::bb::bn_F ts)).
 - replace(106+bn_cost ts)with(94+(bn_cost ts+12))by lia;unfold b16_L,b38_L,b16_C.
   change(csteps b16_tm(94+(bn_cost ts+12))(bn_back StB(bn_code bd++(bn_enc ts++[S3]))(S0::b38_RL))=
   Some(bn_cut(bn_enc[ba;bb]++(bn_enc(bn_F ts)++[S3])))).
   rewrite csteps_add,b16_LD,csteps_add;rewrite b16_normalize;apply b16_RLD.
 - apply b16_done;constructor.
Qed.
Lemma b16_L_F_reaches : forall ts,b16_reaches(b16_L(bn_F ts)).
Proof.
 intro ts;destruct(b16_F_image ts)as(ys&[E|[E|E]]);rewrite E;
 [apply b16_L_A_reaches|apply b16_L_B_reaches|apply b16_L_D_reaches].
Qed.
Lemma b16_C12_A_header : forall ts,csteps b16_tm(45+bn_cost ts)(b16_C12(ba::ts))=Some(b16_L(bn_F ts)).
Proof.
 intro ts;replace(45+bn_cost ts)with(32+(bn_cost ts+(3+10)))by lia;unfold b16_C12,b16_L,b38_L.
 change(csteps b16_tm(32+(bn_cost ts+(3+10)))(bn_cut([S1;S2;S1;S3;S3;S1;S2]++(bn_enc ts++[S3])))=
 Some(bn_back StB(bn_enc(bn_F ts)++[S3])(S0::b38_RL))).
 rewrite csteps_add,b16_C12A,csteps_add;rewrite b16_normalize,csteps_add,b16_pair_finish;apply b16_CBL.
Qed.
Lemma b16_C12_A_reaches : forall ts,b16_reaches(b16_C12(ba::ts)).
Proof. intro ts;eapply b16_after;[apply b16_C12_A_header|apply b16_L_F_reaches]. Qed.
Lemma b16_C12_B_header : forall ts,csteps b16_tm(57+bn_cost ts)(b16_C12(bb::ts))=Some(b16_L(bn_F ts)).
Proof.
 intro ts;replace(57+bn_cost ts)with(44+(bn_cost ts+(3+10)))by lia;unfold b16_C12,b16_L,b38_L.
 change(csteps b16_tm(44+(bn_cost ts+(3+10)))(bn_cut([S1;S2]++bn_code bb++(bn_enc ts++[S3])))=
 Some(bn_back StB(bn_enc(bn_F ts)++[S3])(S0::b38_RL))).
 rewrite csteps_add,b16_header_B,csteps_add;rewrite b16_normalize,csteps_add,b16_pair_finish;apply b16_CBL.
Qed.
Lemma b16_C12_B_reaches : forall ts,b16_reaches(b16_C12(bb::ts)).
Proof. intro ts;eapply b16_after;[apply b16_C12_B_header|apply b16_L_F_reaches]. Qed.
Lemma b16_C12_D_reaches : forall ts,b16_reaches(b16_C12(bd::ts)).
Proof.
 intro ts;eapply b16_after with(n:=43)(cc':=b16_C(bb::ba::bc::ts));[apply b16_C12D|].
 eapply b16_after with(n:=10)(cc':=b16_L(ba::bc::ts));[apply b16_CBL|apply b16_L_A_reaches].
Qed.
Lemma b16_C12_F_reaches : forall ts,b16_reaches(b16_C12(bn_F ts)).
Proof.
 intro ts;destruct(b16_F_image ts)as(ys&[E|[E|E]]);rewrite E;
 [apply b16_C12_A_reaches|apply b16_C12_B_reaches|apply b16_C12_D_reaches].
Qed.
Lemma b16_one_A_reaches : forall ts,b16_reaches(b16_A(ba::ts)[S1]).
Proof.
 intro ts;eapply b16_after with(n:=34+bn_cost ts)(cc':=b16_C12(bn_F ts)).
 - replace(34+bn_cost ts)with(32+(bn_cost ts+2))by lia;unfold b16_A,b16_C12.
   change(csteps b16_tm(32+(bn_cost ts+2))(bn_at StA(bn_code ba++(bn_enc ts++[S3]))S3[S1])=
   Some(bn_cut([S1;S2]++(bn_enc(bn_F ts)++[S3])))).
   rewrite csteps_add,b16_oneA,csteps_add;rewrite b16_normalize;apply b38_three_finish.
 - apply b16_C12_F_reaches.
Qed.
Lemma b16_one_B_reaches : forall ts,b16_reaches(b16_A(bb::ts)[S1]).
Proof.
 intro ts;eapply b16_after with(n:=6)(cc':=b16_C(ba::ts));[apply b16_oneB|apply b16_done;constructor].
Qed.
Lemma b16_one_D_reaches : forall ts,b16_reaches(b16_A(bd::ts)[S1]).
Proof.
 intro ts;eapply b16_after with(n:=42)(cc':=b16_C12(ba::bc::ts));[apply b16_oneD|apply b16_C12_A_reaches].
Qed.
Lemma b16_one_F_reaches : forall ts,b16_reaches(b16_A(bn_F ts)[S1]).
Proof.
 intro ts;destruct(b16_F_image ts)as(ys&[E|[E|E]]);rewrite E;
 [apply b16_one_A_reaches|apply b16_one_B_reaches|apply b16_one_D_reaches].
Qed.
Lemma b16_M_A_reaches : forall ts,b16_reaches(b16_M(ba::ts)).
Proof.
 intro ts;eapply b16_after with(n:=34+bn_cost ts+bn_cost(bn_F ts))(cc':=b16_A(bn_F(bn_F ts))[S1]).
 - replace(34+bn_cost ts+bn_cost(bn_F ts))with(29+(bn_cost ts+(5+bn_cost(bn_F ts))))by lia;unfold b16_M,b16_A.
   change(csteps b16_tm(29+(bn_cost ts+(5+bn_cost(bn_F ts))))(bn_back StB(bn_code ba++(bn_enc ts++[S3]))[S0;S3;S0;S3;S1;S3;S1])=
   Some(bn_at StA(bn_enc(bn_F(bn_F ts))++[S3])S3[S1])).
   rewrite csteps_add,b16_MA,csteps_add;rewrite b16_normalize,csteps_add,b16_MA5;apply b16_normalize.
 - apply b16_one_F_reaches.
Qed.
Lemma b16_M_B_reaches : forall ts,b16_reaches(b16_M(bb::ts)).
Proof.
 intro ts;eapply b16_after with(n:=74+bn_cost ts)(cc':=b16_C12(bb::bn_F ts)).
 - replace(74+bn_cost ts)with(69+(bn_cost ts+5))by lia;unfold b16_M,b16_C12.
   change(csteps b16_tm(69+(bn_cost ts+5))(bn_back StB(bn_code bb++(bn_enc ts++[S3]))[S0;S3;S0;S3;S1;S3;S1])=
   Some(bn_cut([S1;S2]++bn_code bb++(bn_enc(bn_F ts)++[S3])))).
   rewrite csteps_add,b16_MB,csteps_add;rewrite b16_normalize;apply b16_RB5.
 - apply b16_C12_B_reaches.
Qed.
Lemma b16_M_D_reaches : forall ts,b16_reaches(b16_M(bd::ts)).
Proof.
 intro ts;eapply b16_after with(n:=150+bn_cost ts)(cc':=b16_C12(bd::bn_F ts)).
 - replace(150+bn_cost ts)with(94+(bn_cost ts+56))by lia;unfold b16_M,b16_C12.
   change(csteps b16_tm(94+(bn_cost ts+56))(bn_back StB(bn_code bd++(bn_enc ts++[S3]))[S0;S3;S0;S3;S1;S3;S1])=
   Some(bn_cut([S1;S2]++bn_code bd++(bn_enc(bn_F ts)++[S3])))).
   rewrite csteps_add,b16_MD,csteps_add;rewrite b16_normalize;apply b16_RD56.
 - apply b16_C12_D_reaches.
Qed.
Lemma b16_M_F_reaches : forall ts,b16_reaches(b16_M(bn_F ts)).
Proof.
 intro ts;destruct(b16_F_image ts)as(ys&[E|[E|E]]);rewrite E;
 [apply b16_M_A_reaches|apply b16_M_B_reaches|apply b16_M_D_reaches].
Qed.
Lemma b16_K_A_reaches : forall ts,b16_reaches(b16_K(ba::ts)).
Proof.
 intro ts;eapply b16_after with(n:=38+bn_cost ts)(cc':=b16_M(bn_F ts)).
 - replace(38+bn_cost ts)with(29+(bn_cost ts+9))by lia;unfold b16_K,b16_M.
   change(csteps b16_tm(29+(bn_cost ts+9))(bn_back StB(bn_code ba++(bn_enc ts++[S3]))[S0;S3;S3;S3;S0;S3;S1])=
   Some(bn_back StB(bn_enc(bn_F ts)++[S3])[S0;S3;S0;S3;S1;S3;S1])).
   rewrite csteps_add,b16_KA,csteps_add;rewrite b16_normalize;apply b16_toM.
 - apply b16_M_F_reaches.
Qed.
Lemma b16_K_B_reaches : forall ts,b16_reaches(b16_K(bb::ts)).
Proof.
 intro ts;eapply b16_after with(n:=46+bn_cost ts)(cc':=b16_C(ba::bn_F ts)).
 - replace(46+bn_cost ts)with(37+(bn_cost ts+9))by lia;unfold b16_K,b16_C.
   change(csteps b16_tm(37+(bn_cost ts+9))(bn_back StB(bn_code bb++(bn_enc ts++[S3]))[S0;S3;S3;S3;S0;S3;S1])=
   Some(bn_cut(bn_code ba++(bn_enc(bn_F ts)++[S3])))).
   rewrite csteps_add,b16_KB,csteps_add;rewrite b16_normalize;apply b38_last_finish.
 - apply b16_done;constructor.
Qed.
Lemma b16_K_D_reaches : forall ts,b16_reaches(b16_K(bd::ts)).
Proof.
 intro ts;eapply b16_after with(n:=243+bn_cost ts+bn_cost(bn_F ts))(cc':=b16_C(ba::bc::bn_F(bn_F ts))).
 - replace(243+bn_cost ts+bn_cost(bn_F ts))with(98+(bn_cost ts+(115+(bn_cost(bn_F ts)+(6+(10+14))))))by lia.
   unfold b16_K,b16_C.
   change(csteps b16_tm(98+(bn_cost ts+(115+(bn_cost(bn_F ts)+(6+(10+14))))))
   (bn_back StB(bn_code bd++(bn_enc ts++[S3]))[S0;S3;S3;S3;S0;S3;S1])=
   Some(bn_cut(bn_enc[ba;bc]++(bn_enc(bn_F(bn_F ts))++[S3])))).
   rewrite csteps_add,b16_KD,csteps_add;rewrite b16_normalize,csteps_add,b16_KD115,csteps_add,b16_normalize.
   rewrite csteps_add,b16_KD6,csteps_add,b16_CBL;apply b16_LB.
 - apply b16_done;constructor.
Qed.
Lemma b16_K_F_reaches : forall ts,b16_reaches(b16_K(bn_F ts)).
Proof.
 intro ts;destruct(b16_F_image ts)as(ys&[E|[E|E]]);rewrite E;
 [apply b16_K_A_reaches|apply b16_K_B_reaches|apply b16_K_D_reaches].
Qed.
Lemma b16_C_A_header : forall ts,csteps b16_tm(123+bn_cost ts)(b16_C(ba::ts))=Some(b16_K(bn_F ts)).
Proof.
 intro ts;replace(123+bn_cost ts)with(120+(bn_cost ts+3))by lia;unfold b16_C,b16_K.
 change(csteps b16_tm(120+(bn_cost ts+3))(bn_cut(bn_code ba++(bn_enc ts++[S3])))=
 Some(bn_back StB(bn_enc(bn_F ts)++[S3])[S0;S3;S3;S3;S0;S3;S1])).
 rewrite csteps_add,b16_CA,csteps_add;rewrite b16_normalize;apply b16_toK.
Qed.
Lemma b16_C_D_header : forall ts,csteps b16_tm(269+bn_cost ts+bn_cost(bn_F ts))(b16_C(bd::ts))=Some(b16_C12(bb::bn_F(bn_F ts))).
Proof.
 intro ts;replace(269+bn_cost ts+bn_cost(bn_F ts))with(183+(bn_cost ts+(81+(bn_cost(bn_F ts)+5))))by lia;unfold b16_C,b16_C12.
 change(csteps b16_tm(183+(bn_cost ts+(81+(bn_cost(bn_F ts)+5))))(bn_cut(bn_code bd++(bn_enc ts++[S3])))=
 Some(bn_cut([S1;S2]++bn_code bb++(bn_enc(bn_F(bn_F ts))++[S3])))).
 rewrite csteps_add,b16_CD,csteps_add;rewrite b16_normalize,csteps_add,b16_RC81,csteps_add,b16_normalize;apply b16_RB5.
Qed.
Theorem b16_closed : forall ts,b16_valid ts->exists k ys,0<k /\b16_valid ys /\csteps b16_tm k(b16_C ts)=Some(b16_C ys).
Proof.
 intros ts H;destruct H.
 - destruct(b16_K_F_reaches ts)as(k&ys&Hv&E);exists(123+bn_cost ts+k),ys;split;[lia|];split;[exact Hv|].
   rewrite csteps_add,b16_C_A_header;exact E.
 - destruct(b16_C12_B_reaches(bn_F(bn_F ts)))as(k&ys&Hv&E);exists(269+bn_cost ts+bn_cost(bn_F ts)+k),ys;split;[lia|];split;[exact Hv|].
   rewrite csteps_add,b16_C_D_header;exact E.
Qed.
Lemma b16_blank_entry : csteps b16_tm 56 c0=Some(b16_C[ba;bb]).
Proof. reflexivity. Qed.
Theorem b16_returns : forall N,exists t ts,N<=t /\b16_valid ts /\csteps b16_tm t c0=Some(b16_C ts).
Proof.
 induction N as[|N IH].
 - exists 56,[ba;bb];split;[lia|];split;[constructor|apply b16_blank_entry].
 - destruct IH as(t&ts&Ht&Hv&E);destruct(b16_closed ts Hv)as(k&ys&Hk&Hy&E').
   exists(t+k),ys;split;[lia|];split;[exact Hy|];rewrite csteps_add,E;exact E'.
Qed.
Theorem b16_nonhalt : NonHalt b16_tm.
Proof. apply ore_total_nonhalt;intros q h;destruct q,h;eexists;reflexivity. Qed.
Theorem b16_A_recurrent : forall N,exists t,N<=t /\VisitsAt b16_tm StA t.
Proof.
 intro N;destruct(b16_returns N)as(t&ts&Ht&Hv&E);exists t;split;[exact Ht|].
 exists(lift(b16_C ts));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem b16_B_recurrent : forall N,exists t,N<=t /\VisitsAt b16_tm StB t.
Proof.
 intro N;destruct(b16_returns N)as(t&ts&Ht&Hv&E);exists(t+1);split;[lia|].
 exists(lift(bn_back StB(bn_enc ts++[S3])[S1]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem b16_state_zero : QHBound 0 b16_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(b16_A_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(b16_B_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem b16_sound : NonHalt b16_tm /\QHBound 0 b16_tm.
Proof. split;[apply b16_nonhalt|apply b16_state_zero]. Qed.
Print Assumptions b16_closed.
Print Assumptions b16_sound.
