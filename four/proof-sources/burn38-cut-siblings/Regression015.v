From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn38S015Normalizer Require Import Normalizer S015.
Import ListNotations.
Fixpoint br31 n:=match n with 0=>[]|S n=>S3::S1::br31 n end.
Lemma br31_add : forall n m,br31(n+m)=br31 n++br31 m.
Proof. induction n;intro m;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma br31_shift : forall n r,br31 n++S3::S1::r=S3::S1::(br31 n++r).
Proof. induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.
Definition br_G:=[S0;S1;S2;S0;S1;S2].
Definition br_T:=[S1;S3;S3;S1;S3;S3;S1;S2].
Fixpoint br_emit n:=match n with 0=>[]|S n=>br_T++br_emit n end.
Lemma br_emit_shift : forall n l,br_emit n++br_T++l=br_T++br_emit n++l.
Proof. induction n;intro l;[reflexivity|].
 change(br_T++br_emit n++br_T++l=br_T++br_T++br_emit n++l);now rewrite IHn. Qed.
Lemma br_cut_boot : forall v l r,csteps(bn_tm v)3(StA,(S1::S2::l,S0,r))=
 Some(bn_back StB l(S0::S3::S1::r)).
Proof. destruct v;intros l r;destruct l;reflexivity. Qed.
Lemma br_scan13_one : forall v l r,csteps(bn_tm v)6(bn_back StB(S1::S3::l)(S0::r))=
 Some(bn_back StB l(S0::S3::S1::r)).
Proof. destruct v;intros l r;destruct l;reflexivity. Qed.
Lemma br_right_step : forall v l r,csteps(bn_tm v)168
 (StA,(br_G++l,S3,br31 4++r))=Some(StA,(br_G++br_T++l,S3,r)).
Proof. destruct v;intros l r;reflexivity. Qed.
Lemma br_right_scan : forall n v l r,csteps(bn_tm v)(168*n)
 (StA,(br_G++l,S3,br31(4*n)++r))=Some(StA,(br_G++br_emit n++l,S3,r)).
Proof.
 induction n;intros v l r;[reflexivity|].
 replace(168*S n)with(168+168*n)by lia.
 replace(4*S n)with(4+4*n)by lia;rewrite br31_add,<-app_assoc,csteps_add,br_right_step.
 rewrite IHn,br_emit_shift;reflexivity.
Qed.
Fixpoint br13 n := match n with 0=>[]|S n=>S1::S3::br13 n end.
Theorem br_scan13 : forall n v l r,csteps(bn_tm v)(6*n)
 (bn_back StB(br13 n++l)(S0::r))=Some(bn_back StB l(S0::br31 n++r)).
Proof.
 induction n;intros v l r;[reflexivity|].
 replace(6*S n)with(6+6*n)by lia;cbn[br13 app].
 rewrite csteps_add,br_scan13_one,IHn,br31_shift;reflexivity.
Qed.
Definition br_H := [S1;S3;S3;S1;S2;S0;S1;S2;S3].
Theorem br_right_header : forall v r,csteps(bn_tm v)209
 (StB,([],S3,S0::br31 4++r))=Some(StA,(br_G++br_H,S3,r)).
Proof. destruct v;intro r;reflexivity. Qed.
Definition br_bad_paired (v:bn_variant) n := bn_cut(S1::S2::br13(4*n+3)++[S3]).
Theorem br_bad_paired_escape : forall n v,csteps(bn_tm v)(192*n+231)(br_bad_paired v n)=
 Some(StB,(S2::br_G++br_emit n++br_H,S0,[])).
Proof.
 intros n v;unfold br_bad_paired,bn_cut,bn_at.
 replace(192*n+231)with(3+(6*(4*n+3)+(209+(168*n+1))))by lia.
 rewrite csteps_add,br_cut_boot,csteps_add,br_scan13.
 assert(Hpair:br31(4*n+3)++[S3;S1]=br31(4+4*n)).
 {replace(4+4*n)with((4*n+3)+1)by lia;rewrite(br31_add(4*n+3)1);reflexivity. }
 cbn[app]in Hpair.
 change(csteps(bn_tm v)(209+(168*n+1))
 (StB,([],S3,S0::(br31(4*n+3)++[S3;S1])))=
 Some(StB,(S2::br_G++br_emit n++br_H,S0,[]))).
 rewrite Hpair,(br31_add 4(4*n)),csteps_add,br_right_header,csteps_add.
 rewrite <-(app_nil_r(br31(4*n)))at 1;rewrite br_right_scan;reflexivity.
Qed.
Lemma br_repeat_shift : forall(x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Theorem br_B_drift : forall n v l,csteps(bn_tm v)n(StB,(l,S0,[]))=
 Some(StB,(repeat S3 n++l,S0,[])).
Proof.
 induction n;intros v l;[reflexivity|].
 change(csteps(bn_tm v)n(StB,(S3::l,S0,[]))=Some(StB,(S3::(repeat S3 n++l),S0,[]))).
 rewrite IHn,br_repeat_shift;reflexivity.
Qed.
Theorem br_bad_paired_forever : forall n v t,csteps(bn_tm v)(192*n+231+t)(br_bad_paired v n)=
 Some(StB,(repeat S3 t++S2::br_G++br_emit n++br_H,S0,[])).
Proof. intros n v t;rewrite csteps_add,br_bad_paired_escape;apply br_B_drift. Qed.

Example b15_reg_blank : csteps b15_tm 56 c0=Some(b15_main[]).
Proof. exact b15_blank_entry. Qed.
Example b15_reg_cycle_empty : csteps b15_tm 450(b15_main[])=Some(b15_main[ba;bd]).
Proof. exact(b15_cycle[]). Qed.
Example b15_reg_cycle_a : csteps b15_tm 526(b15_main[ba])=Some(b15_main[ba;ba;bd]).
Proof. exact(b15_cycle[ba]). Qed.
Example b15_reg_cycle_b : csteps b15_tm 428(b15_main[bb])=Some(b15_main[ba;ba;bc]).
Proof. exact(b15_cycle[bb]). Qed.
Example b15_reg_cycle_c : csteps b15_tm 438(b15_main[bc])=Some(b15_main[bd;ba;bb]).
Proof. exact(b15_cycle[bc]). Qed.
Example b15_reg_cycle_d : csteps b15_tm 550(b15_main[bd])=Some(b15_main[ba;ba;bb;ba;bb]).
Proof. exact(b15_cycle[bd]). Qed.
Example bn_reg_empty_left_guard : forall v,
 csteps(bn_tm v)31(bn_back StB[S3](S0::bn_Fword))=
 Some(StB,(S2::(bn_enc[ba;bb]++[S3]),S0,[])).
Proof. destruct v;reflexivity. Qed.
Print Assumptions b15_sound.
Print Assumptions br_bad_paired_forever.
