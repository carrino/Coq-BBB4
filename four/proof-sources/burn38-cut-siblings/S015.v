(** S015 keeps the [ab] main prefix and applies the shared normalizer twice. *)
From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement Spec CTape Census OneStateReach TotalCompletion.
From BBB24Burn38S015Normalizer Require Import Normalizer.
Import ListNotations.
Definition b15_tm:=bn_tm bn_RightZero.
Definition b15_main ts:=bn_cut(bn_enc[ba;bb]++bn_enc ts++[S3]).
Lemma b15_first_header : forall l,csteps b15_tm 191
 (bn_cut(bn_enc[ba;bb]++l))=
 Some(bn_back StB l(S0::bn_Fword++bn_Jword++bn_Jword++[S3])).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b15_middle_finish : forall l,csteps b15_tm 2
 (bn_at StA l S3[S3])=Some(bn_cut([S1;S2]++l)).
Proof. reflexivity. Qed.
Lemma b15_second_header : forall l,csteps b15_tm 161
 (bn_cut([S1;S2]++bn_code bb++bn_code bb++l))=
 Some(bn_back StB l(S0::bn_Fword++bn_Jword++bn_Jword++[S1])).
Proof. intro l;destruct l;reflexivity. Qed.
Lemma b15_last_finish : forall l,csteps b15_tm 6
 (bn_at StA(bn_code bb++bn_code bb++l)S3[S1])=
 Some(bn_cut(bn_enc[ba;bb]++l)).
Proof. reflexivity. Qed.
Theorem b15_cycle : forall ts,csteps b15_tm(372+bn_cost ts+bn_cost(bn_F ts))
 (b15_main ts)=Some(b15_main(bn_F(bn_F ts))).
Proof.
 intro ts;unfold b15_main.
 replace(372+bn_cost ts+bn_cost(bn_F ts))with
 (191+(bn_cost ts+(6+(2+(161+(bn_cost(bn_F ts)+(6+6)))))))by lia.
 rewrite csteps_add,b15_first_header,csteps_add.
 unfold b15_tm;rewrite bn_normalize,csteps_add,bn_right_bb,csteps_add.
 change(csteps b15_tm(2+(161+(bn_cost(bn_F ts)+(6+6))))
 (bn_at StA(bn_code bb++bn_code bb++(bn_enc(bn_F ts)++[S3]))S3[S3])=
 Some(bn_cut(bn_enc[ba;bb]++bn_enc(bn_F(bn_F ts))++[S3]))).
 rewrite csteps_add,b15_middle_finish,csteps_add,b15_second_header,csteps_add.
 unfold b15_tm;rewrite bn_normalize,csteps_add,bn_right_bb.
 apply b15_last_finish.
Qed.
Lemma b15_blank_entry : csteps b15_tm 56 c0=Some(b15_main[]).
Proof. reflexivity. Qed.
Theorem b15_returns : forall N,exists t ts,N<=t /\csteps b15_tm t c0=Some(b15_main ts).
Proof.
 intro N;induction N as[|N IH].
 - exists 56,[];split;[lia|apply b15_blank_entry].
 - destruct IH as(t&ts&Ht&E);exists(t+(372+bn_cost ts+bn_cost(bn_F ts))),(bn_F(bn_F ts)).
   split;[lia|];rewrite csteps_add,E;apply b15_cycle.
Qed.
Theorem b15_nonhalt : NonHalt b15_tm.
Proof. apply ore_total_nonhalt;intros q h;destruct q,h;eexists;reflexivity. Qed.
Theorem b15_A_recurrent : forall N,exists t,N<=t /\VisitsAt b15_tm StA t.
Proof.
 intro N;destruct(b15_returns N)as(t&ts&Ht&E).
 exists t;split;[exact Ht|];exists(lift(b15_main ts));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem b15_B_recurrent : forall N,exists t,N<=t /\VisitsAt b15_tm StB t.
Proof.
 intro N;destruct(b15_returns N)as(t&ts&Ht&E).
 exists(t+1);split;[lia|].
 exists(lift(bn_back StB(bn_enc[ba;bb]++bn_enc ts++[S3])[S1]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem b15_state_zero : QHBound 0 b15_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(b15_A_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(b15_B_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem b15_sound : NonHalt b15_tm /\QHBound 0 b15_tm.
Proof. split;[apply b15_nonhalt|apply b15_state_zero]. Qed.
Print Assumptions b15_sound.
