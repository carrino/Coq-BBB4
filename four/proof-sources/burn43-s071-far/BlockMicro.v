(** Exact contextual microstep bridge for the 40 finite FAR block traces.
    Generated from the pinned trace table, checked by Coq reduction.
    No FAR certificate soundness or state classification is asserted here. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement CTape.
From BBB24Burn43S071FAR Require Import Programs.
Import ListNotations.
Definition c52_safe (c:cconf) : Prop :=
 match c with (StB,(_,S0,r)) => all_blank r=false | _ => True end.
Definition c52_right_ok (z:bool) (r:list Sym) : Prop :=
 all_blank r=true -> z=true.
Definition c52_safe_before (k:nat) (c:cconf) : Prop :=
 forall n, n<k -> forall d, csteps s71_tm n c=Some d -> c52_safe d.
Lemma c52_right_ok_false : forall r,
 c52_right_ok false r -> all_blank r=false.
Proof.
 intros r H;destruct(all_blank r)eqn:E;[|reflexivity].
 unfold c52_right_ok in H;specialize(H E);discriminate.
Qed.
Lemma c52_safe_no_literal_spinout : forall c,
 c52_safe c -> forall l,c<>(StB,(l,S0,[])).
Proof. intros c H l E;subst c;cbn[c52_safe all_blank]in H;discriminate. Qed.
Lemma c52_trace_00 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 5 (s71_back StA ([S0;S0]++l) r)=Some(s71_front StA ([S1;S0]++l) r) /\
 c52_safe_before 5 (s71_back StA ([S0;S0]++l) r).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_01 : forall l r,
 c52_right_ok true r ->
 csteps s71_tm 1 (s71_front StA l ([S0;S0]++r))=Some(s71_back StB l ([S1;S0]++r)) /\
 c52_safe_before 1 (s71_front StA l ([S0;S0]++r)).
Proof.
 intros l r Hctx;split;[reflexivity|].
 unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact I || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_02 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 1 (s71_back StB ([S0;S0]++l) r)=Some(s71_front StB ([S0;S0]++l) r) /\
 c52_safe_before 1 (s71_back StB ([S0;S0]++l) r).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_03 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 1 (s71_back StB ([S0;S0]++l) r)=Some(s71_front StB ([S0;S0]++l) r) /\
 c52_safe_before 1 (s71_back StB ([S0;S0]++l) r).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_04 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 1 (s71_back StA ([S1;S0]++l) r)=Some(s71_front StA ([S2;S0]++l) r) /\
 c52_safe_before 1 (s71_back StA ([S1;S0]++l) r).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_05 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 3 (s71_front StA l ([S1;S0]++r))=Some(s71_back StA l ([S0;S1]++r)) /\
 c52_safe_before 3 (s71_front StA l ([S1;S0]++r)).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_06 : forall l r,
 c52_right_ok true r ->
 csteps s71_tm 3 (s71_front StA l ([S1;S0]++r))=Some(s71_back StA l ([S0;S1]++r)) /\
 c52_safe_before 3 (s71_front StA l ([S1;S0]++r)).
Proof.
 intros l r Hctx;split;[reflexivity|].
 unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact I || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact I || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact I || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_07 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 3 (s71_back StB ([S1;S0]++l) r)=Some(s71_front StA ([S1;S0]++l) r) /\
 c52_safe_before 3 (s71_back StB ([S1;S0]++l) r).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_08 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 1 (s71_front StB l ([S1;S0]++r))=Some(s71_back StB l ([S3;S0]++r)) /\
 c52_safe_before 1 (s71_front StB l ([S1;S0]++r)).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_09 : forall l r,
 c52_right_ok true r ->
 csteps s71_tm 1 (s71_front StB l ([S1;S0]++r))=Some(s71_back StB l ([S3;S0]++r)) /\
 c52_safe_before 1 (s71_front StB l ([S1;S0]++r)).
Proof.
 intros l r Hctx;split;[reflexivity|].
 unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact I || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_10 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 2 (s71_front StA l ([S3;S0]++r))=Some(s71_front StB ([S0;S2]++l) r) /\
 c52_safe_before 2 (s71_front StA l ([S3;S0]++r)).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_11 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 3 (s71_front StB l ([S3;S0]++r))=Some(s71_back StB l ([S3;S1]++r)) /\
 c52_safe_before 3 (s71_front StB l ([S3;S0]++r)).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_12 : forall l r,
 c52_right_ok true r ->
 csteps s71_tm 3 (s71_front StB l ([S3;S0]++r))=Some(s71_back StB l ([S3;S1]++r)) /\
 c52_safe_before 3 (s71_front StB l ([S3;S0]++r)).
Proof.
 intros l r Hctx;split;[reflexivity|].
 unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact I || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact I || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact I || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_13 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 3 (s71_front StA l ([S3;S1]++r))=Some(s71_back StA l ([S0;S3]++r)) /\
 c52_safe_before 3 (s71_front StA l ([S3;S1]++r)).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_14 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 2 (s71_front StB l ([S3;S1]++r))=Some(s71_front StA ([S2;S1]++l) r) /\
 c52_safe_before 2 (s71_front StB l ([S3;S1]++r)).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_15 : forall l r,
 c52_right_ok true r ->
 csteps s71_tm 2 (s71_front StB l ([S3;S1]++r))=Some(s71_front StA ([S2;S1]++l) r) /\
 c52_safe_before 2 (s71_front StB l ([S3;S1]++r)).
Proof.
 intros l r Hctx;split;[reflexivity|].
 unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact I || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact I || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_16 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 3 (s71_back StA ([S2;S1]++l) r)=Some(s71_front StB ([S2;S2]++l) r) /\
 c52_safe_before 3 (s71_back StA ([S2;S1]++l) r).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_17 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 4 (s71_back StB ([S2;S1]++l) r)=Some(s71_back StA l ([S0;S1]++r)) /\
 c52_safe_before 4 (s71_back StB ([S2;S1]++l) r).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_18 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 4 (s71_back StB ([S2;S1]++l) r)=Some(s71_back StA l ([S0;S1]++r)) /\
 c52_safe_before 4 (s71_back StB ([S2;S1]++l) r).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_19 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 1 (s71_front StA l ([S0;S1]++r))=Some(s71_back StB l ([S1;S1]++r)) /\
 c52_safe_before 1 (s71_front StA l ([S0;S1]++r)).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_20 : forall l r,
 c52_right_ok true r ->
 csteps s71_tm 1 (s71_front StA l ([S0;S1]++r))=Some(s71_back StB l ([S1;S1]++r)) /\
 c52_safe_before 1 (s71_front StA l ([S0;S1]++r)).
Proof.
 intros l r Hctx;split;[reflexivity|].
 unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact I || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_21 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 4 (s71_front StB l ([S0;S1]++r))=Some(s71_front StA ([S1;S0]++l) r) /\
 c52_safe_before 4 (s71_front StB l ([S0;S1]++r)).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_22 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 2 (s71_front StA l ([S1;S1]++r))=Some(s71_front StA ([S2;S2]++l) r) /\
 c52_safe_before 2 (s71_front StA l ([S1;S1]++r)).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_23 : forall l r,
 c52_right_ok true r ->
 csteps s71_tm 2 (s71_front StA l ([S1;S1]++r))=Some(s71_front StA ([S2;S2]++l) r) /\
 c52_safe_before 2 (s71_front StA l ([S1;S1]++r)).
Proof.
 intros l r Hctx;split;[reflexivity|].
 unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact I || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact I || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_24 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 1 (s71_front StB l ([S1;S1]++r))=Some(s71_back StB l ([S3;S1]++r)) /\
 c52_safe_before 1 (s71_front StB l ([S1;S1]++r)).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_25 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 2 (s71_back StA ([S2;S2]++l) r)=Some(s71_back StA l ([S3;S3]++r)) /\
 c52_safe_before 2 (s71_back StA ([S2;S2]++l) r).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_26 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 2 (s71_back StB ([S2;S2]++l) r)=Some(s71_back StA l ([S3;S0]++r)) /\
 c52_safe_before 2 (s71_back StB ([S2;S2]++l) r).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_27 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 2 (s71_back StB ([S2;S2]++l) r)=Some(s71_back StA l ([S3;S0]++r)) /\
 c52_safe_before 2 (s71_back StB ([S2;S2]++l) r).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_28 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 2 (s71_front StA l ([S3;S3]++r))=Some(s71_front StA ([S1;S2]++l) r) /\
 c52_safe_before 2 (s71_front StA l ([S3;S3]++r)).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_29 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 2 (s71_front StB l ([S3;S3]++r))=Some(s71_front StB ([S2;S1]++l) r) /\
 c52_safe_before 2 (s71_front StB l ([S3;S3]++r)).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_30 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 2 (s71_back StA ([S2;S0]++l) r)=Some(s71_back StB l ([S1;S3]++r)) /\
 c52_safe_before 2 (s71_back StA ([S2;S0]++l) r).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_31 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 2 (s71_back StB ([S2;S0]++l) r)=Some(s71_back StB l ([S1;S0]++r)) /\
 c52_safe_before 2 (s71_back StB ([S2;S0]++l) r).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_32 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 1 (s71_back StA ([S1;S2]++l) r)=Some(s71_front StA ([S2;S2]++l) r) /\
 c52_safe_before 1 (s71_back StA ([S1;S2]++l) r).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_33 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 2 (s71_back StB ([S1;S2]++l) r)=Some(s71_back StA l ([S0;S3]++r)) /\
 c52_safe_before 2 (s71_back StB ([S1;S2]++l) r).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_34 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 1 (s71_front StA l ([S0;S3]++r))=Some(s71_back StB l ([S1;S3]++r)) /\
 c52_safe_before 1 (s71_front StA l ([S0;S3]++r)).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_35 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 2 (s71_front StB l ([S0;S3]++r))=Some(s71_front StA ([S1;S0]++l) r) /\
 c52_safe_before 2 (s71_front StB l ([S0;S3]++r)).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_36 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 2 (s71_front StA l ([S1;S3]++r))=Some(s71_front StB ([S2;S2]++l) r) /\
 c52_safe_before 2 (s71_front StA l ([S1;S3]++r)).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_37 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 1 (s71_front StB l ([S1;S3]++r))=Some(s71_back StB l ([S3;S3]++r)) /\
 c52_safe_before 1 (s71_front StB l ([S1;S3]++r)).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_38 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 2 (s71_back StA ([S0;S2]++l) r)=Some(s71_back StA l ([S0;S1]++r)) /\
 c52_safe_before 2 (s71_back StA ([S0;S2]++l) r).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
destruct n as[|n];[
cbn[csteps cstep s71_tm ctape_move s71_front s71_back chd ctl app]in E;injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Lemma c52_trace_39 : forall l r,
 c52_right_ok false r ->
 csteps s71_tm 1 (s71_back StB ([S0;S2]++l) r)=Some(s71_front StB ([S0;S2]++l) r) /\
 c52_safe_before 1 (s71_back StB ([S0;S2]++l) r).
Proof.
 intros l r Hctx;split;[reflexivity|].
 pose proof(c52_right_ok_false r Hctx)as HR.
unfold c52_safe_before;intros n Hn d E.
destruct n as[|n];[
injection E as <-;cbn[c52_safe s71_front s71_back chd ctl app all_blank sym_eqb];exact HR || exact I || reflexivity|].
lia.
Qed.
Print Assumptions c52_trace_00.
Print Assumptions c52_trace_39.
