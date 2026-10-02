(** * Exact frontier sweeps for the period-three counter core.

    [P n] is [(10)^n 110], [Q n] is [(10)^n 111], and
    [U n] is [1^(2*n+2) 0].  A finite right scan either reaches B0 or
    turns at Q, transfers its stack back to the right, and produces
    [Us ms ++ U n ++ 10 ++ R].  All seven transition hypotheses are
    local; the instruction at B0 is unconstrained. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
Import ListNotations.
Fixpoint vft_zig(n:nat):list Sym:=match n with 0=>[]|S k=>S1::S0::vft_zig k end.
Definition vft_P(n:nat):list Sym:=vft_zig n++[S1;S1;S0].
Definition vft_Q(n:nat):list Sym:=vft_zig n++[S1;S1;S1].
Definition vft_U(n:nat):list Sym:=repeat S1(2*n+2)++[S0].
Definition vft_frame(n:nat):list Sym:=S0::repeat S1(2*n+2).
Fixpoint vft_Ps(ns:list nat):list Sym:=match ns with[]=>[]|n::ns=>vft_P n++vft_Ps ns end.
Fixpoint vft_Us(ns:list nat):list Sym:=match ns with[]=>[]|n::ns=>vft_U n++vft_Us ns end.
Fixpoint vft_stack(ns:list nat)(L:list Sym):list Sym:=
 match ns with[]=>L|n::ns=>repeat S1(2*n+2)++S0::vft_stack ns L end.
Lemma vft_repeat_push:forall(s:Sym)k L,repeat s k++s::L=repeat s(S k)++L.
Proof. induction k;intro L;cbn[repeat app vft_zig];[reflexivity|now rewrite IHk]. Qed.
Lemma vft_Us_app:forall ns ms,vft_Us(ns++ms)=vft_Us ns++vft_Us ms.
Proof. induction ns;intro ms;cbn[vft_Us app];[reflexivity|now rewrite IHns,app_assoc]. Qed.
Section Machine.
Variable tm:TM.
Hypothesis HA0:tm StA S0=Some(mkTrans S1 DR StB).
Hypothesis HA1:tm StA S1=Some(mkTrans S0 DL StC).
Hypothesis HB1:tm StB S1=Some(mkTrans S1 DR StD).
Hypothesis HC0:tm StC S0=Some(mkTrans S1 DL StA).
Hypothesis HC1:tm StC S1=Some(mkTrans S1 DL StC).
Hypothesis HD0:tm StD S0=Some(mkTrans S1 DR StB).
Hypothesis HD1:tm StD S1=Some(mkTrans S0 DR StA).
Local Ltac vft_compute:=
 cbn[Nat.add Nat.mul csteps cstep ctape_move chd ctl t_next t_dir t_write repeat app vft_zig];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[Nat.add Nat.mul csteps cstep ctape_move chd ctl t_next t_dir t_write repeat app vft_zig]);
 repeat rewrite app_nil_r;reflexivity.
Definition vft_run(c d:cconf):Prop:=exists k,csteps tm k c=Some d.
Lemma vft_refl:forall c,vft_run c c.
Proof. intro c;exists 0;reflexivity. Qed.
Lemma vft_trans:forall c d e,vft_run c d->vft_run d e->vft_run c e.
Proof. intros c d e(k&Hk)(j&Hj);exists(k+j);now rewrite csteps_add,Hk. Qed.
Lemma vft_AD:forall k L R,
 csteps tm(S k)(StA,(L,S0,R))=csteps tm(S k)(StD,(L,S0,R)).
Proof. intros;cbn[csteps cstep];rewrite HA0,HD0;reflexivity. Qed.
Lemma vft_right:forall n L R,
 csteps tm(2*n+3)(StA,(L,S0,vft_zig n++S1::S1::R))=
 Some(StA,(S0::repeat S1(2*n+2)++L,chd R,ctl R)).
Proof.
 induction n as[|n IH];intros L R.
 - vft_compute.
 - replace(2*S n+3)with(2+(2*n+3))by lia. rewrite csteps_add.
   assert(E:csteps tm 2(StA,(L,S0,vft_zig(S n)++S1::S1::R))=
    Some(StD,(S1::S1::L,S0,vft_zig n++S1::S1::R))).
   { cbn[vft_zig]. vft_compute. }
   rewrite E. replace(2*n+3)with(S(2*n+2))by lia. rewrite <-vft_AD.
   replace(S(2*n+2))with(2*n+3)by lia. rewrite IH.
   repeat rewrite vft_repeat_push. replace(S(S(2*n+2)))with(2*S n+2)by lia.
   reflexivity.
Qed.
Lemma vft_right_B0:forall n L R,
 csteps tm(2*n+1)(StA,(L,S0,vft_zig n++S0::R))=
 Some(StB,(repeat S1(2*n+1)++L,S0,R)).
Proof.
 induction n as[|n IH];intros L R.
 - vft_compute.
 - replace(2*S n+1)with(2+(2*n+1))by lia. rewrite csteps_add.
   assert(E:csteps tm 2(StA,(L,S0,vft_zig(S n)++S0::R))=
    Some(StD,(S1::S1::L,S0,vft_zig n++S0::R))).
   { cbn[vft_zig]. vft_compute. }
   rewrite E. replace(2*n+1)with(S(2*n))by lia. rewrite <-vft_AD.
   replace(S(2*n))with(2*n+1)by lia. rewrite IH.
   repeat rewrite vft_repeat_push. replace(S(S(2*n+1)))with(2+(2*n+1))by lia.
   reflexivity.
Qed.
Lemma vft_C_left:forall m L R,
 csteps tm m(StC,(ctl(repeat S1 m++L),chd(repeat S1 m++L),R))=
 Some(StC,(ctl L,chd L,repeat S1 m++R)).
Proof.
 induction m as[|m IH];intros L R;[reflexivity|].
 replace(S m)with(1+m)at 1 by lia. rewrite csteps_add.
 assert(E:csteps tm 1(StC,(ctl(repeat S1(S m)++L),chd(repeat S1(S m)++L),R))=
 Some(StC,(ctl(repeat S1 m++L),chd(repeat S1 m++L),S1::R)))by vft_compute.
 rewrite E,IH,vft_repeat_push. reflexivity.
Qed.
Lemma vft_A_left:forall m L R,
 csteps tm(m+2)(StA,(repeat S1 m++S0::L,S1,R))=
 Some(StA,(ctl L,chd L,repeat S1(S m)++S0::R)).
Proof.
 intros m L R. replace(m+2)with(1+(m+1))by lia. rewrite csteps_add.
 assert(E:csteps tm 1(StA,(repeat S1 m++S0::L,S1,R))=
 Some(StC,(ctl(repeat S1 m++S0::L),chd(repeat S1 m++S0::L),S0::R)))by vft_compute.
 rewrite E,csteps_add,vft_C_left. vft_compute.
Qed.
Lemma vft_pop:forall ns L R,
 vft_run(StA,(ctl(vft_stack ns L),chd(vft_stack ns L),R))
 (StA,(ctl L,chd L,vft_Us(rev ns)++R)).
Proof.
 induction ns as[|n ns IH];intros L R.
 - cbn[vft_stack vft_Us rev app]. apply vft_refl.
 - cbn[vft_stack]. replace(2*n+2)with(S(2*n+1))by lia. cbn[repeat app ctl chd].
   eapply vft_trans.
   + exists(2*n+1+2). apply vft_A_left.
   + specialize(IH L(repeat S1(S(2*n+1))++S0::R)).
     replace(S(2*n+1))with(2*n+2)in IH by lia.
     cbn[rev].
     rewrite vft_Us_app. cbn[vft_Us]. rewrite app_nil_r.
     unfold vft_U. repeat rewrite <-app_assoc.
     replace(S(2*n+1))with(2*n+2)by lia. exact IH.
Qed.
Lemma vft_push:forall ms ns L R,
 vft_run(StA,(S0::vft_stack ns L,S0,vft_Ps ms++R))
 (StA,(S0::vft_stack(rev ms++ns)L,S0,R)).
Proof.
 induction ms as[|m ms IH];intros ns L R.
 - cbn[vft_Ps rev app]. apply vft_refl.
 - cbn[vft_Ps]. unfold vft_P. repeat rewrite <-app_assoc.
   eapply vft_trans.
   + exists(2*m+3). apply vft_right.
   + change(vft_run(StA,(S0::vft_stack(m::ns)L,S0,vft_Ps ms++R))
       (StA,(S0::vft_stack(rev(m::ms)++ns)L,S0,R))).
     cbn[rev]. rewrite <-app_assoc. cbn[app]. apply IH.
Qed.
Lemma vft_turn:forall n ns L R,
 csteps tm 2(StA,(vft_frame n++S0::vft_stack ns L,S1,R))=
 Some(StA,(ctl(vft_stack(n::ns)L),chd(vft_stack(n::ns)L),S1::S0::R)).
Proof.
 intros. unfold vft_frame. cbn[vft_stack].
 replace(2*n+2)with(S(2*n+1))by lia. vft_compute.
Qed.
Theorem vft_frontier_explicit:forall ms n L R,
 exists k,0<k /\
 csteps tm k(StA,(S0::L,S0,vft_Ps ms++vft_Q n++R))=
 Some(StA,(ctl L,chd L,vft_Us ms++vft_U n++S1::S0::R)).
Proof.
 intros ms n L R.
 destruct(vft_push ms [] L(vft_Q n++R))as[k Hk]. rewrite app_nil_r in Hk. cbn[vft_stack]in Hk.
 destruct(vft_pop(n::rev ms)L(S1::S0::R))as[j Hj].
 exists(k+((2*n+3)+(2+j))). split;[lia|].
 rewrite csteps_add,Hk,csteps_add.
 unfold vft_Q. rewrite <-app_assoc. cbn[app]. rewrite vft_right. cbn[chd ctl].
 change(S0::repeat S1(2*n+2)++S0::vft_stack(rev ms)L)
 with(vft_frame n++S0::vft_stack(rev ms)L).
 rewrite csteps_add,vft_turn,Hj. cbn[rev]. rewrite rev_involutive,vft_Us_app.
 cbn[vft_Us]. rewrite app_nil_r,<-app_assoc. reflexivity.
Qed.
Theorem vft_terminal_explicit:forall ms n L R,
 exists k L',0<k /\
 csteps tm k(StA,(L,S0,vft_Ps ms++vft_zig n++S0::R))=
 Some(StB,(L',S0,R)).
Proof.
 intros ms n L R.
 (* P-block pushing is valid for any left tape; use a direct induction. *)
 revert L. induction ms as[|m ms IH];intro L.
 - exists(2*n+1),(repeat S1(2*n+1)++L). split;[lia|apply vft_right_B0].
 - cbn[vft_Ps]. unfold vft_P. repeat rewrite <-app_assoc. cbn[app].
   destruct(IH(S0::repeat S1(2*m+2)++L))as[k[L'[Hpos Hk]]].
   exists(2*m+3+k),L'. split;[lia|].
   rewrite csteps_add,vft_right. exact Hk.
Qed.
Theorem vft_frontier:forall ms n R,
 exists k,0<k /\
 stepn tm k(lift(StA,([],S0,vft_Ps ms++vft_Q n++R)))=
 Some(lift(StA,([],S0,vft_Us ms++vft_U n++S1::S0::R))).
Proof.
 intros ms n R. destruct(vft_frontier_explicit ms n [] R)as[k[Hpos Hk]].
 exists k;split;[exact Hpos|].
 assert(E:lift(StA,([],S0,vft_Ps ms++vft_Q n++R))=
 lift(StA,([S0],S0,vft_Ps ms++vft_Q n++R))).
 { unfold lift,lift_tape;cbn[fst snd].
   f_equal. f_equal. apply lpad_eqb_lift. reflexivity. }
 rewrite E. pose proof(csteps_lift tm k _ _ Hk)as H. exact H.
Qed.
End Machine.
