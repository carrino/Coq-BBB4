(** * DyadicFrontierTr: expanded binary digits and a doubling frontier.

    Digit i occupies 2^i consecutive cells.  A carry through e low one
    digits therefore erases 2^e-1 cells and fills the next 2^e cells.
    [df_prefix_sound] proves the finite fill by strong induction on e:
    an auxiliary fixed-width Boolean counter decreases its complement
    rank at every increment, and invokes only smaller carries.

    At the right frontier the left tape is [0^(r-1) 1^r], where r=2^k.
    One overflow followed by a bounded counter drain returns to the same
    frontier with r doubled.  Blank padding is justified after [lift].
    For k>0 the overflow scan/fill fires all eight instructions. *)
From Coq Require Import Arith Lia List Bool.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import ValueLapTr WTape LapCertGlueLift.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Fixpoint df_width(k:nat):nat:=match k with 0=>0|S k=>2*df_width k+1 end.
Definition df_sym(b:bool):Sym:=if b then S1 else S0.
Fixpoint df_encode(w:nat)(bs:list bool):list Sym:=match bs with
 |[]=>[]|b::bs=>repeat(df_sym b)w++df_encode(2*w)bs end.
Fixpoint df_rank(bs:list bool):nat:=match bs with
 |[]=>0|b::bs=>(if b then 0 else 1)+2*df_rank bs end.
Fixpoint df_succ(bs:list bool):option(list bool):=match bs with
 |[]=>None|false::bs=>Some(true::bs)|true::bs=>option_map(cons false)(df_succ bs)end.
Lemma df_encode_prefix:forall e w b bs,
 df_encode w(repeat b e++bs)=repeat(df_sym b)(w*df_width e)++df_encode(w*S(df_width e))bs.
Proof.
 induction e as[|e IH];intros w b bs.
 - cbn[repeat app df_width df_encode]. rewrite Nat.mul_0_r,Nat.mul_1_r. reflexivity.
 - cbn[repeat app df_width df_encode]. rewrite IH,app_assoc,<-repeat_app.
   replace(w+2*w*df_width e)with(w*(2*df_width e+1))by nia.
   replace(2*w*S(df_width e))with(w*S(2*df_width e+1))by nia. reflexivity.
Qed.
Lemma df_encode_repeat:forall e b,
 df_encode 1(repeat b e)=repeat(df_sym b)(df_width e).
Proof.
 intros. rewrite <-(app_nil_r(repeat b e)),df_encode_prefix.
 cbn[df_encode]. rewrite app_nil_r,Nat.mul_1_l. reflexivity.
Qed.
Lemma df_rank_zero:forall bs,df_rank bs=0->bs=repeat true(length bs).
Proof.
 induction bs as[|b bs IH];intro H;[reflexivity|]. destruct b;cbn[df_rank]in H.
 - cbn[length repeat]. f_equal. apply IH. lia.
 - lia.
Qed.
Lemma df_rank_false:forall k,df_rank(repeat false k)=df_width k.
Proof. induction k;cbn[repeat df_rank df_width];[reflexivity|rewrite IHk;lia]. Qed.
Lemma df_succ_none:forall bs,df_succ bs=None->df_rank bs=0.
Proof.
 induction bs as[|b bs IH];intro H;[reflexivity|]. destruct b;cbn[df_succ]in H;[|discriminate].
 destruct(df_succ bs)eqn:E;[discriminate|]. cbn[df_rank]. rewrite(IH eq_refl). reflexivity.
Qed.
Lemma df_succ_spec:forall bs cs,df_succ bs=Some cs->
 length cs=length bs /\ df_rank bs=S(df_rank cs) /\
 exists e tail,e<length bs /\ bs=repeat true e++false::tail /\ cs=repeat false e++true::tail.
Proof.
 induction bs as[|b bs IH];intros cs H;[discriminate|]. destruct b.
 - cbn[df_succ]in H. destruct(df_succ bs)as[ds|]eqn:E;[|discriminate].
   injection H as<-.
   destruct(IH ds eq_refl)as(Hlen&Hrank&e&tail&He&Hbs&Hds).
   split;[cbn[length];lia|]. split;[cbn[df_rank];lia|].
   exists(S e),tail. split;[cbn[length];lia|]. split;cbn[repeat app];now f_equal.
 - cbn[df_succ]in H. injection H as<-. split;[reflexivity|].
   split;[cbn[df_rank];lia|]. exists 0,bs. split;[cbn[length];lia|]. split;reflexivity.
Qed.
Lemma df_encode_carry:forall e tail,
 df_encode 1(repeat true e++false::tail)=
 repeat S1(df_width e)++repeat S0(S(df_width e))++df_encode(2*S(df_width e))tail /\
 df_encode 1(repeat false e++true::tail)=
 repeat S0(df_width e)++repeat S1(S(df_width e))++df_encode(2*S(df_width e))tail.
Proof. intros. split;rewrite df_encode_prefix,Nat.mul_1_l,Nat.mul_1_l;reflexivity. Qed.
Lemma df_repeat_push:forall(s:Sym)k L,repeat s k++s::L=repeat s(S k)++L.
Proof. induction k;intro L;cbn[repeat app];[reflexivity|now rewrite IHk]. Qed.
Lemma df_rank_high:forall k,df_rank(repeat false k++[true])=df_width k.
Proof. induction k;cbn[repeat app df_rank df_width];[reflexivity|rewrite IHk;lia]. Qed.
Lemma df_encode_high:forall k,df_encode 1(repeat false k++[true])=
 repeat S0(df_width k)++repeat S1(S(df_width k)).
Proof. intro k. rewrite df_encode_prefix,Nat.mul_1_l,Nat.mul_1_l.
 cbn[df_encode df_sym]. now rewrite app_nil_r. Qed.
Lemma df_lift_zeros:forall a k,lift_side(a++repeat S0 k)=lift_side a.
Proof.
 intros a k. revert a. induction k;intro a;[now rewrite app_nil_r|].
 change(repeat S0(S k))with([S0]++repeat S0 k).
 rewrite app_assoc,IHk,lift_side_app_blank. reflexivity.
Qed.
Lemma df_lift_pad:forall q L h R a b,
 lift(q,(L++repeat S0 a,h,R++repeat S0 b))=lift(q,(L,h,R)).
Proof. intros. unfold lift,lift_tape. cbn[fst snd]. now rewrite !df_lift_zeros. Qed.
Section Machine.
Variable tm:TM.
Hypothesis HA0:tm StA S0=Some(mkTrans S1 DR StB).
Hypothesis HA1:tm StA S1=Some(mkTrans S0 DL StA).
Hypothesis HB0:tm StB S0=Some(mkTrans S1 DL StC).
Hypothesis HB1:tm StB S1=Some(mkTrans S1 DR StD).
Hypothesis HC0:tm StC S0=Some(mkTrans S0 DL StC).
Hypothesis HC1:tm StC S1=Some(mkTrans S1 DL StA).
Hypothesis HD0:tm StD S0=Some(mkTrans S0 DR StD).
Hypothesis HD1:tm StD S1=Some(mkTrans S0 DR StB).
Local Ltac df_compute:=
 cbn[Nat.add Nat.mul csteps cstep ctape_move chd ctl t_next t_dir t_write repeat app];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[Nat.add Nat.mul csteps cstep ctape_move chd ctl t_next t_dir t_write repeat app]);repeat rewrite app_nil_r;reflexivity.
Definition df_run(c d:cconf):Prop:=exists k,csteps tm k c=Some d.
Lemma df_trans:forall c d e,df_run c d->df_run d e->df_run c e.
Proof. intros c d e(k&Hk)(j&Hj). exists(k+j). now rewrite csteps_add,Hk. Qed.
Lemma df_C0_scan:forall a L R,
 csteps tm(S a)(StC,(repeat S0 a++S1::L,S0,R))=
 Some(StC,(L,S1,repeat S0(S a)++R)).
Proof.
 induction a as[|a IH];intros L R.
 - df_compute.
 - replace(S(S a))with(1+S a)by lia. rewrite csteps_add.
   assert(E:csteps tm 1(StC,(repeat S0(S a)++S1::L,S0,R))=
    Some(StC,(repeat S0 a++S1::L,S0,S0::R)))by df_compute.
   now rewrite E,IH,df_repeat_push.
Qed.
Lemma df_B0_left:forall a L R,
 csteps tm(S a)(StB,(repeat S0 a++S1::L,S0,R))=
 Some(StC,(L,S1,repeat S0 a++S1::R)).
Proof.
 intros[|a]L R.
 - df_compute.
 - replace(S(S a))with(1+S a)by lia. rewrite csteps_add.
   assert(E:csteps tm 1(StB,(repeat S0(S a)++S1::L,S0,R))=
    Some(StC,(repeat S0 a++S1::L,S0,S1::R)))by df_compute.
   now rewrite E,df_C0_scan.

Qed.
Lemma df_A1_scan:forall b L R,
 csteps tm(S b)(StA,(repeat S1 b++S0::L,S1,R))=
 Some(StA,(L,S0,repeat S0(S b)++R)).
Proof.
 induction b as[|b IH];intros L R.
 - df_compute.
 - replace(S(S b))with(1+S b)by lia. rewrite csteps_add.
   assert(E:csteps tm 1(StA,(repeat S1(S b)++S0::L,S1,R))=
    Some(StA,(repeat S1 b++S0::L,S1,S0::R)))by df_compute.
   now rewrite E,IH,df_repeat_push.
Qed.
Lemma df_C1_left:forall b L R,
 csteps tm(S b)(StC,(repeat S1 b++S0::L,S1,R))=
 Some(StA,(L,S0,repeat S0 b++S1::R)).
Proof.
 intros[|b]L R.
 - df_compute.
 - replace(S(S b))with(1+S b)by lia. rewrite csteps_add.
   assert(E:csteps tm 1(StC,(repeat S1(S b)++S0::L,S1,R))=
    Some(StA,(repeat S1 b++S0::L,S1,S1::R)))by df_compute.
   now rewrite E,df_A1_scan.

Qed.
Lemma df_D0_scan:forall a L R,
 csteps tm(S a)(StD,(L,S0,repeat S0 a++S1::R))=
 Some(StD,(repeat S0(S a)++L,S1,R)).
Proof.
 induction a as[|a IH];intros L R.
 - df_compute.
 - replace(S(S a))with(1+S a)by lia. rewrite csteps_add.
   assert(E:csteps tm 1(StD,(L,S0,repeat S0(S a)++S1::R))=
    Some(StD,(S0::L,S0,repeat S0 a++S1::R)))by df_compute.
   now rewrite E,IH,df_repeat_push.
Qed.
Lemma df_B1_right:forall a L R h,
 csteps tm(a+2)(StB,(L,S1,repeat S0 a++S1::h::R))=
 Some(StB,(repeat S0(S a)++S1::L,h,R)).
Proof.
 intros[|a]L R h.
 - df_compute.
 - replace(S a+2)with(1+(S a+1))by lia. rewrite csteps_add.
   assert(E:csteps tm 1(StB,(L,S1,repeat S0(S a)++S1::h::R))=
    Some(StD,(S1::L,S0,repeat S0 a++S1::h::R)))by df_compute.
   rewrite E,csteps_add,df_D0_scan. df_compute.

Qed.
Definition df_prefix(e:nat):Prop:=forall L R h,
 df_run(StA,(repeat S0(df_width e)++L,S0,repeat S0(df_width e)++h::R))
       (StB,(repeat S0(df_width e)++repeat S1(S(df_width e))++L,h,R)).
Lemma df_carry:forall e,df_prefix e->forall a L R h,
 df_run(StB,(repeat S0 a++S1::repeat S1(df_width e)++repeat S0(S(df_width e))++L,S0,h::R))
       (StB,(repeat S0(S a)++S1::repeat S0(df_width e)++repeat S1(S(df_width e))++L,h,R)).
Proof.
 intros e He a L R h.
 eapply df_trans;[exists(S a);apply df_B0_left|].
 cbn[repeat].
 eapply df_trans;[exists(S(df_width e));apply df_C1_left|].
 eapply df_trans;[apply He|].
 exists(a+2). apply df_B1_right.
Qed.
Definition df_counter(a:nat)(bs:list bool)(L stream:list Sym):cconf:=
 (StB,(repeat S0 a++S1::df_encode 1 bs++L,chd stream,ctl stream)).
Lemma df_increment:forall k,(forall e,e<k->df_prefix e)->
 forall bs cs,length bs=k->df_succ bs=Some cs->forall a L stream,
 stream<>[]->df_run(df_counter a bs L(S0::stream))(df_counter(S a)cs L stream).
Proof.
 intros k HP bs cs Hlen Hsucc a L stream Hstream. destruct stream as[|h R];[contradiction|].
 destruct(df_succ_spec bs cs Hsucc)as(_&_&e&tail&He&Hbs&Hcs).
 unfold df_counter. cbn[chd ctl]. rewrite Hbs,Hcs.
 destruct(df_encode_carry e tail)as[Eb Ec]. rewrite Eb,Ec.
 repeat rewrite <-app_assoc. apply df_carry. apply HP. lia.
Qed.
Lemma df_drain:forall k,(forall e,e<k->df_prefix e)->forall n bs,
 df_rank bs=n->length bs=k->forall a L R h,
 df_run(df_counter a bs L(repeat S0 n++h::R))
 (StB,(repeat S0(a+n)++S1::repeat S1(df_width k)++L,h,R)).
Proof.
 intros k HP n. induction n as[|n IH];intros bs Hrank Hlen a L R h.
 - rewrite(df_rank_zero bs Hrank),Hlen. unfold df_counter.
   rewrite df_encode_repeat. replace(a+0)with a by lia. exists 0. reflexivity.
 - destruct(df_succ bs)as[cs|]eqn:E.
   2:{ pose proof(df_succ_none bs E). lia. }
   destruct(df_succ_spec bs cs E)as(Hlength&Hnext&_).
   cbn[repeat].
   eapply df_trans.
   + apply(df_increment k HP bs cs Hlen E). destruct n;discriminate.
   + replace(a+S n)with(S a+n)by lia. apply IH;lia.
Qed.
Theorem df_prefix_sound:forall k,df_prefix k.
Proof.
 induction k using lt_wf_ind. unfold df_prefix. intros L R h.
 eapply df_trans with(d:=df_counter 0(repeat false k)L(repeat S0(df_width k)++h::R)).
 { exists 1. unfold df_counter. rewrite df_encode_repeat.
   cbn[df_sym]. destruct(df_width k);df_compute. }
 pose proof(df_drain k H(df_width k)(repeat false k)(df_rank_false k)(repeat_length false k)0 L R h)as E.
 cbn[Nat.add]in E. exact E.
Qed.
Definition df_front(k:nat):cconf:=
 (StB,(repeat S0(df_width k)++repeat S1(S(df_width k)),S0,[])).
Definition df_overflow(k:nat):cconf:=
 (StB,(repeat S0(df_width k)++S1::repeat S1(df_width k)++repeat S0(S(df_width k)),S0,[S0])).
Definition df_middle(k:nat):cconf:=
 (StB,(repeat S0(S(df_width k))++S1::repeat S0(df_width k)++repeat S1(S(df_width k)),S0,[])).
Lemma df_overflow_lift:forall k,lift(df_overflow k)=lift(df_front k).
Proof.
 intro k. unfold df_overflow,df_front.
 change(S1::repeat S1(df_width k)++repeat S0(S(df_width k)))
 with(repeat S1(S(df_width k))++repeat S0(S(df_width k))).
 rewrite app_assoc.
 exact(df_lift_pad StB(repeat S0(df_width k)++repeat S1(S(df_width k)))S0[](S(df_width k))1).
Qed.
Lemma df_overflow_run:forall k,exists j,
 csteps tm j(df_overflow k)=Some(df_middle k)/\0<j.
Proof.
 intro k. destruct(df_carry k(df_prefix_sound k)(df_width k)[][]S0)as(j&Hj).
 repeat rewrite app_nil_r in Hj. exists j. split;[exact Hj|].
 destruct j;[|lia]. cbn[csteps]in Hj. discriminate Hj.
Qed.
Lemma df_middle_lift:forall k,
 lift(df_counter(S(df_width k))(repeat false k++[true])[](repeat S0(df_width k)++[S0]))=
 lift(df_middle k).
Proof.
 intro k. unfold df_counter,df_middle. rewrite df_encode_high,app_nil_r.
 destruct(df_width k)as[|w].
 - reflexivity.
 - cbn[repeat app chd ctl].
   change(lift(StB,(S0::S0::repeat S0 w++S1::S0::repeat S0 w++S1::S1::repeat S1 w,
     S0,repeat S0 w++[S0]))=
     lift(StB,(S0::S0::repeat S0 w++S1::S0::repeat S0 w++S1::S1::repeat S1 w,S0,[]))).
   assert(E:lift_side(repeat S0 w++[S0])=lift_side[]).
   { rewrite df_repeat_push,app_nil_r. exact(df_lift_zeros[](S w)). }
   unfold lift,lift_tape. cbn[fst snd]. now rewrite E.
Qed.
Lemma df_middle_drain:forall k,exists j,
 stepn tm j(lift(df_middle k))=Some(lift(df_front(S k))).
Proof.
 intro k.
 assert(Hlen:length(repeat false k++[true])=S k)by(rewrite app_length,repeat_length;cbn[length];lia).
 destruct(df_drain(S k)(fun e _=>df_prefix_sound e)(df_width k)
   (repeat false k++[true])(df_rank_high k)Hlen(S(df_width k))[][]S0)as(j&Hj).
 cbn[app]in Hj. exists j. rewrite <-(df_middle_lift k).
 pose proof(csteps_lift _ _ _ _ Hj)as H. rewrite H.
 unfold df_front. cbn[df_width]. replace(S(df_width k)+df_width k)with(2*df_width k+1)by lia.
 rewrite app_nil_r. reflexivity.
Qed.
Lemma df_doubling:forall k,exists j,
 stepn tm j(lift(df_front k))=Some(lift(df_front(S k)))/\0<j.
Proof.
 intro k. destruct(df_overflow_run k)as(i&Hi&Hpos).
 destruct(df_middle_drain k)as(j&Hj). exists(i+j). split;[|lia].
 rewrite <-(df_overflow_lift k),stepn_add,(csteps_lift _ _ _ _ Hi). exact Hj.
Qed.
Lemma df_B1_D1:forall a L R,
 csteps tm(S a)(StB,(L,S1,repeat S0 a++S1::R))=
 Some(StD,(repeat S0 a++S1::L,S1,R)).
Proof.
 intros[|a]L R.
 - df_compute.
 - replace(S(S a))with(1+S a)by lia. rewrite csteps_add.
   assert(E:csteps tm 1(StB,(L,S1,repeat S0(S a)++S1::R))=
    Some(StD,(S1::L,S0,repeat S0 a++S1::R)))by df_compute.
   now rewrite E,df_D0_scan.
Qed.
Definition df_visit(c:cconf)(t:Instr):Prop:=
 exists j d,csteps tm j c=Some d/\cinstr d=t.
Lemma df_visit_trans:forall c d t,df_run c d->df_visit d t->df_visit c t.
Proof.
 intros c d t(i&Hi)(j&e&Hj&Ht). exists(i+j),e. split;[|exact Ht].
 now rewrite csteps_add,Hi.
Qed.
Lemma df_overflow_fires:forall e,0<df_width e->forall t,df_visit(df_overflow e)t.
Proof.
 intros e Hpositive[q s].
 destruct(df_width e)as[|b]eqn:Ew;[lia|].
 assert(EC:df_run(df_overflow e)
   (StC,(repeat S1(S b)++repeat S0(S(S b)),S1,repeat S0(S b)++[S1;S0]))).
 { unfold df_overflow. rewrite Ew. exists(S(S b)). apply df_B0_left. }
 assert(EA:df_run(df_overflow e)
   (StA,(repeat S0(S b),S0,repeat S0(S b)++S1::repeat S0(S b)++[S1;S0]))).
 { eapply df_trans;[exact EC|]. exists(S(S b)). apply df_C1_left. }
 assert(EB:df_run(df_overflow e)
   (StB,(repeat S0(S b)++repeat S1(S(S b)),S1,repeat S0(S b)++[S1;S0]))).
 { eapply df_trans;[exact EA|].
   pose proof(df_prefix_sound e[](repeat S0(S b)++[S1;S0])S1)as H.
   rewrite Ew in H. repeat rewrite app_nil_r in H. exact H. }
 destruct q,s.
 - eapply df_visit_trans;[exact EA|]. exists 0. eexists. split;[reflexivity|reflexivity].
 - eapply df_visit_trans;[exact EC|]. exists 1. eexists. split;[df_compute|reflexivity].
 - exists 0. eexists. split;[reflexivity|reflexivity].
 - eapply df_visit_trans;[exact EB|]. exists 0. eexists. split;[reflexivity|reflexivity].
 - exists 1. eexists. split;[unfold df_overflow;rewrite Ew;df_compute|reflexivity].
 - eapply df_visit_trans;[exact EC|]. exists 0. eexists. split;[reflexivity|reflexivity].
 - eapply df_visit_trans;[exact EB|]. exists 1. eexists. split;[df_compute|reflexivity].
 - eapply df_visit_trans;[exact EB|]. exists(S(S b)). eexists.
   split;[apply df_B1_D1|reflexivity].
Qed.
Lemma df_front_fires:forall k t,exists j c,
 csteps tm j(df_front(S k))=Some c/\cinstr c=t.
Proof.
 intros k t. assert(Hpos:0<df_width(S k))by(cbn[df_width];lia).
 destruct(df_overflow_fires(S k)Hpos t)as(j&c&Ej&Et).
 pose proof(csteps_lift _ _ _ _ Ej)as H. rewrite df_overflow_lift in H.
 destruct(stepn_csteps_at _ _ _ _ H)as(d&Ed&El).
 exists j,d. split;[exact Ed|]. rewrite <-cinstr_lift,El,cinstr_lift. exact Et.
Qed.
Definition df_anchor(n k:nat):cconf:=df_front(S k).
Theorem df_neverqhtr:NeverQuasiHaltsTr tm.
Proof.
 apply(value_lap_neverqhtr tm nat S df_anchor 0).
 - exists 6. rewrite <-lift_c0. apply csteps_lift. unfold c0,df_anchor,df_front.
   cbn[df_width]. df_compute.
 - intros n k. destruct(df_doubling(S k))as(j&Ej&Hj).
   destruct(stepn_csteps_at _ _ _ _ Ej)as(c&Ec&El).
   exists j,c. split;[exact Ec|]. split;[exact El|exact Hj].
 - intros n k. apply df_front_fires.
Qed.
End Machine.
