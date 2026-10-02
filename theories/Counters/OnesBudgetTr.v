(** * OnesBudgetTr: finite carries ranked by their number of ones.

    From A0 with right word 0 R, every finite left word L reaches
    A at the head of R. The returned left word contains exactly two
    more ones and begins with 10 or 110. A D scan erases m ones;
    traversing the resulting zeros invokes smaller instances, each
    restoring two ones. Before every such call the number of ones
    remains strictly below the original budget, so strong induction
    proves termination even when the intermediate word grows.

    Positive returns at the right blank frontier and short explicit
    instruction witnesses give recurrence for all eight instructions.
    The bootstrap is separate, allowing state-renamed instances. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Fixpoint ob_ones(L:list Sym):nat:=match L with []=>0|S0::L=>ob_ones L|S1::L=>S(ob_ones L)end.
Lemma ob_ones_app:forall L R,ob_ones(L++R)=ob_ones L+ob_ones R.
Proof. induction L as[|[] L IH];intro R;cbn[app ob_ones];try rewrite IH;reflexivity. Qed.
Lemma ob_ones_repeat:forall n,ob_ones(repeat S1 n)=n.
Proof. induction n;cbn[repeat ob_ones];auto. Qed.
Lemma ob_zero_push:forall n R,repeat S0 n++S0::R=S0::repeat S0 n++R.
Proof. induction n;intro R;cbn[repeat app];[reflexivity|now rewrite IHn]. Qed.
Lemma ob_split:forall L,exists k U,L=repeat S1 k++U /\(U=[]\/exists Y,U=S0::Y).
Proof.
 induction L as[|[] L IH].
 - exists 0,[];split;[reflexivity|left;reflexivity].
 - exists 0,(S0::L);split;[reflexivity|right;now exists L].
 - destruct IH as(k&U&E&H). exists(S k),U;split;[cbn[repeat app];now rewrite E|exact H].
Qed.
Definition ob_shape(U:list Sym):Prop:=exists X,U=S1::S0::X\/U=S1::S1::S0::X.
Section Machine.
Variable tm:TM.
Hypothesis HA0:tm StA S0=Some(mkTrans S0 DR StB).
Hypothesis HA1:tm StA S1=Some(mkTrans S0 DR StC).
Hypothesis HB0:tm StB S0=Some(mkTrans S1 DL StC).
Hypothesis HB1:tm StB S1=Some(mkTrans S1 DR StC).
Hypothesis HC0:tm StC S0=Some(mkTrans S1 DL StD).
Hypothesis HC1:tm StC S1=Some(mkTrans S1 DR StA).
Hypothesis HD0:tm StD S0=Some(mkTrans S1 DR StA).
Hypothesis HD1:tm StD S1=Some(mkTrans S0 DL StD).
Local Ltac ob_compute:=
 cbn[Nat.add csteps cstep ctape_move chd ctl t_next t_dir t_write repeat app];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[Nat.add csteps cstep ctape_move chd ctl t_next t_dir t_write repeat app]);reflexivity.
Definition ob_cross(L:list Sym):Prop:=forall R,exists k U,
 csteps tm k(StA,(L,S0,S0::R))=Some(StA,(U,chd R,ctl R))/\
 ob_ones U=ob_ones L+2 /\ob_shape U/\0<k.
Lemma ob_zeros:forall N,
 (forall L,ob_ones L<N->ob_cross L)->forall n L R,
 ob_ones L+n<=N->exists k U,
 csteps tm k(StA,(L,S0,repeat S0 n++S1::S1::R))=Some(StA,(U,chd R,ctl R))/\
 ob_ones U=ob_ones L+n+2 /\ob_shape U.
Proof.
 intros N Cross n. induction n as[n IH]using(well_founded_induction lt_wf).
 intros L R Hbound. destruct n as[|[|n]].
 - exists 3,(S1::S1::S0::L). repeat split.
   + ob_compute.
   + cbn[ob_ones];lia.
   + exists L;right;reflexivity.
 - destruct(Cross L ltac:(lia)(S1::S1::R))as(k&U&E&HU&HS&Hk).
   exists(k+2),(S1::S0::U). repeat split.
   + cbn[repeat app]. rewrite csteps_add,E. ob_compute.
   + cbn[ob_ones];lia.
   + exists U;left;reflexivity.
 - destruct(Cross L ltac:(lia)(S0::repeat S0 n++S1::S1::R))as(k&U&E&HU&HS&Hk).
   destruct(IH n ltac:(lia) U R ltac:(lia))as(j&V&F&HV&VS).
   exists(k+j),V. repeat split.
   + cbn[repeat app]in E|-*. rewrite csteps_add,E. exact F.
   + lia.
   + exact VS.
Qed.
Lemma ob_Dscan:forall k U R,
 csteps tm k(StD,(ctl(repeat S1 k++U),chd(repeat S1 k++U),R))=
 Some(StD,(ctl U,chd U,repeat S0 k++R)).
Proof.
 induction k as[|k IH];intros U R;cbn[repeat app chd ctl];[reflexivity|].
 change(S k)with(1+k). rewrite csteps_add.
 assert(E:csteps tm 1(StD,(repeat S1 k++U,S1,R))=
 Some(StD,(ctl(repeat S1 k++U),chd(repeat S1 k++U),S0::R)))by ob_compute.
 now rewrite E,IH,ob_zero_push.
Qed.
Theorem ob_all_cross:forall L,ob_cross L.
Proof.
 assert(H:forall N L,ob_ones L=N->ob_cross L).
 { intro N. induction N as[N IH]using(well_founded_induction lt_wf).
   intros L HN R. destruct(ob_split L)as(m&V&EV&HV).
   assert(Cross:forall U,ob_ones U<N->ob_cross U).
   { intros U HU. exact(IH(ob_ones U)HU U eq_refl). }
   assert(Count:ob_ones L=m+ob_ones V).
   { rewrite EV,ob_ones_app,ob_ones_repeat. reflexivity. }
   assert(E:csteps tm(3+m)(StA,(L,S0,S0::R))=
    Some(StD,(ctl V,chd V,repeat S0 m++S1::S1::R))).
   { rewrite csteps_add.
     assert(E0:csteps tm 3(StA,(L,S0,S0::R))=
      Some(StD,(ctl L,chd L,S1::S1::R)))by ob_compute.
     now rewrite E0,EV,ob_Dscan. }
   assert(Hhead:chd V=S0)by(destruct HV as[->|(Y&->)];reflexivity).
   assert(Hcount:ob_ones(ctl V)=ob_ones V)by(destruct HV as[->|(Y&->)];reflexivity).
   destruct m as[|m].
   - cbn[Nat.add repeat app]in E. exists(3+3),(S1::S0::S1::ctl V). repeat split.
     + rewrite csteps_add,E,Hhead. ob_compute.
     + cbn[ob_ones];lia.
     + exists(S1::ctl V);left;reflexivity.
     + lia.
   - destruct(ob_zeros N Cross m(S1::ctl V)R ltac:(cbn[ob_ones];lia))as(j&U&F&HU&HS).
     exists((3+S m)+(1+j)),U. repeat split.
     + rewrite csteps_add,E,Hhead,csteps_add.
       assert(E1:csteps tm 1(StD,(ctl V,S0,repeat S0(S m)++S1::S1::R))=
         Some(StA,(S1::ctl V,S0,repeat S0 m++S1::S1::R)))by ob_compute.
       now rewrite E1.
     + cbn[ob_ones]in HU;lia.
     + exact HS.
     + lia.
 }
 intro L. apply(H(ob_ones L)L eq_refl).
Qed.
End Machine.
Section Liveness.
Variable tm:TM.
Hypothesis HA0:tm StA S0=Some(mkTrans S0 DR StB).
Hypothesis HA1:tm StA S1=Some(mkTrans S0 DR StC).
Hypothesis HB0:tm StB S0=Some(mkTrans S1 DL StC).
Hypothesis HB1:tm StB S1=Some(mkTrans S1 DR StC).
Hypothesis HC0:tm StC S0=Some(mkTrans S1 DL StD).
Hypothesis HC1:tm StC S1=Some(mkTrans S1 DR StA).
Hypothesis HD0:tm StD S0=Some(mkTrans S1 DR StA).
Hypothesis HD1:tm StD S1=Some(mkTrans S0 DL StD).
Local Ltac ob_compute:=
 cbn[Nat.add csteps cstep ctape_move chd ctl t_next t_dir t_write repeat app];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[Nat.add csteps cstep ctape_move chd ctl t_next t_dir t_write repeat app]);reflexivity.
Local Definition Cross:=ob_all_cross tm HA0 HA1 HB0 HB1 HC0 HC1 HD0 HD1.
Definition ob_anchor L:cconf:=(StA,(L,S0,[])).
Lemma ob_frontier_return:forall L,exists k U,0<k /\ob_shape U /\
 csteps tm k(ob_anchor L)=Some(ob_anchor U).
Proof.
 intro L. destruct(Cross L [])as(k&U&E&HU&HS&Hk).
 exists k,U;split;[exact Hk|]. split;[exact HS|].
 destruct k;[lia|]. unfold ob_anchor. change(csteps tm(S k)(StA,(L,S0,[S0]))=Some(StA,(U,S0,[])))in E.
 assert(F:csteps tm(S k)(StA,(L,S0,[]))=csteps tm(S k)(StA,(L,S0,[S0])))by ob_compute.
 now rewrite F.
Qed.
Lemma ob_short:forall L,csteps tm 8(ob_anchor(S1::S0::L))=Some(ob_anchor(S1::S1::S0::S1::L)).
Proof. intro L;unfold ob_anchor;ob_compute. Qed.
Lemma ob_to_A1:forall L,exists k U,
 csteps tm k(ob_anchor(S1::S1::S0::L))=Some(StA,(U,S1,[S1])).
Proof.
 intro L. destruct(Cross(S1::L)[S1;S1])as(k&U&E&HU&HS&Hk).
 exists(6+k),U. rewrite csteps_add.
 assert(F:csteps tm 6(ob_anchor(S1::S1::S0::L))=Some(StA,(S1::L,S0,[S0;S1;S1])))by(unfold ob_anchor;ob_compute).
 now rewrite F.
Qed.
Lemma ob_to_short:forall L,ob_shape L->exists k U,
 csteps tm k(ob_anchor L)=Some(ob_anchor(S1::S0::U)).
Proof.
 intros L [X [E|E]];subst L.
 - exists 0,X;reflexivity.
 - destruct(ob_to_A1 X)as(k&U&E). exists(k+2),U.
   rewrite csteps_add,E. unfold ob_anchor;ob_compute.
Qed.
Lemma ob_short_fires:forall L t,exists k c,
 csteps tm k(ob_anchor(S1::S0::L))=Some c /\cinstr c=t.
Proof.
 intros L[q h];destruct q,h.
 - exists 0;eexists;split;[reflexivity|reflexivity].
 - destruct(ob_to_A1(S1::L))as(k&U&E).
   exists(8+k),(StA,(U,S1,[S1])). split;[now rewrite csteps_add,ob_short|reflexivity].
 - exists 1;eexists;split;[unfold ob_anchor;ob_compute|reflexivity].
 - exists 6;eexists;split;[unfold ob_anchor;ob_compute|reflexivity].
 - exists 2;eexists;split;[unfold ob_anchor;ob_compute|reflexivity].
 - exists 7;eexists;split;[unfold ob_anchor;ob_compute|reflexivity].
 - exists 4;eexists;split;[unfold ob_anchor;ob_compute|reflexivity].
 - exists 3;eexists;split;[unfold ob_anchor;ob_compute|reflexivity].
Qed.
Lemma ob_all_fires:forall L t,exists k c,csteps tm k(ob_anchor L)=Some c /\cinstr c=t.
Proof.
 intros L t. destruct(ob_frontier_return L)as(k&U&Hk&HU&E).
 destruct(ob_to_short U HU)as(j&V&F). destruct(ob_short_fires V t)as(i&c&G&Ht).
 exists(k+(j+i)),c;split;[now rewrite csteps_add,E,csteps_add,F|exact Ht].
Qed.
Theorem ones_budget_neverqhtr:
 (exists t L,stepn tm t InitES=Some(lift(ob_anchor L)))->NeverQuasiHaltsTr tm.
Proof.
 intro Boot. assert(Reach:forall N,exists t L,N<=t /\stepn tm t InitES=Some(lift(ob_anchor L))).
 { induction N as[|N IH].
   - destruct Boot as(t&L&Et). exists t,L;split;[lia|exact Et].
   - destruct IH as(t&L&Ht&Et). destruct(ob_frontier_return L)as(k&U&Hk&HU&Ek).
     exists(t+k),U;split;[lia|]. rewrite stepn_add,Et. now apply csteps_lift. }
 intros target _ N. destruct(Reach N)as(t&L&Ht&Et).
 destruct(ob_all_fires L target)as(k&c&Ek&Hc).
 exists(t+k);split;[lia|]. exists(lift c);split.
 - rewrite stepn_add,Et. now apply csteps_lift.
 - now rewrite cinstr_lift.
Qed.
End Liveness.
