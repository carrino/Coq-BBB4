(** * Ternary transfers with a positive stack of left blocks.

    Each inner transfer removes three from the near left block, adds
    one to the next block, and adds two to the right block.  Residues
    zero and one reach D0.  Residue two consumes the next stack entry;
    at the last entry the stack resets to [1], and subsequent non-firing
    rounds divide the near block by three.  Positivity of every stored
    block rules out the infinite empty-stack escape.

    D0 returns preserve this invariant.  Right blocks of lengths one,
    two, and three have explicit firing paths; larger blocks enter a
    transfer or residue-two phase containing all other instructions. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import StackCubeTr PairStackTr TriReachTr WTape.
Import ListNotations.
Definition ts_wf w := w<>[] /\ Forall (fun n=>0<n) w.
Definition ts_D w (z:bool) r : cconf :=
 (StD,(pc_word w,S0,(if z then [S0] else [])++sc_ones r)).
Definition ts_found tm c := exists w z r,
 ts_wf w /\ 0<r /\ sc_R tm c (ts_D w z r).
Lemma ts_found_back : forall tm c d,
 sc_R tm c d -> ts_found tm d -> ts_found tm c.
Proof.
 intros tm c d E (w&z&r&W&P&F). exists w,z,r;split;[exact W|]. split;[exact P|].
 eapply sc_R_trans;eauto.
Qed.
Lemma ts_inc_wf : forall k w,0<k -> Forall (fun n=>0<n) w -> ts_wf(pc_inc k w).
Proof.
 intros k [|b w] K W;split;try discriminate.
 - constructor;[exact K|constructor].
 - inversion W;subst. constructor;[cbn[pc_inc];lia|assumption].
Qed.
Lemma ts_inc_keep : forall k w,ts_wf w -> ts_wf(pc_inc k w).
Proof.
 intros k [|b w] [E W];[contradiction|]. split;[discriminate|].
 inversion W;subst. constructor;[cbn[pc_inc];lia|assumption].
Qed.
Lemma ts_cons_wf : forall n w,0<n -> ts_wf w -> ts_wf(n::w).
Proof. intros n w N [E W]. split;[discriminate|constructor;assumption]. Qed.

Section TernaryStack.
Variable tm : TM.
Hypothesis HA0 : tm StA S0=Some(mkTrans S1 DL StB).
Hypothesis HA1 : tm StA S1=Some(mkTrans S1 DR StA).
Hypothesis HB0 : tm StB S0=Some(mkTrans S0 DL StC).
Hypothesis HB1 : tm StB S1=Some(mkTrans S0 DL StD).
Hypothesis HC0 : tm StC S0=Some(mkTrans S1 DR StD).
Hypothesis HC1 : tm StC S1=Some(mkTrans S1 DL StC).
Hypothesis HD0 : tm StD S0=Some(mkTrans S0 DR StC).
Hypothesis HD1 : tm StD S1=Some(mkTrans S0 DR StA).
Local Ltac ts_compute :=
 repeat (cbn [csteps cstep ctape_move chd ctl t_write t_dir t_next app];
  first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1]);reflexivity.
Lemma ts_B_enter : forall L R,
 csteps tm 4 (StB,(S1::L,S1,R))=
 Some(StC,(ctl L,chd L,S0::S1::R)).
Proof. intros;ts_compute. Qed.
Lemma ts_C0_turn : forall L R,
 csteps tm 2 (StC,(L,S0,S1::R))=
 Some(StA,(S0::S1::L,chd R,ctl R)).
Proof. intros;ts_compute. Qed.
Lemma ts_transfer : forall a L R,
 csteps tm (2*a+10) (StB,(sc_ones(a+3)++S0::L,S1,R))=
 Some(StB,(sc_ones a++S0::S1::L,S1,S1::S1::R)).
Proof.
 intros a L R. replace (a+3) with (S(a+2)) by lia.
 cbn[sc_ones repeat app]. replace (2*a+10) with (4+((a+2)+(2+((a+1)+1)))) by lia.
 rewrite csteps_add,ts_B_enter,csteps_add,(pc_C1_sweep tm HC1).
 cbn[chd ctl]. rewrite csteps_add.
 replace (a+2) with (S(S a)) by lia. cbn[sc_ones repeat app]. rewrite ts_C0_turn.
 replace (a+1) with (S a) by lia.
 change (csteps tm (S a+1)
 (StA,(S0::S1::L,chd(sc_ones(S a)++S0::S1::R),ctl(sc_ones(S a)++S0::S1::R)))=Some(StB,(sc_ones a++S0::S1::L,S1,S1::S1::R))).
 rewrite csteps_add,(sc_A1_sweep tm HA1). cbn[chd ctl sc_ones repeat app].
 apply(sc_A0_turn tm HA0).
Qed.
Lemma ts_C_finish : forall a L R,
 csteps tm (2*a+5)
 (StC,(ctl(sc_ones(S a)++S0::L),chd(sc_ones(S a)++S0::L),S1::S0::R))=
 Some(StB,(sc_ones a++S0::S1::L,S1,S1::R)).
Proof.
 intros a L R. replace (2*a+5) with (S a+(2+(S a+1))) by lia.
 rewrite csteps_add,(pc_C1_sweep tm HC1). cbn[chd ctl].
 rewrite csteps_add. cbn[sc_ones repeat app]. rewrite ts_C0_turn.
 rewrite sc_ones_push.
 change (csteps tm (S a+1)
 (StA,(S0::S1::L,chd(sc_ones(S a)++S0::R),ctl(sc_ones(S a)++S0::R)))=Some(StB,(sc_ones a++S0::S1::L,S1,S1::R))).
 rewrite csteps_add,(sc_A1_sweep tm HA1). cbn[chd ctl]. apply(sc_A0_turn tm HA0).
Qed.
Lemma ts_zero : forall L R,
 csteps tm 1 (StB,(S0::L,S1,R))=Some(StD,(L,S0,S0::R)).
Proof. intros;ts_compute. Qed.
Lemma ts_one : forall L R,
 csteps tm 5 (StB,(S1::S0::L,S1,R))=Some(StD,(S1::L,S0,S1::R)).
Proof. intros;ts_compute. Qed.
Lemma ts_two : forall a L R,
 csteps tm (2*a+15) (StB,(S1::S1::S0::sc_ones(S a)++S0::L,S1,R))=
 Some(StB,(sc_ones a++S0::S1::L,S1,S1::S1::S1::R)).
Proof.
 intros. replace (2*a+15) with (10+(2*a+5)) by lia. rewrite csteps_add.
 assert(E:csteps tm 10 (StB,(S1::S1::S0::sc_ones(S a)++S0::L,S1,R))=
  Some(StC,(ctl(sc_ones(S a)++S0::L),chd(sc_ones(S a)++S0::L),S1::S0::S1::S1::R))).
 { cbn[sc_ones repeat app];ts_compute. }
 rewrite E. apply ts_C_finish.
Qed.
Lemma ts_D_long0 : forall a L,
 csteps tm (a+6) (StD,(L,S0,sc_ones(a+2)++[S0]))=
 Some(StB,(sc_ones a++S0::S1::L,S1,[S1])).
Proof.
 intros a L. replace (a+2) with (S(S a)) by lia.
 assert(E:csteps tm 4 (StD,(L,S0,sc_ones(S(S a))++[S0]))=
 Some(StA,(S0::S1::L,chd(sc_ones(S a)++[S0]),ctl(sc_ones(S a)++[S0])))).
 { cbn[sc_ones repeat app];ts_compute. }
 replace (a+6) with (4+(S a+1)) by lia. rewrite csteps_add,E,csteps_add,(sc_A1_sweep tm HA1).
 cbn[chd ctl sc_ones repeat app]. apply(sc_A0_turn tm HA0).
Qed.
Lemma ts_D_long1 : forall a L,
 csteps tm (a+5) (StD,(L,S0,S0::sc_ones(a+2)++[S0]))=
 Some(StB,(sc_ones a++S0::S1::S0::L,S1,[S1])).
Proof.
 intros a L. replace (a+2) with (S(S a)) by lia.
 assert(E:csteps tm 3 (StD,(L,S0,S0::sc_ones(S(S a))++[S0]))=
 Some(StA,(S0::S1::S0::L,chd(sc_ones(S a)++[S0]),ctl(sc_ones(S a)++[S0])))).
 { cbn[sc_ones repeat app];ts_compute. }
 replace (a+5) with (3+(S a+1)) by lia. rewrite csteps_add,E,csteps_add,(sc_A1_sweep tm HA1).
 cbn[chd ctl sc_ones repeat app]. apply(sc_A0_turn tm HA0).
Qed.
Lemma ts_D_short0 : forall a L,
 csteps tm (2*a+12) (StD,(sc_ones(S a)++S0::L,S0,[S1;S0]))=
 Some(StB,(sc_ones a++S0::S1::L,S1,[S1;S1])).
Proof.
 intros. replace (2*a+12) with (7+(2*a+5)) by lia. rewrite csteps_add.
 assert(E:csteps tm 7 (StD,(sc_ones(S a)++S0::L,S0,[S1;S0]))=
 Some(StC,(ctl(sc_ones(S a)++S0::L),chd(sc_ones(S a)++S0::L),[S1;S0;S1]))).
 { cbn[sc_ones repeat app];ts_compute. }
 rewrite E. apply ts_C_finish.
Qed.
Lemma ts_D_short1 : forall a L,
 csteps tm (2*a+16) (StD,(sc_ones(S a)++S0::L,S0,[S0;S1;S0]))=
 Some(StB,(sc_ones a++S0::S1::L,S1,[S1;S1;S1])).
Proof.
 intros. replace (2*a+16) with (11+(2*a+5)) by lia. rewrite csteps_add.
 assert(E:csteps tm 11 (StD,(sc_ones(S a)++S0::L,S0,[S0;S1;S0]))=
 Some(StC,(ctl(sc_ones(S a)++S0::L),chd(sc_ones(S a)++S0::L),[S1;S0;S1;S1]))).
 { cbn[sc_ones repeat app];ts_compute. }
 rewrite E. apply ts_C_finish.
Qed.
Lemma ts_R_loop : forall k a L R,
 sc_R tm (StB,(sc_ones(3*k+a)++S0::L,S1,R))
 (StB,(sc_ones a++S0::sc_ones k++L,S1,sc_ones(2*k)++R)).
Proof.
 induction k as [|k IH];intros a L R.
 - cbn[Nat.mul Nat.add sc_ones repeat app]. apply sc_R_same;reflexivity.
 - replace (3*S k+a) with ((3*k+a)+3) by lia.
   eapply sc_R_trans;[eapply sc_R_steps;apply ts_transfer|].
   pose proof(IH a (S1::L) (S1::S1::R)) as E.
   rewrite !sc_ones_push in E. replace (2*S k) with (S(S(2*k))) by lia. exact E.
Qed.
Lemma ts_R_loop_B : forall k a w r,
 sc_R tm (pc_B(3*k+a) w r) (pc_B a (pc_inc k w) (2*k+r)).
Proof.
 intros. unfold pc_B. eapply sc_R_trans;[apply ts_R_loop|].
 rewrite <-pc_ones_app.
 pose proof(pc_R_inc tm StB (sc_ones a++[S0]) k w S1 (sc_ones(2*k)++sc_ones r)) as E.
 rewrite <-!app_assoc in E. cbn[app]in E. exact E.
Qed.
Lemma ts_R_zero : forall w r,
 sc_R tm (pc_B 0 w r) (ts_D w true r).
Proof. intros;eapply sc_R_steps;apply ts_zero. Qed.
Lemma ts_R_one : forall w r,
 sc_R tm (pc_B 1 w r) (ts_D(pc_inc 1 w) false (S r)).
Proof.
 intros;unfold pc_B,ts_D. cbn[sc_ones repeat app].
 eapply sc_R_trans;[eapply sc_R_steps;apply ts_one|].
 exact(pc_R_inc tm StD [] 1 w S0 (S1::sc_ones r)).
Qed.
Lemma ts_R_two : forall a w r,
 sc_R tm (pc_B 2 (S a::w) r) (pc_B a (pc_inc 1 w) (3+r)).
Proof.
 intros;unfold pc_B. cbn[sc_ones repeat app pc_word].
 eapply sc_R_trans;[eapply sc_R_steps;apply ts_two|].
 pose proof(pc_R_inc tm StB (sc_ones a++[S0]) 1 w S1 (S1::S1::S1::sc_ones r)) as E.
 rewrite <-!app_assoc in E. cbn[app sc_ones repeat]in E. exact E.
Qed.
Lemma ts_mod3 : forall a,exists k,a=3*k \/ a=3*k+1 \/ a=3*k+2.
Proof.
 intro a. exists(a/3). pose proof(Nat.div_mod a 3 ltac:(lia)).
 pose proof(Nat.mod_upper_bound a 3 ltac:(lia)). lia.
Qed.
Lemma ts_single_found : forall a r,0<r -> ts_found tm (pc_B a [1] r).
Proof.
 induction a as[a IH]using lt_wf_ind;intros r P.
 destruct(ts_mod3 a)as(k&[E|[E|E]]);subst a.
 - replace(3*k)with(3*k+0)by lia.
   eapply ts_found_back;[apply ts_R_loop_B|].
   exists(pc_inc k [1]),true,(2*k+r). split;[apply ts_inc_keep;split;[discriminate|repeat constructor;lia]|].
   split;[lia|apply ts_R_zero].
 - eapply ts_found_back;[apply ts_R_loop_B|].
   exists(pc_inc 1 (pc_inc k [1])),false,(S(2*k+r)).
   split;[apply ts_inc_keep,ts_inc_keep;split;[discriminate|repeat constructor;lia]|].
   split;[lia|apply ts_R_one].
 - eapply ts_found_back;[apply ts_R_loop_B|].
   change(ts_found tm (pc_B 2 [k+1] (2*k+r))). replace(k+1)with(S k)by lia.
   eapply ts_found_back;[apply ts_R_two|]. apply IH;lia.
Qed.
Lemma ts_all_found : forall w a r,ts_wf w -> 0<r -> ts_found tm (pc_B a w r).
Proof.
 assert(F:forall n w,length w=n -> forall a r,ts_wf w -> 0<r -> ts_found tm(pc_B a w r)).
 { induction n as[n IH]using lt_wf_ind. intros [|b w] E a r [W P] R;[contradiction|].
   inversion P as[|? ? B V];subst.
   destruct(ts_mod3 a)as(k&[A|[A|A]]);subst a.
   - replace(3*k)with(3*k+0)by lia.
     eapply ts_found_back;[apply ts_R_loop_B|].
     exists(pc_inc k (b::w)),true,(2*k+r). split;[apply ts_inc_keep;split;assumption|].
     split;[lia|apply ts_R_zero].
   - eapply ts_found_back;[apply ts_R_loop_B|].
     exists(pc_inc 1 (pc_inc k (b::w))),false,(S(2*k+r)).
     split;[apply ts_inc_keep,ts_inc_keep;split;assumption|]. split;[lia|apply ts_R_one].
   - eapply ts_found_back;[apply ts_R_loop_B|]. cbn[pc_inc].
     destruct(k+b)as[|s]eqn:K;[lia|]. eapply ts_found_back;[apply ts_R_two|].
     destruct w as[|c w].
     + apply ts_single_found;lia.
     + eapply IH with(m:=length(c::w));[cbn[length];lia|reflexivity|apply ts_inc_wf;[lia|exact V]|lia]. }
 intros w a r W P. eapply F;[reflexivity|exact W|exact P].
Qed.
Lemma ts_R_D_long : forall w z a,
 sc_R tm (ts_D w z (a+2)) (pc_B a (if z then 1::w else pc_inc 1 w) 1).
Proof.
 intros w [];unfold ts_D,pc_B;cbn[app].
 - intro a. eapply sc_R_trans;[apply sc_R_padR|].
   eapply sc_R_steps;apply ts_D_long1.
 - intro a. eapply sc_R_trans;[apply sc_R_padR|].
   eapply sc_R_trans;[eapply sc_R_steps;apply ts_D_long0|].
   pose proof(pc_R_inc tm StB (sc_ones a++[S0]) 1 w S1 [S1])as E.
   rewrite <-!app_assoc in E. cbn[app sc_ones repeat]in E. exact E.
Qed.
Lemma ts_R_D_short : forall a w z,
 sc_R tm (ts_D(S a::w) z 1) (pc_B a (pc_inc 1 w) (if z then 3 else 2)).
Proof.
 intros a w [];unfold ts_D,pc_B;cbn[app pc_word sc_ones repeat].
 - eapply sc_R_trans;[apply sc_R_padR|].
   eapply sc_R_trans;[eapply sc_R_steps;apply ts_D_short1|].
   pose proof(pc_R_inc tm StB (sc_ones a++[S0]) 1 w S1 [S1;S1;S1])as E.
   rewrite <-!app_assoc in E. cbn[app sc_ones repeat]in E. exact E.
 - eapply sc_R_trans;[apply sc_R_padR|].
   eapply sc_R_trans;[eapply sc_R_steps;apply ts_D_short0|].
   pose proof(pc_R_inc tm StB (sc_ones a++[S0]) 1 w S1 [S1;S1])as E.
   rewrite <-!app_assoc in E. cbn[app sc_ones repeat]in E. exact E.
Qed.
Lemma ts_D_return : forall w z r,ts_wf w -> 0<r -> exists a v s,
 ts_wf v /\ 0<s /\ sc_R tm(ts_D w z r)(pc_B a v s).
Proof.
 intros w z [|[|r]] W P;[lia| |].
 - destruct w as[|b w];destruct W as[N W];[contradiction|].
   inversion W;subst. destruct b as[|a];[lia|].
   exists a,(pc_inc 1 w),(if z then 3 else 2).
   split;[apply ts_inc_wf;[lia|assumption]|]. split;[destruct z;lia|apply ts_R_D_short].
 - replace(S(S r))with(r+2)by lia.
   exists r,(if z then 1::w else pc_inc 1 w),1.
   split;[destruct z;[apply ts_cons_wf;[lia|exact W]|apply ts_inc_keep;exact W]|].
   split;[lia|apply ts_R_D_long].
Qed.
Lemma ts_D_progress : forall w z r,ts_wf w -> 0<r -> exists v y s k,
 ts_wf v /\ 0<s /\ 0<k /\ stepn tm k(lift(ts_D w z r))=Some(lift(ts_D v y s)).
Proof.
 intros w z r W P. destruct(ts_D_return w z r W P)as(a&v&s&V&S&n&En).
 destruct(ts_all_found v a s V S)as(u&y&t&U&T&m&Em).
 assert(Hn:0<n).
 { destruct n;[cbn[stepn ts_D pc_B lift]in En;discriminate|lia]. }
 exists u,y,t,(n+m). split;[exact U|]. split;[exact T|]. split;[lia|].
 rewrite stepn_add,En;exact Em.
Qed.

Local Ltac ts_fire_n fuel := eapply(sc_fire_steps tm)with(n:=fuel);[ts_compute|apply sc_fire_now].
Lemma ts_C_finish_A1 : forall a L R,
 tri_reaches_fire tm (StA,S1)
 (StC,(ctl(sc_ones(S a)++S0::L),chd(sc_ones(S a)++S0::L),S1::S0::R)).
Proof.
 intros. eapply(sc_fire_steps tm);[apply(pc_C1_sweep tm HC1)|]. cbn[chd ctl].
 cbn[sc_ones repeat app]. eapply(sc_fire_steps tm);[apply ts_C0_turn|].
 destruct a;apply sc_fire_now.
Qed.
Lemma ts_large_fire : forall a L R t,t<>(StD,S0) ->
 tri_reaches_fire tm t (StB,(sc_ones(a+3)++S0::L,S1,R)).
Proof.
 intros a L R [q h] E. replace(a+3)with(S(S(S a)))by lia. cbn[sc_ones repeat app].
 destruct q,h;try contradiction;try solve[apply sc_fire_now];
 try solve[ts_fire_n 1|ts_fire_n 2|ts_fire_n 3|ts_fire_n 4].
 - eapply(sc_fire_steps tm);[apply ts_B_enter|].
   eapply(sc_fire_steps tm);[apply(pc_C1_sweep tm HC1 (S(S a)) (S0::L))|].
   cbn[chd ctl sc_ones repeat app]. eapply(sc_fire_steps tm);[apply ts_C0_turn|].
   apply sc_fire_now.
 - eapply(sc_fire_steps tm);[apply ts_B_enter|].
   eapply(sc_fire_steps tm);[apply(pc_C1_sweep tm HC1 (S(S a)) (S0::L))|].
   apply sc_fire_now.
Qed.
Lemma ts_two_fire : forall a L R t,t<>(StD,S0) ->
 tri_reaches_fire tm t (StB,(S1::S1::S0::sc_ones(S a)++S0::L,S1,R)).
Proof.
 intros a L R [q h] E. cbn[sc_ones repeat app].
 destruct q,h;try contradiction;try solve[apply sc_fire_now];
 try solve[ts_fire_n 1|ts_fire_n 2|ts_fire_n 3|ts_fire_n 4|ts_fire_n 5].
 eapply(sc_fire_steps tm)with(n:=10);[ts_compute|]. apply ts_C_finish_A1.
Qed.
Lemma ts_B_fire : forall a w r t,ts_wf w -> 2<=a -> t<>(StD,S0) ->
 tri_reaches_fire tm t (pc_B a w r).
Proof.
 intros a w r t [W P] A T. destruct a as[|[|[|a]]];try lia.
 - destruct w as[|b w];[contradiction|]. inversion P;subst. destruct b;[lia|].
   apply ts_two_fire;exact T.
 - replace(S(S(S a)))with(a+3)by lia. apply ts_large_fire;exact T.
Qed.
Lemma ts_short_fire : forall a w z t,
 tri_reaches_fire tm t (ts_D(S a::w) z 1).
Proof.
 intros a w [] [q h];unfold ts_D;cbn[pc_word sc_ones repeat app].
 - eapply(sc_fire_R tm);[apply sc_R_padR|].
   destruct q,h;try solve[apply sc_fire_now];
   try solve[ts_fire_n 1|ts_fire_n 2|ts_fire_n 3|ts_fire_n 4|ts_fire_n 5].
   + eapply(sc_fire_steps tm)with(n:=11);[ts_compute|]. apply ts_C_finish_A1.
   + eapply(sc_fire_steps tm);[apply ts_D_short1|]. apply sc_fire_now.
 - eapply(sc_fire_R tm);[apply sc_R_padR|].
   destruct q,h;try solve[apply sc_fire_now];
   try solve[ts_fire_n 1|ts_fire_n 2|ts_fire_n 3|ts_fire_n 4|ts_fire_n 5].
   + eapply(sc_fire_steps tm)with(n:=7);[ts_compute|]. apply ts_C_finish_A1.
   + eapply(sc_fire_steps tm);[apply ts_D_short0|]. apply sc_fire_now.
Qed.
Lemma ts_next_wf : forall (z:bool) w,ts_wf w -> ts_wf(if z then 1::w else pc_inc 1 w).
Proof. intros [] w W;[apply ts_cons_wf;[lia|exact W]|apply ts_inc_keep;exact W]. Qed.
Lemma ts_D_one_all : forall w z t,ts_wf w -> tri_reaches_fire tm t(ts_D w z 1).
Proof.
 intros [|b w] z t [W P];[contradiction|]. inversion P;subst. destruct b;[lia|]. apply ts_short_fire.
Qed.
Lemma ts_D_two_all : forall w z t,ts_wf w -> tri_reaches_fire tm t(ts_D w z 2).
Proof.
 intros w z t W. eapply(sc_fire_R tm);[apply(ts_R_D_long w z 0)|].
 eapply(sc_fire_R tm);[apply ts_R_zero|]. apply ts_D_one_all,ts_next_wf;exact W.
Qed.
Lemma ts_D_three_all : forall w z t,ts_wf w -> tri_reaches_fire tm t(ts_D w z 3).
Proof.
 intros w z t W. eapply(sc_fire_R tm);[apply(ts_R_D_long w z 1)|].
 eapply(sc_fire_R tm);[apply ts_R_one|]. apply ts_D_two_all,ts_inc_keep,ts_next_wf;exact W.
Qed.
Lemma ts_D_all_fire : forall w z r t,ts_wf w -> 0<r -> tri_reaches_fire tm t(ts_D w z r).
Proof.
 intros w z [|[|[|[|r]]]] t W P;[lia|apply ts_D_one_all;exact W|apply ts_D_two_all;exact W|apply ts_D_three_all;exact W|].
 destruct(instr_eqb t(StD,S0))eqn:E.
 - apply instr_eqb_spec in E;subst t;apply sc_fire_now.
 - replace(S(S(S(S r))))with((r+2)+2)by lia.
   eapply(sc_fire_R tm);[apply ts_R_D_long|].
   apply ts_B_fire;[apply ts_next_wf;exact W|lia|]. intro F;subst t;discriminate.
Qed.
Theorem ternary_stack_neverqhtr :
 (exists T w z r,ts_wf w /\ 0<r /\ stepn tm T InitES=Some(lift(ts_D w z r))) ->
 NeverQuasiHaltsTr tm.
Proof.
 intro Boot.
 assert(Reach:forall N,exists T w z r,N<=T /\ ts_wf w /\ 0<r /\
 stepn tm T InitES=Some(lift(ts_D w z r))).
 { induction N as[|N IH].
   - destruct Boot as(T&w&z&r&W&P&E). exists T,w,z,r. split;[lia|]. split;[exact W|]. split;assumption.
   - destruct IH as(T&w&z&r&HT&W&P&E).
     destruct(ts_D_progress w z r W P)as(v&y&s&k&V&Q&Hk&Ek).
     exists(T+k),v,y,s. split;[lia|]. split;[exact V|]. split;[exact Q|].
     rewrite stepn_add,E;exact Ek. }
 intros t _ N. destruct(Reach N)as(T&w&z&r&HT&W&P&E).
 destruct(ts_D_all_fire w z r t W P)as(k&c&Ek&Et).
 exists(T+k). split;[lia|]. exists c. split;[|exact Et]. rewrite stepn_add,E;exact Ek.
Qed.
End TernaryStack.
