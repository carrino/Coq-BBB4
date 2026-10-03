(** * Triple-sweep finite-tape reachability.

    Seven transition equations force C1 from every finite configuration;
    the transition at C1 is unrestricted. D scans 100 blocks, writing 011
    behind it. At a zero or two ones, the return sweep drains those blocks.
    From the blank left frontier, the return leaves a 101 marker, possibly
    after one additional lap; scanning that marker reaches C1. Strong
    induction on the finite left word extends the result to arbitrary
    tapes. [FiniteInstrTr] turns this reachability into recurrence. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape DyadicWindowTr.
Import ListNotations.
Fixpoint ts_left(n:nat):list Sym := match n with 0=>[]|S n=>S1::S1::S0::ts_left n end.
Fixpoint ts_right(n:nat):list Sym := match n with 0=>[]|S n=>S1::S0::S0::ts_right n end.
Lemma ts_lpush:forall n L,ts_left n++S1::S1::S0::L=ts_left(S n)++L.
Proof. induction n;intros;cbn[ts_left app];[reflexivity|now rewrite IHn]. Qed.
Lemma ts_rpush:forall n L,ts_right n++S1::S0::S0::L=ts_right(S n)++L.
Proof. induction n;intros;cbn[ts_right app];[reflexivity|now rewrite IHn]. Qed.
Definition ts_A(L R:list Sym):cconf := (StA,(ctl L,chd L,R)).
Definition ts_D(L R:list Sym):cconf := (StD,(L,chd R,ctl R)).
Section Core.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S0 DL StB))
 (HA1:tm StA S1=Some(mkTrans S1 DL StA))
 (HB0:tm StB S0=Some(mkTrans S1 DR StC))
 (HB1:tm StB S1=Some(mkTrans S0 DL StA))
 (HC0:tm StC S0=Some(mkTrans S1 DR StD))
 (HD0:tm StD S0=Some(mkTrans S1 DL StB))
 (HD1:tm StD S1=Some(mkTrans S0 DR StB)).
Local Ltac run :=
 cbn[Nat.add Nat.mul csteps cstep ctape_move chd ctl t_next t_dir t_write app ts_A ts_D ts_left ts_right];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HD0|rewrite HD1];
 cbn[Nat.add Nat.mul csteps cstep ctape_move chd ctl t_next t_dir t_write app ts_A ts_D ts_left ts_right]);reflexivity.
Definition ts_hit(c:cconf):Prop:=exists k e,stepn tm k(lift c)=Some e /\ instr_of e=(StC,S1).
Lemma ts_now:forall L R,ts_hit(StC,(L,S1,R)).
Proof. intros;exists 0,(lift(StC,(L,S1,R)));split;reflexivity. Qed.
Lemma ts_back:forall k c d,csteps tm k c=Some d->ts_hit d->ts_hit c.
Proof. intros k c d E(j&e&Hj&Hi). exists(k+j),e;split;[rewrite stepn_add,(csteps_lift _ _ _ _ E);exact Hj|exact Hi]. Qed.
Lemma ts_eq:forall c d,lift c=lift d->ts_hit d->ts_hit c.
Proof. intros c d E H;unfold ts_hit in*;now rewrite E. Qed.
Lemma ts_pad:forall q L h R,lift(q,(L,h,R++[S0]))=lift(q,(L,h,R)).
Proof. intros;unfold lift,lift_tape;cbn;rewrite lift_side_app_blank;reflexivity. Qed.
Lemma ts_scan:forall n L R,
 csteps tm(3*n)(ts_D L(ts_right n++R))=Some(ts_D(ts_left n++L)R).
Proof.
 induction n as[|n IH];intros;[reflexivity|].
 replace(3*S n)with(3+3*n)by lia. rewrite csteps_add.
 assert(E:csteps tm 3(ts_D L(ts_right(S n)++R))=Some(ts_D(S1::S1::S0::L)(ts_right n++R)))by run.
 rewrite E,IH,ts_lpush;reflexivity.
Qed.
Lemma ts_drain:forall n U R,
 csteps tm(3*n+3)(StA,(ts_left n++S1::S1::U,S0,R))=Some(ts_A U(ts_right(S n)++R)).
Proof.
 induction n as[|n IH];intros;[run|].
 replace(3*S n+3)with(3+(3*n+3))by lia. rewrite csteps_add.
 assert(E:csteps tm 3(StA,(ts_left(S n)++S1::S1::U,S0,R))=
 Some(StA,(ts_left n++S1::S1::U,S0,S1::S0::S0::R)))by run.
 rewrite E,IH,ts_rpush;reflexivity.
Qed.
Lemma ts_zero:forall n U R,
 csteps tm(3*n+3)(ts_D(ts_left n++S1::S1::U)(S0::R))=
 Some(ts_A U(ts_right n++S1::S0::S1::R)).
Proof.
 destruct n as[|n];intros;[run|].
 replace(3*S n+3)with(3+(3*n+3))by lia. rewrite csteps_add.
 assert(E:csteps tm 3(ts_D(ts_left(S n)++S1::S1::U)(S0::R))=
 Some(StA,(ts_left n++S1::S1::U,S0,S1::S0::S1::R)))by run.
 rewrite E,ts_drain;reflexivity.
Qed.
Lemma ts_ones:forall n U R,
 csteps tm(2+(3*n+3))(ts_D(ts_left n++S1::S1::U)(S1::S1::R))=
 Some(ts_A U(ts_right(S n)++S0::R)).
Proof.
 intros. rewrite csteps_add.
 assert(E:csteps tm 2(ts_D(ts_left n++S1::S1::U)(S1::S1::R))=
 Some(StA,(ts_left n++S1::S1::U,S0,S0::R)))by run.
 rewrite E,ts_drain;reflexivity.
Qed.
Lemma ts_marker:forall L R,ts_hit(ts_D L(S1::S0::S1::R)).
Proof.
 intros. eapply ts_back with(k:=2)(d:=(StC,(S1::S0::L,S1,R)));[run|apply ts_now].
Qed.
Lemma ts_enter:forall U R,csteps tm 3(StA,(S0::U,S0,R))=Some(ts_D(S1::S1::U)R).
Proof. intros;run. Qed.
Lemma ts_empty:forall R,csteps tm 3(ts_A [] R)=Some(ts_D[S1;S1]R).
Proof. intros;run. Qed.
Lemma ts_blank:forall L,ts_hit(ts_D L[S0])->ts_hit(ts_D L[]).
Proof. intros;exact H. Qed.
Lemma ts_empty_marker:forall n R,ts_hit(ts_A [](ts_right n++S1::S0::S1::R)).
Proof. intros;eapply ts_back;[apply ts_empty|];eapply ts_back;[apply ts_scan|apply ts_marker]. Qed.
Lemma ts_empty_zero:forall n R,ts_hit(ts_A [](ts_right n++S0::R)).
Proof.
 intros;eapply ts_back;[apply ts_empty|];eapply ts_back;[apply ts_scan|].
 eapply ts_back;[apply ts_zero|apply ts_empty_marker].
Qed.
Lemma ts_blank_hit:forall n,ts_hit(ts_D(ts_left n++[S1;S1])[]).
Proof. intros;apply ts_blank;eapply ts_back;[apply ts_zero|apply ts_empty_marker]. Qed.
Lemma ts_frontier:forall R n,ts_hit(ts_D(ts_left n++[S1;S1])R).
Proof.
 fix IH 1. intros R n. destruct R as[|[] R].
 - apply ts_blank. eapply ts_back;[apply ts_zero|apply ts_empty_marker].
 - eapply ts_back;[apply ts_zero|apply ts_empty_marker].
 - destruct R as[|[] R].
   + eapply ts_eq with(d:=ts_D(ts_left n++[S1;S1])[S1;S0;S0]).
     * symmetry. unfold ts_D;cbn[chd ctl].
       change(lift(StD,(ts_left n++[S1;S1],S1,([]++[S0])++[S0]))=lift(StD,(ts_left n++[S1;S1],S1,[]))).
       now rewrite !ts_pad.
     * eapply ts_back;[apply ts_scan with(n:=1)|exact(ts_blank_hit(S n))].
   + destruct R as[|[] R].
     * eapply ts_eq with(d:=ts_D(ts_left n++[S1;S1])[S1;S0;S0]).
       -- symmetry. unfold ts_D;cbn[chd ctl]. apply(ts_pad StD _ S1 [S0]).
       -- eapply ts_back;[apply ts_scan with(n:=1)|exact(ts_blank_hit(S n))].
     * eapply ts_back with(k:=3)(d:=ts_D(ts_left(S n)++[S1;S1])R);[run|apply IH].
     * apply ts_marker.
   + eapply ts_back;[apply ts_ones|apply ts_empty_zero].
Qed.
Lemma ts_empty_hit:forall R,ts_hit(ts_A [] R).
Proof. intro R;eapply ts_back;[apply ts_empty|apply(ts_frontier R 0)]. Qed.
Lemma ts_suffix:forall U,(forall R,ts_hit(ts_A U R))->forall R n,
 ts_hit(ts_D(ts_left n++S1::S1::U)R).
Proof.
 intros U HU. fix IH 1. intros R n. destruct R as[|[] R].
 - apply ts_blank;eapply ts_back;[apply ts_zero|apply HU].
 - eapply ts_back;[apply ts_zero|apply HU].
 - destruct R as[|[] R].
   + eapply ts_eq with(d:=ts_D(ts_left n++S1::S1::U)[S1;S0;S0]).
     * symmetry. unfold ts_D;cbn[chd ctl].
       change(lift(StD,(ts_left n++S1::S1::U,S1,([]++[S0])++[S0]))=lift(StD,(ts_left n++S1::S1::U,S1,[]))).
       now rewrite !ts_pad.
     * eapply ts_back;[apply ts_scan with(n:=1)|].
       change(ts_hit(ts_D(ts_left(S n)++S1::S1::U)[])).
       apply ts_blank;eapply ts_back;[apply ts_zero|apply HU].
   + destruct R as[|[] R].
     * eapply ts_eq with(d:=ts_D(ts_left n++S1::S1::U)[S1;S0;S0]).
       -- symmetry. unfold ts_D;cbn[chd ctl]. apply(ts_pad StD _ S1 [S0]).
       -- eapply ts_back;[apply ts_scan with(n:=1)|].
          change(ts_hit(ts_D(ts_left(S n)++S1::S1::U)[])).
          apply ts_blank;eapply ts_back;[apply ts_zero|apply HU].
     * eapply ts_back with(k:=3)(d:=ts_D(ts_left(S n)++S1::S1::U)R);[run|apply IH].
     * apply ts_marker.
   + eapply ts_back;[apply ts_ones|apply HU].
Qed.
Lemma ts_A_word:forall L R,ts_hit(ts_A L R).
Proof.
 intro L. remember(length L)as z eqn:Ez. revert L Ez.
 induction z using lt_wf_ind;intros L Ez R.
 destruct L as[|[] L];[apply ts_empty_hit| |].
 - destruct L as[|[] L].
   + apply ts_empty_hit.
   + eapply ts_back;[apply ts_enter|].
     assert(HL:forall V,ts_hit(ts_A L V)).
     { intro V;apply(H(length L));[cbn in Ez;lia|reflexivity]. }
     exact(ts_suffix L HL R 0).
   + eapply ts_back with(k:=2)(d:=ts_A L(S0::S0::R));[run|].
     apply(H(length L));[cbn in Ez;lia|reflexivity].
 - eapply ts_back with(k:=1)(d:=ts_A L(S1::R));[run|].
   apply(H(length L));[cbn in Ez;lia|reflexivity].
Qed.
Lemma ts_A_finite:forall L h R,ts_hit(StA,(L,h,R)).
Proof. intros;exact(ts_A_word(h::L)R). Qed.
Lemma ts_Dzero:forall L R,ts_hit(ts_D L(S0::R)).
Proof.
 intros[|[] L] R.
 - eapply ts_back with(k:=2)(d:=(StC,([S1],S1,R)));[run|apply ts_now].
 - eapply ts_back with(k:=2)(d:=(StC,(S1::L,S1,R)));[run|apply ts_now].
 - eapply ts_back with(k:=2)(d:=ts_A L(S0::S1::R));[run|apply ts_A_word].
Qed.
Lemma ts_D_finite:forall R L,ts_hit(ts_D L R).
Proof.
 fix IH 1. intros R L. destruct R as[|[] R].
 - apply ts_blank,ts_Dzero.
 - apply ts_Dzero.
 - destruct R as[|[] R].
   + eapply ts_eq with(d:=ts_D L[S1;S0;S0]).
     * symmetry;unfold ts_D;cbn[chd ctl].
       change(lift(StD,(L,S1,([]++[S0])++[S0]))=lift(StD,(L,S1,[]))).
       now rewrite !ts_pad.
     * eapply ts_back;[apply ts_scan with(n:=1)|apply ts_blank,ts_Dzero].
   + destruct R as[|[] R].
     * eapply ts_eq with(d:=ts_D L[S1;S0;S0]).
       -- symmetry;unfold ts_D;cbn[chd ctl]. apply(ts_pad StD _ S1 [S0]).
       -- eapply ts_back;[apply ts_scan with(n:=1)|apply ts_blank,ts_Dzero].
     * eapply ts_back with(k:=3)(d:=ts_D(S1::S1::S0::L)R);[run|apply IH].
     * apply ts_marker.
   + eapply ts_back with(k:=2)(d:=(StA,(L,S0,S0::R)));[run|apply ts_A_finite].
Qed.
Lemma ts_C_finite:forall L h R,ts_hit(StC,(L,h,R)).
Proof.
 intros L[]R;[|apply ts_now].
 eapply ts_back with(k:=1)(d:=ts_D(S1::L)R);[run|apply ts_D_finite].
Qed.
Theorem ts_finite:forall c,ts_hit c.
Proof.
 intros[q[[L h]R]]. destruct q.
 - apply ts_A_finite.
 - destruct h.
   + eapply ts_back with(k:=1)(d:=(StC,(S1::L,chd R,ctl R)));[run|apply ts_C_finite].
   + eapply ts_back with(k:=1)(d:=ts_A L(S0::R));[run|apply ts_A_word].
 - apply ts_C_finite.
 - exact(ts_D_finite(h::R)L).
Qed.
End Core.
