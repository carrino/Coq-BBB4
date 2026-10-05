(** A finite-tape ranking witness for the M core's A1 instruction. *)
From Coq Require Import Arith Lia List ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr BlockCoreMRankTr.
From BBB4.Counters Require Import BlockCoreMReturnTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Open Scope Z_scope.
(* BEGIN GENERATED A1 RANK CERTIFICATE *)
Definition bmfr_bias(q:St)(h a b c:Sym)(s:bm_dfa):Z:=match q,h,a,b,c,s with
|StA,S0,S0,S0,S0,M0=>13
|StA,S0,S0,S0,S0,M7=>4
|StA,S0,S0,S0,S1,M0=>13
|StA,S0,S0,S0,S1,M7=>4
|StA,S0,S0,S1,S0,M0=>13
|StA,S0,S0,S1,S0,M7=>4
|StA,S0,S0,S1,S1,M0=>13
|StA,S0,S0,S1,S1,M7=>4
|StA,S0,S1,S0,S0,M0=>10
|StA,S0,S1,S0,S0,M1=>10
|StA,S0,S1,S0,S0,M5=>10
|StA,S0,S1,S0,S0,M7=>2
|StA,S0,S1,S0,S0,M10=>2
|StA,S0,S1,S0,S0,M16=>10
|StA,S0,S1,S0,S1,M0=>10
|StA,S0,S1,S0,S1,M1=>10
|StA,S0,S1,S0,S1,M5=>10
|StA,S0,S1,S0,S1,M7=>2
|StA,S0,S1,S0,S1,M10=>2
|StA,S0,S1,S0,S1,M16=>10
|StA,S0,S1,S1,S0,M0=>10
|StA,S0,S1,S1,S0,M1=>10
|StA,S0,S1,S1,S0,M5=>10
|StA,S0,S1,S1,S0,M7=>14
|StA,S0,S1,S1,S0,M10=>14
|StA,S0,S1,S1,S0,M16=>10
|StA,S0,S1,S1,S1,M0=>10
|StA,S0,S1,S1,S1,M1=>10
|StA,S0,S1,S1,S1,M5=>10
|StA,S0,S1,S1,S1,M7=>14
|StA,S0,S1,S1,S1,M10=>14
|StA,S0,S1,S1,S1,M16=>10
|StB,S0,S0,S0,S0,M3=>14
|StB,S0,S0,S0,S0,M4=>14
|StB,S0,S0,S0,S0,M5=>14
|StB,S0,S0,S0,S0,M7=>14
|StB,S0,S0,S0,S0,M10=>14
|StB,S0,S0,S0,S0,M11=>14
|StB,S0,S0,S0,S0,M13=>14
|StB,S0,S0,S0,S0,M15=>14
|StB,S0,S0,S0,S0,M18=>14
|StB,S0,S0,S0,S1,M3=>14
|StB,S0,S0,S0,S1,M4=>14
|StB,S0,S0,S0,S1,M5=>14
|StB,S0,S0,S0,S1,M7=>14
|StB,S0,S0,S0,S1,M10=>14
|StB,S0,S0,S0,S1,M11=>14
|StB,S0,S0,S0,S1,M13=>14
|StB,S0,S0,S0,S1,M15=>14
|StB,S0,S0,S0,S1,M18=>14
|StB,S0,S0,S1,S0,M0=>9
|StB,S0,S0,S1,S0,M4=>14
|StB,S0,S0,S1,S0,M7=>4
|StB,S0,S0,S1,S0,M10=>4
|StB,S0,S0,S1,S0,M11=>14
|StB,S0,S0,S1,S0,M12=>14
|StB,S0,S0,S1,S1,M0=>9
|StB,S0,S0,S1,S1,M4=>14
|StB,S0,S0,S1,S1,M7=>16
|StB,S0,S0,S1,S1,M10=>16
|StB,S0,S0,S1,S1,M11=>14
|StB,S0,S0,S1,S1,M12=>14
|StB,S0,S1,S0,S0,M3=>14
|StB,S0,S1,S0,S0,M4=>14
|StB,S0,S1,S0,S0,M5=>14
|StB,S0,S1,S0,S0,M10=>14
|StB,S0,S1,S0,S0,M11=>14
|StB,S0,S1,S0,S0,M12=>14
|StB,S0,S1,S0,S0,M13=>14
|StB,S0,S1,S0,S0,M15=>14
|StB,S0,S1,S0,S0,M18=>14
|StB,S0,S1,S0,S1,M3=>14
|StB,S0,S1,S0,S1,M4=>14
|StB,S0,S1,S0,S1,M5=>14
|StB,S0,S1,S0,S1,M10=>14
|StB,S0,S1,S0,S1,M11=>14
|StB,S0,S1,S0,S1,M12=>14
|StB,S0,S1,S0,S1,M13=>14
|StB,S0,S1,S0,S1,M15=>14
|StB,S0,S1,S0,S1,M18=>14
|StB,S0,S1,S1,S0,M3=>14
|StB,S0,S1,S1,S0,M4=>14
|StB,S0,S1,S1,S0,M5=>14
|StB,S0,S1,S1,S0,M10=>14
|StB,S0,S1,S1,S0,M11=>14
|StB,S0,S1,S1,S0,M12=>14
|StB,S0,S1,S1,S0,M15=>14
|StB,S0,S1,S1,S0,M18=>14
|StB,S0,S1,S1,S1,M3=>14
|StB,S0,S1,S1,S1,M4=>14
|StB,S0,S1,S1,S1,M5=>14
|StB,S0,S1,S1,S1,M10=>14
|StB,S0,S1,S1,S1,M11=>14
|StB,S0,S1,S1,S1,M12=>14
|StB,S0,S1,S1,S1,M15=>14
|StB,S0,S1,S1,S1,M18=>14
|StB,S1,S0,S0,S0,M4=>6
|StB,S1,S0,S0,S0,M6=>14
|StB,S1,S0,S0,S0,M8=>14
|StB,S1,S0,S0,S0,M11=>14
|StB,S1,S0,S0,S0,M12=>14
|StB,S1,S0,S0,S0,M14=>14
|StB,S1,S0,S0,S1,M4=>6
|StB,S1,S0,S0,S1,M6=>14
|StB,S1,S0,S0,S1,M8=>14
|StB,S1,S0,S0,S1,M11=>14
|StB,S1,S0,S0,S1,M12=>14
|StB,S1,S0,S0,S1,M14=>14
|StB,S1,S0,S1,S0,M4=>4
|StB,S1,S0,S1,S0,M6=>14
|StB,S1,S0,S1,S0,M8=>14
|StB,S1,S0,S1,S0,M11=>14
|StB,S1,S0,S1,S0,M12=>14
|StB,S1,S0,S1,S0,M14=>14
|StB,S1,S0,S1,S1,M4=>16
|StB,S1,S0,S1,S1,M6=>14
|StB,S1,S0,S1,S1,M8=>14
|StB,S1,S0,S1,S1,M11=>14
|StB,S1,S0,S1,S1,M12=>14
|StB,S1,S0,S1,S1,M14=>14
|StB,S1,S1,S0,S0,M4=>6
|StB,S1,S1,S0,S0,M6=>14
|StB,S1,S1,S0,S0,M8=>14
|StB,S1,S1,S0,S0,M11=>14
|StB,S1,S1,S0,S0,M12=>14
|StB,S1,S1,S0,S0,M14=>14
|StB,S1,S1,S0,S1,M4=>6
|StB,S1,S1,S0,S1,M6=>14
|StB,S1,S1,S0,S1,M8=>14
|StB,S1,S1,S0,S1,M11=>14
|StB,S1,S1,S0,S1,M12=>14
|StB,S1,S1,S0,S1,M14=>14
|StB,S1,S1,S1,S0,M4=>6
|StB,S1,S1,S1,S0,M6=>16
|StB,S1,S1,S1,S0,M8=>14
|StB,S1,S1,S1,S0,M11=>14
|StB,S1,S1,S1,S0,M12=>14
|StB,S1,S1,S1,S0,M14=>14
|StB,S1,S1,S1,S1,M4=>6
|StB,S1,S1,S1,S1,M6=>16
|StB,S1,S1,S1,S1,M8=>14
|StB,S1,S1,S1,S1,M11=>14
|StB,S1,S1,S1,S1,M12=>14
|StB,S1,S1,S1,S1,M14=>14
|StC,S0,S0,S0,S0,M6=>20
|StC,S0,S0,S0,S0,M8=>20
|StC,S0,S0,S0,S0,M11=>20
|StC,S0,S0,S0,S0,M12=>20
|StC,S0,S0,S0,S0,M14=>20
|StC,S0,S0,S0,S1,M6=>20
|StC,S0,S0,S0,S1,M8=>20
|StC,S0,S0,S0,S1,M11=>20
|StC,S0,S0,S0,S1,M12=>20
|StC,S0,S0,S0,S1,M14=>20
|StC,S0,S0,S1,S0,M4=>10
|StC,S0,S0,S1,S0,M6=>20
|StC,S0,S0,S1,S0,M8=>20
|StC,S0,S0,S1,S0,M11=>20
|StC,S0,S0,S1,S0,M12=>20
|StC,S0,S0,S1,S0,M14=>20
|StC,S0,S0,S1,S1,M4=>22
|StC,S0,S0,S1,S1,M6=>20
|StC,S0,S0,S1,S1,M8=>20
|StC,S0,S0,S1,S1,M11=>20
|StC,S0,S0,S1,S1,M12=>20
|StC,S0,S0,S1,S1,M14=>20
|StC,S0,S1,S0,S0,M12=>10
|StC,S0,S1,S0,S1,M1=>10
|StC,S0,S1,S0,S1,M3=>10
|StC,S0,S1,S0,S1,M7=>2
|StC,S0,S1,S0,S1,M10=>2
|StC,S0,S1,S0,S1,M13=>10
|StC,S0,S1,S0,S1,M17=>10
|StC,S1,S0,S0,S0,M8=>10
|StC,S1,S0,S0,S0,M9=>20
|StC,S1,S0,S0,S0,M10=>0
|StC,S1,S0,S0,S0,M12=>10
|StC,S1,S0,S0,S0,M13=>10
|StC,S1,S0,S0,S1,M1=>10
|StC,S1,S0,S0,S1,M3=>10
|StC,S1,S0,S0,S1,M7=>10
|StC,S1,S0,S0,S1,M8=>10
|StC,S1,S0,S0,S1,M9=>20
|StC,S1,S0,S0,S1,M10=>0
|StC,S1,S0,S0,S1,M12=>10
|StC,S1,S0,S0,S1,M13=>10
|StC,S1,S0,S0,S1,M17=>10
|StC,S1,S0,S1,S0,M1=>8
|StC,S1,S0,S1,S0,M3=>8
|StC,S1,S0,S1,S0,M8=>10
|StC,S1,S0,S1,S0,M10=>0
|StC,S1,S0,S1,S0,M12=>10
|StC,S1,S0,S1,S0,M13=>10
|StC,S1,S0,S1,S0,M17=>8
|StC,S1,S0,S1,S1,M1=>8
|StC,S1,S0,S1,S1,M3=>8
|StC,S1,S0,S1,S1,M8=>10
|StC,S1,S0,S1,S1,M10=>0
|StC,S1,S0,S1,S1,M12=>10
|StC,S1,S0,S1,S1,M13=>10
|StC,S1,S0,S1,S1,M17=>8
|StC,S1,S1,S0,S0,M1=>8
|StC,S1,S1,S0,S0,M3=>8
|StC,S1,S1,S0,S0,M8=>10
|StC,S1,S1,S0,S0,M12=>10
|StC,S1,S1,S0,S0,M13=>10
|StC,S1,S1,S0,S0,M17=>8
|StC,S1,S1,S0,S1,M4=>2
|StC,S1,S1,S0,S1,M8=>10
|StC,S1,S1,S0,S1,M12=>10
|StC,S1,S1,S0,S1,M13=>10
|StC,S1,S1,S1,S0,M1=>8
|StC,S1,S1,S1,S0,M3=>8
|StC,S1,S1,S1,S0,M8=>10
|StC,S1,S1,S1,S0,M12=>10
|StC,S1,S1,S1,S0,M13=>10
|StC,S1,S1,S1,S0,M17=>8
|StC,S1,S1,S1,S1,M1=>8
|StC,S1,S1,S1,S1,M3=>8
|StC,S1,S1,S1,S1,M8=>10
|StC,S1,S1,S1,S1,M12=>10
|StC,S1,S1,S1,S1,M13=>10
|StC,S1,S1,S1,S1,M17=>8
|StD,S0,S0,S0,S0,M8=>14
|StD,S0,S0,S0,S0,M10=>4
|StD,S0,S0,S0,S0,M12=>14
|StD,S0,S0,S0,S0,M13=>14
|StD,S0,S0,S0,S1,M8=>14
|StD,S0,S0,S0,S1,M10=>4
|StD,S0,S0,S0,S1,M12=>14
|StD,S0,S0,S0,S1,M13=>14
|StD,S0,S0,S1,S0,M8=>14
|StD,S0,S0,S1,S0,M10=>4
|StD,S0,S0,S1,S0,M12=>14
|StD,S0,S0,S1,S0,M13=>14
|StD,S0,S0,S1,S1,M8=>14
|StD,S0,S0,S1,S1,M10=>4
|StD,S0,S0,S1,S1,M12=>14
|StD,S0,S0,S1,S1,M13=>14
|StD,S0,S1,S0,S0,M8=>14
|StD,S0,S1,S0,S0,M10=>16
|StD,S0,S1,S0,S0,M12=>14
|StD,S0,S1,S0,S0,M13=>14
|StD,S0,S1,S0,S1,M8=>14
|StD,S0,S1,S0,S1,M10=>16
|StD,S0,S1,S0,S1,M12=>14
|StD,S0,S1,S0,S1,M13=>14
|StD,S0,S1,S1,S0,M8=>14
|StD,S0,S1,S1,S0,M10=>16
|StD,S0,S1,S1,S0,M12=>14
|StD,S0,S1,S1,S0,M13=>14
|StD,S0,S1,S1,S1,M8=>14
|StD,S0,S1,S1,S1,M10=>16
|StD,S0,S1,S1,S1,M12=>14
|StD,S0,S1,S1,S1,M13=>14
|StD,S1,S0,S0,S0,M6=>14
|StD,S1,S0,S0,S0,M7=>4
|StD,S1,S0,S0,S0,M9=>14
|StD,S1,S0,S0,S0,M10=>4
|StD,S1,S0,S0,S0,M12=>14
|StD,S1,S0,S0,S1,M6=>14
|StD,S1,S0,S0,S1,M7=>4
|StD,S1,S0,S0,S1,M9=>14
|StD,S1,S0,S0,S1,M10=>4
|StD,S1,S0,S0,S1,M12=>14
|StD,S1,S0,S1,S0,M6=>14
|StD,S1,S0,S1,S0,M7=>16
|StD,S1,S0,S1,S0,M9=>14
|StD,S1,S0,S1,S0,M10=>16
|StD,S1,S0,S1,S0,M12=>14
|StD,S1,S0,S1,S1,M6=>14
|StD,S1,S0,S1,S1,M7=>16
|StD,S1,S0,S1,S1,M9=>14
|StD,S1,S0,S1,S1,M10=>16
|StD,S1,S0,S1,S1,M12=>14
|StD,S1,S1,S0,S0,M4=>14
|StD,S1,S1,S0,S0,M7=>4
|StD,S1,S1,S0,S0,M10=>4
|StD,S1,S1,S0,S0,M11=>14
|StD,S1,S1,S0,S0,M12=>14
|StD,S1,S1,S0,S1,M4=>14
|StD,S1,S1,S0,S1,M7=>16
|StD,S1,S1,S0,S1,M10=>16
|StD,S1,S1,S0,S1,M11=>14
|StD,S1,S1,S0,S1,M12=>14
|StD,S1,S1,S1,S0,M7=>16
|StD,S1,S1,S1,S0,M8=>14
|StD,S1,S1,S1,S0,M10=>16
|StD,S1,S1,S1,S0,M12=>14
|StD,S1,S1,S1,S1,M7=>16
|StD,S1,S1,S1,S1,M10=>16
|StD,S1,S1,S1,S1,M12=>14
|_,_,_,_,_,_=>12 end.
(* END GENERATED A1 RANK CERTIFICATE *)
Definition bmfr_integer(c:cconf):Z:=let '(q,(L,h,R)):=c in
 4*(bmr_ones L+bmr_bit h+bmr_ones R)+3*Z.of_nat(length R)+
 bmfr_bias q h(chd L)(chd(ctl L))(chd(ctl(ctl L)))(bm_fold R).
Definition bmfr_rank(c:cconf):nat:=Z.to_nat(bmfr_integer c).
Lemma bmfr_bias_nonneg:forall q h a b c s,0<=bmfr_bias q h a b c s.
Proof. intros;destruct q,h,a,b,c,s;vm_compute;discriminate. Qed.
Lemma bmfr_nonneg:forall c,0<=bmfr_integer c.
Proof.
 intros[q[[L h]R]]. pose proof(bmr_ones_nonneg L);pose proof(bmr_ones_nonneg R).
 pose proof(bmfr_bias_nonneg q h(chd L)(chd(ctl L))(chd(ctl(ctl L)))(bm_fold R)).
 unfold bmfr_integer;destruct h;cbn[bmr_bit];lia.
Qed.
Definition bmfr_edge(q:St)(h a b c d r:Sym)(s:bm_dfa):Prop:=
 let tr:=match bm_tm q h with Some tr=>tr|None=>mkTrans S0 DR StA end in
 match t_dir tr with
 |DL=>bm_ok q h a b c s=true -> (q,h)<>(StA,S1) -> (t_next tr,a)<>(StA,S1) ->
   4*(bmr_bit(t_write tr)-bmr_bit h)+3+
   bmfr_bias(t_next tr)a b c d(bm_cons(t_write tr)s)<bmfr_bias q h a b c s
 |DR=>bm_ok q h a b c(bm_cons r s)=true -> (q,h)<>(StA,S1) -> (t_next tr,r)<>(StA,S1) ->
   4*(bmr_bit(t_write tr)-bmr_bit h)-3+
   bmfr_bias(t_next tr)r(t_write tr)a b s<bmfr_bias q h a b c(bm_cons r s)
 end.
Lemma bmfr_edges:forall q h a b c d r s,bmfr_edge q h a b c d r s.
Proof. intros;destruct q,h,a,b,c,d,r,s;vm_compute;intuition discriminate. Qed.
Lemma bmfr_ones_cons:forall s L,bmr_ones(s::L)=bmr_bit s+bmr_ones L.
Proof. intros [] L;reflexivity. Qed.
Lemma bmfr_ones_uncons:forall L,bmr_ones L=bmr_bit(chd L)+bmr_ones(ctl L).
Proof. intros[|[]L];reflexivity. Qed.
Section Machine.
Variable tm:TM.
Hypothesis Htm:forall q h,tm q h=bm_tm q h.
Lemma bmfr_step:forall c d,cstep tm c=Some d->bm_inv c->
 (cinstr c<>(StB,S0) \/ snd(snd c)<>[])->
 cinstr c<>(StA,S1)->cinstr d<>(StA,S1)->bmfr_integer d<bmfr_integer c.
Proof.
 intros[q[[L h]R]] e HE HI HB HC HD.
 assert(HP:=bmfr_edges q h(chd L)(chd(ctl L))(chd(ctl(ctl L)))
   (chd(ctl(ctl(ctl L))))(chd R)(bm_fold R)).
 assert(HO:=bmfr_edges q h(chd L)(chd(ctl L))(chd(ctl(ctl L)))
   (chd(ctl(ctl(ctl L))))(chd R)(bm_fold(ctl R))).
 unfold bm_inv in HI;cbn in HB,HC.
 unfold cstep in HE;rewrite Htm in HE.
 destruct q,h;cbn[bm_tm ctape_move t_dir t_write t_next]in HE;
 cbn[bmfr_edge bm_tm t_dir t_write t_next]in HP,HO;
 try(exfalso;apply HC;reflexivity).
 - destruct R as[|r R].
   + cbn[chd ctl]in HE;injection HE as <-.
     unfold bmfr_integer;cbn[bm_fold chd ctl length bmr_bit].
     rewrite bmfr_ones_cons. cbn[bmr_bit].
     destruct(chd L),(chd(ctl L)),(chd(ctl(ctl L)));cbn[bmfr_bias];lia.
   + injection HE as <-. cbn[cinstr]in HD.
     cbn[bm_fold]in HI;cbn[chd ctl]in HO.
     specialize(HO HI HC HD). unfold bmfr_integer.
     cbn[chd ctl bm_fold length];rewrite !bmfr_ones_cons,Nat2Z.inj_succ.
     cbn[bmr_bit]in HO|-*. lia.
 - destruct R as[|r R].
   + destruct HB as[HB|HB];exfalso;apply HB;reflexivity.
   + injection HE as <-. cbn[cinstr]in HD.
     cbn[bm_fold]in HI;cbn[chd ctl]in HO.
     specialize(HO HI HC HD). unfold bmfr_integer.
     cbn[chd ctl bm_fold length];rewrite !bmfr_ones_cons,Nat2Z.inj_succ.
     cbn[bmr_bit]in HO|-*. lia.
 - destruct R as[|r R].
   + apply bm_empty in HI;intuition discriminate.
   + injection HE as <-. cbn[cinstr]in HD.
     cbn[bm_fold]in HI;cbn[chd ctl]in HO.
     specialize(HO HI HC HD). unfold bmfr_integer.
     cbn[chd ctl bm_fold length];rewrite !bmfr_ones_cons,Nat2Z.inj_succ.
     cbn[bmr_bit]in HO|-*. lia.
 - injection HE as <-. cbn[cinstr]in HD.
   specialize(HP HI HC HD). unfold bmfr_integer.
   cbn[chd ctl bm_fold length];rewrite !bmfr_ones_cons,Nat2Z.inj_succ.
   rewrite(bmfr_ones_uncons L). cbn[bmr_bit]in HP|-*. lia.
 - destruct R as[|r R].
   + apply bm_empty in HI;intuition discriminate.
   + injection HE as <-. cbn[cinstr]in HD.
     cbn[bm_fold]in HI;cbn[chd ctl]in HO.
     specialize(HO HI HC HD). unfold bmfr_integer.
     cbn[chd ctl bm_fold length];rewrite !bmfr_ones_cons,Nat2Z.inj_succ.
     cbn[bmr_bit]in HO|-*. lia.
 - destruct R as[|r R].
   + apply bm_empty in HI;intuition discriminate.
   + injection HE as <-. cbn[cinstr]in HD.
     cbn[bm_fold]in HI;cbn[chd ctl]in HO.
     specialize(HO HI HC HD). unfold bmfr_integer.
     cbn[chd ctl bm_fold length];rewrite !bmfr_ones_cons,Nat2Z.inj_succ.
     cbn[bmr_bit]in HO|-*. lia.
 - injection HE as <-. cbn[cinstr]in HD.
   specialize(HP HI HC HD). unfold bmfr_integer.
   cbn[chd ctl bm_fold length];rewrite !bmfr_ones_cons,Nat2Z.inj_succ.
   rewrite(bmfr_ones_uncons L). cbn[bmr_bit]in HP|-*. lia.
Qed.
Lemma bmfr_reset:forall L,Reach0 tm(StB,(L,S0,[]))(StA,(L,S1,[S1;S0])).
Proof.
 intro L;eapply(r0_run _ 2 _ (StA,(L,S1,[S1]))).
 - repeat(cbn[csteps cstep];rewrite ?Htm;cbn[bm_tm ctape_move t_dir t_next t_write chd ctl]);reflexivity.
 - eapply reach0_lift_r;[|apply reach0_refl].
   change(lift(StA,(L,S1,[S1]++rep[S0]1))=lift(StA,(L,S1,[S1]))).
   apply lift_padR.
Qed.
Theorem bmfr_A1:forall c,bm_inv c->
 exists d,bm_inv d /\ cinstr d=(StA,S1) /\ Reach0 tm c d.
Proof.
 refine(well_founded_induction_type(well_founded_ltof cconf bmfr_rank)
  (fun c=>bm_inv c->exists d,bm_inv d /\ cinstr d=(StA,S1) /\ Reach0 tm c d) _).
 intros c IH HI.
 assert(Dec:forall x:cconf,cinstr x=(StA,S1)\/cinstr x<>(StA,S1)).
 { intros[q[[L h]R]];destruct q,h;try(right;discriminate);left;reflexivity. }
 destruct(Dec c)as[HT|HN].
 - exists c;repeat split;try assumption;apply reach0_refl.
 - assert(Cases:(exists L,c=(StB,(L,S0,[]))) \/ (cinstr c<>(StB,S0)\/snd(snd c)<>[])).
   { destruct c as[q[[L h]R]]. destruct q,h;try(right;left;discriminate).
     destruct R as[|r R];[left;exists L;reflexivity|right;right;discriminate]. }
   destruct Cases as[[L ->]|HB].
   + exists(StA,(L,S1,[S1;S0]));split;[reflexivity|split;[reflexivity|apply bmfr_reset]].
   + assert(Next:exists d,cstep tm c=Some d).
     { destruct c as[q[[L h]R]];unfold cstep;rewrite Htm;destruct q,h;eexists;reflexivity. }
     destruct Next as(d&HS).
     assert(HID:bm_inv d)by(eapply bm_step;eauto).
     destruct(Dec d)as[HT|HD].
     * exists d;repeat split;try assumption.
       eapply(r0_run _ 1);[cbn[csteps];rewrite HS;reflexivity|apply reach0_refl].
     * assert(Hless:ltof cconf bmfr_rank d c).
       { unfold ltof,bmfr_rank;apply Z2Nat.inj_lt;try apply bmfr_nonneg.
         eapply bmfr_step;eassumption. }
       destruct(IH d Hless HID)as(e&HIE&HT&HR).
       exists e;repeat split;try assumption.
       eapply(r0_run _ 1);[cbn[csteps];rewrite HS;reflexivity|exact HR].
Qed.
End Machine.
