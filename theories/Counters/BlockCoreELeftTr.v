(** Binary descent for a finite left excursion of core E. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
Import ListNotations.
Fixpoint bel_value (w:list Sym):nat :=
 match w with []=>0 | S0::u=>2*bel_value u | S1::u=>1+2*bel_value u end.
Definition bel_left(q:St):Prop:=q=StA\/q=StB\/q=StC.
Definition bel_right(q:St):Prop:=q=StC\/q=StD.
Lemma bel_zero_head:forall L,bel_value L=0->chd L=S0.
Proof. intros[|[]L];cbn[bel_value chd];intros;auto;lia. Qed.
Section Core.
Variable tm:TM.
Hypotheses
 (HA1:tm StA S1=Some(mkTrans S1 DL StB))
 (HB0:tm StB S0=Some(mkTrans S1 DL StA))
 (HB1:tm StB S1=Some(mkTrans S0 DL StC))
 (HC0:tm StC S0=Some(mkTrans S0 DL StA))
 (HC1:tm StC S1=Some(mkTrans S0 DR StD))
 (HD0:tm StD S0=Some(mkTrans S1 DR StC))
 (HD1:tm StD S1=Some(mkTrans S1 DR StD)).
Definition bel_hit(R:list Sym)(c:cconf):Prop:=
 exists L P,Reach0 tm c(StA,(L,S0,P++R)).
Definition bel_result(U R:list Sym)(c:cconf):Prop:=
 bel_hit R c \/ exists q V,bel_right q/\bel_value V<bel_value U/\
 Reach0 tm c(cR q V R).
Lemma bel_hit_back:forall R c d,Reach0 tm c d->bel_hit R d->bel_hit R c.
Proof. intros R c d H(L&P&Hr);exists L,P;eapply reach0_trans;eauto. Qed.
Lemma bel_hit_prefix:forall P R c,bel_hit(P++R)c->bel_hit R c.
Proof. intros P R c(L&Q&H);exists L,(Q++P);rewrite<-app_assoc;exact H. Qed.
Lemma bel_result_back:forall U R c d,Reach0 tm c d->bel_result U R d->bel_result U R c.
Proof.
 intros U R c d H[HH|(q&V&Hq&Hlt&Hr)].
 - left;eapply bel_hit_back;eauto.
 - right;exists q,V;repeat split;try assumption;eapply reach0_trans;eauto.
Qed.
Local Ltac run:=
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR];
 repeat(first[rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR]);reflexivity.
Local Ltac go n:=eapply(r0_run _ n);[run|].
Lemma bel_zero:forall U R q,bel_value U=0->bel_left q->bel_hit R(cL q U R).
Proof.
 intros U R q HV[-> | [-> | ->]].
 - exists(ctl U),[];unfold cL;rewrite(bel_zero_head _ HV);r0.
 - exists(ctl(ctl U)),[S1]. unfold cL.
   rewrite(bel_zero_head _ HV).
   assert(HV':bel_value(ctl U)=0)by(destruct U as[|[]U];cbn[ctl bel_value]in*;lia).
   eapply(r0_run _ 1).
   + cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write];rewrite HB0;cbn.
     rewrite(bel_zero_head _ HV');reflexivity.
   + r0.
 - exists(ctl(ctl U)),[S0]. unfold cL.
   rewrite(bel_zero_head _ HV).
   assert(HV':bel_value(ctl U)=0)by(destruct U as[|[]U];cbn[ctl bel_value]in*;lia).
   eapply(r0_run _ 1).
   + cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write];rewrite HC0;cbn.
     rewrite(bel_zero_head _ HV');reflexivity.
   + r0.
Qed.
Lemma bel_excursion_bound:forall n U,bel_value U=n->forall R q,bel_left q->
 bel_result U R(cL q U R).
Proof.
 intro n;induction n using lt_wf_ind;intros U HV R q Hq.
 destruct(eq_nat_dec n 0)as[->|HN].
 { left;apply bel_zero;assumption. }
 destruct U as[|d U];[cbn[bel_value]in HV;lia|].
 assert(HU:bel_value U<n)by(destruct d;cbn[bel_value]in HV;lia).
 assert(Hwall:forall b q',bel_left q'->
   bel_result(d::U)R(cL q' U(b::R))).
 {
   intros b q' HL.
   destruct(H(bel_value U)HU U eq_refl(b::R)q' HL)as[HH|(q''&V&HQ&HV'&HR)].
   - left;apply(bel_hit_prefix[b]);exact HH.
   - eapply bel_result_back;[exact HR|].
     destruct HQ as[-> | ->];destruct b.
     + assert(HVV:bel_value(S0::V)<n)by(cbn[bel_value];destruct d;cbn[bel_value]in HV;lia).
       change(bel_result(d::U)R(cL StC(S0::V)R)).
       destruct(H _ HVV(S0::V)eq_refl R StC ltac:(right;right;reflexivity))as[HH|(qq&VV&HH&HN'&HR')].
       * left;exact HH.
       * right;exists qq,VV;repeat split;try assumption;rewrite HV;lia.
     + right;exists StD,(S0::V);repeat split;try(left;reflexivity);try(right;reflexivity).
       * cbn[bel_value];destruct d;cbn[bel_value];lia.
       * go 1;r0.
     + right;exists StC,(S1::V);repeat split;try(left;reflexivity);try(right;reflexivity).
       * cbn[bel_value];destruct d;cbn[bel_value];lia.
       * go 1;r0.
     + right;exists StD,(S1::V);repeat split;try(left;reflexivity);try(right;reflexivity).
       * cbn[bel_value];destruct d;cbn[bel_value];lia.
       * go 1;r0.
 }
 destruct Hq as[-> | [-> | ->]];destruct d.
 - left;exists U,[];r0.
 - eapply bel_result_back;[go 1;r0|]. apply Hwall;right;left;reflexivity.
 - eapply bel_result_back;[go 1;r0|]. apply Hwall;left;reflexivity.
 - eapply bel_result_back;[go 1;r0|]. apply Hwall;right;right;reflexivity.
 - eapply bel_result_back;[go 1;r0|]. apply Hwall;left;reflexivity.
 - right;exists StD,(S0::U);repeat split.
   + right;reflexivity.
   + cbn[bel_value];lia.
   + go 1;r0.
Qed.
Theorem bel_excursion:forall U R q,bel_left q->bel_result U R(cL q U R).
Proof. intros;apply(bel_excursion_bound(bel_value U));auto. Qed.
End Core.
