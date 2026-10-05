(** A finite-tape potential for the M core away from B0. *)
From Coq Require Import Arith Lia List ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Open Scope Z_scope.
Fixpoint bmr_ones(w:list Sym):Z:=match w with
| []=>0 | S0::w=>bmr_ones w | S1::w=>1+bmr_ones w end.
Definition bmr_bit(s:Sym):Z:=match s with S0=>0|S1=>1 end.
Definition bmr_bias(q:St)(h l r:Sym):Z:=4+match q,h with
| StA,S0=>match l,r with S0,S0=>0|_,_=> -2 end
| StA,S1=>match l with S0=>10|S1=>4 end
| StB,S0=>0
| StB,S1=>match l,r with S1,S1=> -4|_,_=>0 end
| StC,S0=>match l with S0=>6|S1=>18 end
| StC,S1=>match r with S0=> -4|S1=>2 end
| StD,S0=>match r with S0=>0|S1=>6 end
| StD,S1=>0 end.
Definition bmr_energy(c:cconf):Z:=let '(q,(L,h,R)):=c in
 4*(bmr_ones L+bmr_bit h+bmr_ones R)+bmr_bias q h(chd L)(chd R).
Lemma bmr_ones_nonneg:forall L,0<=bmr_ones L.
Proof. induction L as[|s L IH]. - reflexivity. - destruct s;[exact IH|change(0<=1+bmr_ones L);lia]. Qed.
Lemma bmr_energy_nonneg:forall c,0<=bmr_energy c.
Proof.
 intros[q[[L h]R]]. pose proof(bmr_ones_nonneg L);pose proof(bmr_ones_nonneg R).
 unfold bmr_energy,bmr_bias. destruct q,h,(chd L),(chd R);cbv beta iota zeta delta [bmr_bit];lia.
Qed.
Definition bmr_delta(q:St)(h:Sym):Z:=match q,h with
| StA,S1 | StC,S0 | StD,S1=> -1 | _,_=>1 end.
Section Machine.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S0 DR StB))
 (HA1:tm StA S1=Some(mkTrans S1 DL StD))
 (HB1:tm StB S1=Some(mkTrans S0 DR StC))
 (HC0:tm StC S0=Some(mkTrans S1 DL StA))
 (HC1:tm StC S1=Some(mkTrans S1 DR StA))
 (HD0:tm StD S0=Some(mkTrans S1 DR StA))
 (HD1:tm StD S1=Some(mkTrans S0 DL StD)).
Lemma bmr_energy_step:forall c d,cstep tm c=Some d->
 cinstr c<>(StB,S0)->cinstr d<>(StB,S0)->
 bmr_energy d+1<=bmr_energy c+3*bmr_delta(fst c)(snd(fst(snd c))).
Proof.
 intros[q[[L h]R]] d H HC HD;destruct q,h;try(exfalso;apply HC;reflexivity);
 cbn[cstep]in H;rewrite ?HA0,?HA1,?HB1,?HC0,?HC1,?HD0,?HD1 in H;
 destruct L as[|[]L];destruct R as[|[]R];
 try(destruct L as[|[]L]);try(destruct R as[|[]R]);
 cbn[ctape_move chd ctl t_next t_dir t_write]in H;injection H as <-;
 cbn[cinstr]in HD;try(exfalso;apply HD;reflexivity);
 cbv beta iota zeta delta [bmr_energy bmr_ones bmr_bit bmr_bias bmr_delta chd fst snd];fold bmr_ones;lia.
Qed.
Lemma bmr_next:forall c,cinstr c<>(StB,S0)->exists d,cstep tm c=Some d.
Proof.
 intros[q[[L h]R]] H;destruct q,h;try(exfalso;apply H;reflexivity);
 cbn[cstep];rewrite ?HA0,?HA1,?HB1,?HC0,?HC1,?HD0,?HD1;eexists;reflexivity.
Qed.
Definition bmr_integer(c:cconf):Z:=bmr_energy c+3*Z.of_nat(length(snd(snd c))).
Definition bmr_rank(c:cconf):nat:=Z.to_nat(bmr_integer c).
Lemma bmr_integer_nonneg:forall c,0<=bmr_integer c.
Proof. intro c;unfold bmr_integer;pose proof(bmr_energy_nonneg c);lia. Qed.
Lemma bmr_right_length:forall c d,cstep tm c=Some d->cinstr c<>(StB,S0)->
 (snd(snd c)<>[] \/ bmr_delta(fst c)(snd(fst(snd c)))= -1)->
 Z.of_nat(length(snd(snd d)))+bmr_delta(fst c)(snd(fst(snd c)))=
 Z.of_nat(length(snd(snd c))).
Proof.
 intros[q[[L h]R]] d HS HN HB;destruct q,h;try(exfalso;apply HN;reflexivity);
 cbn[cstep]in HS;rewrite ?HA0,?HA1,?HB1,?HC0,?HC1,?HD0,?HD1 in HS;
 destruct L as[|l L];destruct R as[|r R];
 cbn[ctape_move chd ctl t_next t_dir t_write]in HS;injection HS as <-;
 cbn[bmr_delta fst snd]in HB|-*;try(destruct HB;[contradiction|discriminate]);
 cbn[length];rewrite ?Nat2Z.inj_succ;lia.
Qed.
Theorem bmr_finite_hit:forall(Inv:cconf->Prop),
 (forall c d,Inv c->cinstr c<>(StB,S0)->cstep tm c=Some d->Inv d)->
 (forall q L h d,Inv(q,(L,h,[]))->(q,h)<>(StB,S0)->
   cstep tm(q,(L,h,[]))=Some d->cinstr d<>(StB,S0)->bmr_delta q h= -1)->
 forall c,Inv c->exists d,Inv d/\cinstr d=(StB,S0)/\Reach0 tm c d.
Proof.
 intros Inv HC HB.
 refine(well_founded_induction_type(well_founded_ltof cconf bmr_rank)
  (fun c=>Inv c->exists d,Inv d/\cinstr d=(StB,S0)/\Reach0 tm c d) _).
 intros c IH HI.
 assert(Dec:forall x:cconf,cinstr x=(StB,S0)\/cinstr x<>(StB,S0)).
 { intros[q[[L h]R]];destruct q,h;try(right;discriminate);left;reflexivity. }
 destruct(Dec c)as[HT|HN].
 - exists c;repeat split;try assumption;apply reach0_refl.
 - destruct(bmr_next c HN)as(d&HS).
   assert(HID:Inv d)by(eapply HC;eauto).
   destruct(Dec d)as[HT|HD].
   + exists d;repeat split;try assumption.
     eapply(r0_run _ 1);[cbn[csteps];rewrite HS;reflexivity|apply reach0_refl].
   + assert(HB':snd(snd c)<>[]\/bmr_delta(fst c)(snd(fst(snd c)))= -1).
     { destruct c as[q[[L h]R]];destruct R as[|r R];[right;eapply HB;eassumption|left;discriminate]. }
     pose proof(bmr_energy_step c d HS HN HD)as HE.
     pose proof(bmr_right_length c d HS HN HB')as HL.
     assert(Hless:ltof cconf bmr_rank d c).
     { unfold ltof,bmr_rank;apply Z2Nat.inj_lt;try apply bmr_integer_nonneg.
       unfold bmr_integer;lia. }
     destruct(IH d Hless HID)as(e&HIE&HT&HR).
     exists e;repeat split;try assumption.
     eapply(r0_run _ 1);[cbn[csteps];rewrite HS;reflexivity|exact HR].
Qed.
End Machine.
