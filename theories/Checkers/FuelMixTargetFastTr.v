(** * Short-circuit replay for independent FuelMix target certificates.

    The returned Boolean is equal to the landed checker. In particular,
    a lexicographically strict edge need not also evaluate every component
    for the alternative runner case. *)
From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape PosEnc Records Closure ClosureTr.
From BBB4.Checkers Require Import NGram FuelWide FuelWideTr FuelSCC FuelSCCTr FuelMixTr FuelMixPartialTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Checkers Require Import FuelMixTargetTr.
Import ListNotations.
Lemma fmx_forallb_ext:forall A(f g:A->bool)l,(forall a,f a=g a)->forallb f l=forallb g l.
Proof. intros A f g l H;induction l;cbn;[reflexivity|now rewrite H,IHl]. Qed.
(** Avoid computing an irrelevant pattern delta outside its finite gate. *)
Fixpoint fmx_lex_edge_fast {A:Type}(comps:list(lexcomp A))(a b:A):bool:=
 match comps with
 |[]=>false
 |comp::rest=>
  match comp with
  |LexRank _ phi=>if phi b <? phi a then true else
    if phi b <=? phi a then fmx_lex_edge_fast rest a b else false
  |LexMeas _ _ md K phi gate=>
    if gate b then if gate a then
      let z:=(Z.of_nat K*md a b+Z.of_nat(phi b)-Z.of_nat(phi a))%Z in
      if(z<=? -1)%Z then true else
      if(z<=?0)%Z then fmx_lex_edge_fast rest a b else false
    else false else fmx_lex_edge_fast rest a b
  end
 end.
Lemma fmx_lex_edge_fast_eq:forall A comps a b,
 @fmx_lex_edge_fast A comps a b=lex_edge_ok A comps a b.
Proof.
 intros A comps;induction comps as[|comp rest IH];intros a b;[reflexivity|].
 destruct comp as[phi|mv md K phi gate];cbn[fmx_lex_edge_fast lex_edge_ok comp_strict comp_noninc];
 rewrite IH;[reflexivity|]. destruct(gate a),(gate b);reflexivity.
Qed.
Definition fscc_instr_fast {A:Type} (instr:A->Instr)(succs:A->option(list A))
 (moves fuel:A->bool)(Sl:list A)q(comps:list(lexcomp A))(rg:A->bool):bool:=
 rgate_tr_ok A instr moves fuel Sl q rg &&
 forallb(fun a=>if instr_eqb(instr a)q then true else
 match succs a with
 |None=>false
 |Some bs=>forallb(fun b=>if instr_eqb(instr b)q then true else
   if fmx_lex_edge_fast comps a b then true else
   if rg a then if rg b then lex_noninc_all A comps a b else false else false)bs
 end)Sl.
Lemma fscc_instr_fast_eq:forall A instr succs moves fuel Sl q comps rg,
 @fscc_instr_fast A instr succs moves fuel Sl q comps rg=
 fscc_instr_ok A instr succs moves fuel Sl q comps rg.
Proof.
 intros. unfold fscc_instr_fast,fscc_instr_ok. f_equal.
 apply fmx_forallb_ext. intro a. destruct(instr_eqb(instr a)q);[reflexivity|].
 destruct(succs a)as[bs|];[|reflexivity]. apply fmx_forallb_ext. intro b.
 unfold fscc_edge_ok. rewrite fmx_lex_edge_fast_eq.
 destruct(instr_eqb(instr b)q),(lex_edge_ok A comps a b),(rg a),(rg b);reflexivity.
Qed.
Definition closure_check_fuelmix_target_fast (tm:TM) {A:Type}(enc:A->positive)
 (instr:A->Instr)(succs:A->option(list A))(moves rfuel:A->bool)
 (t fuel:nat)(a0:A)(skip:Instr->bool)(cert:Instr->list(lexcomp A)*(A->bool)):bool:=
 match csteps tm t c0 with
 |None=>false
 |Some ct=>match close A enc succs fuel [] PositiveSet.empty[a0]with
  |None=>false
  |Some Sl=>closed_b A enc succs Sl && mem A enc a0 Sl &&
   forallb(fun q=>if skip q then true else
    if cfires tm c0 t q || existsb(fun a=>instr_eqb(instr a)q)Sl then
      fscc_instr_fast instr succs moves rfuel Sl q(fst(cert q))(snd(cert q))
    else true)all_Instr
  end
 end.
Lemma closure_check_fuelmix_target_fast_eq:forall tm A enc instr succs moves rfuel t fuel a0 skip cert,
 @closure_check_fuelmix_target_fast tm A enc instr succs moves rfuel t fuel a0 skip cert=
 closure_check_neverqh_fuelscctr_except tm A enc instr succs moves rfuel t fuel a0 skip cert.
Proof.
 intros. unfold closure_check_fuelmix_target_fast,closure_check_neverqh_fuelscctr_except.
 destruct(csteps tm t c0);[|reflexivity].
 destruct(close A enc succs fuel [] PositiveSet.empty[a0]);[|reflexivity].
 f_equal. apply fmx_forallb_ext. intro q. rewrite fscc_instr_fast_eq.
 destruct(skip q),(cfires tm c0 t q || existsb(fun a=>instr_eqb(instr a)q)l);reflexivity.
Qed.
Definition ngram_check_fuelmix_target_fast(tm:TM)(n t fuel rounds:nat)(skip:Instr->bool)
 (cert:Instr->list fmxcomp*list positive):bool:=
 (1<=?n)&&
 match csteps tm t c0 with
 |None=>false
 |Some cc=>let '(q,(l,h,r)):=cc in
  let lset0:=gadds(ng_seed_side n l)gempty in
  let rset0:=gadds(ng_seed_side n r)gempty in
  let a0:=ng_start n cc in
  let '(lset,rset):=ng_grow tm a0 fuel rounds lset0 rset0 in
  ng_seed_ok n lset rset cc &&
  closure_check_fuelmix_target_fast tm fcconf_enc fw_instr(fw_succs tm lset rset)
   (fwnode_moves_right tm)fwnode_rfuel_ge1 t fuel(fw_start n cc)skip
   (fun q=>fmx_cert_denote tm n(cert q))
 end.
Lemma ngram_check_fuelmix_target_fast_eq:forall tm n t fuel rounds skip cert,
 ngram_check_fuelmix_target_fast tm n t fuel rounds skip cert=
 ngram_check_neverqh_fuelmixtr_except tm n t fuel rounds skip cert.
Proof.
 intros. unfold ngram_check_fuelmix_target_fast,ngram_check_neverqh_fuelmixtr_except.
 destruct(csteps tm t c0)as[[q[[l h]r]]|];[|reflexivity].
 match goal with |- context [ng_grow ?a ?b ?c ?d ?e ?f] =>
   destruct (ng_grow a b c d e f) end.
 cbn. now rewrite closure_check_fuelmix_target_fast_eq.
Qed.
Theorem ngram_check_fuelmix_target_fast_sound:forall tm n t fuel rounds skip cert,
 ngram_check_fuelmix_target_fast tm n t fuel rounds skip cert=true->
 forall q,skip q=false->FiredTr tm q->forall N,exists j,N<=j /\FiresAt tm q j.
Proof. intros tm n t fuel rounds skip cert H. rewrite ngram_check_fuelmix_target_fast_eq in H.
 now apply(ngram_check_neverqh_fuelmixtr_target_sound tm n t fuel rounds skip cert).
Qed.
