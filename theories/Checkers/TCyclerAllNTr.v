(** A binary-fuel translated-cycle checker when every instruction fires
    inside the guarded lap.  It reuses [cstepsN] for the bootstrap and
    proves the existing [TCyclerTr] certificate from the stronger gate.
    The guarded firing scan stops as soon as its target is observed. *)
From Coq Require Import Arith Lia Bool List NArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape GTape Mirror.
From BBB4.Checkers Require Import TCycler TCyclerTr TCyclerN.
From BBB4.CensusTr Require Import TNF_QHTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Fixpoint gfires_short(tm:TM)(g:cconf)(len:nat)(tg:Instr):bool:=
 match len with
 |0=>false
 |S m=>if instr_eqb(cinstr g)tg then true else
    match gstep tm g with Some g'=>gfires_short tm g' m tg|None=>false end
 end.
Lemma gfires_short_eq:forall tm n g tg,gfires_short tm g n tg=gfires tm g n tg.
Proof.
 intros tm n. induction n as[|n IH];intros g tg;[reflexivity|].
 cbn[gfires_short gfires]. destruct(instr_eqb(cinstr g)tg);[reflexivity|].
 destruct(gstep tm g);[apply IH|reflexivity].
Qed.
Definition tcycler_all_N_check(tm:TM)(boot:N)(P W:nat):bool:=
 (0<?P)&&
 match cstepsN tm boot c0 with
 |Some(q,(L,h,R))=>
  let g:=(q,(firstn_pad W L,h,R))in
  match gsteps tm P g with
  |Some g'=>gmatch g g'&&forallb(fun t=>gfires_short tm g P t)all_Instr
  |None=>false end
 |None=>false end.
Theorem tcycler_all_N_check_sound:forall tm boot P W,
 tcycler_all_N_check tm boot P W=true->NeverQuasiHaltsTr tm.
Proof.
 intros tm boot P W H.
 apply(tcycler_check_neverqhtr_sound tm(N.to_nat boot)P W).
 unfold tcycler_all_N_check in H. rewrite cstepsN_nat in H.
 unfold tcycler_check_neverqhtr.
 apply andb_prop in H as[Hp H]. rewrite Hp. cbn[andb].
 destruct(csteps tm(N.to_nat boot)c0)as[[q[[L h]R]]|];[|discriminate].
 destruct(gsteps tm P(q,(firstn_pad W L,h,R)))as[g'|];[|discriminate].
 apply andb_prop in H as[Hg Hf]. rewrite Hg. cbn[andb].
 rewrite forallb_forall in Hf. apply forallb_forall. intros t Ht.
 specialize(Hf t Ht). rewrite gfires_short_eq in Hf. rewrite Hf.
 apply implb_true_r.
Qed.
Corollary tcycler_all_N_check_sound_L:forall tm boot P W,
 tcycler_all_N_check(mirror_tm tm)boot P W=true->NeverQuasiHaltsTr tm.
Proof. intros. apply neverqhtr_mirror. eapply tcycler_all_N_check_sound;eauto. Qed.
