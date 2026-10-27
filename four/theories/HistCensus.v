From Coq Require Import NArith Arith Lia Bool List.
From BBB24 Require Import Statement StatementTr Spec CTape PosEnc Closure ClosureTr Bounds
 AbstractCensus StateBounds HistRankSearch FiniteCensus.
From BBB24.Checkers Require Import NGram NGramHist.
Import ListNotations.
Lemma hcovers_instr : forall n ls rs a c,
 hcovers n ls rs a c -> hainstr a=instr_of c.
Proof.
 intros n ls rs [q[[lw s]rw]] c (hc & <- & Hcov).
 destruct hc as [qc[[l h]r]]. destruct Hcov as (Hq&Hh&_).
 unfold hainstr,hproj,cinstr,instr_of,lift,lift_tape; cbn; congruence.
Qed.
Definition hn_components tm cs := map(hn_comp_denote tm)cs.
Lemma hn_components_exact : forall tm k n ls rs cs,
 1<=n -> Forall(comp_exact tm hcconf(hng_succs tm k n ls rs)(hcovers n ls rs))(hn_components tm cs).
Proof.
 intros tm k n ls rs cs Hn. apply Forall_forall; intros comp Hin.
 apply in_map_iff in Hin as (c & <- & _). destruct c; cbn [hn_comp_denote comp_exact]; [exact I|].
 intros a cc a' cc' sl (hc & Hlift & Hcov) Hca' Hstep Es Hin'. unfold hndelta.
 rewrite (hproj_eq_ngstart n ls rs a hc cc Hcov Hlift).
 apply ngm_start_exact; assumption.
Qed.
Definition hn_check_mode (state:bool) bs bi tm k n t fuel rounds :=
 if 1<=?n then match hcsteps tm k t hcconf0 with
 |None=>false
 |Some cc=>let '(q,(l,h,r)):=cc in
   let a0:=hng_start n cc in
   let '(ls,rs):=hn_grow tm k n a0 fuel rounds
      (hseed_side n l)(hseed_side n r)in
   let Sl:=hn_explore tm k n ls rs fuel [] PositiveSet.empty[a0]in
   if hseed_ok n ls rs cc then
   if closed_tr_b hcconf hctx_enc(hng_succs tm k n ls rs)Sl then
   if mem_tr hcconf hctx_enc a0 Sl then
   if state then
     if state_prefix_gate bs tm t(tail_states(labels hainstr Sl)) then
       live_lex_ok hcconf hctx_enc (fun a=>fst(hainstr a))(hng_succs tm k n ls rs)Sl
         (fun q=>hn_components tm(hn_rank_procedure tm k n ls rs Sl(fun a=>st_eqb(fst a)q)))
     else false
   else if prefix_gate bs bi tm t(tail_states(labels hainstr Sl))(tail_instrs(labels hainstr Sl)) then
       live_lex_ok_tr hcconf hctx_enc hainstr(hng_succs tm k n ls rs)Sl
         (fun tg=>hn_components tm(hn_rank_procedure tm k n ls rs Sl(fun a=>instr_eqb(hainstr a)tg)))
     else false
   else false else false else false
 end else false.
Theorem hn_check_mode_sound : forall state bs bi tm k n t fuel rounds,
 hn_check_mode state bs bi tm k n t fuel rounds=true ->
 NonHalt tm /\ (if state then QHBound (N.to_nat bs) tm else Bounds bs bi tm).
Proof.
 intros state bs bi tm k n t fuel rounds H. unfold hn_check_mode in H.
 destruct (1<=?n) eqn:Hn; [apply Nat.leb_le in Hn|discriminate].
 destruct (hcsteps tm k t hcconf0) as [[q[[l h]r]]|] eqn:Et; [|discriminate].
 match type of H with (let '(_,_) := ?G in _) = true => destruct G as [ls rs] end.
 cbv beta iota zeta in H.
 match type of H with (if ?b then _ else _) = true => destruct b eqn:Hseed end; [|discriminate].
 match type of H with (if ?b then _ else _) = true => destruct b eqn:Hcl end; [|discriminate].
 match type of H with (if ?b then _ else _) = true => destruct b eqn:Hmem end; [|discriminate].
 assert (Eproj:csteps tm t c0=Some(hproj(q,(l,h,r)))).
 { rewrite <-hproj_hcconf0. eapply hcsteps_proj; exact Et. }
 destruct state; cbv beta iota in H|-*;
 match type of H with (if ?b then _ else _) = true => destruct b eqn:Hpre end; try discriminate.
 - rewrite fn_closed_equiv in Hcl.
   eapply (abstract_state_bound tm hcconf hctx_enc hainstr(hng_succs tm k n ls rs)(hcovers n ls rs));
     [exact hctx_enc_inj|apply hcovers_instr| |exact Eproj| |exact Hcl|exact Hmem| |exact H|exact Hpre].
   + intros a c Hc; apply hng_succs_sound; assumption.
   + exists (q,(l,h,r)); split; [reflexivity|apply hng_start_covers; exact Hseed].
   + intros; apply hn_components_exact; exact Hn.
 - eapply (abstract_bounds bs bi tm hcconf hctx_enc hainstr(hng_succs tm k n ls rs)(hcovers n ls rs));
     [exact hctx_enc_inj|apply hcovers_instr| |exact Eproj| |exact Hcl|exact Hmem| |exact H|exact Hpre].
   + intros a c Hc; apply hng_succs_sound; assumption.
   + exists (q,(l,h,r)); split; [reflexivity|apply hng_start_covers; exact Hseed].
   + intros; apply hn_components_exact; exact Hn.
Qed.
