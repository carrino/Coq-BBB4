From Coq Require Import Arith Lia Bool List FunctionalExtensionality.
From SmallBB Require Import Statement StatementTr CTape PosEnc Closure ClosureTr Bounds
 AbstractCensus StateBounds FiniteRankSearch.
From SmallBB.Checkers Require Import NGram FiniteNGram.
Import ListNotations.
Lemma fn_closed_equiv : forall A enc succs Sl,
 closed_tr_b A enc succs Sl=closed_b A enc succs Sl.
Proof.
 intros; unfold closed_tr_b,closed_b; rewrite allb_tr_eq.
 f_equal; apply functional_extensionality; intro a. unfold node_ok_tr,node_ok.
 destruct (succs a); [rewrite allb_tr_eq|]; reflexivity.
Qed.
Definition fn_components tm cs := map(fn_comp_denote tm)cs.
Lemma fn_components_exact : forall tm n ls rs cs,
 1<=n -> Forall(comp_exact tm cconf(fn_succs tm n ls rs)(fn_covers n ls rs))(fn_components tm cs).
Proof.
 intros tm n ls rs cs Hn. apply Forall_forall; intros comp Hin.
 apply in_map_iff in Hin as (c & <- & _). destruct c; cbn [fn_comp_denote comp_exact]; [exact I|].
 intros a cc a' cc' sl Hca Hca' Hstep Es Hin'. eapply fnm_exact; eauto.
Qed.
Definition fn_check_mode (state:bool) bs bi tm n t fuel rounds :=
 if 1<=?n then match csteps tm t c0 with
 |None=>false
 |Some cc=>let '(q,(l,h,r)):=cc in
   let a0:=fn_start n cc in
   let '(ls,rs):=fn_grow tm n a0 fuel rounds
      (gadds(fn_seed_side n l)gempty)(gadds(fn_seed_side n r)gempty)in
   let Sl:=fn_explore tm n ls rs fuel [] PositiveSet.empty[a0]in
   if fn_seed_ok n ls rs cc then
   if closed_tr_b cconf cconf_enc(fn_succs tm n ls rs)Sl then
   if mem_tr cconf cconf_enc a0 Sl then
   if state then
     if state_prefix_gate bs tm t(tail_states(labels cinstr Sl)) then
       live_lex_ok cconf cconf_enc (fun a=>fst(cinstr a))(fn_succs tm n ls rs)Sl
         (fun q=>fn_components tm(fn_rank_procedure tm n ls rs Sl(fun a=>st_eqb(fst a)q)))
     else false
   else if prefix_gate bs bi tm t(tail_states(labels cinstr Sl))(tail_instrs(labels cinstr Sl)) then
       live_lex_ok_tr cconf cconf_enc cinstr(fn_succs tm n ls rs)Sl
         (fun tg=>fn_components tm(fn_rank_procedure tm n ls rs Sl(fun a=>instr_eqb(cinstr a)tg)))
     else false
   else false else false else false
 end else false.
Theorem fn_check_mode_sound : forall state bs bi tm n t fuel rounds,
 fn_check_mode state bs bi tm n t fuel rounds=true ->
 NonHalt tm /\ (if state then QHBound bs tm else Bounds bs bi tm).
Proof.
 intros state bs bi tm n t fuel rounds H. unfold fn_check_mode in H.
 destruct (1<=?n) eqn:Hn; [apply Nat.leb_le in Hn|discriminate].
 destruct (csteps tm t c0) as [[q[[l h]r]]|] eqn:Et; [|discriminate].
 match type of H with (let '(_,_) := ?G in _) = true => destruct G as [ls rs] end.
 cbv beta iota zeta in H.
 match type of H with (if ?b then _ else _) = true => destruct b eqn:Hseed end; [|discriminate].
 match type of H with (if ?b then _ else _) = true => destruct b eqn:Hcl end; [|discriminate].
 match type of H with (if ?b then _ else _) = true => destruct b eqn:Hmem end; [|discriminate].
 destruct state; cbv beta iota in H|-*;
 match type of H with (if ?b then _ else _) = true => destruct b eqn:Hpre end; try discriminate.
 - rewrite fn_closed_equiv in Hcl.
   eapply (abstract_state_bound tm cconf cconf_enc cinstr(fn_succs tm n ls rs)(fn_covers n ls rs));
     [exact cconf_enc_inj|apply fn_covers_instr| |exact Et| |exact Hcl|exact Hmem| |exact H|exact Hpre].
   + intros a c Hc; apply fn_succs_sound; assumption.
   + apply fn_start_covers; exact Hseed.
   + intros; apply fn_components_exact; exact Hn.
 - eapply (abstract_bounds bs bi tm cconf cconf_enc cinstr(fn_succs tm n ls rs)(fn_covers n ls rs));
     [exact cconf_enc_inj|apply fn_covers_instr| |exact Et| |exact Hcl|exact Hmem| |exact H|exact Hpre].
   + intros a c Hc; apply fn_succs_sound; assumption.
   + apply fn_start_covers; exact Hseed.
   + intros; apply fn_components_exact; exact Hn.
Qed.
