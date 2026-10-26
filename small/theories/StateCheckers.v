From Coq Require Import Arith Lia Bool List.
From SmallBB Require Import Statement StatementTr CTape PosEnc Closure ClosureTr Bounds AbstractCensus
 StateBounds StateRankSearch RankSearch RepWLSearch NGramCensus.
From SmallBB.Checkers Require Import NGram RepWL.
Import ListNotations.

Definition ng_state_check bs tm n t fuel rounds :=
 if 1<=?n then match csteps tm t c0 with
 | None=>false
 | Some cc=>let '(q,(l,h,r)):=cc in
   let a0:=ng_start n cc in
   let '(ls,rs):=ng_grow tm a0 fuel rounds
       (gadds (ng_seed_side n l) gempty) (gadds (ng_seed_side n r) gempty) in
   let Sl:=ng_explore tm ls rs fuel [] PositiveSet.empty [a0] in
   if ng_seed_ok n ls rs cc then
   if closed_b cconf cconf_enc (ng_succs tm ls rs) Sl then
   if mem cconf cconf_enc a0 Sl then
   if state_prefix_gate bs tm t (tail_states (labels cinstr Sl)) then
     live_lex_ok cconf cconf_enc (fun a=>fst(cinstr a)) (ng_succs tm ls rs) Sl
       (fun tg=>map (ng_comp_denote tm n) (ng_state_rank tm ls rs Sl tg))
   else false else false else false else false
 end else false.
Theorem ng_state_check_sound : forall bs tm n t fuel rounds,
 ng_state_check bs tm n t fuel rounds=true -> NonHalt tm /\ QHBound bs tm.
Proof.
 intros bs tm n t fuel rounds H. unfold ng_state_check in H.
 destruct (1<=?n) eqn:Hn; [apply Nat.leb_le in Hn|discriminate].
 destruct (csteps tm t c0) as [[q[[l h]r]]|] eqn:Et; [|discriminate].
 match type of H with (let '(_,_) := ?G in _) = true => destruct G as [ls rs] end.
 cbv beta iota zeta in H.
 match type of H with (if ?b then _ else _) = true => destruct b eqn:Hseed end; [|discriminate].
 match type of H with (if ?b then _ else _) = true => destruct b eqn:Hcl end; [|discriminate].
 match type of H with (if ?b then _ else _) = true => destruct b eqn:Hmem end; [|discriminate].
 match type of H with (if ?b then _ else _) = true => destruct b eqn:Hpre end; [|discriminate].
 eapply (abstract_state_bound tm cconf cconf_enc cinstr (ng_succs tm ls rs) (ng_covers n ls rs));
   [exact cconf_enc_inj|apply ng_covers_instr| |exact Et| |exact Hcl|exact Hmem| |exact H|exact Hpre].
 - intros a c Hc; apply ng_succs_sound; assumption.
 - apply ng_start_covers; exact Hseed.
 - intros tg; apply ng_components_exact; exact Hn.
Qed.

Definition rw_state_check bs tm L T t fuel :=
 if (1<=?L) && (2<=?T) then match csteps tm t c0 with
 | None=>false
 | Some cc=>let a0:=rw_seed L T cc in
   match close_tr rconf rconf_enc (rw_succs tm L T) fuel [] PositiveSet.empty [a0] with
   | None=>false
   | Some Sl=>
     if closed_b rconf rconf_enc (rw_succs tm L T) Sl then
     if mem rconf rconf_enc a0 Sl then
     if state_prefix_gate bs tm t (tail_states (labels rw_instr Sl)) then
       live_lex_ok rconf rconf_enc (fun a=>fst(rw_instr a)) (rw_succs tm L T) Sl
         (fun tg=>map (rw_comp_denote tm) (rw_state_rank tm L T Sl tg))
     else false else false else false
   end
 end else false.
Theorem rw_state_check_sound : forall bs tm L T t fuel,
 rw_state_check bs tm L T t fuel=true -> NonHalt tm /\ QHBound bs tm.
Proof.
 intros bs tm L T t fuel H. unfold rw_state_check in H.
 destruct ((1<=?L) && (2<=?T)) eqn:Hpar; [|discriminate].
 apply andb_prop in Hpar as [HL HT]; apply Nat.leb_le in HL,HT.
 destruct (csteps tm t c0) as [cc|] eqn:Et; [|discriminate].
 destruct (close_tr rconf rconf_enc (rw_succs tm L T) fuel [] PositiveSet.empty [rw_seed L T cc])
   as [Sl|] eqn:Es; [|discriminate].
 match type of H with (if ?b then _ else _) = true => destruct b eqn:Hcl end; [|discriminate].
 match type of H with (if ?b then _ else _) = true => destruct b eqn:Hmem end; [|discriminate].
 match type of H with (if ?b then _ else _) = true => destruct b eqn:Hpre end; [|discriminate].
 eapply (abstract_state_bound tm rconf rconf_enc rw_instr (rw_succs tm L T) rw_covers');
   [exact rconf_enc_inj| | |exact Et| |exact Hcl|exact Hmem| |exact H|exact Hpre].
 - intros [q[[[[li lb]h]rb]ri]] c [(Hq & Hh & _) _].
   unfold rw_instr,instr_of; rewrite Hq,Hh; reflexivity.
 - intros a c Hc; apply rw_succs_sound'; assumption.
 - split; [apply rw_seed_covers|apply rw_seed_wf]; assumption.
 - intros tg. apply Forall_forall; intros comp Hin.
   apply in_map_iff in Hin as (cs & <- & _). destruct cs; simpl; [exact I|].
   intros a cc' a' cc'' sl Hca Hca' Hstep Es' Hin'. eapply rw_meas_exact; eauto.
Qed.
