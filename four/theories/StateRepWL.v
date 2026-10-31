(** Repeated-word closure with STATE recurrence; no instruction-bound claim.
    Reuses the checked RepWL abstraction and its untrusted SCC/rank searches. *)
From Coq Require Import Arith Bool List NArith.
From Coq Require Import FSets.FMapPositive.
From BBB24 Require Import Statement StatementTr Spec CTape PosEnc Closure ClosureTr
  Bounds AbstractCensus StateBounds RepWLSearch.
From BBB24.Checkers Require Import RepWL.
Import ListNotations.

Definition srw_qsuccs tm L T (q : St) a :=
  match rw_succs tm L T a with
  | Some next => filter (fun b=>negb(st_eqb (fst (rw_instr b)) q)) next
  | None => []
  end.
Definition srw_build_adj tm L T q (nodes : list rconf) : RAdj :=
  fold_left (fun g a=>radj_set g a (srw_qsuccs tm L T q a))
    nodes (PositiveMap.empty _).
Definition srw_rank_procedure tm L T (Sl : list rconf) q : list rwcomp :=
  let nodes:=filter (fun a=>negb(st_eqb (fst (rw_instr a)) q)) Sl in
  let g:=srw_build_adj tm L T q nodes in
  match rproc_rounds 100 tm (S (S (length nodes))) (S (length nodes*8+8)) nodes g [] with
  | Some cs=>cs | None=>[] end.
Definition srw_check (bs : N) tm L T t fuel :=
  if (1<=?L) && (2<=?T) then
  match csteps tm t c0 with
  | None=>false
  | Some cc=>
    let a0:=rw_seed L T cc in
    match close_tr rconf rconf_enc (rw_succs tm L T) fuel [] PositiveSet.empty [a0] with
    | None=>false
    | Some Sl=>
      if closed_b rconf rconf_enc (rw_succs tm L T) Sl then
      if mem rconf rconf_enc a0 Sl then
      if state_prefix_gate bs tm t (tail_states (labels rw_instr Sl)) then
        live_lex_ok rconf rconf_enc (fun a=>fst(rw_instr a)) (rw_succs tm L T) Sl
          (fun q=>map (rw_comp_denote tm) (srw_rank_procedure tm L T Sl q))
      else false else false else false
    end
  end else false.
Theorem srw_check_sound : forall bs tm L T t fuel,
  srw_check bs tm L T t fuel=true -> NonHalt tm /\ QHBound (N.to_nat bs) tm.
Proof.
  intros bs tm L T t fuel H. unfold srw_check in H.
  destruct ((1<=?L) && (2<=?T)) eqn:Hpar; [|discriminate].
  apply andb_prop in Hpar as [HL HT]. apply Nat.leb_le in HL,HT.
  destruct (csteps tm t c0) as [cc|] eqn:Et; [|discriminate].
  destruct (close_tr rconf rconf_enc (rw_succs tm L T) fuel [] PositiveSet.empty [rw_seed L T cc])
    as [Sl|] eqn:Es; [|discriminate].
  match type of H with (if ?b then _ else _) = true => destruct b eqn:Hcl end; [|discriminate].
  match type of H with (if ?b then _ else _) = true => destruct b eqn:Hmem end; [|discriminate].
  match type of H with (if ?b then _ else _) = true => destruct b eqn:Hpre end; [|discriminate].
  eapply (abstract_state_bound tm rconf rconf_enc rw_instr (rw_succs tm L T) rw_covers');
    [exact rconf_enc_inj| | |exact Et| |exact Hcl|exact Hmem| |exact H|exact Hpre].
  - intros [q [[[[li lb] h] rb] ri]] c [(Hq&Hh&_) _].
    unfold rw_instr,instr_of. rewrite Hq,Hh. reflexivity.
  - intros a c Hc. apply rw_succs_sound'; assumption.
  - split; [apply rw_seed_covers|apply rw_seed_wf]; assumption.
  - intros q. apply Forall_forall. intros comp Hin.
    apply in_map_iff in Hin as (cs&<-&_). destruct cs; simpl; [exact I|].
    intros a cc' a' cc'' sl Hca Hca' Hstep Es' Hin'. eapply rw_meas_exact; eauto.
Qed.
Print Assumptions srw_check_sound.
