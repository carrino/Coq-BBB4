From Coq Require Import Arith Lia Bool List NArith.
From BBB24 Require Import Statement StatementTr CTape PosEnc Closure ClosureTr Bounds AbstractCensus RepWLSearch.
From BBB24.Checkers Require Import RepWL.
Import ListNotations.
Section Parameters.
Variable bs bi : N.

Definition rw_check tm L T t fuel :=
  if (1 <=? L) && (2 <=? T) then
  match csteps tm t c0 with
  | None => false
  | Some cc =>
    let a0 := rw_seed L T cc in
    match close_tr rconf rconf_enc (rw_succs tm L T) fuel [] PositiveSet.empty [a0] with
    | None => false
    | Some Sl =>
      if closed_tr_b rconf rconf_enc (rw_succs tm L T) Sl then
      if mem_tr rconf rconf_enc a0 Sl then
      if prefix_gate bs bi tm t (tail_states (labels rw_instr Sl)) (tail_instrs (labels rw_instr Sl)) then
        live_lex_ok_tr rconf rconf_enc rw_instr (rw_succs tm L T) Sl
          (fun tg => map (rw_comp_denote tm) (rw_rank_procedure tm L T Sl tg))
      else false else false else false
    end
  end else false.

Theorem rw_check_sound : forall tm L T t fuel,
  rw_check tm L T t fuel = true -> NonHalt tm /\ Bounds bs bi tm.
Proof.
  intros tm L T t fuel H. unfold rw_check in H.
  destruct ((1 <=? L) && (2 <=? T)) eqn:Hpar; [|discriminate].
  apply andb_prop in Hpar as [HL HT]. apply Nat.leb_le in HL, HT.
  destruct (csteps tm t c0) as [cc|] eqn:Et; [|discriminate].
  destruct (close_tr rconf rconf_enc (rw_succs tm L T) fuel [] PositiveSet.empty [rw_seed L T cc])
    as [Sl|] eqn:Es; [|discriminate].
  match type of H with (if ?b then _ else _) = true => destruct b eqn:Hcl end; [|discriminate].
  match type of H with (if ?b then _ else _) = true => destruct b eqn:Hmem end; [|discriminate].
  match type of H with (if ?b then _ else _) = true => destruct b eqn:Hpre end; [|discriminate].
  eapply (abstract_bounds bs bi tm rconf rconf_enc rw_instr (rw_succs tm L T) rw_covers');
    [exact rconf_enc_inj| | |exact Et| |exact Hcl|exact Hmem| |exact H|exact Hpre].
  - intros [q [[[[li lb] h] rb] ri]] c [(Hq & Hh & _) _].
    unfold rw_instr, instr_of. rewrite Hq, Hh. reflexivity.
  - intros a c Hc. apply rw_succs_sound'; assumption.
  - split; [apply rw_seed_covers|apply rw_seed_wf]; assumption.
  - intros tg. apply Forall_forall. intros comp Hin.
    apply in_map_iff in Hin as (cs & <- & _). destruct cs; simpl; [exact I|].
    intros a cc' a' cc'' sl Hca Hca' Hstep Es' Hin'. eapply rw_meas_exact; eauto.
Qed.

End Parameters.
