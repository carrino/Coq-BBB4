(** Supplied repeated-word graphs and ranks, checked without discovery search.
    Arbitrary external witnesses are safe: every semantic obligation is checked. *)
From Coq Require Import Arith Lia Bool List NArith.
From BBB24 Require Import Statement StatementTr CTape PosEnc Closure ClosureTr Bounds
  AbstractCensus RepWLSearch Pipeline Closeout Spec Bootstrap Census.
From BBB24.Checkers Require Import RepWL.
Import ListNotations.

Definition next_rw_check bs bi tm L T t (Sl : list rconf)
    (cert : Instr -> list rwcomp) :=
  if (1 <=? L) && (2 <=? T) then
  match csteps tm t c0 with
  | None => false
  | Some cc =>
      if closed_tr_b rconf rconf_enc (rw_succs tm L T) Sl then
      if mem_tr rconf rconf_enc (rw_seed L T cc) Sl then
      if prefix_gate bs bi tm t (tail_states (labels rw_instr Sl)) (tail_instrs (labels rw_instr Sl)) then
        live_lex_ok_tr rconf rconf_enc rw_instr (rw_succs tm L T) Sl
          (fun tg => map (rw_comp_denote tm) (cert tg))
      else false else false else false
  end else false.

Theorem next_rw_check_sound : forall bs bi tm L T t Sl cert,
  next_rw_check bs bi tm L T t Sl cert = true -> NonHalt tm /\ Bounds bs bi tm.
Proof.
  intros bs bi tm L T t Sl cert H. unfold next_rw_check in H.
  destruct ((1 <=? L) && (2 <=? T)) eqn:Hpar; [|discriminate].
  apply andb_prop in Hpar as [HL HT]. apply Nat.leb_le in HL, HT.
  destruct (csteps tm t c0) as [cc|] eqn:Et; [|discriminate].
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

Record NextRWRow := next_rw_row {
  row_codes : list nat; row_L : nat; row_T : nat; row_t : nat;
  row_graph : list rconf; row_ranks : list (list rwcomp)
}.
Definition next_rw_row_check bs bi r :=
  next_rw_check bs bi (machine_of_codes (row_codes r)) (row_L r) (row_T r) (row_t r)
    (row_graph r) (fun tg => nth (4 * st_index (fst tg) + sym_index (snd tg)) (row_ranks r) []).
Definition next_rw_batch_check bs bi rows := forallb (next_rw_row_check bs bi) rows.
Definition next_rw_board rows := map (fun r => machine_of_codes (row_codes r)) rows.
Theorem next_rw_board_sound : forall bs bi rows,
  next_rw_batch_check bs bi rows = true -> BoardSound bs bi (next_rw_board rows).
Proof.
  intros bs bi rows H family Hin tm Hle.
  apply in_map_iff in Hin as (r & <- & Hin).
  apply forallb_forall with (x:=r) in H; [|exact Hin].
  unfold next_rw_row_check in H.
  apply next_rw_check_sound in H as [Hnh Hb].
  eapply extend_bounds; eauto.
Qed.
Theorem next_rw_board_nonhalt : forall bs bi rows,
  next_rw_batch_check bs bi rows = true ->
  forall family, In family (next_rw_board rows) -> NonHalt family.
Proof.
  intros bs bi rows H family Hin.
  apply in_map_iff in Hin as (r & <- & Hin).
  apply forallb_forall with (x:=r) in H; [|exact Hin].
  unfold next_rw_row_check in H.
  exact (proj1 (next_rw_check_sound _ _ _ _ _ _ _ _ H)).
Qed.
Print Assumptions next_rw_check_sound.
