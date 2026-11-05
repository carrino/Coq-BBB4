(** Repeated-word blocks preserve parity information lost by the n-gram
    abstraction.  This closes the final instruction-silence families of
    the two-state, three-symbol waiting census. *)
From Coq Require Import Arith Lia Bool List PArith.
From SmallBB Require Import Statement StatementTr CTape Size PosEnc ClosureTr Bounds
  AbstractCensus RepWLSearch.
From SmallBB.Checkers Require Import RepWL.
From BBBWait Require Import SpecTr Tail.
Import ListNotations.

Definition rw_tail tm L T t fuel : option (list cconf) :=
  if (1 <=? L) && (2 <=? T) then
  match csteps tm t c0 with
  | None => None
  | Some cc =>
    let a0 := rw_seed L T cc in
    match close_tr rconf rconf_enc (rw_succs tm L T)
      fuel [] PositiveSet.empty [a0] with
    | None => None
    | Some Sl =>
      if closed_tr_b rconf rconf_enc (rw_succs tm L T) Sl then
      if mem_tr rconf rconf_enc a0 Sl then Some (labels rw_instr Sl) else None
      else None
    end
  end else None.

Lemma rw_covers_instr : forall a c,
  rw_covers' a c -> rw_instr a = instr_of c.
Proof.
  intros [q [[[[li lb] h] rb] ri]] c [(Hq & Hh & _) _].
  unfold rw_instr, instr_of; rewrite Hq, Hh; reflexivity.
Qed.

Theorem rw_tail_sound : forall tm L T t fuel Sl,
  rw_tail tm L T t fuel = Some Sl ->
  forall s tg, t <= s -> FiresAt tm tg s -> tail_instrs Sl tg = true.
Proof.
  intros tm L T t fuel Sl H.
  unfold rw_tail in H.
  destruct ((1 <=? L) && (2 <=? T)) eqn:Hparams; [|discriminate].
  apply andb_prop in Hparams as [HL HT]; apply Nat.leb_le in HL, HT.
  destruct (csteps tm t c0) as [cc|] eqn:Et; [|discriminate].
  set (a0 := rw_seed L T cc) in *.
  destruct (close_tr rconf rconf_enc (rw_succs tm L T)
    fuel [] PositiveSet.empty [a0]) as [nodes|] eqn:Eclose; [|discriminate].
  match type of H with (if ?b then _ else _) = _ => destruct b eqn:Hcl end;
    [|discriminate].
  match type of H with (if ?b then _ else _) = _ => destruct b eqn:Hmem end;
    [|discriminate].
  injection H as <-.
  assert (HIn : In a0 nodes) by (eapply mem_In_tr; [exact rconf_enc_inj|exact Hmem]).
  assert (Hcov : rw_covers' a0 (lift cc)).
  { split; [apply rw_seed_covers|apply rw_seed_wf]; assumption. }
  assert (Hstart : stepn tm t InitES = Some (lift cc)).
  { rewrite <- lift_c0; apply csteps_lift; exact Et. }
  assert (Hinv : forall j, exists c a, stepn tm j (lift cc) = Some c /\
      In a nodes /\ rw_covers' a c).
  { eapply closure_invariant_tr; [exact rconf_enc_inj| |exact Hcl|exact HIn|exact Hcov].
    intros a c Hc; apply rw_succs_sound'; assumption. }
  intros s tg Hts (c & Hrun & Htg).
  destruct (Hinv (s-t)) as (c' & a & Hrun' & Ha & Hca).
  replace s with (t+(s-t)) in Hrun by lia.
  rewrite stepn_add, Hstart, Hrun' in Hrun; injection Hrun as <-.
  rewrite labels_instr; apply existsb_exists; exists a; split; [exact Ha|].
  apply instr_eqb_spec; rewrite <- Htg; now apply rw_covers_instr.
Qed.

Definition rw_wait_check_tr tm B w L T t fuel :=
  (t <=? S (B+w)) &&
  match rw_tail tm L T t fuel with
  | None => false
  | Some Sl => tail_instr_gate tm B w Sl
  end.

Theorem rw_wait_check_tr_sound : forall tm B w L T t fuel,
  rw_wait_check_tr tm B w L T t fuel = true ->
  forall tg, FutureBeepTr tm tg B -> BeepWindowTr tm tg B w.
Proof.
  intros tm B w L T t fuel H.
  unfold rw_wait_check_tr in H; apply andb_prop in H as [Hanchor H].
  apply Nat.leb_le in Hanchor.
  destruct (rw_tail tm L T t fuel) as [Sl|] eqn:E; [|discriminate].
  eapply tail_instr_wait_sound; [exact Hanchor|exact H|].
  now apply (rw_tail_sound tm L T t fuel Sl).
Qed.

Print Assumptions rw_wait_check_tr_sound.

(** The 44 exceptional labeled tables. Each listed table is rechecked;
    exhaustive coverage of the complete domain is a separate census theorem. *)
Definition exceptional23_tables : list TM := [
  (* 1RB2RB1LA_2LA2RA0LA *)
  machine_of_codes 2 3 [7;11;4;8;10;0];
  (* 2RB2RA1LA_2LA1RB0LB *)
  machine_of_codes 2 3 [11;10;4;8;7;1];
  (* 1LB2LB1RA_2RA2LA0RA *)
  machine_of_codes 2 3 [5;9;6;10;8;2];
  (* 2LB2LA1RA_2RA1LB0RB *)
  machine_of_codes 2 3 [9;8;6;10;5;3];
  (* 2LB2RA1LB_1RA0RA1LA *)
  machine_of_codes 2 3 [9;10;5;6;2;4];
  (* 2LB2RA1LB_1RA1RA1LA *)
  machine_of_codes 2 3 [9;10;5;6;6;4];
  (* 1RB0RB1LB_2LA2RB1LA *)
  machine_of_codes 2 3 [7;3;5;8;11;4];
  (* 1RB1RB1LB_2LA2RB1LA *)
  machine_of_codes 2 3 [7;7;5;8;11;4];
  (* 2LB2RB0LB_1RA2RA1LB *)
  machine_of_codes 2 3 [9;11;1;6;10;5];
  (* 2LB2RB2LB_1RA2RA1LB *)
  machine_of_codes 2 3 [9;11;9;6;10;5];
  (* 1RB0RB2LA_1LA2RB1LB *)
  machine_of_codes 2 3 [7;3;8;4;11;5];
  (* 1RB1LB2LA_1LA2RB1LB *)
  machine_of_codes 2 3 [7;5;8;4;11;5];
  (* 1RB1RB2LA_1LA2RB1LB *)
  machine_of_codes 2 3 [7;7;8;4;11;5];
  (* 1RB2LA2LA_1LA2RB1LB *)
  machine_of_codes 2 3 [7;8;8;4;11;5];
  (* 2LB1RA0LB_2RA2RB1LB *)
  machine_of_codes 2 3 [9;6;1;10;11;5];
  (* 2LB1RA1RA_2RA2RB1LB *)
  machine_of_codes 2 3 [9;6;6;10;11;5];
  (* 2LB1RA2LB_2RA2RB1LB *)
  machine_of_codes 2 3 [9;6;9;10;11;5];
  (* 2LB1RA2RB_2RA2RB1LB *)
  machine_of_codes 2 3 [9;6;11;10;11;5];
  (* 2RB2LA1RB_1LA0LA1RA *)
  machine_of_codes 2 3 [11;8;7;4;0;6];
  (* 2RB2LA1RB_1LA1LA1RA *)
  machine_of_codes 2 3 [11;8;7;4;4;6];
  (* 1LB0LB1RB_2RA2LB1RA *)
  machine_of_codes 2 3 [5;1;7;10;9;6];
  (* 1LB1LB1RB_2RA2LB1RA *)
  machine_of_codes 2 3 [5;5;7;10;9;6];
  (* 2RB2LB0RB_1LA2LA1RB *)
  machine_of_codes 2 3 [11;9;3;4;8;7];
  (* 2RB2LB2RB_1LA2LA1RB *)
  machine_of_codes 2 3 [11;9;11;4;8;7];
  (* 1LB0LB2RA_1RA2LB1RB *)
  machine_of_codes 2 3 [5;1;10;6;9;7];
  (* 1LB1LB2RA_1RA2LB1RB *)
  machine_of_codes 2 3 [5;5;10;6;9;7];
  (* 1LB1RB2RA_1RA2LB1RB *)
  machine_of_codes 2 3 [5;7;10;6;9;7];
  (* 1LB2RA2RA_1RA2LB1RB *)
  machine_of_codes 2 3 [5;10;10;6;9;7];
  (* 2RB1LA0RB_2LA2LB1RB *)
  machine_of_codes 2 3 [11;4;3;8;9;7];
  (* 2RB1LA1LA_2LA2LB1RB *)
  machine_of_codes 2 3 [11;4;4;8;9;7];
  (* 2RB1LA2LB_2LA2LB1RB *)
  machine_of_codes 2 3 [11;4;9;8;9;7];
  (* 2RB1LA2RB_2LA2LB1RB *)
  machine_of_codes 2 3 [11;4;11;8;9;7];
  (* 2LB2LA1RA_2RA1LB2LA *)
  machine_of_codes 2 3 [9;8;6;10;5;8];
  (* 2RB2RA1LA_2LA1RB2LA *)
  machine_of_codes 2 3 [11;10;4;8;7;8];
  (* 1RB2RB1LA_2LA2RA2LA *)
  machine_of_codes 2 3 [7;11;4;8;10;8];
  (* 1LB2RA1LA_1RA0RB2LB *)
  machine_of_codes 2 3 [5;10;4;6;3;9];
  (* 1LB2RA1LA_1RA1LA2LB *)
  machine_of_codes 2 3 [5;10;4;6;4;9];
  (* 1LB2RA1LA_1RA1RA2LB *)
  machine_of_codes 2 3 [5;10;4;6;6;9];
  (* 2LB2LA1RA_2RA1LB2RA *)
  machine_of_codes 2 3 [9;8;6;10;5;10];
  (* 2RB2RA1LA_2LA1RB2RA *)
  machine_of_codes 2 3 [11;10;4;8;7;10];
  (* 1LB2LB1RA_2RA2LA2RA *)
  machine_of_codes 2 3 [5;9;6;10;8;10];
  (* 1RB2LA1RA_1LA0LB2RB *)
  machine_of_codes 2 3 [7;8;6;4;1;11];
  (* 1RB2LA1RA_1LA1LA2RB *)
  machine_of_codes 2 3 [7;8;6;4;4;11];
  (* 1RB2LA1RA_1LA1RA2RB *)
  machine_of_codes 2 3 [7;8;6;4;6;11]].

Lemma exceptional23_checked :
  forallb (fun tm => rw_wait_check_tr tm 67 693 2 2 760 4096)
    exceptional23_tables = true.
Proof. native_compute; reflexivity. Qed.

Theorem exceptional23_wait : forall tm, In tm exceptional23_tables ->
  forall tg, FutureBeepTr tm tg 67 -> BeepWindowTr tm tg 67 693.
Proof.
  intros tm Hin.
  pose proof exceptional23_checked as H.
  apply forallb_forall with (x:=tm) in H; [|exact Hin].
  exact (rw_wait_check_tr_sound tm 67 693 2 2 760 4096 H).
Qed.

Print Assumptions exceptional23_wait.
