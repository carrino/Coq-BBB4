(** * BlankTail: a one-state march on blank tape closes the machine.

    The cheapest closer in the project, and the one that lands the
    historical BBB(4) champions.

    Measured shape (`docs/RESIDUE_VISIT_MEASUREMENT.md` sections 4b and 4c):
    a handful of residue machines -- including the current champion
    [1RB1LD_1RC1RB_1LC1LA_0RC0RD] and both previous ones -- reach, after a
    finite prefix, a configuration in which

    - the machine is in some state [q],
    - the cell under the head is blank,
    - the whole half-tape AHEAD (in the direction [q] travels on a blank)
      is blank, and
    - [tm q S0 = Some (mkTrans w d q)] -- a SELF-LOOP on blank.

    From there it marches off across virgin tape forever, in that one state,
    writing symbols it never re-reads.  Every other state is therefore quiet
    from the prefix onward, so [QHBound B] holds for any [B] at least the
    prefix length.

    For the champion the tape is COMPLETELY erased at that moment, which is
    why it is simultaneously the BLB(4) blanking champion: the blanking event
    and the quiet point are the same event.

    The invariant is "the list on the travel side is ALL BLANK" -- not "is
    [[]]".  [csteps] conses actual written symbols, so a machine that has
    erased its tape holds a list of [S0]s rather than the empty list; the two
    are [lift]-equal but not syntactically equal, and the per-machine
    [vm_compute] produces the former.  [chd] and [ctl] preserve all-blankness
    ([chd [] = S0] too), which keeps the induction two lines.

    Axiom footprint: this file adds none.  [csteps_lift] carries the standing
    [functional_extensionality_dep] and nothing else. *)

From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4 Require Import Census.TNF_QH.
Import ListNotations.

(** ** All-blank half-tapes *)

Definition blank_list (l : list Sym) : Prop := Forall (fun s => s = S0) l.

Fixpoint blank_listb (l : list Sym) : bool :=
  match l with
  | [] => true
  | S0 :: t => blank_listb t
  | _ => false
  end.

Lemma blank_listb_spec : forall l, blank_listb l = true -> blank_list l.
Proof.
  induction l as [|s t IH]; intro H.
  - constructor.
  - destruct s; [|discriminate]. constructor; [reflexivity | apply IH, H].
Qed.

Lemma chd_blank : forall l, blank_list l -> chd l = S0.
Proof. intros [|s t] H; [reflexivity|]. inversion H; subst; reflexivity. Qed.

Lemma ctl_blank : forall l, blank_list l -> blank_list (ctl l).
Proof. intros [|s t] H; [constructor|]. inversion H; assumption. Qed.

(** ** One step of the march *)

Lemma march_L_step : forall tm q w l r,
  tm q S0 = Some (mkTrans w DL q) ->
  blank_list l ->
  cstep tm (q, (l, S0, r)) = Some (q, (ctl l, S0, w :: r)).
Proof.
  intros tm q w l r H Hb. unfold cstep. rewrite H. cbn [ctape_move].
  rewrite (chd_blank l Hb). reflexivity.
Qed.

Lemma march_R_step : forall tm q w l r,
  tm q S0 = Some (mkTrans w DR q) ->
  blank_list r ->
  cstep tm (q, (l, S0, r)) = Some (q, (w :: l, S0, ctl r)).
Proof.
  intros tm q w l r H Hb. unfold cstep. rewrite H. cbn [ctape_move].
  rewrite (chd_blank r Hb). reflexivity.
Qed.

(** ** The march runs forever, staying in [q] *)

Lemma march_L : forall tm q w n l r,
  tm q S0 = Some (mkTrans w DL q) ->
  blank_list l ->
  exists ct, csteps tm n (q, (l, S0, r)) = Some (q, ct).
Proof.
  intros tm q w n. induction n as [|n IH]; intros l r H Hb.
  - exists (l, S0, r). reflexivity.
  - cbn [csteps]. rewrite (march_L_step tm q w l r H Hb).
    apply (IH (ctl l) (w :: r) H (ctl_blank l Hb)).
Qed.

Lemma march_R : forall tm q w n l r,
  tm q S0 = Some (mkTrans w DR q) ->
  blank_list r ->
  exists ct, csteps tm n (q, (l, S0, r)) = Some (q, ct).
Proof.
  intros tm q w n. induction n as [|n IH]; intros l r H Hb.
  - exists (l, S0, r). reflexivity.
  - cbn [csteps]. rewrite (march_R_step tm q w l r H Hb).
    apply (IH (w :: l) (ctl r) H (ctl_blank r Hb)).
Qed.

(** ** From the prefix onward the state is always [q] *)

Section Tail.

Variable tm : TM.
Variable q : St.
Variable N0 : nat.
Variable ct : ctape.

Hypothesis Hpre  : csteps tm N0 c0 = Some (q, ct).
Hypothesis Hloop : forall n, exists ct', csteps tm n (q, ct) = Some (q, ct').

Lemma tail_visits : forall n, N0 <= n ->
  exists c, stepn tm n InitES = Some c /\ fst c = q.
Proof.
  intros n Hn.
  replace n with (N0 + (n - N0)) by lia.
  rewrite stepn_add.
  rewrite <- lift_c0, (csteps_lift _ _ _ _ Hpre).
  destruct (Hloop (n - N0)) as (ct' & Hm).
  exists (lift (q, ct')). split.
  - exact (csteps_lift _ _ _ _ Hm).
  - reflexivity.
Qed.

Lemma tail_no_other : forall q' n,
  q' <> q -> N0 <= n -> ~ VisitsAt tm q' n.
Proof.
  intros q' n Hne Hn (c & Hc & Hcq).
  destruct (tail_visits n Hn) as (c2 & Hc2 & Hc2q).
  rewrite Hc in Hc2. injection Hc2 as <-. congruence.
Qed.

(** ** The closer *)

Theorem qhbound_blank_tail : forall B, N0 <= B -> QHBound B tm.
Proof.
  intros B HB q' s [Hvis Hquiet].
  destruct (st_eqb q' q) eqn:Eq.
  - (* q' = q : [q] recurs forever, so it is never quiet *)
    apply st_eqb_spec in Eq. subst q'.
    exfalso.
    destruct (tail_visits (S (Nat.max s N0)) ltac:(lia)) as (c & Hc & Hcq).
    apply (Hquiet (S (Nat.max s N0))); [lia|].
    exists c. split; assumption.
  - (* q' <> q : every visit of [q'] precedes N0 *)
    assert (Hne : q' <> q).
    { intro E. subst q'.
      rewrite (proj2 (st_eqb_spec q q) eq_refl) in Eq. discriminate. }
    destruct (le_lt_dec N0 s) as [Hle|Hlt].
    + exfalso. exact (tail_no_other q' s Hne Hle Hvis).
    + lia.
Qed.

End Tail.

(** ** Packaged forms, one per direction

    These are what a per-machine file instantiates.  Both side conditions are
    [vm_compute]-able: a concrete prefix run and a boolean blankness check. *)

Theorem qhbound_blank_tail_L : forall tm q w N0 l r B,
  tm q S0 = Some (mkTrans w DL q) ->
  csteps tm N0 c0 = Some (q, (l, S0, r)) ->
  blank_listb l = true ->
  N0 <= B ->
  QHBound B tm.
Proof.
  intros tm q w N0 l r B Hq Hpre Hbl HB.
  apply (qhbound_blank_tail tm q N0 (l, S0, r) Hpre); [|exact HB].
  intro n. destruct (march_L tm q w n l r Hq (blank_listb_spec l Hbl)) as (ct & H).
  exists ct. exact H.
Qed.

Theorem qhbound_blank_tail_R : forall tm q w N0 l r B,
  tm q S0 = Some (mkTrans w DR q) ->
  csteps tm N0 c0 = Some (q, (l, S0, r)) ->
  blank_listb r = true ->
  N0 <= B ->
  QHBound B tm.
Proof.
  intros tm q w N0 l r B Hq Hpre Hbr HB.
  apply (qhbound_blank_tail tm q N0 (l, S0, r) Hpre); [|exact HB].
  intro n. destruct (march_R tm q w n l r Hq (blank_listb_spec r Hbr)) as (ct & H).
  exists ct. exact H.
Qed.

(** ** Boolean interface

    A per-machine file should not have to name the prefix tape.  These run the
    prefix and check the landing configuration in one [vm_compute]. *)

Definition blank_tail_checkb (dir : Dir) (tm : TM) (q : St) (N0 : nat) : bool :=
  match csteps tm N0 c0 with
  | Some (q', (l, h, r)) =>
      st_eqb q' q && sym_eqb h S0 &&
      (match dir with DL => blank_listb l | DR => blank_listb r end)
  | None => false
  end.

Theorem qhbound_blank_tail_check : forall tm q w d N0 B,
  tm q S0 = Some (mkTrans w d q) ->
  blank_tail_checkb d tm q N0 = true ->
  N0 <= B ->
  QHBound B tm.
Proof.
  intros tm q w d N0 B Hq Hchk HB.
  unfold blank_tail_checkb in Hchk.
  destruct (csteps tm N0 c0) as [[q' [[l h] r]]|] eqn:Epre; [|discriminate].
  apply andb_prop in Hchk as [Hchk Hside].
  apply andb_prop in Hchk as [Hq' Hh].
  apply st_eqb_spec in Hq'. apply sym_eqb_spec in Hh. subst q' h.
  destruct d.
  - exact (qhbound_blank_tail_L tm q w N0 l r B Hq Epre Hside HB).
  - exact (qhbound_blank_tail_R tm q w N0 l r B Hq Epre Hside HB).
Qed.
