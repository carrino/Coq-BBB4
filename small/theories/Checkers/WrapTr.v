(* Adapted from theories/Checkers/WrapTr.v for the common small-machine carrier. *)
(** * Checkers/WrapTr: quiet-INSTRUCTION quasihalting via the
    multi-cell halt-redirect machine.

    Wrap.v's halt-redirect argument at transition level
    (SCOPING_INSTR.md sections 3.2, 5).  The load-bearing difference
    from the state level, measured on the v0 suspects: a
    transition-quasihalting machine typically has SEVERAL quiet
    instructions (a quiet state contributes two at once, plus
    stragglers), and a closure wrapped at only one of them keeps the
    others as appearing-but-never-recurring nodes — the liveness gate
    then rightly fails.  So the wrap blanks the machine's whole
    CLAIMED-QUIET SET [tgs] ([tm_wrap_trs]): a halt-free closure of
    that machine says none of them ever fires after [t], and the
    ClosureTr rank gate over the same closure makes every OTHER
    appearing instruction recur.  Each pair [(tg, s)] in [tgs] is
    additionally pinned by simulation: [tg] fires at [s] and not in
    [(s, t]].

    Delivered (census R_QH contract at transition level):

      [NonHalt tm /\ QHBoundTr (S t) tm /\ QuasiHaltsTr tm]

    (the middle conjunct stated unfolded, keeping this file below the
    census layer). *)

From Coq Require Import Arith Lia Bool List ZArith.
From SmallBB Require Import Statement StatementTr CTape PosEnc
  Closure ClosureTr.
From SmallBB.Checkers Require Import Cycle.
From SmallBB.Checkers.IRules Require Import Engine AnchorVisits AnchorVisitsTr.
Import ListNotations.
Open Scope nat_scope.

(** Branch before growing a closure or searching liveness certificates.
    Unlike a call to [andb], this notation short-circuits under native and
    VM evaluation; it is definitionally equal to boolean conjunction. *)
Local Notation "a &&& b" := (if a then b else false)
  (at level 40, left associativity).

(** ** The multi-cell halt-redirect machine *)

Definition tr_inb (t : Instr) (tgs : list Instr) : bool :=
  existsb (instr_eqb t) tgs.

Lemma tr_inb_spec : forall t tgs, tr_inb t tgs = true <-> In t tgs.
Proof.
  intros t tgs. unfold tr_inb. rewrite existsb_exists.
  split.
  - intros (t' & Hin & He). apply instr_eqb_spec in He. now subst.
  - intros Hin. exists t. split; [exact Hin|].
    apply instr_eqb_spec; reflexivity.
Qed.

Definition tm_wrap_trs (tm : TM) (tgs : list Instr) : TM :=
  fun p x => if tr_inb (p, x) tgs then None else tm p x.

Lemma tm_wrap_trs_at : forall tm tgs p x,
  In (p, x) tgs -> tm_wrap_trs tm tgs p x = None.
Proof.
  intros tm tgs p x H. unfold tm_wrap_trs.
  now rewrite (proj2 (tr_inb_spec (p, x) tgs) H).
Qed.

Lemma tm_wrap_trs_off : forall tm tgs p x,
  ~ In (p, x) tgs -> tm_wrap_trs tm tgs p x = tm p x.
Proof.
  intros tm tgs p x H. unfold tm_wrap_trs.
  destruct (tr_inb (p, x) tgs) eqn:E; [|reflexivity].
  apply tr_inb_spec in E. contradiction.
Qed.

Lemma wrap_trs_step_off : forall tm tgs c,
  ~ In (instr_of c) tgs -> step (tm_wrap_trs tm tgs) c = step tm c.
Proof.
  intros tm tgs [p tp] H. unfold step; simpl in *.
  rewrite tm_wrap_trs_off; [reflexivity | exact H].
Qed.

Lemma wrap_trs_step_at : forall tm tgs c,
  In (instr_of c) tgs -> step (tm_wrap_trs tm tgs) c = None.
Proof.
  intros tm tgs [p tp] H. unfold instr_of in H; simpl in H.
  unfold step; simpl.
  now rewrite (tm_wrap_trs_at tm tgs p (t_head tp) H).
Qed.

(** While the wrapped run survives, the two runs coincide and never
    fire anything in [tgs]. *)
Lemma wrap_trs_agree : forall tm tgs c,
  (forall j, stepn (tm_wrap_trs tm tgs) j c <> None) ->
  forall k, stepn (tm_wrap_trs tm tgs) k c = stepn tm k c /\
            (forall c', stepn tm k c = Some c' -> ~ In (instr_of c') tgs).
Proof.
  intros tm tgs c Him k. induction k as [|k IH].
  - split; [reflexivity|].
    intros c' Hc' Hq. simpl in Hc'. injection Hc' as <-.
    apply (Him 1). cbn [stepn].
    rewrite wrap_trs_step_at by assumption. reflexivity.
  - destruct IH as [IHeq IHq].
    destruct (stepn (tm_wrap_trs tm tgs) k c) as [ck|] eqn:Ek;
      [| now destruct (Him k)].
    assert (Hck : stepn tm k c = Some ck) by congruence.
    assert (Hoff : ~ In (instr_of ck) tgs) by (apply (IHq ck Hck)).
    assert (Heq : stepn (tm_wrap_trs tm tgs) (S k) c = stepn tm (S k) c).
    { replace (S k) with (k + 1) by lia.
      rewrite !stepn_add, Ek, Hck. cbn [stepn].
      rewrite wrap_trs_step_off by assumption. reflexivity. }
    split; [exact Heq|].
    intros c' Hc' Hq'.
    apply (Him (S k + 1)).
    rewrite stepn_add, Heq, Hc'. cbn [stepn].
    rewrite wrap_trs_step_at by assumption. reflexivity.
Qed.

