(** * BBB4_Statement: machine model and quasihalting semantics.

    The (4,2) Turing machine model and the Beeping Busy Beaver
    (quasihalting) definitions, following the conventions of the BBB
    harness repo (carrino/BBB, README "Definitions"):

    - deterministic TM, 4 states x 2 symbols, two-way-infinite blank
      tape, start state A;
    - an undefined transition is a halt;
    - the tape is head-at-origin: [Tape] carries the two half-tapes as
      total functions [nat -> Sym] (offset 0 = the cell adjacent to the
      head) plus the head cell, and a move shifts the representation.
      Configurations are therefore compared *relative to the head*; the
      dynamics cannot observe absolute position, so this loses nothing.

    Step-counting convention: the BBB harness numbers steps 1,2,... and
    a transition of state [q] fires at step [n+1] exactly when the
    configuration with index [n] (i.e. after [n] steps, [stepn n]) is
    in state [q].  [VisitsAt tm q n] speaks of configuration indices;
    the harness's "last visit step" of a state is thus (last visited
    configuration index) + 1. *)

From Coq Require Import Arith Lia List.
Import ListNotations.

(** ** States, symbols, directions *)

Inductive St : Set := StA | StB | StC | StD.
Inductive Sym : Set := S0 | S1.
Inductive Dir : Set := DL | DR.

Definition all_St : list St := [StA; StB; StC; StD].

Lemma all_St_complete : forall q, In q all_St.
Proof. destruct q; simpl; auto. Qed.

Definition st_eqb (a b : St) : bool :=
  match a, b with
  | StA, StA | StB, StB | StC, StC | StD, StD => true
  | _, _ => false
  end.

Lemma st_eqb_spec : forall a b, st_eqb a b = true <-> a = b.
Proof. destruct a, b; simpl; split; congruence. Qed.

Definition sym_eqb (a b : Sym) : bool :=
  match a, b with S0, S0 | S1, S1 => true | _, _ => false end.

Lemma sym_eqb_spec : forall a b, sym_eqb a b = true <-> a = b.
Proof. destruct a, b; simpl; split; congruence. Qed.

(** ** Machines *)

Record Trans : Set := mkTrans { t_write : Sym; t_dir : Dir; t_next : St }.

(** [None] = undefined transition = halt. *)
Definition TM : Type := St -> Sym -> option Trans.

(** ** Configurations and steps *)

Record Tape : Type := mkTape {
  t_left : nat -> Sym;   (* cells left of the head, nearest first *)
  t_head : Sym;
  t_right : nat -> Sym   (* cells right of the head, nearest first *)
}.

Definition ExecState : Type := (St * Tape)%type.

Definition push_side (s : Sym) (f : nat -> Sym) : nat -> Sym :=
  fun n => match n with 0 => s | S m => f m end.

Definition tail_side (f : nat -> Sym) : nat -> Sym := fun n => f (S n).

Definition tape_move (d : Dir) (w : Sym) (tp : Tape) : Tape :=
  match d with
  | DR => mkTape (push_side w (t_left tp)) (t_right tp 0) (tail_side (t_right tp))
  | DL => mkTape (tail_side (t_left tp)) (t_left tp 0) (push_side w (t_right tp))
  end.

Definition step (tm : TM) (c : ExecState) : option ExecState :=
  let (q, tp) := c in
  match tm q (t_head tp) with
  | None => None
  | Some tr => Some (t_next tr, tape_move (t_dir tr) (t_write tr) tp)
  end.

Fixpoint stepn (tm : TM) (n : nat) (c : ExecState) : option ExecState :=
  match n with
  | 0 => Some c
  | S m => match step tm c with
           | None => None
           | Some c' => stepn tm m c'
           end
  end.

Definition blank_side : nat -> Sym := fun _ => S0.
Definition InitES : ExecState := (StA, mkTape blank_side S0 blank_side).

(** ** Elementary [stepn] algebra *)

Lemma stepn_add : forall tm a b c,
  stepn tm (a + b) c =
  match stepn tm a c with
  | Some c' => stepn tm b c'
  | None => None
  end.
Proof.
  induction a; intros; simpl.
  - reflexivity.
  - destruct (step tm c); [apply IHa | reflexivity].
Qed.

Lemma stepn_prefix : forall tm a b c c',
  a <= b -> stepn tm b c = Some c' ->
  exists cm, stepn tm a c = Some cm /\ stepn tm (b - a) cm = Some c'.
Proof.
  intros tm a b c c' Hle H.
  replace b with (a + (b - a)) in H by lia.
  rewrite stepn_add in H.
  destruct (stepn tm a c) eqn:E; [eauto | discriminate].
Qed.

(** ** Halting *)

Definition Halts (tm : TM) : Prop := exists n, stepn tm n InitES = None.
Definition NonHalt (tm : TM) : Prop := forall n, stepn tm n InitES <> None.

(** ** Quasihalting (state level -- BBB proper)

    A state is visited at configuration index [n] when the machine is
    in that state after [n] steps (about to fire one of its
    transitions).  The machine quasihalts iff some state is visited at
    least once but only finitely often.  A halting machine quasihalts
    trivially (after the halt there are no configurations at all, so
    every state is eventually quiet).

    [NeverQuasiHaltsSt] is stated in the constructively strong form
    "every visited state is visited at unboundedly large indices",
    which is what the checkers actually establish; it implies the
    negation of [QuasiHaltsSt] ([never_qh_not_qh]) and non-halting
    ([never_qh_nonhalt]).

    Never-visited ("silent") states do not witness [QuasiHaltsSt]
    (the [Visited] conjunct): this matches the BBB harness treatment,
    where a silent state's score-0 "quasihalt" is a convention question
    that cannot affect any BBB value. *)

Definition VisitsAt (tm : TM) (q : St) (n : nat) : Prop :=
  exists c, stepn tm n InitES = Some c /\ fst c = q.

Definition Visited (tm : TM) (q : St) : Prop := exists n, VisitsAt tm q n.

Definition QuietFrom (tm : TM) (q : St) (N : nat) : Prop :=
  forall n, N <= n -> ~ VisitsAt tm q n.

Definition QuasiHaltsSt (tm : TM) : Prop :=
  exists q, Visited tm q /\ exists N, QuietFrom tm q N.

Definition NeverQuasiHaltsSt (tm : TM) : Prop :=
  forall q, Visited tm q -> forall N, exists n, N <= n /\ VisitsAt tm q n.

(** State [q]'s last visit is at configuration index [s] (in harness
    terms: the last transition of state [q] fires at step [s+1], and
    the state-level score contributed by [q] is [s+1]). *)
Definition QuietAfter (tm : TM) (q : St) (s : nat) : Prop :=
  VisitsAt tm q s /\ forall n, s < n -> ~ VisitsAt tm q n.

Lemma never_qh_not_qh : forall tm, NeverQuasiHaltsSt tm -> ~ QuasiHaltsSt tm.
Proof.
  intros tm H (q & Hv & N & HN).
  destruct (H q Hv N) as (n & Hn & Hvis).
  exact (HN n Hn Hvis).
Qed.

Lemma never_qh_nonhalt : forall tm, NeverQuasiHaltsSt tm -> NonHalt tm.
Proof.
  intros tm H n Hnone.
  assert (Hv : Visited tm StA) by (exists 0, InitES; split; reflexivity).
  destruct (H StA Hv n) as (m & Hm & c & Hc & _).
  replace m with (n + (m - n)) in Hc by lia.
  rewrite stepn_add, Hnone in Hc. discriminate.
Qed.

Lemma quiet_after_qh : forall tm q s,
  QuietAfter tm q s -> QuasiHaltsSt tm.
Proof.
  intros tm q s [Hvis Hq].
  exists q. split.
  - exists s; exact Hvis.
  - exists (S s). intros n Hn. apply Hq. lia.
Qed.
