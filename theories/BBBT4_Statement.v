(** * BBBT4_Statement: transition-level (instruction-level) quasihalting.

    The transition-level ("instruction-level") Beeping Busy Beaver
    definitions on the machine model of BBB4_Statement.v, following the
    BBB harness's native bookkeeping (carrino/BBB, README
    "Transition-level bookkeeping"):

    - an INSTRUCTION is a (state, read symbol) pair -- 8 per (4,2)
      machine; instruction [(q, a)] FIRES at configuration index [n]
      when the machine is in state [q] reading [a] after [n] steps
      (about to fire that table cell);
    - the machine quasihalts at transition level iff some instruction
      fires at least once but only finitely often; the score of an
      eventually-quiet instruction is its last firing index + 1, with
      the same step-numbering convention as the state level.

    Relationship to the state level (all proved below):

    - a state is visited at [n] iff one of its instructions fires at
      [n] ([visits_fires]);
    - state-level quasihalting implies transition-level quasihalting
      ([qh_st_tr]) -- the transition convention is WEAKER to satisfy;
    - transition-level never-quasihalting implies state-level
      never-quasihalting ([never_qh_tr_st]) -- the "never" side is a
      STRONGER obligation;
    - a quiet state yields a quiet instruction at an index at most the
      state's ([quiet_after_st_tr]), so per machine the transition
      score is >= the state score, and BBB_tr(4) >= BBB(4).

    Convention notes, mirroring the state level's:

    - a NEVER-FIRED ("silent") instruction does not witness
      quasihalting (the [FiredTr] conjunct) -- the harness's class N;
      there are many more of these than silent states (every undefined
      slot, and defined slots the run never reaches), and none can
      affect the value for the same reason silent states cannot;
    - HALTING machines quasihalt trivially at both levels (no
      configurations exist after the halt). *)

From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement.
Import ListNotations.

(** ** Instructions *)

Definition Instr : Set := (St * Sym)%type.

Definition all_Instr : list Instr :=
  [ (StA, S0); (StA, S1); (StB, S0); (StB, S1);
    (StC, S0); (StC, S1); (StD, S0); (StD, S1) ].

Lemma all_Instr_complete : forall t : Instr, In t all_Instr.
Proof. intros [q a]; destruct q, a; simpl; tauto. Qed.

Definition instr_eqb (x y : Instr) : bool :=
  st_eqb (fst x) (fst y) && sym_eqb (snd x) (snd y).

Lemma instr_eqb_spec : forall x y, instr_eqb x y = true <-> x = y.
Proof.
  intros [qa sa] [qb sb]; unfold instr_eqb; simpl; split; intro H.
  - apply andb_prop in H as [H1 H2].
    apply st_eqb_spec in H1; apply sym_eqb_spec in H2. congruence.
  - injection H as -> ->.
    apply andb_true_intro; split;
      [apply st_eqb_spec | apply sym_eqb_spec]; reflexivity.
Qed.

(** the instruction a configuration is about to fire *)
Definition instr_of (c : ExecState) : Instr := (fst c, t_head (snd c)).

(** ** Firing, quiet instructions, transition-level quasihalting *)

Definition FiresAt (tm : TM) (t : Instr) (n : nat) : Prop :=
  exists c, stepn tm n InitES = Some c /\ instr_of c = t.

Definition FiredTr (tm : TM) (t : Instr) : Prop := exists n, FiresAt tm t n.

Definition QuietFromTr (tm : TM) (t : Instr) (N : nat) : Prop :=
  forall n, N <= n -> ~ FiresAt tm t n.

Definition QuasiHaltsTr (tm : TM) : Prop :=
  exists t, FiredTr tm t /\ exists N, QuietFromTr tm t N.

Definition NeverQuasiHaltsTr (tm : TM) : Prop :=
  forall t, FiredTr tm t -> forall N, exists n, N <= n /\ FiresAt tm t n.

(** instruction [t]'s last fire is at configuration index [s]; its
    transition-level score is [S s]. *)
Definition QuietAfterTr (tm : TM) (t : Instr) (s : nat) : Prop :=
  FiresAt tm t s /\ forall n, s < n -> ~ FiresAt tm t n.

(** ** Bridges to the state level *)

Lemma visits_fires : forall tm q n,
  VisitsAt tm q n <-> exists a, FiresAt tm (q, a) n.
Proof.
  intros tm q n; split.
  - intros (c & Hc & Hq).
    exists (t_head (snd c)), c.
    split; [exact Hc|].
    unfold instr_of. rewrite Hq. reflexivity.
  - intros (a & c & Hc & Ht).
    exists c. split; [exact Hc|].
    unfold instr_of in Ht. injection Ht as Hq _. exact Hq.
Qed.

Lemma fires_visits : forall tm q a n,
  FiresAt tm (q, a) n -> VisitsAt tm q n.
Proof.
  intros tm q a n H. apply visits_fires. exists a. exact H.
Qed.

(** transition-level never-quasihalting is the stronger property *)
Lemma never_qh_tr_st : forall tm,
  NeverQuasiHaltsTr tm -> NeverQuasiHaltsSt tm.
Proof.
  intros tm H q Hv N.
  destruct Hv as (n0 & Hv0).
  apply visits_fires in Hv0.
  destruct Hv0 as (a & Hf0).
  destruct (H (q, a) (ex_intro _ n0 Hf0) N) as (n & Hn & Hf).
  exists n. split; [exact Hn|].
  exact (fires_visits tm q a n Hf).
Qed.

(** a quiet state yields a quiet instruction, no later *)
Lemma quiet_after_st_tr : forall tm q s,
  QuietAfter tm q s ->
  exists a s', s' <= s /\ QuietAfterTr tm (q, a) s'.
Proof.
  intros tm q s [Hvis Hq].
  apply visits_fires in Hvis.
  destruct Hvis as (a & Hf).
  exists a, s. split; [lia|].
  split; [exact Hf|].
  intros n Hn Hfn.
  exact (Hq n Hn (fires_visits tm q a n Hfn)).
Qed.

(** state-level quasihalting implies transition-level quasihalting *)
Lemma qh_st_tr : forall tm, QuasiHaltsSt tm -> QuasiHaltsTr tm.
Proof.
  intros tm (q & Hv & N & HN).
  destruct Hv as (n0 & Hv0).
  apply visits_fires in Hv0.
  destruct Hv0 as (a & Hf0).
  exists (q, a). split.
  - exists n0. exact Hf0.
  - exists N. intros n Hn Hf.
    exact (HN n Hn (fires_visits tm q a n Hf)).
Qed.

Lemma quiet_after_tr_qh : forall tm t s,
  QuietAfterTr tm t s -> QuasiHaltsTr tm.
Proof.
  intros tm t s [Hf Hq].
  exists t. split.
  - exists s. exact Hf.
  - exists (S s). intros n Hn. apply Hq. lia.
Qed.

(** never-quasihalting (transition level) implies non-halting, through
    the state level *)
Lemma never_qh_tr_nonhalt : forall tm, NeverQuasiHaltsTr tm -> NonHalt tm.
Proof.
  intros tm H. apply never_qh_nonhalt, never_qh_tr_st, H.
Qed.

Lemma never_qh_tr_not_qh : forall tm,
  NeverQuasiHaltsTr tm -> ~ QuasiHaltsTr tm.
Proof.
  intros tm H (t & Hf & N & HN).
  destruct (H t Hf N) as (n & Hn & Hfn).
  exact (HN n Hn Hfn).
Qed.
