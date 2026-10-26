(** Instruction quasihalting, using the same conventions as SmallBB. *)
From Coq Require Import Arith Lia List.
From BBB24 Require Import Statement.
Import ListNotations.

(** ** Instructions *)

Definition Instr : Set := (St * Sym)%type.

Definition all_Instr : list Instr :=
  [ (StA, S0); (StA, S1); (StA, S2); (StA, S3);
    (StB, S0); (StB, S1); (StB, S2); (StB,S3) ].

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
