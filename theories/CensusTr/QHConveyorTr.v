(** * QHConveyorTr: the wrapped n-gram QHBound rungs as standalone
    checkers for the offline QH-side conveyor
    (tools/censustr/gen_provtr_qh.py, stages ProvTr_QH_NN).

    The in-walk tier (DecideTr [try_qhbtr]) pins the quiet
    instructions at the last fires it finds within 16 x 1024 steps and
    tries the wrapped closure at t <= 1024.  The deferred quiet
    machines mostly quiet later than that; the conveyor supplies the
    exact pins from a long scan and calls the same checkers at a [t]
    just past the last quiet fire.  [qh_plain_at] is
    [WrapTr.ngram_check_qhboundtr] itself; [qh_lex_at] is the lex-gated
    rung of DecideTr [try_qhbtr_lex_at] with the pins and the fuel
    passed explicitly (and without the in-walk [S t <=? B] guard: the
    stage lemma checks [S t <= B_tr] separately). *)

From Coq Require Import Arith Bool List NArith PArith.
From Coq Require Import FSets.FMapPositive MSets.MSetPositive.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape Mirror.
From BBB4.Checkers Require Import NGram NGramTr WrapTr TCyclerQHTr.
From BBB4.Census Require Import RankSearch.
From BBB4.CensusTr Require Import TNF_QHTr DecideTr.
Import ListNotations.

Definition qh_plain_at (tm : TM) (pins : list (Instr * nat))
    (n t fuel rounds : nat) : bool :=
  ngram_check_qhboundtr tm pins n t fuel rounds.

Definition qh_lex_at (tm : TM) (pins : list (Instr * nat))
    (n t fuel rounds : nat) : bool :=
  match csteps tm t c0 with
  | None => false
  | Some ct =>
      let tmw := tm_wrap_trs tm (map fst pins) in
      let '(q1, (l, h, r)) := ct in
      let lset0 := gadds (ng_seed_side n l) gempty in
      let rset0 := gadds (ng_seed_side n r) gempty in
      let a0 := ng_start n ct in
      let '(lset, rset) := ng_grow tmw a0 fuel rounds lset0 rset0 in
      let closure :=
        ng_explore tmw lset rset fuel [] PositiveSet.empty [a0] in
      ngram_check_qhboundtr_lex tm pins n t fuel rounds
        (fun tg' => rank_procedure_tr tmw lset rset closure tg')
  end.

Theorem qh_plain_at_sound : forall tm pins n t fuel rounds,
  qh_plain_at tm pins n t fuel rounds = true ->
  NonHalt tm
  /\ (forall tg' s', QuietAfterTr tm tg' s' -> S s' <= S t)
  /\ QuasiHaltsTr tm.
Proof.
  intros tm pins n t fuel rounds H.
  exact (ngram_check_qhboundtr_sound tm pins n t fuel rounds H).
Qed.

Theorem qh_lex_at_sound : forall tm pins n t fuel rounds,
  qh_lex_at tm pins n t fuel rounds = true ->
  NonHalt tm
  /\ (forall tg' s', QuietAfterTr tm tg' s' -> S s' <= S t)
  /\ QuasiHaltsTr tm.
Proof.
  intros tm pins n t fuel rounds H.
  unfold qh_lex_at in H.
  destruct (csteps tm t c0) as [ct|] eqn:E; [|discriminate].
  destruct ct as [q1 [[l h] r]].
  destruct (ng_grow _ _ _ _ _ _) as [lset rset].
  exact (ngram_check_qhboundtr_lex_sound _ _ _ _ _ _ _ H).
Qed.

(** the stage lemmas' bound step, with the literal B_tr = 32779478
    (RunTr.v defines [B_tr] and imports the stages, so the stages
    cannot name it) *)
Lemma qh_bound_of : forall (B : nat) tm t,
  (S t <=? B) = true ->
  (forall tg' s', QuietAfterTr tm tg' s' -> S s' <= S t) ->
  QHBoundTr B tm.
Proof.
  intros B tm t Hle Hb tg s Hq.
  apply Nat.leb_le in Hle.
  exact (Nat.le_trans _ _ _ (Hb tg s Hq) Hle).
Qed.

(** the same for a checker whose bound is a plain [n] (the
    translated-cycler anchor of Checkers/TCyclerQHTr) *)
Lemma qh_bound_of_le : forall (B : nat) tm n,
  (n <=? B) = true ->
  (forall tg' s', QuietAfterTr tm tg' s' -> S s' <= n) ->
  QHBoundTr B tm.
Proof.
  intros B tm n Hle Hb tg s Hq.
  apply Nat.leb_le in Hle.
  exact (Nat.le_trans _ _ _ (Hb tg s Hq) Hle).
Qed.

(** ** Stage lemmas: one [apply] and two [vm_cast_no_check] goals

    The generated stages close each machine with
    [apply (qh_*_stage tm ... B); all: vm_cast_no_check (eq_refl true)]:
    the checker verdict and the bound check are kernel-evaluated by the
    VM.  (Destructuring the soundness lemma on a [vm_cast_no_check]
    term instead makes the elaborator re-reduce the checker with the
    default machine, ~300x slower than the probe.) *)
Lemma qh_plain_stage : forall tm pins n t fuel rounds B,
  qh_plain_at tm pins n t fuel rounds = true ->
  (S t <=? B) = true ->
  NonHalt tm /\ QHBoundTr B tm /\ QuasiHaltsTr tm.
Proof.
  intros tm pins n t fuel rounds B H Hle.
  destruct (qh_plain_at_sound tm pins n t fuel rounds H) as [Hnh [Hb Hq]].
  split; [exact Hnh|]. split; [exact (qh_bound_of B tm t Hle Hb) | exact Hq].
Qed.

Lemma qh_lex_stage : forall tm pins n t fuel rounds B,
  qh_lex_at tm pins n t fuel rounds = true ->
  (S t <=? B) = true ->
  NonHalt tm /\ QHBoundTr B tm /\ QuasiHaltsTr tm.
Proof.
  intros tm pins n t fuel rounds B H Hle.
  destruct (qh_lex_at_sound tm pins n t fuel rounds H) as [Hnh [Hb Hq]].
  split; [exact Hnh|]. split; [exact (qh_bound_of B tm t Hle Hb) | exact Hq].
Qed.

Lemma tcycler_qh_stage : forall tm n1 P W B,
  tcycler_check_qhboundtr tm n1 P W = true ->
  (n1 <=? B) = true ->
  NonHalt tm /\ QHBoundTr B tm /\ QuasiHaltsTr tm.
Proof.
  intros tm n1 P W B H Hle.
  destruct (tcycler_check_qhboundtr_sound tm n1 P W H) as [Hnh [Hb Hq]].
  split; [exact Hnh|]. split; [exact (qh_bound_of_le B tm n1 Hle Hb) | exact Hq].
Qed.

Lemma tcycler_qh_stage_L : forall tm n1 P W B,
  tcycler_check_qhboundtr (mirror_tm tm) n1 P W = true ->
  (n1 <=? B) = true ->
  NonHalt tm /\ QHBoundTr B tm /\ QuasiHaltsTr tm.
Proof.
  intros tm n1 P W B H Hle.
  destruct (tcycler_check_qhboundtr_sound_L tm n1 P W H) as [Hnh [Hb Hq]].
  split; [exact Hnh|]. split; [exact (qh_bound_of_le B tm n1 Hle Hb) | exact Hq].
Qed.
