(** Exact queue instrumentation for offline hint regeneration.
    Every popped node calls the fallback tracer once and retains its winner.
    Projection targets use [decider_tr_fallback], never the hinted decider.
    The production fast frontier and all walk budgets remain shared. *)
From Coq Require Import Arith Bool List PArith.
From BBB4.Census Require Import TNF_QH Decide.
From BBB4.CensusTr Require Import RunTr_WalkCompute.
From BBB4.CensusTr Require Import HintTagTr.
From BBB4HintTrace Require Import TraceRungsTr.
Import ListNotations.

(** These reference computations reproduce the pre-hint walk on the same
    [frontier_nodes_tr]. They are regeneration tools, not production units. *)
Definition q_suc_tr_fallback (q : SearchQueue) : SearchQueue :=
  SearchQueue_upds q decider_tr_fallback 13.

Fixpoint unit_ok_fallback (N i j : nat) (l : list TNF_Node) : bool :=
  match l with
  | [] => true
  | h :: t =>
      (if Nat.eqb (j mod N) i
       then queue_empty_b (Nat.iter ITER_TR q_suc_tr_fallback ([h], []))
       else true)
      && unit_ok_fallback N i (S j) t
  end.

Definition TraceQueueTr : Type := (SearchQueue * list TrHintRow)%type.

Definition trace_upd (qr : TraceQueueTr) : TraceQueueTr :=
  let '(q, rows) := qr in
  match q with
  | (h :: t, q2) =>
      let '(verdict, winner) := trace_decider (node_tm h) in
      let rows' :=
        match winner with
        | Some tag => (tm_enc (node_tm h), tag) :: rows
        | None => rows
        end in
      let q' :=
        match verdict with
        | R_Halt s i => (node_expand h s i ++ t, q2)
        | R_NeverQH | R_QH | R_Leaf | R_Deferred => (t, q2)
        | R_Unknown => (t, h :: q2)
        end in
      (q', rows')
  | _ => qr
  end.

Lemma trace_upd_projection : forall qr,
  fst (trace_upd qr) = SearchQueue_upd (fst qr) decider_tr_fallback.
Proof.
  intros [[front back] rows].
  destruct front as [|h t]; [reflexivity|].
  unfold trace_upd, SearchQueue_upd; cbn [fst].
  destruct (trace_decider (node_tm h)) as [verdict winner] eqn:E.
  pose proof (trace_decider_spec (node_tm h)) as H.
  rewrite E in H; cbn [fst] in H.
  rewrite <- H.
  destruct verdict; destruct winner; reflexivity.
Qed.

(** IMPORTANT: fuel 13 gives binary recursion with up to 8192 queue pops.
    It is not a loop of 13 pops. The original empty-front shortcut is kept,
    including the case where the deferred/back queue remains nonempty. *)
Fixpoint trace_upds (qr : TraceQueueTr) (n : nat) : TraceQueueTr :=
  match fst (fst qr) with
  | [] => qr
  | _ =>
      match n with
      | O => trace_upd qr
      | S n0 => trace_upds (trace_upds qr n0) n0
      end
  end.

Lemma trace_upds_projection : forall n qr,
  fst (trace_upds qr n) = SearchQueue_upds (fst qr) decider_tr_fallback n.
Proof.
  induction n as [|n IH]; intros [[front back] rows];
    destruct front as [|h t].
  - reflexivity.
  - change (fst (trace_upd ((h :: t, back), rows)) =
            SearchQueue_upd (h :: t, back) decider_tr_fallback).
    apply trace_upd_projection.
  - reflexivity.
  - change (fst (trace_upds (trace_upds ((h :: t, back), rows) n) n) =
            SearchQueue_upds
              (SearchQueue_upds (h :: t, back) decider_tr_fallback n) decider_tr_fallback n).
    rewrite IH, IH. reflexivity.
Qed.

Definition trace_q_suc (qr : TraceQueueTr) : TraceQueueTr :=
  trace_upds qr 13.

Lemma trace_q_suc_projection : forall qr,
  fst (trace_q_suc qr) = q_suc_tr_fallback (fst qr).
Proof. intro qr; apply trace_upds_projection. Qed.

Lemma trace_rounds_projection : forall n qr,
  fst (Nat.iter n trace_q_suc qr) = Nat.iter n q_suc_tr_fallback (fst qr).
Proof.
  induction n as [|n IH]; intro qr; [reflexivity|].
  change (fst (trace_q_suc (Nat.iter n trace_q_suc qr)) =
          q_suc_tr_fallback (Nat.iter n q_suc_tr_fallback (fst qr))).
  rewrite trace_q_suc_projection, IH. reflexivity.
Qed.

Definition trace_subtree (h : TNF_Node) (rows : list TrHintRow)
  : bool * list TrHintRow :=
  let '(q, rows') := Nat.iter ITER_TR trace_q_suc (([h], []), rows) in
  (queue_empty_b q, rows').

Lemma trace_subtree_projection : forall h rows,
  fst (trace_subtree h rows) =
  queue_empty_b (Nat.iter ITER_TR q_suc_tr_fallback ([h], [])).
Proof.
  intros h rows. unfold trace_subtree.
  destruct (Nat.iter ITER_TR trace_q_suc (([h], []), rows))
    as [q rows'] eqn:E; cbn [fst].
  pose proof (trace_rounds_projection ITER_TR (([h], []), rows)) as H.
  rewrite E in H; cbn [fst] in H. now rewrite H.
Qed.

(** Match the Boolean short circuit of unit_ok_fallback. A failed subtree is retained
    only for diagnostics; the offline parser rejects every failed packet. *)
Fixpoint trace_unit_acc (N i j : nat) (l : list TNF_Node)
  (rows : list TrHintRow) : bool * list TrHintRow :=
  match l with
  | [] => (true, rows)
  | h :: t =>
      if Nat.eqb (j mod N) i then
        let '(ok, rows') := trace_subtree h rows in
        if ok then trace_unit_acc N i (S j) t rows' else (false, rows')
      else trace_unit_acc N i (S j) t rows
  end.

Lemma trace_unit_acc_projection : forall N i l j rows,
  fst (trace_unit_acc N i j l rows) = unit_ok_fallback N i j l.
Proof.
  intros N i l; induction l as [|h t IH]; intros j rows;
    [reflexivity|].
  cbn [trace_unit_acc unit_ok_fallback].
  destruct (Nat.eqb (j mod N) i) eqn:Eassign.
  - destruct (trace_subtree h rows) as [ok rows'] eqn:Esubtree.
    pose proof (trace_subtree_projection h rows) as H.
    rewrite Esubtree in H; cbn [fst] in H. rewrite <- H.
    destruct ok; cbn [fst andb]; [apply IH|reflexivity].
  - cbn [andb]. apply IH.
Qed.

Definition trace_unit (N i j : nat) (l : list TNF_Node)
  : bool * list TrHintRow := trace_unit_acc N i j l [].

Lemma trace_unit_projection : forall N i j l,
  fst (trace_unit N i j l) = unit_ok_fallback N i j l.
Proof. intros; apply trace_unit_acc_projection. Qed.

(** Typed wire format. Dedicated constructor chains avoid confusing a key
    with a frontier index, count, or tag. Code 38 marks an invalid tag and
    is rejected by the parser. There is no acceptance of offline verdicts
    by production proof code: these rows are only advisory hints. *)
Inductive TrWireRowsV1 : Type :=
| TrRowsNilV1
| TrRowsConsV1 (key : positive) (tag : nat) (tail : TrWireRowsV1).

Fixpoint wire_rows_v1 (rows : list TrHintRow) : TrWireRowsV1 :=
  match rows with
  | [] => TrRowsNilV1
  | (key, winner) :: tail =>
      TrRowsConsV1 key (tr_winner_code winner) (wire_rows_v1 tail)
  end.

Inductive TrWireIndicesV1 : Type :=
| TrIndicesNilV1
| TrIndicesConsV1 (index : nat) (tail : TrWireIndicesV1).

Fixpoint wire_indices_v1 (indices : list nat) : TrWireIndicesV1 :=
  match indices with
  | [] => TrIndicesNilV1
  | index :: tail => TrIndicesConsV1 index (wire_indices_v1 tail)
  end.

Inductive TraceInventoryPacketV1 : Type :=
| TrInventoryV1 (units unit frontier_count levels rounds pop_exponent : nat)
    (indices : TrWireIndicesV1).

Definition trace_inventory_packet (N i : nat) : TraceInventoryPacketV1 :=
  TrInventoryV1 N i (length frontier_nodes_tr) FRONTIER_LEVELS_TR ITER_TR 13
    (wire_indices_v1
      (filter (fun j => Nat.eqb (j mod N) i)
        (seq 0 (length frontier_nodes_tr)))).

Inductive TraceShardPacketV1 : Type :=
| TrShardV1 (units unit index frontier_count : nat)
    (present complete : bool) (row_count : nat) (rows : TrWireRowsV1).

Definition trace_shard_packet (N i j : nat) : TraceShardPacketV1 :=
  if Nat.eqb (j mod N) i then
    match nth_error frontier_nodes_tr j with
    | Some h =>
        let '(complete, rows) := trace_subtree h [] in
        TrShardV1 N i j (length frontier_nodes_tr)
          true complete (length rows) (wire_rows_v1 rows)
    | None => TrShardV1 N i j (length frontier_nodes_tr)
                false false 0 TrRowsNilV1
    end
  else TrShardV1 N i j (length frontier_nodes_tr)
         false false 0 TrRowsNilV1.

(** Kernel assumption audits for the fallback queue projection. *)
Print Assumptions trace_upd_projection.
Print Assumptions trace_upds_projection.
Print Assumptions trace_q_suc_projection.
Print Assumptions trace_rounds_projection.
Print Assumptions trace_subtree_projection.
Print Assumptions trace_unit_acc_projection.
Print Assumptions trace_unit_projection.
