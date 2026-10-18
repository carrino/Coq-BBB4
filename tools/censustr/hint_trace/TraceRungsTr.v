(** Exact instrumentation of the unchanged instruction-census fallback.
    Each checker is called once at its existing branch; tracing does not run
    a decider first and replay it to discover the winning rung.

    The projection is literal verdict equality to [decider_tr_fallback] for
    every machine. It makes no equality claim about the public hinted
    [decider_tr]. The source manifest pins these fixed ladder parameters. *)
From Coq Require Import Arith Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers Require Import NGramTr.
From BBB4.Census Require Import TNF_QH Decide.
From BBB4.CensusTr Require Import DecideTr RepWLTr RunTr_Compute
  ProvTr_Data ProvQHTr_Data.
From BBB4.CensusTr Require Import HintTagTr.
Import ListNotations.
Open Scope nat_scope.

Definition TrBoolTrace : Type := (bool * option TrWinner)%type.
Definition TrDecisionTrace : Type := (QHResult * option TrWinner)%type.

(** Tail recursion follows [anyb]'s short-circuit exactly. The index is
    incremented only after failure; no list of candidate results is built. *)
Fixpoint trace_anyb {A : Type} (check : A -> bool)
    (tag : nat -> TrWinner) (index : nat) (rungs : list A) : TrBoolTrace :=
  match rungs with
  | [] => (false, None)
  | rung :: rest =>
      if check rung then (true, Some (tag index))
      else trace_anyb check tag (S index) rest
  end.

Lemma trace_anyb_spec : forall (A : Type) (check : A -> bool) tag index rungs,
  fst (trace_anyb check tag index rungs) = anyb check rungs.
Proof.
  intros A check tag index rungs. revert index.
  induction rungs as [|rung rest IH]; intros index.
  - reflexivity.
  - cbn [trace_anyb anyb]. destruct (check rung); [reflexivity|apply IH].
Qed.

(** Projection lemmas expose only results; tracing remains strict in each
    [let] binding and shares its result between its boolean and tag. *)
Lemma trace_fst_if : forall (A C : Type) (b : bool) (x y : A * C),
  fst (if b then x else y) = if b then fst x else fst y.
Proof. intros A C b x y. destruct b; reflexivity. Qed.

Lemma try_ngram_tr_anyb : forall fuel rounds rungs tm,
  try_ngram_tr fuel rounds rungs tm =
  if anyb (fun '(n,t) => ngram_check_neverqhtr tm n t fuel rounds) rungs
  then R_NeverQH else R_Unknown.
Proof.
  intros fuel rounds rungs. induction rungs as [|[n t] rest IH]; intros tm.
  - reflexivity.
  - cbn [try_ngram_tr anyb].
    destruct (ngram_check_neverqhtr tm n t fuel rounds); [reflexivity|apply IH].
Qed.

Lemma try_rank_tr_anyb : forall fuel rounds rungs tm,
  try_rank_tr fuel rounds rungs tm =
  if anyb (fun '(n,t) => rank_tier_tr tm n t fuel rounds) rungs
  then R_NeverQH else R_Unknown.
Proof.
  intros fuel rounds rungs. induction rungs as [|[n t] rest IH]; intros tm.
  - reflexivity.
  - cbn [try_rank_tr anyb].
    destruct (rank_tier_tr tm n t fuel rounds); [reflexivity|apply IH].
Qed.

Definition trace_ngram_tr (tm : TM) : TrBoolTrace :=
  trace_anyb (fun '(n,t) => ngram_check_neverqhtr tm n t 200000 512)
    WNGram 0 ng_rungs_tr.

Definition trace_rank_tr (tm : TM) : TrBoolTrace :=
  trace_anyb (fun '(n,t) => rank_tier_tr tm n t 200000 512)
    WRank 0 rank_rungs_tr.

Definition trace_qhbtr_with_lf (horizon : TrHorizon) (tm : TM)
    (lf : list (Instr * nat)) : TrBoolTrace :=
  if existsb (fun p => snd p <? qhb_tmax_tr qhb_rungs_tr) lf then
    let plain := trace_anyb
      (try_qhbtr_at B_search_tr 200000 512 tm lf)
      (WQHPlain horizon) 0 qhb_rungs_tr in
    if fst plain then plain else
    let lex := trace_anyb
      (try_qhbtr_lex_at B_search_tr 200000 512 tm lf)
      (WQHLex horizon) 0 qhb_lex_rungs_tr in
    if fst lex then lex else
    trace_anyb (try_rw_qhbtr_at B_search_tr rw_fuel_tr rw_cut_tr tm lf)
      (WQHRW horizon) 0 rw_qhb_rungs_tr
  else (false, None).

Lemma trace_qhbtr_with_lf_spec : forall horizon tm lf,
  fst (trace_qhbtr_with_lf horizon tm lf) =
  try_qhbtr_with_lf B_search_tr 200000 512 qhb_rungs_tr
    qhb_lex_rungs_tr rw_qhb_rungs_tr rw_fuel_tr rw_cut_tr tm lf.
Proof.
  intros horizon tm lf.
  unfold trace_qhbtr_with_lf, try_qhbtr_with_lf. cbn zeta.
  repeat rewrite trace_fst_if. repeat rewrite trace_anyb_spec.
  destruct (existsb (fun p => snd p <? qhb_tmax_tr qhb_rungs_tr) lf);
    [|reflexivity].
  destruct (anyb (try_qhbtr_at B_search_tr 200000 512 tm lf) qhb_rungs_tr);
    [reflexivity|].
  destruct (anyb (try_qhbtr_lex_at B_search_tr 200000 512 tm lf)
    qhb_lex_rungs_tr); reflexivity.
Qed.

(** The short FireScan is shared with the resumed full scan. A negative
    short candidate guard stops without resuming, exactly as production.
    A positive guard with failed short rungs resumes 12*tmax further steps.
    The horizon tag records the actual candidate list used by the winner. *)
Definition trace_qhbtr (tm : TM) : TrBoolTrace :=
  let prefix := qh_fire_scan_prefix qhb_rungs_tr tm in
  let lf := fire_candidates (scan_times prefix) in
  let short := trace_qhbtr_with_lf TrShort tm lf in
  if fst short then short
  else if existsb (fun p => snd p <? qhb_tmax_tr qhb_rungs_tr) lf then
    trace_qhbtr_with_lf TrFull tm
      (fire_candidates (scan_times
        (resume_last_fires tm (12 * qhb_tmax_tr qhb_rungs_tr) prefix)))
  else (false, None).

Lemma trace_qhbtr_spec : forall tm,
  fst (trace_qhbtr tm) =
  try_qhbtr B_search_tr 200000 512 qhb_rungs_tr qhb_lex_rungs_tr
    rw_qhb_rungs_tr rw_fuel_tr rw_cut_tr tm.
Proof.
  intros tm. unfold trace_qhbtr, try_qhbtr. cbn zeta.
  repeat rewrite trace_fst_if. repeat rewrite trace_qhbtr_with_lf_spec.
  destruct (try_qhbtr_with_lf B_search_tr 200000 512 qhb_rungs_tr
    qhb_lex_rungs_tr rw_qhb_rungs_tr rw_fuel_tr rw_cut_tr tm
    (fire_candidates (scan_times (qh_fire_scan_prefix qhb_rungs_tr tm))));
    reflexivity.
Qed.

Definition trace_rw_tr (tm : TM) : TrBoolTrace :=
  trace_anyb (fun '(L,T,t) => rw_tier_tr tm L T t rw_fuel_tr rw_cut_tr)
    WRW 0 rw_rungs_tr.

Lemma trace_rw_tr_spec : forall tm,
  fst (trace_rw_tr tm) = try_rw_tr rw_rungs_tr rw_fuel_tr rw_cut_tr tm.
Proof. intros tm. unfold trace_rw_tr, try_rw_tr. apply trace_anyb_spec. Qed.

(** Lookup, halting, loop, deferred, and unknown outcomes never emit a
    hint. The two loop scans remain ahead of every dynamic tagged rung. *)
Definition trace_decide_easy_tr (pm qm dm : DeferredMap) (tm : TM)
    : TrDecisionTrace :=
  match find_halt tm 130 0 c0 with
  | Some (n,s,i) =>
      (if S n <=? B_search_tr then R_Halt s i else R_Unknown, None)
  | None =>
      if deferred_lookup pm tm then (R_NeverQH, None) else
      if deferred_lookup qm tm then (R_QH, None) else
      if deferred_lookup dm tm then (R_Deferred, None) else
      if scan_loops B_search_tr tm 130 then (R_Leaf, None) else
      if scan_loops B_search_tr tm 512 then (R_Leaf, None) else
      let ng := trace_ngram_tr tm in
      if fst ng then (R_NeverQH, snd ng) else
      let rank := trace_rank_tr tm in
      if fst rank then (R_NeverQH, snd rank) else
      let qh := trace_qhbtr tm in
      if fst qh then (R_QH, snd qh) else
      let rw := trace_rw_tr tm in
      if fst rw then (R_NeverQH, snd rw) else (R_Unknown, None)
  end.

Lemma trace_decide_easy_tr_spec : forall pm qm dm tm,
  fst (trace_decide_easy_tr pm qm dm tm) =
  decide_easy_tr B_search_tr 130 512 200000 512 ng_rungs_tr rank_rungs_tr
    qhb_rungs_tr qhb_lex_rungs_tr rw_qhb_rungs_tr
    rw_rungs_tr rw_fuel_tr rw_cut_tr pm qm dm tm.
Proof.
  intros pm qm dm tm. unfold trace_decide_easy_tr, decide_easy_tr.
  destruct (find_halt tm 130 0 c0) as [[[n s] i]|]; [reflexivity|].
  cbn zeta. repeat rewrite trace_fst_if.
  unfold trace_ngram_tr, trace_rank_tr.
  repeat rewrite trace_anyb_spec.
  rewrite trace_qhbtr_spec, trace_rw_tr_spec.
  rewrite try_ngram_tr_anyb, try_rank_tr_anyb.
  destruct (deferred_lookup pm tm); [reflexivity|].
  destruct (deferred_lookup qm tm); [reflexivity|].
  destruct (deferred_lookup dm tm); [reflexivity|].
  destruct (scan_loops B_search_tr tm 130); [reflexivity|].
  destruct (scan_loops B_search_tr tm 512); [reflexivity|].
  destruct (anyb (fun '(n,t) => ngram_check_neverqhtr tm n t 200000 512)
    ng_rungs_tr); [reflexivity|].
  destruct (anyb (fun '(n,t) => rank_tier_tr tm n t 200000 512)
    rank_rungs_tr); reflexivity.
Qed.

(** Keep the map-building partial application outside the machine lambda,
    matching [decider_tr_fallback], so native evaluation memoizes its three maps. *)
Definition trace_decider : TM -> TrDecisionTrace :=
  trace_decide_easy_tr (dmap_of prov_tr_data) (dmap_of provqh_tr_data)
    (dmap_of D_tr).

Theorem trace_decider_spec : forall tm,
  fst (trace_decider tm) = decider_tr_fallback tm.
Proof. intros tm. unfold trace_decider, decider_tr_fallback. apply trace_decide_easy_tr_spec. Qed.

Theorem trace_decider_projection : forall tm,
  fst (trace_decider tm) = decider_tr_fallback tm.
Proof. apply trace_decider_spec. Qed.

(** Kernel assumption audits for the exact projection. *)
Print Assumptions trace_anyb_spec.
Print Assumptions trace_qhbtr_spec.
Print Assumptions trace_decider_spec.
