(** * RRNQ_0RB0RD_1RC____1RD1LC_0LC1RA: machine 0RB0RD_1RC---_1RD1LC_0LC1RA,
    boarded by RE-ROOT off a boarded core row.

    This row was a SHADOW (`tools/closeout/shadow_rows.tsv`) of the core row
    `1RB---_1RC1LB_0LB1RD_0RA0RC`: its first transition writes the blank, so
    it runs an all-blank prefix of length 1 and thereafter IS its re-root
    [TM_swap StA StB] started fresh, and that re-root is the core row with
    two non-start states relabelled.  A shadow only resolves through the
    [skipped] disjunct while its core row is still DEFERRED, so when the core
    row boarded (`NLAP_1RB____1RC1LB_0LB1RD_0RA0RC.v`) this row fell out of
    the shadow table and into the core list.  It boards off the same proof:

      TM_swap StC StD (TM_swap StB StC (TM_swap StA StB tm)) = the core row

    [Census/Reroot.neverqh_reroot] carries [NeverQuasiHaltsSt] back across the
    blank prefix, and the two remaining swaps move no start state, so they are
    a pure relabelling of the trace.

    ON THE TWO LOCAL LEMMAS.  [neverqh_swap] below (never-quasihalting is
    invariant under relabelling two NON-start states) is general and belongs
    beside [Reroot.neverqh_reroot]; it is kept local here only because
    [Census/Reroot.v] sits under the whole census and closeout, and moving a
    lemma into it costs a full rebuild of both.  It is the same argument as
    [Reroot.visitsat_reroot], with [es_swap_init] in place of the prefix
    identity.

    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift] and
    [Census/Reroot]). *)
From Coq Require Import Arith Lia Bool List.
From Coq Require Import FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH Reroot.
From BBB4.Machines.Counters Require Import NLAP_1RB____1RC1LB_0LB1RD_0RA0RC.
Import ListNotations.

Definition mk_0RB0RD_1RC____1RD1LC_0LC1RA (w : Sym) (d : Dir) (n : St)
  : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB0RD_1RC____1RD1LC_0LC1RA.

(** 0RB0RD_1RC---_1RD1LC_0LC1RA *)
Definition tm_0RB0RD_1RC____1RD1LC_0LC1RA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S0 DR StD
  | StB, S0 => mk S1 DR StC | StB, S1 => None
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S1 DL StC
  | StD, S0 => mk S0 DL StC | StD, S1 => mk S1 DR StA end.
Local Notation tm := tm_0RB0RD_1RC____1RD1LC_0LC1RA.

(** Its re-root [TM_swap StA StB tm], written out so every obligation about
    it is a [vm_compute] against a literal. *)
Definition rr_0RB0RD_1RC____1RD1LC_0LC1RA : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StC | StA, S1 => None
  | StB, S0 => mk S0 DR StA | StB, S1 => mk S0 DR StD
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S1 DL StC
  | StD, S0 => mk S0 DL StC | StD, S1 => mk S1 DR StB end.
Local Notation rr := rr_0RB0RD_1RC____1RD1LC_0LC1RA.

(** ** Never-quasihalting is invariant under relabelling two non-start states *)

Lemma visitsat_swap_0RB0RD_1RC____1RD1LC_0LC1RA : forall u v m q n,
  u <> StA -> v <> StA ->
  (VisitsAt (TM_swap u v m) q n <-> VisitsAt m (St_swap u v q) n).
Proof.
  intros u v m q n Hu Hv. unfold VisitsAt.
  rewrite stepn_swap, (es_swap_init u v Hu Hv).
  destruct (stepn m n InitES) as [c0|]; cbn [option_map].
  - split.
    + intros (c & Hc & Hq). injection Hc as <-.
      exists c0. split; [reflexivity|].
      unfold es_swap in Hq; cbn [fst] in Hq.
      rewrite <- Hq, St_swap_swap. reflexivity.
    + intros (c & Hc & Hq). injection Hc as <-.
      eexists. split; [reflexivity|].
      unfold es_swap; cbn [fst]. rewrite Hq, St_swap_swap. reflexivity.
  - split; intros (c & Hc & _); discriminate.
Qed.

Lemma neverqh_swap_0RB0RD_1RC____1RD1LC_0LC1RA : forall u v m,
  u <> StA -> v <> StA ->
  NeverQuasiHaltsSt m -> NeverQuasiHaltsSt (TM_swap u v m).
Proof.
  intros u v m Hu Hv H q Hvis N.
  assert (Hv' : Visited m (St_swap u v q)).
  { destruct Hvis as (n & Hn). exists n.
    exact (proj1 (visitsat_swap_0RB0RD_1RC____1RD1LC_0LC1RA u v m q n Hu Hv) Hn). }
  destruct (H (St_swap u v q) Hv' N) as (n & Hn & Hvn).
  exists n. split; [exact Hn|].
  exact (proj2 (visitsat_swap_0RB0RD_1RC____1RD1LC_0LC1RA u v m q n Hu Hv) Hvn).
Qed.

(** ** The re-root is the core row, twice relabelled *)

Lemma rr_eq_0RB0RD_1RC____1RD1LC_0LC1RA : TM_swap StA StB tm = rr.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Lemma rr_core_0RB0RD_1RC____1RD1LC_0LC1RA :
  rr = TM_swap StB StC (TM_swap StC StD tm_1RB____1RC1LB_0LB1RD_0RA0RC).
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Lemma nqh_rr_0RB0RD_1RC____1RD1LC_0LC1RA : NeverQuasiHaltsSt rr.
Proof.
  rewrite rr_core_0RB0RD_1RC____1RD1LC_0LC1RA.
  apply neverqh_swap_0RB0RD_1RC____1RD1LC_0LC1RA; [discriminate | discriminate |].
  apply neverqh_swap_0RB0RD_1RC____1RD1LC_0LC1RA; [discriminate | discriminate |].
  exact nqh_1RB____1RC1LB_0LB1RD_0RA0RC.
Qed.

(** ** The re-root visits every state

    [Reroot.visited_prefix] only reaches states of the blank prefix, and [rr]
    writes on its first step, so the witnesses are ordinary short runs read
    off [csteps] instead. *)

Lemma visited_c_0RB0RD_1RC____1RD1LC_0LC1RA : forall m n q,
  match csteps m n c0 with Some c => st_eqb (fst c) q | None => false end = true ->
  Visited m q.
Proof.
  intros m n q H. destruct (csteps m n c0) as [c|] eqn:E; [|discriminate].
  apply st_eqb_spec in H.
  exists n, (lift c). split.
  - rewrite <- lift_c0. apply csteps_lift. exact E.
  - rewrite lift_state. exact H.
Qed.

Lemma vis_rr_0RB0RD_1RC____1RD1LC_0LC1RA : forall q, Visited rr q.
Proof.
  intro q. destruct q.
  - apply (visited_c_0RB0RD_1RC____1RD1LC_0LC1RA rr 0 StA); vm_compute; reflexivity.
  - apply (visited_c_0RB0RD_1RC____1RD1LC_0LC1RA rr 7 StB); vm_compute; reflexivity.
  - apply (visited_c_0RB0RD_1RC____1RD1LC_0LC1RA rr 1 StC); vm_compute; reflexivity.
  - apply (visited_c_0RB0RD_1RC____1RD1LC_0LC1RA rr 2 StD); vm_compute; reflexivity.
Qed.

(** ** The closer *)

Theorem nqh_0RB0RD_1RC____1RD1LC_0LC1RA : NeverQuasiHaltsSt tm.
Proof.
  apply (neverqh_reroot tm StB 1).
  - apply prefix_ok_sound; vm_compute; reflexivity.
  - rewrite rr_eq_0RB0RD_1RC____1RD1LC_0LC1RA.
    exact nqh_rr_0RB0RD_1RC____1RD1LC_0LC1RA.
  - rewrite rr_eq_0RB0RD_1RC____1RD1LC_0LC1RA.
    exact vis_rr_0RB0RD_1RC____1RD1LC_0LC1RA.
Qed.

Theorem nonhalt_0RB0RD_1RC____1RD1LC_0LC1RA : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_0RB0RD_1RC____1RD1LC_0LC1RA. Qed.
