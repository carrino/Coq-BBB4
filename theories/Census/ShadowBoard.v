(** * ShadowBoard: a shadow's whole argument as ONE lemma

    A SHADOW is a frozen row whose start transition writes the blank, so it
    runs an all-blank prefix and thereafter IS its re-root [TM_swap StA q*]
    started fresh -- and that re-root is some CORE row with non-start states
    relabelled and possibly mirrored.  Both transports are already proved in
    general ([Reroot.neverqh_reroot] across the prefix, [RerootSwap]'s
    [neverqh_swap] / [neverqh_mirror] across the relabelling), so a shadow
    board carries NO new mathematics.

    WHAT THIS FILE IS FOR.  It carries no new mathematics either -- it moves
    the last three per-machine obligations out of the generated boards and
    states them ONCE, as booleans the kernel evaluates:

      - the blank prefix.  [Reroot.prefix_ok] was already boolean.
      - the table identity.  A board used to prove
        [TM_swap StA q* tm = rr] by [functional_extensionality] over an
        eight-way [destruct], against a SECOND literal table it also had to
        carry.  [tm_eqb] decides it instead, and [tm_eqb_spec] is where the
        funext goes -- once, here.
      - [neverqh_reroot]'s [forall q, Visited] side condition.  A board used
        to carry four [visited_csteps] witnesses at four hand-picked step
        indices, which is the part a generator gets wrong quietly.
        [all_visited_b] searches for them.

    So a generated shadow board is now the sentence you would say out loud:
    *the first t steps write only blanks, and what is left is that machine
    over there, which is proved.*  Three [vm_compute]s and the core theorem:

<<
      Theorem nqh_SPEC : NeverQuasiHaltsSt tm.
      Proof.
        apply (shadow_nqh tm (mirror_tm CORE) StB 1 5).
        - vm_compute; reflexivity.        (* the prefix is all blanks   *)
        - vm_compute; reflexivity.        (* ...and then it IS CORE     *)
        - vm_compute; reflexivity.        (* CORE visits every state    *)
        - apply neverqh_mirror; exact nqh_CORE.
      Qed.
>>

    Nothing here is trusted: a wrong re-root state, a wrong prefix length, a
    wrong op chain or a short fuel all make the [vm_compute] fail to close,
    so the file does not compile.  It cannot yield a false theorem.

    Axiom footprint: [functional_extensionality_dep], via [CTape.lift] and
    [tm_eqb_spec].  Nothing new. *)
From Coq Require Import Arith Bool List.
From Coq Require Import FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From BBB4.Census Require Import TNF_QH Reroot RerootSwap.
Import ListNotations.

(** ** Deciding equality of two transition tables

    [TM] is a function type, so equating two of them is where a generated
    board would otherwise have to state [functional_extensionality] itself.
    Eight cells decide it; the extensionality is discharged once, below. *)

Definition dir_eqb (a b : Dir) : bool :=
  match a, b with DL, DL | DR, DR => true | _, _ => false end.

Lemma dir_eqb_spec : forall a b, dir_eqb a b = true -> a = b.
Proof. intros [] []; simpl; congruence. Qed.

Definition trans_eqb (a b : option Trans) : bool :=
  match a, b with
  | None, None => true
  | Some t1, Some t2 =>
      sym_eqb (t_write t1) (t_write t2)
      && dir_eqb (t_dir t1) (t_dir t2)
      && st_eqb (t_next t1) (t_next t2)
  | _, _ => false
  end.

Lemma trans_eqb_spec : forall a b, trans_eqb a b = true -> a = b.
Proof.
  intros [[w1 d1 n1]|] [[w2 d2 n2]|] H; simpl in H; try discriminate;
    [|reflexivity].
  apply andb_prop in H as [H Hn]; apply andb_prop in H as [Hw Hd].
  apply sym_eqb_spec in Hw; apply dir_eqb_spec in Hd; apply st_eqb_spec in Hn.
  subst; reflexivity.
Qed.

(** All eight cells of the (4,2) table. *)
Definition all_cells : list (St * Sym) :=
  [(StA, S0); (StA, S1); (StB, S0); (StB, S1);
   (StC, S0); (StC, S1); (StD, S0); (StD, S1)].

Definition tm_eqb (m1 m2 : TM) : bool :=
  forallb (fun c => trans_eqb (m1 (fst c) (snd c)) (m2 (fst c) (snd c)))
          all_cells.

Lemma tm_eqb_spec : forall m1 m2, tm_eqb m1 m2 = true -> m1 = m2.
Proof.
  intros m1 m2 H.
  apply functional_extensionality; intro q.
  apply functional_extensionality; intro s.
  apply trans_eqb_spec.
  unfold tm_eqb in H. rewrite forallb_forall in H.
  apply (H (q, s)).
  unfold all_cells; destruct q, s; simpl; tauto.
Qed.

(** ** Deciding [forall q, Visited m q] by a bounded search

    [neverqh_reroot]'s third premise.  A generated board used to name four
    step indices, one per state; searching [0 .. f-1] for each instead means
    the generator supplies a FUEL and not four facts, and a fuel that is too
    small fails loudly at [vm_compute] rather than proving something else.

    [csteps] is re-run from [c0] per index, so this is quadratic in [f] --
    irrelevant at the sizes involved (every shadow in the tree has all four
    states visited within a handful of steps, [f <= 8]). *)

Definition visited_b (m : TM) (f : nat) (q : St) : bool :=
  existsb (fun n => match csteps m n c0 with
                    | Some c => st_eqb (fst c) q
                    | None => false
                    end)
          (seq 0 f).

Definition all_visited_b (m : TM) (f : nat) : bool :=
  forallb (visited_b m f) [StA; StB; StC; StD].

Lemma visited_b_sound : forall m f q, visited_b m f q = true -> Visited m q.
Proof.
  intros m f q H. unfold visited_b in H.
  apply existsb_exists in H as (n & _ & Hn).
  exact (visited_csteps m n q Hn).
Qed.

Lemma all_visited_b_sound : forall m f,
  all_visited_b m f = true -> forall q, Visited m q.
Proof.
  intros m f H q. unfold all_visited_b in H.
  rewrite forallb_forall in H.
  apply (visited_b_sound m f).
  apply H. destruct q; simpl; tauto.
Qed.

(** ** The shadow board, in one lemma

    [tm] runs [t] steps writing only blanks and arrives in [qs]; its re-root
    is [rr]; [rr] never quasihalts and visits every state.  Then [tm] never
    quasihalts.

    The three booleans are exactly the three sentences: *the prefix is all
    blanks*, *and then it IS that machine*, *which gets everywhere*.  The
    fourth premise is the neighbouring board's own theorem, carried across
    the relabelling by [neverqh_swap] / [neverqh_mirror] at the call site --
    those stay outside because the op chain differs per row and each op is
    one [apply]. *)
Theorem shadow_nqh : forall (tm rr : TM) (qs : St) (t f : nat),
  prefix_ok tm qs t = true ->
  tm_eqb (TM_swap StA qs tm) rr = true ->
  all_visited_b rr f = true ->
  NeverQuasiHaltsSt rr ->
  NeverQuasiHaltsSt tm.
Proof.
  intros tm rr qs t f Hpre Heq Hvis Hnqh.
  apply tm_eqb_spec in Heq.
  apply (neverqh_reroot tm qs t).
  - apply prefix_ok_sound. exact Hpre.
  - rewrite Heq. exact Hnqh.
  - rewrite Heq. exact (all_visited_b_sound rr f Hvis).
Qed.

(** [NonHalt] comes free, as it does for every never-quasihalting board. *)
Corollary shadow_nonhalt : forall (tm rr : TM) (qs : St) (t f : nat),
  prefix_ok tm qs t = true ->
  tm_eqb (TM_swap StA qs tm) rr = true ->
  all_visited_b rr f = true ->
  NeverQuasiHaltsSt rr ->
  NonHalt tm.
Proof.
  intros tm rr qs t f H1 H2 H3 H4.
  apply never_qh_nonhalt, (shadow_nqh tm rr qs t f H1 H2 H3 H4).
Qed.
