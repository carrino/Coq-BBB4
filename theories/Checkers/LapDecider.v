(** * LapDecider: an EXACT lap decider — one soundness theorem, per-machine
    cost a [vm_compute].

    Wave-12 established (docs/WHY_NO_HAMMER.md) that no lossy abstraction can
    finish this residue: the n-gram closure always closes, but the q-avoiding
    subgraph the liveness certificate needs stays cyclic at every precision
    setting, because a counter's carry after ~2^k steps is invisible to any
    finite window.  Exactness is required for the LIVENESS half.

    What was wrong was not the exactness, it was the EXPONENT: waves 8-12 spent
    one hand-authored theorem per machine (five emitters, ~500 boards against a
    1,385 residue).  This file is the fix — the same symbolic lap those
    emitters compute, but as a CHECKABLE certificate with the soundness
    argument discharged once.

    The idea.  Every lap chain those emitters derived has the same shape: each
    tape side is a fixed prefix, one repeated block whose count is affine in
    the carry index [j], and a fixed suffix.  So a symbolic side

      sside := (pre, u, (a, b), post)   denoting   pre ++ rep u (a*j+b) ++ post

    is expressive enough for the whole family, and a chain of three step kinds
    (framed window, leftward cycle, rightward cycle) covers every phase.  The
    checker runs the chain symbolically; [chain_sound] turns a successful
    symbolic run into a concrete [csteps] for EVERY [j] at once.

    UNTRUSTED input, trusted checker: a certificate is just data.  A wrong one
    fails to typecheck or fails the boolean check; it cannot mis-prove. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape.
Import ListNotations.

(** ** Symbolic tape sides *)

(** [pre ++ rep u (a*j+b) ++ post] *)
Record sside := mkS {
  s_pre  : list Sym;
  s_u    : list Sym;
  s_a    : nat;
  s_b    : nat;
  s_post : list Sym
}.

Definition sden (j : nat) (s : sside) : list Sym :=
  s_pre s ++ rep (s_u s) (s_a s * j + s_b s) ++ s_post s.

(** A purely fixed side. *)
Definition sfix (w : list Sym) : sside := mkS w [] 0 0 [].

Lemma sden_sfix : forall j w, sden j (sfix w) = w.
Proof. intros. unfold sden, sfix; simpl. now rewrite app_nil_r. Qed.

(** ** Symbolic configurations *)

Record sconf := mkC {
  c_st : St;
  c_l  : sside;
  c_h  : Sym;
  c_r  : sside
}.

Definition cden (j : nat) (c : sconf) : cconf :=
  (c_st c, (sden j (c_l c), c_h c, sden j (c_r c))).

(** ** Chain steps

    [SWin] frames a fixed window against the PREFIXES of both sides, so its
    entry is concrete and its unit lemma closes by [reflexivity] in the
    emitted certificate.  [SCycL]/[SCycR] consume the repeated block. *)

Inductive lstep :=
| SWin  (n : nat) (lw rw : nat) (el : list Sym) (eh : Sym) (er : list Sym)
        (q' : St) (xl : list Sym) (xh : Sym) (xr : list Sym)
| SCycL (n : nat) (u rw w : list Sym) (a b : nat)
| SCycR (n : nat) (u w : list Sym) (a b : nat).

(** ** Soundness of the two cycle steps, uniformly in [j]

    These are [WTape.cycL] / [WTape.cycR] with the count read off the
    symbolic side, so the repetition count is [a*j+b] rather than a literal. *)

Lemma scycL_sound : forall tm P q h u rw w,
  wsteps true true tm P (q, (u, h, rw)) = Some (q, ([], h, rw ++ w)) ->
  forall k L R,
  csteps tm (P * k) (q, (rep u k ++ L, h, rw ++ R))
    = Some (q, (L, h, rw ++ rep w k ++ R)).
Proof. intros. now apply cycL. Qed.

Lemma scycR_sound : forall tm P q h u w,
  wsteps true true tm P (q, ([], h, u)) = Some (q, (w, h, [])) ->
  forall k L R,
  csteps tm (P * k) (q, (L, h, rep u k ++ R))
    = Some (q, (rep w k ++ L, h, R)).
Proof. intros. now apply cycR. Qed.

(** ** The lap obligation, stated once

    A certificate proves this for an anchor family [Cf].  [glue_neverqh]
    (Counters/LapGlue.v) consumes exactly this plus boot and visits, so a
    decided certificate plugs straight into the existing closer. *)

Definition LapStep (tm : TM) (Cf : positive -> cconf) : Prop :=
  forall p, exists n c', csteps tm n (Cf p) = Some c'
                    /\ lift c' = lift (Cf (Pos.succ p))
                    /\ 0 < n.

(** A chain that runs symbolically from [c0] to [c1] in [n j] steps yields the
    concrete run at every [j] — this is the shape every emitted lap proof has,
    with the per-machine rep-algebra replaced by the denotation [sden]. *)
Definition ChainSound (tm : TM) (c0 c1 : sconf) (n : nat -> nat) : Prop :=
  forall j, csteps tm (n j) (cden j c0) = Some (cden j c1).

Lemma ChainSound_trans : forall tm a b c na nb,
  ChainSound tm a b na -> ChainSound tm b c nb ->
  ChainSound tm a c (fun j => na j + nb j).
Proof.
  intros tm a b c na nb Hab Hbc j.
  rewrite csteps_add, (Hab j). exact (Hbc j).
Qed.

Lemma ChainSound_refl : forall tm a, ChainSound tm a a (fun _ => 0).
Proof. intros tm a j. reflexivity. Qed.
