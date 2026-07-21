(** * WaveCounter: the never-quasihalting closer for the wave family.

    The six wave_counter machines (BBB certs counter6/7/17/24/27/36) and
    the one wave4_counter (#15) are PARITY-WAVE ODOMETERS: the event
    config is a block word

      1^{B_0} 0 1^{B_1} 0 ... 0 1^{B_m}   (single-0 separators),

    the head one cell past the frontier at the edge state, and one pass
    increments the frontier (B_m += 1) then propagates a parity carry
    leftward, stopping at the first odd block (depositing +1 there) or,
    if every interior block is even and the lead is 1, SPAWNING a new
    length-1 block after the lead.  The wave depth and block lengths are
    both unbounded, so a pass is a NESTED translated cycle, NOT a single
    parametric run -- unlike the mono/spacer families [LapGlue] was built
    for.  See the wave design appendix in NEXT_SESSION.md.

    This file carries the machine-INDEPENDENT closer.  Where [LapGlue]
    indexes its anchors by a [positive] advanced by [Pos.succ], the wave
    anchors are indexed by an arbitrary state type [A] advanced by a
    total successor [nextA], constrained to a preserved invariant [Inv]
    (the parity-safety predicate: the wave never stops at the lead and
    every spawn has lead 1).  The reachability argument is identical to
    [LapGlue.glue_reach] with [Nat.iter k nextA a0] in place of the
    positive anchor.  No axioms. *)

From Coq Require Import Arith Lia List Bool.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape.
Import ListNotations.

Section WaveGlue.

Variable tm : TM.
Variable A : Type.
Variable nextA : A -> A.
Variable Inv : A -> Prop.
Variable Cf : A -> cconf.
Variable a0 : A.

Hypothesis Hinv0 : Inv a0.
Hypothesis Hinv_step : forall a, Inv a -> Inv (nextA a).
Hypothesis Hboot : exists t0, stepn tm t0 InitES = Some (lift (Cf a0)).
Hypothesis Hlap : forall a, Inv a ->
  exists n c', csteps tm n (Cf a) = Some c' /\
               lift c' = lift (Cf (nextA a)) /\ 0 < n.
Hypothesis Hvis : forall a q, Inv a ->
  exists k c, csteps tm k (Cf a) = Some c /\ fst c = q.

(** The [k]-th anchor, and that the invariant rides the whole orbit. *)
Definition anc (k : nat) : A := Nat.iter k nextA a0.

Lemma anc_inv : forall k, Inv (anc k).
Proof.
  induction k as [|k IH].
  - exact Hinv0.
  - apply Hinv_step. exact IH.
Qed.

(** The [k]-th anchor is reached at a global index of at least [k]. *)
Lemma wglue_reach : forall k, exists T, k <= T /\
  stepn tm T InitES = Some (lift (Cf (anc k))).
Proof.
  induction k as [|k IH].
  - destruct Hboot as (t0 & H0). exists t0. split; [lia | exact H0].
  - destruct IH as (T & HT & Hstep).
    destruct (Hlap (anc k) (anc_inv k)) as (n & c' & Hrun & Hlift & Hn).
    exists (T + n). split; [lia|].
    rewrite stepn_add, Hstep.
    rewrite (csteps_lift _ _ _ _ Hrun), Hlift.
    reflexivity.
Qed.

Theorem wglue_neverqh : NeverQuasiHaltsSt tm.
Proof.
  intros q _ N.
  destruct (wglue_reach N) as (T & HN & Hstep).
  destruct (Hvis (anc N) q (anc_inv N)) as (k & c & Hc & Hqc).
  exists (T + k). split; [lia|].
  exists (lift c). split.
  - rewrite stepn_add, Hstep. apply csteps_lift; exact Hc.
  - rewrite lift_state. exact Hqc.
Qed.

End WaveGlue.

(** * The abstract parity odometer and its safety invariant (P2).

    The wave state is the block vector; we drop the LEAD block (always 1)
    and carry the FRONTIER-FIRST list of the non-lead blocks
    [front = [B_m; B_{m-1}; ...; B_1]] (all >= 1).  One pass increments
    the frontier (head) and propagates a parity carry: the carry deposits
    +1 at the block just LEAD-ward of the first "effective-odd" block
    (the frontier's parity is read with the machine's [poff] offset),
    or -- if every block is effective-even -- SPAWNS a new length-1 block
    (append [1]).  [nextf] is exactly verify.c's [wc_expected] on this
    representation (validated by [Compute] against the raw orbit).

    The SAFETY the family needs (verify.c [wc_parity_schema]): the carry
    never runs past the lead (LEAD-STOP) and every spawn keeps the lead
    at 1.  In this representation lead=1 is implicit, so bad-spawn cannot
    occur; and LEAD-STOP is the carry depositing off the end of [front].
    The invariant that forbids it: the EFFECTIVE PARITY WORD has an EVEN
    number of set bits ([fp = false]).  Each pass flips exactly two parity
    bits (frontier + deposit), so even-popcount is preserved; and a
    lead-stop word is [0..0 1] (odd popcount), hence excluded.  This is
    machine-independent -- proved once for all six wave machines. *)

(** XOR of block parities. *)
Fixpoint pbits (l : list nat) : bool :=
  match l with [] => false | x :: r => xorb (Nat.odd x) (pbits r) end.

(** Carry propagation from the frontier: [po] = "the previous block was
    effective-odd, deposit here".  [[] , true] is the (unreachable under
    the invariant) LEAD-STOP; [[] , false] is the SPAWN. *)
Fixpoint carry (po : bool) (blocks : list nat) : list nat :=
  match blocks with
  | [] => if po then [] else [1]
  | b :: r => if po then S b :: r else b :: carry (Nat.odd b) r
  end.

(** One abstract pass: increment the frontier, propagate the carry. *)
Definition nextf (poff : nat) (front : list nat) : list nat :=
  match front with
  | [] => []
  | b0 :: r => S b0 :: carry (Nat.odd (b0 + poff)) r
  end.

(** The effective parity word's popcount parity (frontier read with poff). *)
Definition fp (poff : nat) (front : list nat) : bool :=
  match front with [] => false | b :: r => xorb (Nat.odd (b + poff)) (pbits r) end.

Lemma odd_Spoff : forall b0 poff,
  Nat.odd (S b0 + poff) = negb (Nat.odd (b0 + poff)).
Proof. intros. rewrite Nat.add_succ_l, Nat.odd_succ, Nat.negb_odd. reflexivity. Qed.

Lemma pbits_true_step : forall blocks, pbits blocks = true ->
  pbits (carry true blocks) = false /\ blocks <> [].
Proof.
  intros [|b r] H; simpl in H; [discriminate|].
  split; [|discriminate]. simpl. rewrite Nat.odd_succ, <- Nat.negb_odd.
  destruct (Nat.odd b), (pbits r); simpl in *; congruence.
Qed.

Lemma pbits_false_step : forall blocks, pbits blocks = false ->
  pbits (carry false blocks) = true.
Proof.
  induction blocks as [|b r IH]; intros H; [reflexivity|].
  simpl in H. simpl. destruct (Nat.odd b) eqn:Eb.
  - assert (pbits r = true) by (destruct (pbits r); simpl in H; congruence).
    destruct (pbits_true_step r H0) as [Hc _]. simpl. rewrite Hc. reflexivity.
  - assert (pbits r = false) by (destruct (pbits r); simpl in H; congruence).
    rewrite (IH H0). reflexivity.
Qed.

(** The core preservation: even effective-popcount is a pass invariant. *)
Lemma fp_preserved : forall poff front,
  fp poff front = false -> fp poff (nextf poff front) = false.
Proof.
  intros poff [|b0 r] H; [reflexivity|].
  simpl in H. unfold nextf, fp. rewrite odd_Spoff.
  destruct (Nat.odd (b0 + poff)) eqn:E0; simpl.
  - assert (Hr : pbits r = true) by (destruct (pbits r); simpl in H; congruence).
    destruct (pbits_true_step r Hr) as [Hc _]. rewrite Hc. reflexivity.
  - assert (Hr : pbits r = false) by (destruct (pbits r); simpl in H; congruence).
    rewrite (pbits_false_step r Hr). reflexivity.
Qed.

(** Wellformedness (every block >= 1) is preserved. *)
Lemma carry_pos : forall po blocks, Forall (fun x => 1 <= x) blocks ->
  Forall (fun x => 1 <= x) (carry po blocks).
Proof.
  intros po blocks; revert po; induction blocks as [|b r IH]; intros po H.
  - destruct po; simpl; [constructor | repeat constructor; lia].
  - inversion H; subst. destruct po; simpl.
    + constructor; [lia | assumption].
    + constructor; [assumption | apply IH; assumption].
Qed.

Lemma nextf_pos : forall poff front, Forall (fun x => 1 <= x) front ->
  Forall (fun x => 1 <= x) (nextf poff front).
Proof.
  intros poff [|b0 r] H; [constructor|].
  inversion H; subst. simpl. constructor; [lia | apply carry_pos; assumption].
Qed.

Lemma nextf_nonnil : forall poff front, front <> [] -> nextf poff front <> [].
Proof. intros poff [|b0 r] H; [congruence|]. simpl. discriminate. Qed.

(** The safety invariant. *)
Definition WInv (poff : nat) (front : list nat) : Prop :=
  fp poff front = false /\ Forall (fun x => 1 <= x) front /\ front <> [].

Theorem WInv_preserved : forall poff front,
  WInv poff front -> WInv poff (nextf poff front).
Proof.
  intros poff front (Hf & Hp & Hn). repeat split.
  - apply fp_preserved; assumption.
  - apply nextf_pos; assumption.
  - apply nextf_nonnil; assumption.
Qed.

(** Explicit "never lead-stops": [carry_ok] is [false] exactly when the
    carry would deposit past the lead; the invariant rules it out. *)
Fixpoint carry_ok (po : bool) (blocks : list nat) : bool :=
  match blocks with
  | [] => negb po
  | b :: r => if po then true else carry_ok (Nat.odd b) r
  end.

Lemma carry_ok_of_par : forall blocks po,
  po = pbits blocks -> carry_ok po blocks = true.
Proof.
  induction blocks as [|b r IH]; intros po H; simpl in *.
  - subst; reflexivity.
  - destruct po; [reflexivity|]. apply IH.
    destruct (Nat.odd b), (pbits r); simpl in *; congruence.
Qed.

Theorem WInv_no_leadstop : forall poff b0 r,
  WInv poff (b0 :: r) -> carry_ok (Nat.odd (b0 + poff)) r = true.
Proof.
  intros poff b0 r (Hf & _ & _). simpl in Hf.
  apply carry_ok_of_par.
  destruct (Nat.odd (b0 + poff)), (pbits r); simpl in *; congruence.
Qed.

(** * Reachability closure (for the nested per-pass laps).

    A wave pass is a NESTED fold (a leftward carry wave + a rightward
    reconstruction), so -- like the doubling families -- the per-machine
    [Hlap] is built from a reachability preorder rather than one
    parametric [csteps].  [creach] and its fold [creach_iter] are the
    outer-loop closer; [creach_lap] packages a [creach] with a positive
    prefix into the [wglue] / [LapGlue] [Hlap] existential. *)

Definition wreach (tm : TM) (c c' : cconf) : Prop :=
  exists n, csteps tm n c = Some c'.

Lemma wreach_refl : forall tm c, wreach tm c c.
Proof. intros. exists 0. reflexivity. Qed.

Lemma wreach_csteps : forall tm n c c', csteps tm n c = Some c' -> wreach tm c c'.
Proof. intros tm n c c' H. exists n. exact H. Qed.

Lemma wreach_trans : forall tm c1 c2 c3,
  wreach tm c1 c2 -> wreach tm c2 c3 -> wreach tm c1 c3.
Proof.
  intros tm c1 c2 c3 (n1 & H1) (n2 & H2).
  exists (n1 + n2). eapply csteps_chain; eauto.
Qed.

Lemma wreach_iter : forall tm (f : nat -> cconf) k,
  (forall i, i < k -> wreach tm (f i) (f (S i))) ->
  wreach tm (f 0) (f k).
Proof.
  intros tm f k H. induction k as [| k IH].
  - apply wreach_refl.
  - eapply wreach_trans; [apply IH; intros i Hi; apply H; lia | apply H; lia].
Qed.

(** Package a positive-prefix [wreach] into the [Hlap] existential
    (goal reached up to blank padding [lift]). *)
Lemma wreach_lap : forall tm n c c1 cnext,
  csteps tm n c = Some c1 -> 0 < n -> wreach tm c1 cnext ->
  exists m c', csteps tm m c = Some c' /\ lift c' = lift cnext /\ 0 < m.
Proof.
  intros tm n c c1 cnext Hpre Hn (n2 & Hr).
  exists (n + n2), cnext.
  split; [eapply csteps_chain; eauto | split; [reflexivity | lia]].
Qed.
