(** * NestedLapHalf: the nested overflow whose inner run stops HALFWAY

    [NestedLapLift.nested_overflow_lift] composes boot + inner + exit with the
    inner run going from [Cin v0] all the way to [Cin (fill v0)] -- a FULL
    octave of the inner counter.  `tools/counters/innerrun.py` measured that
    16 of the 54 nested arms it looked at do not do that: the inner count runs

        2^m .. 2^m + 2^(m-1) - 1

    and the exit fires from the HALFWAY value, not from the fill.  Wave-32
    proved the carrier for a bounded run ([NestedLapLift.inner_to_add_lift],
    a plain induction on the step count with [k <= tovf v] as the entire side
    condition) but wrote no board around it, because the emitter had no way to
    name the endpoint: [inner_to_add_lift] states it as [Nat.iter k Pos.succ v]
    and [Nat.iter] is not an sside.

    It does not have to be.  The halfway value has a NAME:

        2^m + 2^(m-1) - 1  =  1 0 1^(m-1)  in binary  =  [half2 (m-1)]

    which is a perfectly ordinary digit family -- [half2 n]'s [cview] is
    [(n, Some xH)], so the board reads it off with the SAME [cview_some_*]
    bridge its interior lap already uses, and the encoded word is one
    [rep] ([Ip (half2 n) = rep uS n ++ uD ++ soD] and its analogues, emitted
    per board exactly like [iepow]).

    So the only thing missing was the arithmetic that connects the two
    spellings: [iter_succ_to] says that iterating [Pos.succ] by the numeric
    difference lands on the target, and [half_step_le] discharges
    [inner_to_add_lift]'s side condition once and for all -- the run from
    [2^(m)] of length [2^(m-1) - 1] stays inside its octave, because
    [tovf (pow2 m) = 2^m - 1].

    Axiom footprint: whatever [CTape.lift] carries
    ([functional_extensionality_dep]); nothing new is introduced here. *)

From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape MonoCounter JpCounter LapGlue
                                  IXPGadgets LapCertGlue LapCertGlueLift
                                  NestedLap NestedLapLift.
Import ListNotations.

(** ** The halfway value

    [half2 n] is [2^(n+1) + 2^n - 1]: binary [1 0 1^n], i.e. [n] copies of the
    digit 1 under a single 0 under the leading sentinel.  In [positive] the
    least significant bit is outermost, so that is [n] [xI]s on top of
    [xO xH]. *)
Fixpoint half2 (n : nat) : positive :=
  match n with O => xO xH | S m => xI (half2 m) end.

Lemma half2_cview : forall n, cview (half2 n) = (n, Some xH).
Proof.
  induction n as [|n IH]; [reflexivity | cbn [half2 cview]; rewrite IH; reflexivity].
Qed.

Lemma one_le_pow2 : forall n, 1 <= 2 ^ n.
Proof. induction n as [|n IH]; cbn; lia. Qed.

Lemma pos2nat_pow2 : forall n, Pos.to_nat (pow2 n) = 2 ^ n.
Proof.
  induction n as [|n IH]; [reflexivity |].
  cbn [pow2 Nat.pow]. rewrite Pos2Nat.inj_xO, IH. lia.
Qed.

Lemma pos2nat_half2 : forall n, Pos.to_nat (half2 n) = 2 ^ (S n) + 2 ^ n - 1.
Proof.
  induction n as [|n IH]; [reflexivity |].
  cbn [half2]. rewrite Pos2Nat.inj_xI, IH.
  assert (H : 1 <= 2 ^ n) by (apply one_le_pow2).
  cbn [Nat.pow]. lia.
Qed.

Lemma tovf_pow2 : forall n, tovf (pow2 n) = 2 ^ n - 1.
Proof.
  induction n as [|n IH]; [reflexivity |].
  cbn [pow2 tovf Nat.pow]. rewrite IH.
  assert (H : 1 <= 2 ^ n) by (apply one_le_pow2). lia.
Qed.

(** ** [Nat.iter Pos.succ] is numeric addition, so it can hit a NAMED target *)

Lemma iter_succ_nat : forall d v, Pos.to_nat (Nat.iter d Pos.succ v) = Pos.to_nat v + d.
Proof.
  induction d as [|d IH]; intro v; [cbn; lia |].
  rewrite Nat.iter_succ_r, IH, Pos2Nat.inj_succ. lia.
Qed.

Lemma iter_succ_to : forall v E, Pos.to_nat v <= Pos.to_nat E ->
  Nat.iter (Pos.to_nat E - Pos.to_nat v) Pos.succ v = E.
Proof.
  intros v E H. apply Pos2Nat.inj. rewrite iter_succ_nat. lia.
Qed.

(** The two facts the halfway run needs, in numeric form. *)
Lemma half_le : forall n, Pos.to_nat (pow2 (S n)) <= Pos.to_nat (half2 n).
Proof.
  intro n. rewrite pos2nat_pow2, pos2nat_half2.
  assert (H : 1 <= 2 ^ n) by (apply one_le_pow2). lia.
Qed.

Lemma half_step_le : forall n,
  Pos.to_nat (half2 n) - Pos.to_nat (pow2 (S n)) <= tovf (pow2 (S n)).
Proof.
  intro n. rewrite pos2nat_pow2, pos2nat_half2, tovf_pow2.
  assert (H : 1 <= 2 ^ n) by (apply one_le_pow2).
  cbn [Nat.pow] in *. lia.
Qed.


(** ** The OFFSET start

    `innerrun.py` also measured runs that START a small constant above the
    octave: [lo = 2^m + c].  The start has a name too -- it is the concrete
    constructor word of [c] on top of [pow2 (m - width c)], which the emitter
    writes down directly -- so the only thing a board needs is the numeric
    side condition, and that is [inner_to_named_lift] below: any [v] and any
    [E] in the SAME octave, stated purely in [Pos.to_nat] and [tovf], with no
    commitment to how either was built.

    [tovf_size] is what turns [tovf] of a built-up start into arithmetic. *)

Lemma size_nat_pow2 : forall n, Pos.size_nat (pow2 n) = S n.
Proof. induction n as [|n IH]; [reflexivity | cbn [pow2 Pos.size_nat]; lia]. Qed.

Lemma size_nat_half2 : forall n, Pos.size_nat (half2 n) = S (S n).
Proof. induction n as [|n IH]; [reflexivity | cbn [half2 Pos.size_nat]; lia]. Qed.

Lemma pos_lt_pow2_size : forall v, Pos.to_nat v < 2 ^ Pos.size_nat v.
Proof.
  induction v as [v IH|v IH|]; cbn [Pos.size_nat Nat.pow].
  - rewrite Pos2Nat.inj_xI. lia.
  - rewrite Pos2Nat.inj_xO. lia.
  - cbn. lia.
Qed.

Lemma tovf_size : forall v, tovf v = 2 ^ Pos.size_nat v - 1 - Pos.to_nat v.
Proof.
  induction v as [v IH|v IH|]; [| | reflexivity];
    cbn [tovf Pos.size_nat Nat.pow]; rewrite IH;
    [rewrite Pos2Nat.inj_xI | rewrite Pos2Nat.inj_xO];
    pose proof (pos_lt_pow2_size v); lia.
Qed.

(** [half2 n] as [3 * 2^n - 1] -- the form a board's side conditions reduce
    to once [Nat.pow_add_r] has split the index shift off. *)
Lemma pos2nat_half2' : forall n, Pos.to_nat (half2 n) = 3 * 2 ^ n - 1.
Proof.
  intro n. rewrite pos2nat_half2. cbn [Nat.pow].
  pose proof (one_le_pow2 n). lia.
Qed.

Section InnerHalfLift.

Variable tm : TM.
Variable Cin : positive -> cconf.

Hypothesis Hin : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).

(** The inner counter, run from its octave start to the HALFWAY value.  The
    [exists n] is the whole [Theta(2^n)] middle; no formula for it is written
    down, exactly as in [inner_to_fill_lift]. *)
(** Any two anchors of the same octave: the run from [v] to [E] takes
    [Pos.to_nat E - Pos.to_nat v] increments, and the side condition is
    [inner_to_add_lift]'s verbatim.  Neither endpoint has to be a power of
    two, a fill or a half -- the board names them and discharges the two
    numeric premises. *)
Lemma inner_to_named_lift : forall v E,
  Pos.to_nat v <= Pos.to_nat E ->
  Pos.to_nat E - Pos.to_nat v <= tovf v ->
  exists m, stepn tm m (lift (Cin v)) = Some (lift (Cin E)).
Proof.
  intros v E Hle Hk.
  destruct (inner_to_add_lift tm Cin Hin
              (Pos.to_nat E - Pos.to_nat v) v Hk) as (m & Hm).
  exists m. rewrite (iter_succ_to _ _ Hle) in Hm. exact Hm.
Qed.

Lemma inner_to_half_lift : forall n,
  exists m, stepn tm m (lift (Cin (pow2 (S n)))) = Some (lift (Cin (half2 n))).
Proof.
  intro n.
  destruct (inner_to_add_lift tm Cin Hin
              (Pos.to_nat (half2 n) - Pos.to_nat (pow2 (S n)))
              (pow2 (S n)) (half_step_le n)) as (m & Hm).
  exists m. rewrite (iter_succ_to _ _ (half_le n)) in Hm. exact Hm.
Qed.

End InnerHalfLift.

Section NestedOverflowHalf.

Variable tm : TM.
Variable Cc Cin : positive -> cconf.

Hypothesis Hin : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).

(** A state that fires in the EXIT half of a HALFWAY arm -- after the inner
    counter's laps -- is still visited from the outer overflow anchor.  The
    [vis_via_fill] twin. *)
Lemma vis_via_half : forall (q : St) (p : positive) (n : nat),
  (exists m c, csteps tm m (Cc p) = Some c /\ lift c = lift (Cin (pow2 (S n)))) ->
  (exists k e, stepn tm k (lift (Cin (half2 n))) = Some e /\ fst e = q) ->
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros q p n (m & c & Hm & Hl) (k & e & Hk & Hq).
  destruct (inner_to_half_lift tm Cin Hin n) as (mi & Hi).
  exists (m + (mi + k)), e. split; [| exact Hq].
  rewrite stepn_add, (csteps_lift _ _ _ _ Hm), Hl, stepn_add, Hi. exact Hk.
Qed.

(** [vis_via_half] / [nested_overflow_half_lift] with both endpoints NAMED by
    the board instead of fixed at [pow2 (S n)] and [half2 n]. *)
Lemma vis_via_named : forall (q : St) (p v E : positive),
  Pos.to_nat v <= Pos.to_nat E ->
  Pos.to_nat E - Pos.to_nat v <= tovf v ->
  (exists m c, csteps tm m (Cc p) = Some c /\ lift c = lift (Cin v)) ->
  (exists k e, stepn tm k (lift (Cin E)) = Some e /\ fst e = q) ->
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros q p v E Hle Hk (m & c & Hm & Hl) (k & e & Hk2 & Hq).
  destruct (inner_to_named_lift tm Cin Hin v E Hle Hk) as (mi & Hi).
  exists (m + (mi + k)), e. split; [| exact Hq].
  rewrite stepn_add, (csteps_lift _ _ _ _ Hm), Hl, stepn_add, Hi. exact Hk2.
Qed.

Theorem nested_overflow_named_lift : forall (p v E : positive),
  Pos.to_nat v <= Pos.to_nat E ->
  Pos.to_nat E - Pos.to_nat v <= tovf v ->
  (exists m c, 0 < m /\ csteps tm m (Cc p) = Some c /\ lift c = lift (Cin v)) ->
  (exists m c', csteps tm m (Cin E) = Some c'
                /\ lift c' = lift (Cc (Pos.succ p))) ->
  exists m c', csteps tm m (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < m.
Proof.
  intros p v E Hle Hk (nb & cb & Hnb & Hb & Hbl) (ne & ce & He & Hel).
  destruct (inner_to_named_lift tm Cin Hin v E Hle Hk) as (ni & Hi).
  assert (Hrest : stepn tm (ni + ne) (lift cb) = Some (lift ce)).
  { rewrite stepn_add, Hbl, Hi. exact (csteps_lift _ _ _ _ He). }
  destruct (stepn_csteps_at tm (ni + ne) cb (lift ce) Hrest)
    as (cf & Hcf & Hcfl).
  exists (nb + (ni + ne)), cf. split; [| split].
  - rewrite csteps_add, Hb. exact Hcf.
  - rewrite Hcfl. exact Hel.
  - lia.
Qed.

(** The outer overflow branch of a HALFWAY arm, in the shape
    [LapGlue.glue_neverqh] consumes. *)
Theorem nested_overflow_half_lift : forall (p : positive) (n : nat),
  (exists m c, 0 < m /\ csteps tm m (Cc p) = Some c
               /\ lift c = lift (Cin (pow2 (S n)))) ->
  (exists m c', csteps tm m (Cin (half2 n)) = Some c'
                /\ lift c' = lift (Cc (Pos.succ p))) ->
  exists m c', csteps tm m (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < m.
Proof.
  intros p n (nb & cb & Hnb & Hb & Hbl) (ne & ce & He & Hel).
  destruct (inner_to_half_lift tm Cin Hin n) as (ni & Hi).
  assert (Hrest : stepn tm (ni + ne) (lift cb) = Some (lift ce)).
  { rewrite stepn_add, Hbl, Hi. exact (csteps_lift _ _ _ _ He). }
  destruct (stepn_csteps_at tm (ni + ne) cb (lift ce) Hrest)
    as (cf & Hcf & Hcfl).
  exists (nb + (ni + ne)), cf. split; [| split].
  - rewrite csteps_add, Hb. exact Hcf.
  - rewrite Hcfl. exact Hel.
  - lia.
Qed.

End NestedOverflowHalf.
