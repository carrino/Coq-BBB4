(** * Checkers.LadderCheckMirrorTr: a binary counter held TWICE, once on each
    side of the head (SCOPING_INSTR 7.4.LE7).

    LE6's survey has a group of rows whose tape grows two cells per doubling
    of time at BOTH ends (per-round growth ratio sqrt 2).  Read by hand,
    [1RB0RA_1LC1RA_1LD0LC_1LA1LD] at its anchor [A1] is

      left (read outward from the head):   (00 | 11)^n
      right (read outward from the head):  (00 | 01)^n

    with the SAME digit string [x] on both sides, least significant digit at
    the head: the machine adds one on one side, walks across, adds one on the
    other, and at the top of a width both sides gain a digit.  No one-sided
    family states it ([LadderFam.Fam] has one counter side and a fixed far
    side), but [LapDecider.sconf] has a repeated block on EACH side with ONE
    shared index, which is exactly a class [t^n d] of the mirrored counter.
    So this file is [LadderCheckTr]'s positional counter with the far side
    replaced by a second copy of the counter:

      cells:  (q, (preL ++ flat_map DL x ++ sufL, h, preR ++ flat_map DR x ++ sufR))
      law:    x -> x + 1, and an all-top x widens: (b-1)^n -> 0^n 1

    Two arm classes: the interior [t^n d -> 0^n (d+1)] with both rests
    opaque, and the top [t^n -> 0^n 1] with both tails known empty.
    Liveness: within a width the value rises, so every width reaches its
    top; the fires are read from the top arms.

    Nothing landed is modified.  Axiom footprint: [functional_extensionality_dep],
    via [CTape.lift]. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr.
From BBB4.Counters Require Import WTape LapCertGlueLift.
From BBB4.Checkers Require Import WrapTr LapDecider LadderKernel LadderFam LadderCheck LadderCheckTr LadderNest LadderCheckNestTr TCyclerQHTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

(** ** 1. The counter *)

Section Mir.

Variable b : nat.
Variable DL DR : list (list Sym).    (** digit words per side, index = digit *)
Variable preL preR sufL sufR : list Sym.
Variable q : St.
Variable hs : Sym.

Definition digL (d : nat) : list Sym := nth d DL [].
Definition digR (d : nat) : list Sym := nth d DR [].

Fixpoint incW (x : list nat) : list nat :=
  match x with
  | [] => [1]
  | d :: t => if d =? b - 1 then 0 :: incW t else S d :: t
  end.

Definition alltopW (x : list nat) : bool := forallb (Nat.eqb (b - 1)) x.

Fixpoint iterW (x : list nat) (n : nat) : list nat :=
  match n with
  | O => x
  | S n' => iterW (incW x) n'
  end.

Lemma iter_addW : forall n1 n2 x, iterW x (n1 + n2) = iterW (iterW x n1) n2.
Proof. induction n1 as [|n1 IH]; intros n2 x; [reflexivity | apply IH]. Qed.

Definition mcellsL (x : list nat) : list Sym := preL ++ flat_map digL x ++ sufL.
Definition mcellsR (x : list nat) : list Sym := preR ++ flat_map digR x ++ sufR.

Definition mcfg (x : list nat) : cconf := (q, (mcellsL x, hs, mcellsR x)).

Lemma flat_map_repeatW : forall (f : nat -> list Sym) t n,
  flat_map f (repeat t n) = rep (f t) n.
Proof.
  intros f t n. induction n as [|n IH]; [reflexivity|].
  cbn [repeat flat_map rep]. rewrite IH. reflexivity.
Qed.

(** *** The carry, and the value it adds one to *)

Lemma inc_classW : forall n d rest, d < b - 1 ->
  incW (repeat (b - 1) n ++ d :: rest) = repeat 0 n ++ S d :: rest.
Proof.
  induction n as [|n IH]; intros d rest Hd; cbn [repeat app incW].
  - destruct (Nat.eqb_spec d (b - 1)); [lia | reflexivity].
  - rewrite Nat.eqb_refl, IH by exact Hd. reflexivity.
Qed.

Lemma inc_topW : forall n, incW (repeat (b - 1) n) = repeat 0 n ++ [1].
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat incW app].
  rewrite Nat.eqb_refl, IH. reflexivity.
Qed.

Lemma alltop_classW : forall n d rest, d <> b - 1 ->
  alltopW (repeat (b - 1) n ++ d :: rest) = false.
Proof.
  induction n as [|n IH]; intros d rest Hd; cbn [repeat app alltopW forallb].
  - destruct (Nat.eqb_spec (b - 1) d); [lia | reflexivity].
  - rewrite Nat.eqb_refl. apply IH. exact Hd.
Qed.

Hypothesis Hb : 1 < b.

Lemma inc_valW : forall x, Forall (fun d => d < b) x -> alltopW x = false ->
  val_pos b (incW x) = S (val_pos b x).
Proof.
  induction x as [|d t IH]; intros Hx Ht; [discriminate|].
  inversion Hx as [|? ? Hd Htl]; subst.
  cbn [incW alltopW forallb] in *.
  destruct (Nat.eqb_spec d (b - 1)) as [E|E].
  - subst d. rewrite Nat.eqb_refl in Ht. cbn [andb] in Ht.
    cbn [val_pos]. rewrite (IH Htl Ht). nia.
  - cbn [val_pos]. lia.
Qed.

Lemma inc_lenW : forall x, alltopW x = false -> length (incW x) = length x.
Proof.
  induction x as [|d t IH]; intros Ht; [discriminate|]. cbn [incW alltopW forallb] in *.
  destruct (Nat.eqb_spec d (b - 1)) as [E|E].
  - subst d. rewrite Nat.eqb_refl in Ht. cbn [andb] in Ht.
    cbn [length]. rewrite (IH Ht). reflexivity.
  - reflexivity.
Qed.

Lemma inc_bndW : forall x, Forall (fun d => d < b) x ->
  Forall (fun d => d < b) (incW x).
Proof.
  induction x as [|d t IH]; intros Hx; [constructor; [lia | constructor]|].
  inversion Hx as [|? ? Hd Htl]; subst. cbn [incW].
  destruct (Nat.eqb_spec d (b - 1)) as [E|E].
  - constructor; [lia | apply IH; exact Htl].
  - constructor; [lia | exact Htl].
Qed.

Lemma inc_neW : forall x, incW x <> [].
Proof. intros [|d t]; cbn [incW]; [discriminate|]. destruct (d =? b - 1); discriminate. Qed.

(** *** Tops recur *)

Definition MInv (x : list nat) : Prop := Forall (fun d => d < b) x /\ x <> [].

Lemma inc_invW : forall x, MInv x -> MInv (incW x).
Proof. intros x [Hx _]. split; [apply inc_bndW, Hx | apply inc_neW]. Qed.

Lemma iter_invW : forall n x, MInv x -> MInv (iterW x n).
Proof. induction n as [|n IH]; intros x Hx; [exact Hx|]. apply IH, inc_invW, Hx. Qed.

Lemma top_reachedW : forall v x, MInv x ->
  Nat.pow b (length x) - val_pos b x <= v ->
  exists n, alltopW (iterW x n) = true /\ MInv (iterW x n).
Proof.
  induction v as [|v IHv]; intros x Hs Hv.
  - exfalso. pose proof (val_pos_lt b x Hb (proj1 Hs)). lia.
  - destruct (alltopW x) eqn:E.
    + exists 0. cbn [iterW]. auto.
    + destruct (IHv (incW x) (inc_invW x Hs)) as (n & Hn).
      * rewrite (inc_lenW x E), (inc_valW x (proj1 Hs) E). lia.
      * exists (S n). exact Hn.
Qed.

Theorem top_cofinalW : forall x N, MInv x ->
  exists n, N <= n /\ alltopW (iterW x n) = true /\ MInv (iterW x n).
Proof.
  intros x N Hs.
  pose proof (iter_invW N x Hs) as HsN.
  destruct (top_reachedW (Nat.pow b (length (iterW x N)) - val_pos b (iterW x N))
              (iterW x N) HsN (le_n _)) as (n & Hn).
  exists (N + n). rewrite iter_addW. split; [lia | exact Hn].
Qed.

(** *** The cells of each class *)

Lemma mcells_intL : forall t r st n d rest,
  mcellsL (repeat t (r + st * n) ++ d :: rest)
    = sden (flat_map digL rest ++ sufL) n
        (blk (preL ++ rep (digL t) r) (digL t) st (digL d)).
Proof.
  intros t r st n d rest. unfold mcellsL.
  rewrite blk_den, flat_map_app, flat_map_repeatW.
  cbn [flat_map]. rewrite rep_add, !app_assoc. reflexivity.
Qed.

Lemma mcells_intR : forall t r st n d rest,
  mcellsR (repeat t (r + st * n) ++ d :: rest)
    = sden (flat_map digR rest ++ sufR) n
        (blk (preR ++ rep (digR t) r) (digR t) st (digR d)).
Proof.
  intros t r st n d rest. unfold mcellsR.
  rewrite blk_den, flat_map_app, flat_map_repeatW.
  cbn [flat_map]. rewrite rep_add, !app_assoc. reflexivity.
Qed.

Lemma mcells_topL : forall t r st n,
  mcellsL (repeat t (r + st * n))
    = sden [] n (blk (preL ++ rep (digL t) r) (digL t) st sufL).
Proof.
  intros t r st n. unfold mcellsL.
  rewrite blk_den, flat_map_repeatW, rep_add, app_nil_r, !app_assoc. reflexivity.
Qed.

Lemma mcells_topR : forall t r st n,
  mcellsR (repeat t (r + st * n))
    = sden [] n (blk (preR ++ rep (digR t) r) (digR t) st sufR).
Proof.
  intros t r st n. unfold mcellsR.
  rewrite blk_den, flat_map_repeatW, rep_add, app_nil_r, !app_assoc. reflexivity.
Qed.

Lemma mcells_widL : forall r st n,
  mcellsL (repeat 0 (r + st * n) ++ [1])
    = sden [] n (blk (preL ++ rep (digL 0) r) (digL 0) st (digL 1 ++ sufL)).
Proof.
  intros r st n. unfold mcellsL.
  rewrite blk_den, flat_map_app, flat_map_repeatW, rep_add.
  cbn [flat_map]. rewrite !app_nil_r, !app_assoc. reflexivity.
Qed.

Lemma mcells_widR : forall r st n,
  mcellsR (repeat 0 (r + st * n) ++ [1])
    = sden [] n (blk (preR ++ rep (digR 0) r) (digR 0) st (digR 1 ++ sufR)).
Proof.
  intros r st n. unfold mcellsR.
  rewrite blk_den, flat_map_app, flat_map_repeatW, rep_add.
  cbn [flat_map]. rewrite !app_nil_r, !app_assoc. reflexivity.
Qed.

(** The class configurations: one block on each side, one shared index. *)
Definition mconf (l r : sside) : sconf := mkC q l hs r.

Lemma mconf_den : forall l r XL XR n x,
  mcellsL x = sden XL n l -> mcellsR x = sden XR n r ->
  cden XL XR n (mconf l r) = mcfg x.
Proof.
  intros l r XL XR n x HL HR. unfold cden, mconf, mcfg. cbn [c_st c_l c_h c_r].
  rewrite HL, HR. reflexivity.
Qed.

End Mir.

(** *** Halves

    One increment is TWO one-sided programs that meet at a fixed (state,
    symbol) on the anchor cell: the machine finishes one side's carry and is
    back on the anchor cell, with the other side still as it was, before it
    starts the other.  Each half has ONE repeated block (the side it rewrites)
    and treats the other side as an opaque tail, so it is an ordinary
    [ReachL] arm; [halves_reach] composes them through [lift].  [lf] says
    which side goes first. *)

Definition hcL (q : St) (l : sside) (h : Sym) : sconf := mkC q l h (sflat []).
Definition hcR (q : St) (r : sside) (h : Sym) : sconf := mkC q (sflat []) h r.

Definition halfA (lf : bool) (q : St) (h : Sym) (l r : sside) : sconf :=
  if lf then hcL q l h else hcR q r h.
Definition halfB (lf : bool) (q : St) (h : Sym) (l r : sside) : sconf :=
  if lf then hcR q r h else hcL q l h.

Lemma halfA_den : forall (lf : bool) (q : St) (h : Sym) (l r : sside) (XL XR : list Sym) (n : nat) (LL RR : list Sym),
  (if lf then sden XL n l = LL else sden XR n r = RR) ->
  cden (if lf then XL else LL) (if lf then RR else XR) n (halfA lf q h l r) = (q, (LL, h, RR)).
Proof.
  intros [|] q h l r XL XR n LL RR H; unfold halfA, hcL, hcR, cden;
    cbn [c_st c_l c_h c_r]; rewrite sden_flat; cbn [app]; rewrite H; reflexivity.
Qed.

Lemma halfB_den : forall (lf : bool) (q : St) (h : Sym) (l r : sside) (XL XR : list Sym) (n : nat) (LL RR : list Sym),
  (if lf then sden XR n r = RR else sden XL n l = LL) ->
  cden (if lf then LL else XL) (if lf then XR else RR) n (halfB lf q h l r) = (q, (LL, h, RR)).
Proof.
  intros [|] q h l r XL XR n LL RR H; unfold halfB, hcL, hcR, cden;
    cbn [c_st c_l c_h c_r]; rewrite sden_flat; cbn [app]; rewrite H; reflexivity.
Qed.

Lemma halves_reach : forall tm el1 er1 el2 er2 A1 A2 XL1 XR1 XL2 XR2 n,
  ReachL tm el1 er1 (lr_lhs A1) (lr_rhs A1) ->
  (el1 = true -> XL1 = []) -> (er1 = true -> XR1 = []) ->
  ReachL tm el2 er2 (lr_lhs A2) (lr_rhs A2) ->
  (el2 = true -> XL2 = []) -> (er2 = true -> XR2 = []) ->
  cden XL1 XR1 n (lr_rhs A1) = cden XL2 XR2 n (lr_lhs A2) ->
  exists m c'', 0 < m /\ csteps tm m (cden XL1 XR1 n (lr_lhs A1)) = Some c''
                /\ lift c'' = lift (cden XL2 XR2 n (lr_rhs A2)).
Proof.
  intros tm el1 er1 el2 er2 A1 A2 XL1 XR1 XL2 XR2 n H1 HL1 HR1 H2 HL2 HR2 Hmid.
  destruct (H1 XL1 XR1 n HL1 HR1) as (m1 & c1 & Hm1 & Hc1 & Hl1).
  destruct (H2 XL2 XR2 n HL2 HR2) as (m2 & c2 & Hm2 & Hc2 & Hl2).
  assert (Hs : stepn tm (m1 + m2) (lift (cden XL1 XR1 n (lr_lhs A1))) = Some (lift c2)).
  { rewrite stepn_add, (csteps_lift _ _ _ _ Hc1), Hl1, Hmid. apply csteps_lift. exact Hc2. }
  destruct (stepn_csteps_at tm (m1 + m2) _ _ Hs) as (c'' & Hc'' & Hl'').
  exists (m1 + m2), c''. split; [lia|]. split; [exact Hc''|]. rewrite Hl''. exact Hl2.
Qed.

(** ** 2. The board *)

Section BoardMir.

Variable tm0   : TM.
Variable pins  : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable b     : nat.
Variable DL DR : list (list Sym).
Variable preL preR sufL sufR : list Sym.
Variable q     : St.
Variable hs    : Sym.
Variable lf    : bool.                  (** the left side's carry comes first *)
Variable qI qT : St.                    (** where the halves meet: interior, top *)
Variable hI hT : Sym.
Variable AI1 AI2 : nat -> nat -> LRule.   (** interior halves: digit, index *)
Variable N0i sti : nat.
Variable AT1 AT2 : nat -> LRule.          (** top halves: index (the width) *)
Variable N0t stt : nat.
Variable rsv   : list LRule.
Variable vsegs1 vsegs2 : nat -> Instr -> list nseg.
Variable visI1 visI2 : nat -> Instr -> list lstep.
Variable x0    : list nat.

Local Notation dL := (digL DL).
Local Notation dR := (digR DR).

Definition sLt (N0 st d r : nat) (w : list Sym) : sside :=
  blk (preL ++ rep (dL (b - 1)) r) (dL (b - 1)) (astride N0 st r) w.
Definition sRt (N0 st d r : nat) (w : list Sym) : sside :=
  blk (preR ++ rep (dR (b - 1)) r) (dR (b - 1)) (astride N0 st r) w.
Definition sL0 (N0 st r : nat) (w : list Sym) : sside :=
  blk (preL ++ rep (dL 0) r) (dL 0) (astride N0 st r) w.
Definition sR0 (N0 st r : nat) (w : list Sym) : sside :=
  blk (preR ++ rep (dR 0) r) (dR 0) (astride N0 st r) w.

Hypothesis Hb    : 1 < b.
Hypothesis Hinv0 : MInv b x0.

Hypothesis Hsti : 0 < sti.
Hypothesis HAI1S : forall d r, d < b - 1 -> r < N0i + sti ->
  ReachL tm false false (lr_lhs (AI1 d r)) (lr_rhs (AI1 d r)).
Hypothesis HAI2S : forall d r, d < b - 1 -> r < N0i + sti ->
  ReachL tm false false (lr_lhs (AI2 d r)) (lr_rhs (AI2 d r)).
Hypothesis HAI1L : forall d r, d < b - 1 -> r < N0i + sti ->
  lr_lhs (AI1 d r) = halfA lf q hs (sLt N0i sti d r (dL d)) (sRt N0i sti d r (dR d)).
Hypothesis HAI1R : forall d r, d < b - 1 -> r < N0i + sti ->
  lr_rhs (AI1 d r) = halfA lf qI hI (sL0 N0i sti r (dL (S d))) (sR0 N0i sti r (dR (S d))).
Hypothesis HAI2L : forall d r, d < b - 1 -> r < N0i + sti ->
  lr_lhs (AI2 d r) = halfB lf qI hI (sLt N0i sti d r (dL d)) (sRt N0i sti d r (dR d)).
Hypothesis HAI2R : forall d r, d < b - 1 -> r < N0i + sti ->
  lr_rhs (AI2 d r) = halfB lf q hs (sL0 N0i sti r (dL (S d))) (sR0 N0i sti r (dR (S d))).

Hypothesis Hstt : 0 < stt.
Hypothesis HN0t : 0 < N0t.
Hypothesis HAT1S : forall r, 0 < r -> r < N0t + stt ->
  ReachL tm lf (negb lf) (lr_lhs (AT1 r)) (lr_rhs (AT1 r)).
Hypothesis HAT2S : forall r, 0 < r -> r < N0t + stt ->
  ReachL tm (negb lf) lf (lr_lhs (AT2 r)) (lr_rhs (AT2 r)).
Hypothesis HAT1L : forall r, 0 < r -> r < N0t + stt ->
  lr_lhs (AT1 r) = halfA lf q hs (sLt N0t stt 0 r sufL) (sRt N0t stt 0 r sufR).
Hypothesis HAT1R : forall r, 0 < r -> r < N0t + stt ->
  lr_rhs (AT1 r) = halfA lf qT hT (sL0 N0t stt r (dL 1 ++ sufL)) (sR0 N0t stt r (dR 1 ++ sufR)).
Hypothesis HAT2L : forall r, 0 < r -> r < N0t + stt ->
  lr_lhs (AT2 r) = halfB lf qT hT (sLt N0t stt 0 r sufL) (sRt N0t stt 0 r sufR).
Hypothesis HAT2R : forall r, 0 < r -> r < N0t + stt ->
  lr_rhs (AT2 r) = halfB lf q hs (sL0 N0t stt r (dL 1 ++ sufL)) (sR0 N0t stt r (dR 1 ++ sufR)).

Hypothesis Hrsv : Forall (RuleSound tm false false) rsv.
(** each instruction is witnessed in one half of every top arm *)
Hypothesis Hfire : forall t, ~ In t pins ->
  forall r, 0 < r -> r < N0t + stt ->
    nfire tm lf (negb lf) rsv (vsegs1 r t) (visI1 r t) (lr_lhs (AT1 r)) = Some t
    \/ nfire tm (negb lf) lf rsv (vsegs2 r t) (visI2 r t) (lr_lhs (AT2 r)) = Some t.

Local Notation MCF := (mcfg DL DR preL preR sufL sufR q hs).
Local Notation Cf := (fun n => MCF (iterW b x0 n)).

(** The top class at width [j]: its index, block count, and the four
    denotations the two halves meet at. *)
Lemma top_classM : forall x, x = repeat (b - 1) (length x) -> 0 < length x ->
  let j := length x in let r := aoff N0t stt j in let n := acnt N0t stt j in
  0 < r /\ r < N0t + stt
  /\ mcellsL DL preL sufL x = sden [] n (sLt N0t stt 0 r sufL)
  /\ mcellsR DR preR sufR x = sden [] n (sRt N0t stt 0 r sufR)
  /\ mcellsL DL preL sufL (incW b x) = sden [] n (sL0 N0t stt r (dL 1 ++ sufL))
  /\ mcellsR DR preR sufR (incW b x) = sden [] n (sR0 N0t stt r (dR 1 ++ sufR)).
Proof.
  intros x Htop Hj j r n.
  assert (Hr0 : 0 < r) by (apply arm_index_pos; assumption).
  assert (Hrlt : r < N0t + stt) by (apply arm_index_lt; assumption).
  assert (Hk : r + astride N0t stt r * n = j) by (apply arm_index; assumption).
  split; [exact Hr0|]. split; [exact Hrlt|].
  assert (Hx : x = repeat (b - 1) (r + astride N0t stt r * n)) by (rewrite Hk; exact Htop).
  assert (Hx' : incW b x = repeat 0 (r + astride N0t stt r * n) ++ [1]).
  { rewrite Hx, (inc_topW b). reflexivity. }
  rewrite Hx' at 1 2. rewrite Hx at 1 2.
  unfold sLt, sRt, sL0, sR0.
  split; [apply mcells_topL|]. split; [apply mcells_topR|].
  split; [apply mcells_widL | apply mcells_widR].
Qed.

Lemma board_armM : forall x, MInv b x ->
  exists A1 A2 el1 er1 el2 er2 XL1 XR1 XL2 XR2 n,
    ReachL tm el1 er1 (lr_lhs A1) (lr_rhs A1)
    /\ (el1 = true -> XL1 = []) /\ (er1 = true -> XR1 = [])
    /\ ReachL tm el2 er2 (lr_lhs A2) (lr_rhs A2)
    /\ (el2 = true -> XL2 = []) /\ (er2 = true -> XR2 = [])
    /\ MCF x = cden XL1 XR1 n (lr_lhs A1)
    /\ cden XL1 XR1 n (lr_rhs A1) = cden XL2 XR2 n (lr_lhs A2)
    /\ MCF (incW b x) = cden XL2 XR2 n (lr_rhs A2).
Proof.
  intros x [Hx Hne].
  destruct (digs_decomp (b - 1) x) as [Htop | (n & d & rest & Hxe & Hd)].
  - (* the top: both sides widen *)
    assert (Hj : 0 < length x) by (destruct x; [congruence | cbn; lia]).
    destruct (top_classM x Htop Hj) as (Hr0 & Hrlt & HL & HR & HL' & HR').
    set (r := aoff N0t stt (length x)) in *.
    set (k := acnt N0t stt (length x)) in *.
    set (LL := mcellsL DL preL sufL x) in *. set (RR := mcellsR DR preR sufR x) in *.
    set (LL' := mcellsL DL preL sufL (incW b x)) in *.
    set (RR' := mcellsR DR preR sufR (incW b x)) in *.
    exists (AT1 r), (AT2 r), lf, (negb lf), (negb lf), lf,
      (if lf then [] else LL), (if lf then RR else []),
      (if lf then LL' else []), (if lf then [] else RR'), k.
    split; [exact (HAT1S r Hr0 Hrlt)|].
    split; [intros ->; reflexivity|]. split; [destruct lf; [discriminate | reflexivity]|].
    split; [exact (HAT2S r Hr0 Hrlt)|].
    split; [destruct lf; [discriminate | reflexivity]|]. split; [intros ->; reflexivity|].
    split; [|split].
    + rewrite (HAT1L r Hr0 Hrlt). symmetry.
      apply (halfA_den lf q hs _ _ [] [] k LL RR); destruct lf; symmetry; assumption.
    + rewrite (HAT1R r Hr0 Hrlt), (HAT2L r Hr0 Hrlt).
      destruct lf.
      * rewrite (halfA_den true qT hT _ _ [] [] k LL' RR) by (symmetry; assumption).
        rewrite (halfB_den true qT hT _ _ [] [] k LL' RR) by (symmetry; assumption).
        reflexivity.
      * rewrite (halfA_den false qT hT _ _ [] [] k LL RR') by (symmetry; assumption).
        rewrite (halfB_den false qT hT _ _ [] [] k LL RR') by (symmetry; assumption).
        reflexivity.
    + rewrite (HAT2R r Hr0 Hrlt). symmetry.
      destruct lf.
      * apply (halfB_den true q hs _ _ [] [] k LL' RR'); symmetry; assumption.
      * apply (halfB_den false q hs _ _ [] [] k LL' RR'); symmetry; assumption.
  - (* the interior *)
    rewrite Hxe in Hx.
    apply Forall_app in Hx as [_ Hrest'].
    inversion Hrest' as [|? ? Hdb Hrest].
    assert (Hdlt : d < b - 1) by lia.
    remember (aoff N0i sti n) as r eqn:Er.
    assert (Hrlt : r < N0i + sti) by (subst r; apply arm_index_lt; assumption).
    assert (Hn : r + astride N0i sti r * acnt N0i sti n = n)
      by (subst r; apply arm_index; assumption).
    set (k := acnt N0i sti n) in *.
    set (XL := flat_map dL rest ++ sufL). set (XR := flat_map dR rest ++ sufR).
    assert (HxL : mcellsL DL preL sufL x = sden XL k (sLt N0i sti d r (dL d))).
    { rewrite Hxe, <- Hn at 1. apply mcells_intL. }
    assert (HxR : mcellsR DR preR sufR x = sden XR k (sRt N0i sti d r (dR d))).
    { rewrite Hxe, <- Hn at 1. apply mcells_intR. }
    assert (Hx' : incW b x = repeat 0 n ++ S d :: rest)
      by (rewrite Hxe; apply inc_classW; exact Hdlt).
    assert (HxL' : mcellsL DL preL sufL (incW b x) = sden XL k (sL0 N0i sti r (dL (S d)))).
    { rewrite Hx', <- Hn at 1. apply mcells_intL. }
    assert (HxR' : mcellsR DR preR sufR (incW b x) = sden XR k (sR0 N0i sti r (dR (S d)))).
    { rewrite Hx', <- Hn at 1. apply mcells_intR. }
    set (LL := mcellsL DL preL sufL x) in *. set (RR := mcellsR DR preR sufR x) in *.
    set (LL' := mcellsL DL preL sufL (incW b x)) in *.
    set (RR' := mcellsR DR preR sufR (incW b x)) in *.
    exists (AI1 d r), (AI2 d r), false, false, false, false,
      (if lf then XL else LL), (if lf then RR else XR),
      (if lf then LL' else XL), (if lf then XR else RR'), k.
    split; [exact (HAI1S d r Hdlt Hrlt)|].
    split; [discriminate|]. split; [discriminate|].
    split; [exact (HAI2S d r Hdlt Hrlt)|].
    split; [discriminate|]. split; [discriminate|].
    split; [|split].
    + rewrite (HAI1L d r Hdlt Hrlt). symmetry.
      apply (halfA_den lf q hs _ _ XL XR k LL RR); destruct lf; symmetry; assumption.
    + rewrite (HAI1R d r Hdlt Hrlt), (HAI2L d r Hdlt Hrlt).
      destruct lf.
      * rewrite (halfA_den true qI hI _ _ XL XR k LL' RR) by (symmetry; assumption).
        rewrite (halfB_den true qI hI _ _ XL XR k LL' RR) by (symmetry; assumption).
        reflexivity.
      * rewrite (halfA_den false qI hI _ _ XL XR k LL RR') by (symmetry; assumption).
        rewrite (halfB_den false qI hI _ _ XL XR k LL RR') by (symmetry; assumption).
        reflexivity.
    + rewrite (HAI2R d r Hdlt Hrlt). symmetry.
      destruct lf.
      * apply (halfB_den true q hs _ _ XL XR k LL' RR'); symmetry; assumption.
      * apply (halfB_den false q hs _ _ XL XR k LL' RR'); symmetry; assumption.
Qed.

Lemma lapM : forall n, exists m c',
  0 < m /\ csteps tm m (Cf n) = Some c' /\ lift c' = lift (Cf (S n)).
Proof.
  intros n.
  pose proof (iter_invW b Hb n x0 Hinv0) as Hi.
  destruct (board_armM _ Hi)
    as (A1 & A2 & el1 & er1 & el2 & er2 & XL1 & XR1 & XL2 & XR2 & k
        & H1 & HL1 & HR1 & H2 & HL2 & HR2 & Hl & Hmid & Hr).
  destruct (halves_reach tm el1 er1 el2 er2 A1 A2 XL1 XR1 XL2 XR2 k H1 HL1 HR1 H2 HL2 HR2 Hmid)
    as (m & c' & Hm & Hc' & Hlc).
  exists m, c'. split; [exact Hm|]. split.
  - cbn beta. rewrite Hl. exact Hc'.
  - rewrite Hlc, <- Hr. cbn beta.
    replace (S n) with (n + 1) by lia. rewrite iter_addW. reflexivity.
Qed.

Lemma fireM : forall t N, ~ In t pins ->
  exists n k c', N <= n /\ csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t N Hnp.
  destruct (top_cofinalW b Hb x0 N Hinv0) as (n & HN & Htop & Hi).
  exists n.
  set (x := iterW b x0 n) in Htop, Hi |- *.
  destruct (digs_decomp (b - 1) x) as [Hx | (n' & d & rest & Hxe & Hd)].
  2:{ exfalso. rewrite Hxe, (alltop_classW b n' d rest Hd) in Htop. discriminate. }
  assert (Hj : 0 < length x) by (destruct Hi as [_ Hne]; destruct x; [congruence | cbn; lia]).
  destruct (top_classM x Hx Hj) as (Hr0 & Hrlt & HL & HR & HL' & HR').
  set (r := aoff N0t stt (length x)) in *.
  set (k := acnt N0t stt (length x)) in *.
  set (LL := mcellsL DL preL sufL x) in *. set (RR := mcellsR DR preR sufR x) in *.
  set (LL' := mcellsL DL preL sufL (incW b x)) in *.
  set (RR' := mcellsR DR preR sufR (incW b x)) in *.
  assert (Hden : MCF x = cden (if lf then [] else LL) (if lf then RR else []) k (lr_lhs (AT1 r))).
  { rewrite (HAT1L r Hr0 Hrlt). symmetry.
    apply (halfA_den lf q hs _ _ [] [] k LL RR); destruct lf; symmetry; assumption. }
  destruct (Hfire t Hnp r Hr0 Hrlt) as [H1 | H2].
  - destruct (nfire_sound tm lf (negb lf) rsv (vsegs1 r t) (visI1 r t)
                (lr_lhs (AT1 r)) t Hrsv H1 (if lf then [] else LL) (if lf then RR else []) k)
      as (kk & c' & Hc' & Ht).
    + intros ->; reflexivity.
    + destruct lf; [discriminate | reflexivity].
    + exists kk, c'. cbn beta. fold x. rewrite Hden.
      split; [exact HN | split; [exact Hc' | exact Ht]].
  - set (XL2 := if lf then LL' else []). set (XR2 := if lf then [] else RR').
    assert (Hmid : cden (if lf then [] else LL) (if lf then RR else []) k (lr_rhs (AT1 r))
                   = cden XL2 XR2 k (lr_lhs (AT2 r))).
    { rewrite (HAT1R r Hr0 Hrlt), (HAT2L r Hr0 Hrlt). unfold XL2, XR2.
      destruct lf.
      - rewrite (halfA_den true qT hT _ _ [] [] k LL' RR) by (symmetry; assumption).
        rewrite (halfB_den true qT hT _ _ [] [] k LL' RR) by (symmetry; assumption).
        reflexivity.
      - rewrite (halfA_den false qT hT _ _ [] [] k LL RR') by (symmetry; assumption).
        rewrite (halfB_den false qT hT _ _ [] [] k LL RR') by (symmetry; assumption).
        reflexivity. }
    destruct (HAT1S r Hr0 Hrlt (if lf then [] else LL) (if lf then RR else []) k)
      as (m1 & c1 & _ & Hc1 & Hl1).
    { intros ->; reflexivity. }
    { destruct lf; [discriminate | reflexivity]. }
    destruct (nfire_sound tm (negb lf) lf rsv (vsegs2 r t) (visI2 r t)
                (lr_lhs (AT2 r)) t Hrsv H2 XL2 XR2 k) as (kk & c' & Hc' & Ht).
    + unfold XL2. destruct lf; [discriminate | reflexivity].
    + unfold XR2. intros ->; reflexivity.
    + assert (Hs : stepn tm (m1 + kk) (lift (MCF x)) = Some (lift c')).
      { rewrite Hden, stepn_add, (csteps_lift _ _ _ _ Hc1), Hl1, Hmid.
        apply csteps_lift. exact Hc'. }
      destruct (stepn_csteps_at tm (m1 + kk) _ _ Hs) as (c'' & Hc'' & Hl'').
      exists (m1 + kk), c''. cbn beta. fold x.
      split; [exact HN | split; [exact Hc''|]].
      rewrite <- cinstr_lift, Hl'', cinstr_lift. exact Ht.
Qed.

Theorem boardM_neverqhtr : forall t0,
  stepn tm t0 InitES = Some (lift (MCF x0)) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros t0 Hboot.
  apply (glue_neverqhtrN tm0 pins Cf).
  - exists t0. exact Hboot.
  - intros n. destruct (lapM n) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [exact Hl | exact Hm]].
  - intros t Hnp N. exact (fireM t N Hnp).
Qed.

Lemma reachM : forall d n,
  exists Tm, stepn tm Tm (lift (Cf n)) = Some (lift (Cf (n + d))).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (Tm & HT).
    destruct (lapM (n + d)) as (m & c' & _ & Hm & Hl).
    exists (Tm + m). rewrite stepn_add, HT.
    replace (n + S d) with (S (n + d)) by lia.
    rewrite <- Hl. apply csteps_lift. exact Hm.
Qed.

Lemma fire_everyM : forall t, ~ In t pins -> forall n,
  exists k c', csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t Hnp n.
  destruct (fireM t n Hnp) as (m & k & c' & Hm & Hk & Hc').
  destruct (reachM (m - n) n) as (Tm & HT).
  replace (n + (m - n)) with m in HT by lia.
  assert (Hs : stepn tm (Tm + k) (lift (Cf n)) = Some (lift c')).
  { rewrite stepn_add, HT. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (Tm + k) (Cf n) (lift c') Hs) as (c'' & Hc'' & Hl').
  exists (Tm + k), c''. split; [exact Hc''|].
  rewrite <- cinstr_lift, Hl', cinstr_lift. exact Hc'.
Qed.

Theorem boardM_qhtr : forall t0 B,
  stepn tm0 t0 InitES = Some (lift (MCF x0)) ->
  existsb (fun tg => cfires tm0 CTape.c0 t0 tg) pins = true ->
  (t0 <=? B) = true ->
  NonHalt tm0 /\ QHBoundTr B tm0 /\ QuasiHaltsTr tm0.
Proof.
  intros t0 B Hboot Hwit Hle.
  apply (lap_qh_stage tm0 pins (fun p => Cf (Nat.pred (Pos.to_nat p)))
           1%positive t0 B).
  - exact Hboot.
  - intros p _.
    destruct (lapM (Nat.pred (Pos.to_nat p))) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (fire_everyM t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End BoardMir.
