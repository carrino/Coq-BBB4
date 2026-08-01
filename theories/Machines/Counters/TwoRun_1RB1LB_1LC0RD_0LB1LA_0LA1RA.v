(** * TwoRun_1RB1LB_1LC0RD_0LB1LA_0LA1RA: the machine never quasihalts.

    A core row of the residue, and one of the two rows `LADDER_NOFAM.md`
    reads as "a quadratic bouncer with two alternating tape phases" -- i.e.
    NOT a counter.  It is not; it is a bouncer whose ONE side carries TWO
    repeated blocks with DIFFERENT indices, which is the shape every reader
    in this tree is one short of (`docs/MXDYS_INDUCTIVE_RESIDUE.md` section 3:
    "the family, found; the grammar, one piece short").  The grammar piece is
    not needed for a hand board: `WTape.cycR` / `cycL` / `cycLW` already cross
    one repeated block each, and a lap is a CHAIN of them.

    The anchor family, in this file's own notation, is

      Wf a b = (StC, ([S1], S0, S1 :: rep P a ++ rep Q b))
      P = [S0;S1]      Q = [S0;S1;S1;S1;S1]

    and the machine's whole orbit past the boot is the three sweeps

      Wf a b        -->^4                     Uf a b
      Uf (2j+1) b   -->^(22j+14b+36)          Vf (2j+3) b
      Vf (2j+3) b   -->^(22j+14b+48)          Wf (2j+4) b
      Uf (2j+2) b   -->^(22j+14b+35)          Wf (2j+1) (S b)

    (with [Uf], [Vf] the same tape in [StB] at head [S0] resp. [S1]).  Each
    sweep is: a constant prologue, one [cycR] over the [P] block, a constant
    joint, one [cycR] over the [Q] block, the turn, one [cycLW] back over the
    [(S0 S0 S0 S1 S1)] blocks the [Q] pass deposited, and one [cycL] over the
    zeros the [P] pass deposited -- eight pieces, four of them iterated.

    Chaining a [Wf]-to-[Uf], sweep one, sweep two, a second [Wf]-to-[Uf] and
    sweep three gives the lap

      CF k = Wf (2k+1) (k+3)     -->^(108k+275)     CF (k+1)

    which is [LapGlue.glue_neverqh]'s [Hlap] at [p = k+1].  The boot is
    [csteps 229 c0 = CF 0] and the visits are the first four configurations
    of the lap: [StC], [StB], [StD], [StA] at offsets 0, 1, 2, 3.  All four
    transitions of the table are defined, so nothing halts, and every state
    recurs at every anchor -- [NeverQuasiHaltsSt] verbatim.

    Every rule below was differentially validated against the raw simulator
    before any Coq was written: the four unit rules over ALL instantiations
    of their unknown context (left and right, every word up to length 6),
    the eight-piece chain of each sweep over a grid of (j, b), and the lap
    and the boot against a blank-tape replay.

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Counters Require Import WTape LapGlue.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB1LB_1LC0RD_0LB1LA_0LA1RA *)
Definition tm_1RB1LB_1LC0RD_0LB1LA_0LA1RA : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StB
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DR StD
  | StC, S0 => mk S0 DL StB | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S0 DL StA | StD, S1 => mk S1 DR StA end.
Local Notation tm := tm_1RB1LB_1LC0RD_0LB1LA_0LA1RA.

(** ** 0. Repetition algebra the chain needs beyond [WTape]'s own *)

Lemma zsum : forall a b l,
  rep [S0] (a + b) ++ l = rep [S0] a ++ rep [S0] b ++ l.
Proof. intros a b l. rewrite rep_add, <- app_assoc. reflexivity. Qed.

Lemma z1 : forall a l, rep [S0] (a + 1) ++ l = rep [S0] a ++ S0 :: l.
Proof. intros a l. rewrite rep_add, <- app_assoc. reflexivity. Qed.

Lemma z2 : forall a l, rep [S0] (a + 2) ++ l = rep [S0] a ++ S0 :: S0 :: l.
Proof. intros a l. rewrite rep_add, <- app_assoc. reflexivity. Qed.

Lemma rep_rep : forall u n k, rep (rep u n) k = rep u (n * k).
Proof.
  intros u n; induction k as [|k IH]; cbn [rep].
  - rewrite Nat.mul_0_r. reflexivity.
  - rewrite IH, <- rep_add. f_equal. lia.
Qed.

Lemma rep_two : forall u k, rep (u ++ u) k = rep u (2 * k).
Proof.
  intros u k. rewrite <- (rep_rep u 2 k). cbn [rep]. rewrite app_nil_r.
  reflexivity.
Qed.

Local Notation P := [S0; S1].
Local Notation Q := [S0; S1; S1; S1; S1].
Local Notation K := [S0; S0; S0; S1; S1].

(** ** 1. The four unit rules, and their repetition cycles

    Each premise is a WINDOWED run ([wsteps true true]): the head stays
    inside the word shown, so [WTape]'s transport carries it into any
    context. *)

(** [L1]: rightward, one [P P] pair of the low block becomes four zeros. *)
Lemma unitP : forall k L R,
  csteps tm (18 * k) (StD, (L, S1, rep (P ++ P) k ++ R))
  = Some (StD, (rep (rep [S0] 4) k ++ L, S1, R)).
Proof. apply (cycR tm 18 StD S1 (P ++ P) (rep [S0] 4)). reflexivity. Qed.

(** [L2]: rightward, one [Q] block becomes one [K] block. *)
Lemma unitQ : forall k L R,
  csteps tm (9 * k) (StD, (L, S1, rep Q k ++ R))
  = Some (StD, (rep K k ++ L, S1, R)).
Proof. apply (cycR tm 9 StD S1 Q K). reflexivity. Qed.

Lemma unitQ0 : forall k L,
  csteps tm (9 * k) (StD, (L, S1, rep Q k))
  = Some (StD, (rep K k ++ L, S1, [])).
Proof. intros k L. rewrite <- (app_nil_r (rep Q k)). apply unitQ. Qed.

(** [L3]: leftward under the marker [S1], one [K] block becomes one [Q]
    block on the far side (spelled rotated, [S1 :: Q ...] -- [rep_rot]). *)
Lemma unitK : forall k L R,
  csteps tm (5 * k) (StC, ([S1] ++ rep K k ++ L, S1, R))
  = Some (StC, ([S1] ++ L, S1, rep (S1 :: [S0; S1; S1; S1]) k ++ R)).
Proof.
  intros k L R.
  apply (cycLW tm 5 StC S1 [S1] K [] (S1 :: [S0; S1; S1; S1])).
  reflexivity.
Qed.

(** [L4]: leftward, two zeros become one [P] block on the far side. *)
Lemma unitZ : forall k L R,
  csteps tm (2 * k) (StB, (rep [S0; S0] k ++ L, S0, R))
  = Some (StB, (L, S0, rep P k ++ R)).
Proof. apply (cycL tm 2 StB S0 [S0; S0] [] P). reflexivity. Qed.

(** ** 2. The constant joints

    Three of them run off an end of the window and use the one-sided
    transport; the rest are framed on both sides. *)

(** [Wf] to [Uf]: four steps that leave the tape alone. *)
Lemma jWU : forall R,
  csteps tm 4 (StC, ([S1], S0, S1 :: R)) = Some (StB, ([S1], S0, S1 :: R)).
Proof.
  intros R.
  exact (wsteps_frame_l tm 4 StC [S1] S0 [S1] StB [S1] S0 [S1] R eq_refl).
Qed.

(** [Uf]'s prologue: onto the low block, in [StD]. *)
Lemma jU : forall R,
  csteps tm 7 (StB, ([S1], S0, S1 :: R))
  = Some (StD, ([S0; S0; S1], S1, R)).
Proof.
  intros R.
  exact (wsteps_frame_l tm 7 StB [S1] S0 [S1] StD [S0; S0; S1] S1 [] R eq_refl).
Qed.

(** [Vf]'s prologue: the same, one step, from head [S1]. *)
Lemma jV : forall R,
  csteps tm 1 (StB, ([S1], S1, S1 :: R))
  = Some (StD, ([S0; S1], S1, R)).
Proof.
  intros R.
  exact (wsteps_frame_l tm 1 StB [S1] S1 [S1] StD [S0; S1] S1 [] R eq_refl).
Qed.

(** The joint between the two blocks: the last [P] and the first [Q]
    together become seven zeros. *)
Lemma jPQ : forall L R,
  csteps tm 27 (StD, (L, S1, P ++ Q ++ R))
  = Some (StD, (rep [S0] 7 ++ L, S1, R)).
Proof.
  intros L R.
  exact (wsteps_frame tm 27 StD [] S1 (P ++ Q) StD (rep [S0] 7) S1 [] L R
           eq_refl).
Qed.

(** The turn at the right end: the tape's right side is the whole
    half-tape there. *)
Lemma jTurn : forall L,
  csteps tm 3 (StD, (L, S1, [])) = Some (StC, (S1 :: L, S1, [S1])).
Proof.
  intros L.
  exact (wsteps_frame_r tm 3 StD [] S1 [] StC [S1] S1 [S1] L eq_refl).
Qed.

(** After the [K] pass: three zeros go, one whole [Q] block arrives. *)
Lemma jBack : forall L R,
  csteps tm 4 (StC, ([S1; S0; S0; S0] ++ L, S1, S1 :: R))
  = Some (StB, (L, S0, Q ++ R)).
Proof.
  intros L R.
  exact (wsteps_frame tm 4 StC [S1; S0; S0; S0] S1 [S1] StB [] S0 Q L R
           eq_refl).
Qed.

(** The two ends of the zero pass: [Vf] when the zeros run out exactly,
    [Wf] when one is left over. *)
Lemma jV' : forall R,
  csteps tm 3 (StB, ([S1], S0, R)) = Some (StB, ([S1], S1, S1 :: R)).
Proof.
  intros R.
  exact (wsteps_frame_l tm 3 StB [S1] S0 [] StB [S1] S1 [S1] R eq_refl).
Qed.

Lemma jW' : forall L R,
  csteps tm 1 (StB, ([S0] ++ L, S0, R)) = Some (StC, (L, S0, S1 :: R)).
Proof.
  intros L R.
  exact (wsteps_frame tm 1 StB [S0] S0 [] StC [] S0 [S1] L R eq_refl).
Qed.

(** ** 3. The three anchors *)

Definition Wf (a b : nat) : cconf :=
  (StC, ([S1], S0, S1 :: rep P a ++ rep Q b)).
Definition Uf (a b : nat) : cconf :=
  (StB, ([S1], S0, S1 :: rep P a ++ rep Q b)).
Definition Vf (a b : nat) : cconf :=
  (StB, ([S1], S1, S1 :: rep P a ++ rep Q b)).

Lemma chain2 : forall n1 n2 c c1 c2,
  csteps tm n1 c = Some c1 -> csteps tm n2 c1 = Some c2 ->
  csteps tm (n1 + n2) c = Some c2.
Proof. intros. rewrite csteps_add, H. assumption. Qed.

Ltac step_by L := eapply chain2; [apply L|].

(** The two shapes the [rep] algebra has to produce on the fly. *)
Lemma repP_even : forall j, rep P (2 * j) = rep (P ++ P) j.
Proof. intros j. rewrite rep_two. reflexivity. Qed.

Lemma repZ4 : forall j, rep (rep [S0] 4) j = rep [S0] (4 * j).
Proof. intros j. apply rep_rep. Qed.

Lemma repZ2 : forall k, rep [S0; S0] k = rep [S0] (2 * k).
Proof. intros k. apply (rep_dbl S0). Qed.

Lemma repKQ : forall k,
  rep (S1 :: [S0; S1; S1; S1]) k ++ [S1] = S1 :: rep Q k.
Proof.
  intros k. rewrite <- (rep_rot S1 [S0; S1; S1; S1] k). cbn [app].
  reflexivity.
Qed.

(** ** 4. Sweep one: [Uf (2j+1) (S b')  -->  Vf (2j+3) (S b')] *)

Lemma sweep1 : forall j b',
  csteps tm (22 * j + 14 * S b' + 36) (Uf (2 * j + 1) (S b'))
  = Some (Vf (2 * j + 3) (S b')).
Proof.
  intros j b'. unfold Uf, Vf.
  replace (22 * j + 14 * S b' + 36)
    with (7 + (18 * j + (27 + (9 * b' + (3 + (5 * b'
          + (4 + (2 * (2 * j + 3) + 3)))))))) by lia.
  (* the low block, split as [2j] pairs then the odd one *)
  replace (rep P (2 * j + 1) ++ rep Q (S b'))
    with (rep (P ++ P) j ++ (P ++ Q ++ rep Q b')).
  2:{ rewrite (rep_add P (2 * j) 1), repP_even.
      cbn [rep]. rewrite app_nil_r, <- !app_assoc. reflexivity. }
  step_by jU.
  step_by (unitP j [S0; S0; S1] (P ++ Q ++ rep Q b')).
  rewrite repZ4.
  step_by (jPQ (rep [S0] (4 * j) ++ [S0; S0; S1]) (rep Q b')).
  (* the left is now [rep [S0] (4j+9) ++ [S1]] *)
  replace (rep [S0] 7 ++ rep [S0] (4 * j) ++ [S0; S0; S1])
    with (rep [S0] (4 * j + 9) ++ [S1]).
  2:{ replace (4 * j + 9) with (7 + (4 * j + 2)) by lia.
      rewrite (zsum 7 (4 * j + 2) [S1]), (z2 (4 * j) [S1]). reflexivity. }
  step_by (unitQ0 b' (rep [S0] (4 * j + 9) ++ [S1])).
  step_by (jTurn (rep K b' ++ rep [S0] (4 * j + 9) ++ [S1])).
  step_by (unitK b' (rep [S0] (4 * j + 9) ++ [S1]) [S1]).
  (* the right side rotates into [S1 :: rep Q b'] *)
  rewrite (repKQ b').
  (* peel three zeros off the left for [jBack] *)
  replace ([S1] ++ rep [S0] (4 * j + 9) ++ [S1])
    with ([S1; S0; S0; S0] ++ (rep [S0] (4 * j + 6) ++ [S1])).
  2:{ replace (4 * j + 9) with (3 + (4 * j + 6)) by lia.
      rewrite (zsum 3 (4 * j + 6) [S1]). reflexivity. }
  step_by (jBack (rep [S0] (4 * j + 6) ++ [S1]) (rep Q b')).
  replace (rep [S0] (4 * j + 6)) with (rep [S0; S0] (2 * j + 3))
    by (rewrite repZ2; f_equal; lia).
  step_by (unitZ (2 * j + 3) [S1] (Q ++ rep Q b')).
  replace (Q ++ rep Q b') with (rep Q (S b')) by reflexivity.
  apply jV'.
Qed.

(** ** 5. Sweep two: [Vf (2j+3) (S b')  -->  Wf (2j+4) (S b')] *)

Lemma sweep2 : forall j b',
  csteps tm (22 * j + 14 * S b' + 48) (Vf (2 * j + 3) (S b'))
  = Some (Wf (2 * j + 4) (S b')).
Proof.
  intros j b'. unfold Vf, Wf.
  replace (22 * j + 14 * S b' + 48)
    with (1 + (18 * S j + (27 + (9 * b' + (3 + (5 * b'
          + (4 + (2 * (2 * j + 4) + 1)))))))) by lia.
  replace (rep P (2 * j + 3) ++ rep Q (S b'))
    with (rep (P ++ P) (S j) ++ (P ++ Q ++ rep Q b')).
  2:{ replace (2 * j + 3) with (2 * S j + 1) by lia.
      rewrite (rep_add P (2 * S j) 1), repP_even.
      cbn [rep]. rewrite app_nil_r, <- !app_assoc. reflexivity. }
  step_by jV.
  step_by (unitP (S j) [S0; S1] (P ++ Q ++ rep Q b')).
  rewrite repZ4.
  step_by (jPQ (rep [S0] (4 * S j) ++ [S0; S1]) (rep Q b')).
  replace (rep [S0] 7 ++ rep [S0] (4 * S j) ++ [S0; S1])
    with (rep [S0] (4 * j + 12) ++ [S1]).
  2:{ replace (4 * j + 12) with (7 + (4 * S j + 1)) by lia.
      rewrite (zsum 7 (4 * S j + 1) [S1]), (z1 (4 * S j) [S1]).
      reflexivity. }
  step_by (unitQ0 b' (rep [S0] (4 * j + 12) ++ [S1])).
  step_by (jTurn (rep K b' ++ rep [S0] (4 * j + 12) ++ [S1])).
  step_by (unitK b' (rep [S0] (4 * j + 12) ++ [S1]) [S1]).
  rewrite (repKQ b').
  replace ([S1] ++ rep [S0] (4 * j + 12) ++ [S1])
    with ([S1; S0; S0; S0] ++ (rep [S0] (4 * j + 9) ++ [S1])).
  2:{ replace (4 * j + 12) with (3 + (4 * j + 9)) by lia.
      rewrite (zsum 3 (4 * j + 9) [S1]). reflexivity. }
  step_by (jBack (rep [S0] (4 * j + 9) ++ [S1]) (rep Q b')).
  replace (rep [S0] (4 * j + 9) ++ [S1])
    with (rep [S0; S0] (2 * j + 4) ++ ([S0] ++ [S1])).
  2:{ rewrite repZ2.
      replace (4 * j + 9) with (2 * (2 * j + 4) + 1) by lia.
      rewrite (z1 (2 * (2 * j + 4)) [S1]). reflexivity. }
  step_by (unitZ (2 * j + 4) ([S0] ++ [S1]) (Q ++ rep Q b')).
  replace (Q ++ rep Q b') with (rep Q (S b')) by reflexivity.
  apply jW'.
Qed.

(** ** 6. Sweep three: [Uf (2j+2) b  -->  Wf (2j+1) (S b)]

    The low block is EVEN here, so the [jPQ] joint never fires: the [P]
    pass runs straight into the [Q] pass, and the extra [Q] block the lap
    gains is the one the [jBack] joint deposits. *)

Lemma sweep3 : forall j b,
  csteps tm (22 * j + 14 * b + 35) (Uf (2 * j + 2) b)
  = Some (Wf (2 * j + 1) (S b)).
Proof.
  intros j b. unfold Uf, Wf.
  replace (22 * j + 14 * b + 35)
    with (7 + (18 * S j + (9 * b + (3 + (5 * b
          + (4 + (2 * (2 * j + 1) + 1))))))) by lia.
  replace (rep P (2 * j + 2)) with (rep (P ++ P) (S j))
    by (rewrite <- repP_even; f_equal; lia).
  step_by jU.
  step_by (unitP (S j) [S0; S0; S1] (rep Q b)).
  rewrite repZ4.
  replace (rep [S0] (4 * S j) ++ [S0; S0; S1])
    with (rep [S0] (4 * j + 6) ++ [S1]).
  2:{ replace (4 * j + 6) with (4 * S j + 2) by lia.
      rewrite (z2 (4 * S j) [S1]). reflexivity. }
  step_by (unitQ0 b (rep [S0] (4 * j + 6) ++ [S1])).
  step_by (jTurn (rep K b ++ rep [S0] (4 * j + 6) ++ [S1])).
  step_by (unitK b (rep [S0] (4 * j + 6) ++ [S1]) [S1]).
  rewrite (repKQ b).
  replace ([S1] ++ rep [S0] (4 * j + 6) ++ [S1])
    with ([S1; S0; S0; S0] ++ (rep [S0] (4 * j + 3) ++ [S1])).
  2:{ replace (4 * j + 6) with (3 + (4 * j + 3)) by lia.
      rewrite (zsum 3 (4 * j + 3) [S1]). reflexivity. }
  step_by (jBack (rep [S0] (4 * j + 3) ++ [S1]) (rep Q b)).
  replace (rep [S0] (4 * j + 3) ++ [S1])
    with (rep [S0; S0] (2 * j + 1) ++ ([S0] ++ [S1])).
  2:{ rewrite repZ2.
      replace (4 * j + 3) with (2 * (2 * j + 1) + 1) by lia.
      rewrite (z1 (2 * (2 * j + 1)) [S1]). reflexivity. }
  step_by (unitZ (2 * j + 1) ([S0] ++ [S1]) (Q ++ rep Q b)).
  replace (Q ++ rep Q b) with (rep Q (S b)) by reflexivity.
  apply jW'.
Qed.

(** ** 7. The lap *)

Definition CF (k : nat) : cconf := Wf (2 * k + 1) (k + 3).

Lemma lap : forall k, csteps tm (108 * k + 275) (CF k) = Some (CF (S k)).
Proof.
  intros k. unfold CF.
  replace (108 * k + 275)
    with (4 + ((22 * k + 14 * S (k + 2) + 36)
          + ((22 * k + 14 * S (k + 2) + 48)
             + (4 + (22 * S k + 14 * (k + 3) + 35))))) by lia.
  replace (k + 3) with (S (k + 2)) by lia.
  step_by (jWU (rep P (2 * k + 1) ++ rep Q (S (k + 2)))).
  step_by (sweep1 k (k + 2)).
  step_by (sweep2 k (k + 2)).
  replace (Wf (2 * k + 4) (S (k + 2)))
    with (Wf (2 * (S k) + 2) (S (k + 2))) by (f_equal; lia).
  unfold Wf at 1.
  step_by (jWU (rep P (2 * S k + 2) ++ rep Q (S (k + 2)))).
  replace (StB, ([S1], S0, S1 :: rep P (2 * S k + 2) ++ rep Q (S (k + 2))))
    with (Uf (2 * S k + 2) (S (k + 2))) by reflexivity.
  rewrite (sweep3 (S k) (S (k + 2))).
  replace (S (S (k + 2))) with (S k + 3) by lia. reflexivity.
Qed.

(** ** 8. The boot, the visits, and the closer *)

Lemma boot : csteps tm 229 c0 = Some (CF 0).
Proof. vm_compute. reflexivity. Qed.

(** [StC], [StB], [StD], [StA] at offsets 0, 1, 2, 3 of every anchor: the
    head never leaves the anchor's own first two cells, so the run is the
    same computation at every [k]. *)
Lemma visits : forall k q, exists n c,
  csteps tm n (CF k) = Some c /\ fst c = q.
Proof.
  intros k q. unfold CF, Wf.
  set (R := rep P (2 * k + 1) ++ rep Q (k + 3)).
  destruct q.
  - exists 3, (StA, ([], S0, S0 :: S1 :: R)). split; reflexivity.
  - exists 1, (StB, ([], S1, S0 :: S1 :: R)). split; reflexivity.
  - exists 0, (StC, ([S1], S0, S1 :: R)). split; reflexivity.
  - exists 2, (StD, ([S0], S0, S1 :: R)). split; reflexivity.
Qed.

Definition Cfp (p : positive) : cconf := CF (Nat.pred (Pos.to_nat p)).

Theorem nqh_1RB1LB_1LC0RD_0LB1LA_0LA1RA :
  NeverQuasiHaltsSt tm_1RB1LB_1LC0RD_0LB1LA_0LA1RA.
Proof.
  apply (glue_neverqh tm Cfp 1%positive).
  - exists 229. rewrite <- lift_c0. apply csteps_lift.
    unfold Cfp. cbn [Nat.pred Pos.to_nat Pos.iter_op]. apply boot.
  - intros p _. unfold Cfp.
    set (k := Nat.pred (Pos.to_nat p)).
    exists (108 * k + 275), (CF (S k)).
    split; [apply lap|]. split; [|lia].
    f_equal. f_equal. unfold k.
    rewrite Pos2Nat.inj_succ.
    pose proof (Pos2Nat.is_pos p). cbn [Nat.pred]. lia.
  - intros p q _. unfold Cfp. apply visits.
Qed.
