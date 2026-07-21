(** * Double_9: WORK IN PROGRESS foundation for double_counter #9,
    1RB0LC_1RC0RD_1LA0LC_1RD0RA.

    (cert results/counter9.cert: type double_counter, edge state D,
    gen comb (1 0), side R, kg = 2^j - 1, acc = 3j, doubling
    kg -> 2kg+1, acc -> acc+3.)

    #9 doubles the (10)-comb by driving a REFLECTED GRAY-CODE counter:
    the i-th left-edge turnaround config is

      f_i = (StA, ([], S0, rep [S1;S0] (kg+1+i) ++ gray_region(kg-i, j)))
      gray_region(v,j) = [S0] ++ concat_{s<j} [bit_s(G v); S0; S0] ++ [S1]

    with G v = v xor (v>>1); consecutive f_i differ by ONE gray-bit
    flip (validated: tools/counters/lap9.py, ALL OK j=2..6, step totals
    125/445/1661/6397/25085 vs raw).  The macro lap D9(j) -> D9(j+1)
    chains kg mini-laps (one gray step each) via [CReach.creach_iter];
    each mini-lap is a Gray_19-style comb crossing + cview-slot flip.

    THIS FILE carries the machine-checked FOUNDATION -- the TM, the
    anchor, the two comb translated-cycle units and their transported
    phases, the right-edge visit units, and the bootstrap -- all
    reflexivity/vm_compute.  The lap (creach_iter over the gray
    mini-laps) + the theorem remain: see the "double track" section of
    NEXT_SESSION.md for the full plan and the Gray_19.v template. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue DblCounter CReach.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB0LC_1RC0RD_1LA0LC_1RD0RA *)
Definition tm_9 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StC
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S0 DR StD
  | StC, S0 => mk S1 DL StA | StC, S1 => mk S0 DL StC
  | StD, S0 => mk S1 DR StD | StD, S1 => mk S0 DR StA
  end.

(** ** The anchor family

    D9(j) = (10)^kg 1^acc, head on the rightmost 1, state D, right
    half-tape blank.  In cconf the left list is the reversal of
    (10)^kg 1^(acc-1): 1^(acc-1) then (01)^kg. *)
Definition D9 (j : nat) : cconf :=
  (StD, (rep [S1] (3 * j - 1) ++ rep [S0; S1] (2 ^ j - 1), S1, [])).

(** ** The two comb translated-cycle units (validated: probe9.py) *)

(** Collapse (leftward): one comb unit [0;1] read from the left is
    rewritten [1;0] and deposited under the head, state/head fixed. *)
Lemma Ucol : wsteps true true tm_9 2 (StA, ([S0; S1], S1, []))
             = Some (StA, ([], S1, [S1; S0])).
Proof. reflexivity. Qed.

(** Spread (rightward): two comb units [0;1;0;1] are crossed in 4
    steps, deposited [1;0;1;0] on the left (comb shifts one cell). *)
Lemma Uspr : wsteps true true tm_9 4 (StB, ([], S1, [S0; S1; S0; S1]))
             = Some (StB, ([S1; S0; S1; S0], S1, [])).
Proof. reflexivity. Qed.

(** ** Right-edge visit / poke units (from the anchor head) *)

(** From the anchor's head [(D, _, S1, [])] the doubling starts:
    D1 = 0RA pokes right into the blank, visiting A, B, C. *)
Lemma UvA : wsteps true false tm_9 1 (StD, ([], S1, []))
            = Some (StA, ([S0], S0, [])).
Proof. reflexivity. Qed.

Lemma UvB : wsteps true false tm_9 2 (StD, ([], S1, []))
            = Some (StB, ([S1; S0], S0, [])).
Proof. reflexivity. Qed.

Lemma UvC : wsteps true false tm_9 3 (StD, ([], S1, []))
            = Some (StC, ([S1; S1; S0], S0, [])).
Proof. reflexivity. Qed.

(** ** Transported phases (the [rep]-cycle forms the lap chains) *)

Lemma phUcol : forall k L R,
  csteps tm_9 (2 * k) (StA, (rep [S0; S1] k ++ L, S1, R))
  = Some (StA, (L, S1, rep [S1; S0] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ Ucol k L R) as H.
  cbn [app] in H. exact H.
Qed.

Lemma phUspr : forall k L R,
  csteps tm_9 (4 * k) (StB, (L, S1, rep [S0; S1; S0; S1] k ++ R))
  = Some (StB, (rep [S1; S0; S1; S0] k ++ L, S1, R)).
Proof. intros. exact (cycR _ _ _ _ _ _ Uspr k L R). Qed.

Lemma phUvA : forall L,
  csteps tm_9 1 (StD, (L, S1, [])) = Some (StA, (S0 :: L, S0, [])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L UvA). Qed.

Lemma phUvB : forall L,
  csteps tm_9 2 (StD, (L, S1, [])) = Some (StB, (S1 :: S0 :: L, S0, [])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L UvB). Qed.

Lemma phUvC : forall L,
  csteps tm_9 3 (StD, (L, S1, [])) = Some (StC, (S1 :: S1 :: S0 :: L, S0, [])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L UvC). Qed.

(** ** Bootstrap: the blank tape reaches D9(2) in 47 steps. *)
Lemma boot_9 : exists t0, stepn tm_9 t0 InitES = Some (lift (D9 2)).
Proof.
  exists 47.
  assert (H : match csteps tm_9 47 c0 with
              | Some c => ceqb c (D9 2)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_9 47 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits: from any anchor D9(j) every state is reached (offsets
    0/1/2/3), independent of the counter -- the head pokes right into
    the blank frontier. *)
Lemma vis_9 : forall j q, exists k c, csteps tm_9 k (D9 j) = Some c /\ fst c = q.
Proof.
  intros j q. unfold D9. destruct q.
  - exists 1. eexists. split; [apply phUvA | reflexivity].
  - exists 2. eexists. split; [apply phUvB | reflexivity].
  - exists 3. eexists. split; [apply phUvC | reflexivity].
  - exists 0. eexists. split; reflexivity.
Qed.

(** ** Comb algebra: [(1 0)] pairs regroup into 4-cell spread units. *)

Lemma rep4_10 : forall k, rep [S1; S0] (2 * k) = rep [S1; S0; S1; S0] k.
Proof.
  induction k.
  - reflexivity.
  - replace (2 * S k) with (S (S (2 * k))) by lia.
    cbn [rep]. rewrite IHk. reflexivity.
Qed.

Lemma rep4_01 : forall k, rep [S0; S1] (2 * k) = rep [S0; S1; S0; S1] k.
Proof.
  induction k.
  - reflexivity.
  - replace (2 * S k) with (S (S (2 * k))) by lia.
    cbn [rep]. rewrite IHk. reflexivity.
Qed.

(** ** The mini-lap unit runs (windowed, each by [reflexivity]) *)

(** Spread (rightward, entry [A] head [S0] = the frontier blank): two
    comb units are crossed in 4 steps, the frontier fills. *)
Lemma Uspr9 : wsteps true true tm_9 4 (StA, ([], S0, [S1; S0; S1; S0]))
              = Some (StA, ([S0; S1; S0; S1], S0, [])).
Proof. reflexivity. Qed.

(** Materialize: the left-edge blank turns into the new comb prefix. *)
Lemma Umat9 : wsteps false true tm_9 2 (StA, ([], S1, []))
              = Some (StA, ([], S0, [S1; S0])).
Proof. reflexivity. Qed.

(** Enter (even case): frontier fill + clear the leftover comb 1. *)
Lemma Uenter9 : wsteps true true tm_9 2 (StA, ([], S0, [S1; S0]))
                = Some (StD, ([S0; S1], S0, [])).
Proof. reflexivity. Qed.

(** D-fill: one empty slot cell filled per step (rightward). *)
Lemma UDf9 : wsteps true true tm_9 1 (StD, ([], S0, [S0]))
             = Some (StD, ([S1], S0, [])).
Proof. reflexivity. Qed.

(** Flip approach at the marker: [D0 D1 A0 B0] reach the flip cell. *)
Lemma Ufapp1 : wsteps true true tm_9 4 (StD, ([], S0, [S1; S0; S0; S1]))
               = Some (StC, ([S1; S1; S0; S1], S1, [])).
Proof. reflexivity. Qed.

Lemma Ufapp0 : wsteps true true tm_9 4 (StD, ([], S0, [S1; S0; S0; S0]))
               = Some (StC, ([S1; S1; S0; S1], S0, [])).
Proof. reflexivity. Qed.

(** Flip prefix (clear / set), 4 steps, into the D-fill 1-run. *)
Lemma UfpreC : wsteps true true tm_9 4 (StC, ([S1; S1; S0; S1], S1, []))
               = Some (StA, ([], S1, [S1; S0; S0; S0])).
Proof. reflexivity. Qed.

Lemma UfpreS : wsteps true true tm_9 4 (StC, ([S1; S1; S0; S1], S0, []))
               = Some (StA, ([], S1, [S1; S0; S0; S1])).
Proof. reflexivity. Qed.

(** D-fill clear boundary: [A1] then the [C1] clear cycle, then [C1 C0]. *)
Lemma UdA1 : wsteps true true tm_9 1 (StA, ([S1], S1, []))
             = Some (StC, ([], S1, [S0])).
Proof. reflexivity. Qed.

Lemma UDclr : wsteps true true tm_9 1 (StC, ([S1], S1, []))
              = Some (StC, ([], S1, [S0])).
Proof. reflexivity. Qed.

Lemma UdC1C0 : wsteps true true tm_9 2 (StC, ([S0; S1], S1, []))
              = Some (StA, ([], S1, [S1; S0])).
Proof. reflexivity. Qed.

(** Odd flip at slot 0 (both slot-0 bit values), 6 steps. *)
Lemma UflipO0 : wsteps true true tm_9 6 (StA, ([S0; S1], S0, [S0; S0; S0; S0]))
                = Some (StA, ([], S1, [S1; S0; S0; S1; S0; S0])).
Proof. reflexivity. Qed.

Lemma UflipO1 : wsteps true true tm_9 6 (StA, ([S0; S1], S0, [S0; S1; S0; S0]))
                = Some (StA, ([], S1, [S1; S0; S0; S0; S0; S0])).
Proof. reflexivity. Qed.

(** ** Transported phases *)

(** Spread over [2*k] comb units (entry [A] head [S0]). *)
Lemma phSpr9 : forall k L R,
  csteps tm_9 (4 * k) (StA, (L, S0, rep [S1; S0] (2 * k) ++ R))
  = Some (StA, (rep [S0; S1] (2 * k) ++ L, S0, R)).
Proof.
  intros. rewrite rep4_10, rep4_01.
  exact (cycR _ _ _ _ _ _ Uspr9 k L R).
Qed.

(** D-fill over [k] empty cells (entry [D] head [S0]). *)
Lemma phDf9 : forall k L R,
  csteps tm_9 k (StD, (L, S0, rep [S0] k ++ R))
  = Some (StD, (rep [S1] k ++ L, S0, R)).
Proof.
  intros. pose proof (cycR _ _ _ _ _ _ UDf9 k L R) as H.
  rewrite Nat.mul_1_l in H. exact H.
Qed.

(** D-fill 1-run clear over [k] cells (entry [C] head [S1]). *)
Lemma phDclr9 : forall k L R,
  csteps tm_9 k (StC, (rep [S1] k ++ L, S1, R))
  = Some (StC, (L, S1, rep [S0] k ++ R)).
Proof.
  intros. pose proof (cycL _ _ _ _ _ _ _ UDclr k L R) as H.
  rewrite Nat.mul_1_l in H. cbn [app] in H. exact H.
Qed.

Lemma phMat9 : forall R,
  csteps tm_9 2 (StA, ([], S1, R)) = Some (StA, ([], S0, [S1; S0] ++ R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R Umat9). Qed.

Lemma phEnter9 : forall L R,
  csteps tm_9 2 (StA, (L, S0, [S1; S0] ++ R))
  = Some (StD, ([S0; S1] ++ L, S0, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R Uenter9). Qed.

Lemma phFapp1 : forall L R,
  csteps tm_9 4 (StD, (L, S0, [S1; S0; S0; S1] ++ R))
  = Some (StC, ([S1; S1; S0; S1] ++ L, S1, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R Ufapp1). Qed.

Lemma phFapp0 : forall L R,
  csteps tm_9 4 (StD, (L, S0, [S1; S0; S0; S0] ++ R))
  = Some (StC, ([S1; S1; S0; S1] ++ L, S0, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R Ufapp0). Qed.

Lemma phFpreC : forall L R,
  csteps tm_9 4 (StC, ([S1; S1; S0; S1] ++ L, S1, R))
  = Some (StA, (L, S1, [S1; S0; S0; S0] ++ R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UfpreC). Qed.

Lemma phFpreS : forall L R,
  csteps tm_9 4 (StC, ([S1; S1; S0; S1] ++ L, S0, R))
  = Some (StA, (L, S1, [S1; S0; S0; S1] ++ R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UfpreS). Qed.

Lemma phdA1 : forall L R,
  csteps tm_9 1 (StA, ([S1] ++ L, S1, R))
  = Some (StC, (L, S1, [S0] ++ R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UdA1). Qed.

Lemma phdC1C0 : forall L R,
  csteps tm_9 2 (StC, ([S0; S1] ++ L, S1, R))
  = Some (StA, (L, S1, [S1; S0] ++ R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UdC1C0). Qed.

Lemma phFlipO0 : forall L R,
  csteps tm_9 6 (StA, ([S0; S1] ++ L, S0, [S0; S0; S0; S0] ++ R))
  = Some (StA, (L, S1, [S1; S0; S0; S1; S0; S0] ++ R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UflipO0). Qed.

Lemma phFlipO1 : forall L R,
  csteps tm_9 6 (StA, ([S0; S1] ++ L, S0, [S0; S1; S0; S0] ++ R))
  = Some (StA, (L, S1, [S1; S0; S0; S0; S0; S0] ++ R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UflipO1). Qed.
