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

(** ** The mini-lap: one gray-decrement step (creach). *)

Definition g9 (j n w : nat) : cconf :=
  (StA, ([], S0, rep [S1; S0] n ++ grr w j)).

(* comb split/fold helpers *)
Lemma rep_split1 : forall (u : list Sym) a,
  rep u (2 * S a) = u ++ rep u (2 * a + 1).
Proof. intros. replace (2 * S a) with (S (2 * a + 1)) by lia. reflexivity. Qed.

Lemma rep_fold1 : forall (u : list Sym) a,
  rep u (2 * a + 1) ++ u = rep u (2 * S a).
Proof.
  intros. rewrite rep_shift.
  replace (2 * S a) with (S (2 * a + 1)) by lia. reflexivity.
Qed.

Lemma minilap9_odd : forall j' n q,
  0 < n -> Nat.even n = true ->
  creach tm_9 (g9 (S j') n (S (2 * q))) (g9 (S j') (S n) (2 * q)).
Proof.
  intros j' n q Hn Hne.
  apply Nat.even_spec in Hne. destruct Hne as [cc Hcc].
  destruct cc as [| m]; [lia |].
  subst n. clear Hn.
  unfold g9.
  destruct (grr_odd q j') as [Godd Gev].
  rewrite Godd, Gev.
  set (TAIL := slotsf (gbn q j') ++ [S1]).
  eapply creach_csteps.
  (* Phase 1: spread over the whole comb *)
  eapply csteps_chain.
  { apply (phSpr9 (S m)). }
  rewrite app_nil_r.
  rewrite (rep_split1 [S0; S1] m).
  (* now L = [S0;S1] ++ rep[S0;S1](2m+1); flip on the slot-0 bit *)
  destruct (Nat.odd q) eqn:Hq; cbn [negb].
  - (* odd q = true: slot0 bit S0 (set to S1) -> phFlipO0 *)
    eapply csteps_chain.
    { apply (phFlipO0 (rep [S0; S1] (2 * m + 1)) TAIL). }
    (* Phase 3: collapse *)
    rewrite <- (app_nil_r (rep [S0; S1] (2 * m + 1))).
    eapply csteps_chain.
    { apply (phUcol (2 * m + 1) []). }
    (* fold rep[S1;S0](2m+1) ++ [S1;S0] and materialize *)
    change ([S1;S0;S0;S1;S0;S0] ++ TAIL)
      with ([S1;S0] ++ ([S0;S1;S0;S0] ++ TAIL)).
    rewrite (app_assoc (rep [S1;S0] (2*m+1)) [S1;S0]).
    rewrite (rep_fold1 [S1;S0] m).
    apply phMat9.
  - (* odd q = false: slot0 bit S1 (clear to S0) -> phFlipO1 *)
    eapply csteps_chain.
    { apply (phFlipO1 (rep [S0; S1] (2 * m + 1)) TAIL). }
    rewrite <- (app_nil_r (rep [S0; S1] (2 * m + 1))).
    eapply csteps_chain.
    { apply (phUcol (2 * m + 1) []). }
    change ([S1;S0;S0;S0;S0;S0] ++ TAIL)
      with ([S1;S0] ++ ([S0;S0;S0;S0] ++ TAIL)).
    rewrite (app_assoc (rep [S1;S0] (2*m+1)) [S1;S0]).
    rewrite (rep_fold1 [S1;S0] m).
    apply phMat9.
Qed.

Lemma rep_snoc : forall (u : list Sym) k, rep u (S k) = rep u k ++ u.
Proof. intros. cbn [rep]. symmetry. apply rep_shift. Qed.

Lemma rep000 : forall k, rep [S0; S0; S0] k = rep [S0] (3 * k).
Proof.
  induction k.
  - reflexivity.
  - replace (3 * S k) with (S (S (S (3 * k)))) by lia.
    cbn [rep]. rewrite IHk. reflexivity.
Qed.

Lemma grr_even_df : forall r u j, Nat.odd u = true ->
  grr (2 ^ S r * u) (S r + S j)
  = rep [S0] (S (3 * r)) ++ S1 :: S0 :: S0
      :: (if Nat.odd (Nat.div2 u) then S0 else S1) :: S0 :: S0
      :: slotsf (gbn (Nat.div2 u) j) ++ [S1].
Proof.
  intros r u j Hu. rewrite grr_even_flip by exact Hu.
  rewrite rep000. reflexivity.
Qed.

Lemma even_fold : forall cc r (X : list Sym),
  [S1; S0] ++ (rep [S1; S0] (2 * cc) ++ [S1; S0] ++ rep [S0] (3 * r) ++ [S0] ++ X)
  = rep [S1; S0] (S (S (2 * cc))) ++ S0 :: rep [S0] (3 * r) ++ X.
Proof.
  intros cc r X.
  rewrite (app_assoc (rep [S1;S0] (2*cc)) [S1;S0]).
  rewrite <- (rep_snoc [S1;S0] (2*cc)).
  rewrite (app_assoc [S1;S0] (rep [S1;S0] (S (2*cc)))).
  change ([S1;S0] ++ rep [S1;S0] (S (2*cc))) with (rep [S1;S0] (S (S (2*cc)))).
  f_equal. symmetry. apply rep_slide.
Qed.

Lemma minilap9_even : forall r j'' n u,
  0 < n -> Nat.odd n = true -> Nat.odd u = true ->
  creach tm_9 (g9 (S r + S j'') n (2 ^ S r * u))
              (g9 (S r + S j'') (S n) (2 ^ S r * u - 1)).
Proof.
  intros r j'' n u Hn Hnodd Hu.
  set (cc := Nat.div2 n).
  assert (Hnc : n = S (2 * cc)).
  { unfold cc. rewrite (Nat.div2_odd n) at 1. rewrite Hnodd. cbn [Nat.b2n]. lia. }
  set (FB := Nat.odd (Nat.div2 u)).
  set (MTAIL := slotsf (gbn (Nat.div2 u) j'') ++ [S1]).
  unfold g9.
  rewrite grr_even_df by exact Hu.
  rewrite (grr_even_pred r u j'' Hu).
  fold FB MTAIL.
  rewrite Hnc.
  (* comb: rep[S1;S0](S(2cc)) = rep[S1;S0](2cc) ++ [S1;S0] *)
  rewrite (rep_snoc [S1; S0] (2 * cc)).
  rewrite <- app_assoc.
  eapply creach_csteps.
  (* Phase 1: spread over 2cc units *)
  eapply csteps_chain.
  { apply (phSpr9 cc []). }
  rewrite app_nil_r.
  (* Phase 2: enter (frontier + clear leftover comb) *)
  eapply csteps_chain.
  { apply phEnter9. }
  (* Phase 3: D-fill *)
  eapply csteps_chain.
  { apply (phDf9 (S (3 * r))). }
  destruct FB eqn:HFB.
  - (* FB = true: flip cell S0 (set) *)
    eapply csteps_chain. { apply phFapp0. }
    eapply csteps_chain. { apply phFpreS. }
    eapply csteps_chain. { apply phdA1. }
    eapply csteps_chain. { apply (phDclr9 (3 * r)). }
    eapply csteps_chain. { apply phdC1C0. }
    rewrite <- (app_nil_r (rep [S0; S1] (2 * cc))).
    eapply csteps_chain. { apply (phUcol (2 * cc) []). }
    rewrite rep000. rewrite <- even_fold. apply phMat9.
  - (* FB = false: flip cell S1 (clear) *)
    eapply csteps_chain. { apply phFapp1. }
    eapply csteps_chain. { apply phFpreC. }
    eapply csteps_chain. { apply phdA1. }
    eapply csteps_chain. { apply (phDclr9 (3 * r)). }
    eapply csteps_chain. { apply phdC1C0. }
    rewrite <- (app_nil_r (rep [S0; S1] (2 * cc))).
    eapply csteps_chain. { apply (phUcol (2 * cc) []). }
    rewrite rep000. rewrite <- even_fold. apply phMat9.
Qed.

Lemma minilap9 : forall j n w,
  0 < n -> 0 < w -> w < 2 ^ j -> Nat.odd (n + w) = true ->
  creach tm_9 (g9 j n w) (g9 j (S n) (w - 1)).
Proof.
  intros j n w Hn Hw Hwj Hpar.
  destruct (factor2 w Hw) as (r & u & Hu & Hwru).
  destruct r as [| r'].
  - (* w = u odd *)
    rewrite Nat.pow_0_r, Nat.mul_1_l in Hwru.
    destruct j as [| j']; [cbn in Hwj; lia |].
    set (q := Nat.div2 u).
    assert (Hw2 : w = S (2 * q)).
    { subst w. unfold q. rewrite (Nat.div2_odd u) at 1. rewrite Hu.
      cbn [Nat.b2n]. lia. }
    assert (Hne : Nat.even n = true).
    { rewrite Nat.odd_add in Hpar. rewrite Hw2 in Hpar.
      rewrite Nat.odd_succ in Hpar.
      replace (Nat.even (2 * q)) with true in Hpar
        by (symmetry; rewrite Nat.even_mul; reflexivity).
      rewrite xorb_true_r in Hpar. apply negb_true_iff in Hpar.
      rewrite <- Nat.negb_odd. rewrite Hpar. reflexivity. }
    rewrite Hw2. replace (S (2 * q) - 1) with (2 * q) by lia.
    apply minilap9_odd; assumption.
  - (* w = 2^(S r') * u, even *)
    assert (Hle : 2 ^ S r' <= w).
    { rewrite Hwru. assert (1 <= u) by (destruct u; [discriminate Hu | lia]).
      assert (2 ^ S r' <> 0) by (apply Nat.pow_nonzero; lia). nia. }
    assert (Hlt : S r' < j).
    { destruct (le_lt_dec j (S r')) as [Hc | Hc]; [| exact Hc].
      assert (2 ^ j <= 2 ^ S r') by (apply Nat.pow_le_mono_r; lia). lia. }
    assert (Hj : exists j'', j = S r' + S j'') by (exists (j - S (S r')); lia).
    destruct Hj as (j'' & Hj). subst j.
    assert (Hno : Nat.odd n = true).
    { rewrite Nat.odd_add in Hpar.
      assert (Hwe : Nat.odd w = false).
      { rewrite Hwru, Nat.pow_succ_r', <- Nat.mul_assoc, Nat.odd_mul.
        reflexivity. }
      rewrite Hwe, xorb_false_r in Hpar. exact Hpar. }
    rewrite Hwru. apply minilap9_even; assumption.
Qed.

(** ** The macro lap: poke prefix + creach_iter + final spread. *)

(** grr of the all-ones counter [2^j - 1]: a single marker at slot j-1. *)
Lemma gbn_allones : forall j',
  gbn (2 ^ S j' - 1) (S j') = repeat false j' ++ [true].
Proof.
  induction j' as [| k IH].
  - reflexivity.
  - assert (Hq : 2 ^ S (S k) - 1 = S (2 * (2 ^ S k - 1))).
    { rewrite (Nat.pow_succ_r' 2 (S k)).
      assert (0 < 2 ^ S k) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia). lia. }
    rewrite Hq. rewrite gbn_odd_hd.
    assert (Hoq : Nat.odd (2 ^ S k - 1) = true).
    { assert (He : Nat.even (2 ^ S k) = true)
        by (rewrite (Nat.pow_succ_r' 2 k), Nat.even_mul; reflexivity).
      assert (0 < 2 ^ S k) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
      rewrite <- Nat.negb_odd in He. apply negb_true_iff in He.
      replace (2 ^ S k) with (S (2 ^ S k - 1)) in He by lia.
      rewrite Nat.odd_succ, <- Nat.negb_odd in He.
      apply negb_false_iff in He. exact He. }
    rewrite Hoq. cbn [negb]. rewrite IH. reflexivity.
Qed.

Lemma grr_kg : forall j',
  grr (2 ^ S j' - 1) (S j')
  = rep [S0] (S (3 * j')) ++ [S1; S0; S0; S1].
Proof.
  intros j'. unfold grr. rewrite gbn_allones.
  rewrite slotsf_app, slotsf_repeat_false. cbn [slotsf].
  rewrite rep000, <- app_assoc. reflexivity.
Qed.

(** New poke units. *)
Lemma Upokein : wsteps true false tm_9 3 (StD, ([], S1, []))
                = Some (StC, ([S1; S1; S0], S0, [])).
Proof. reflexivity. Qed.

Lemma Upseed : wsteps true true tm_9 4 (StC, ([S1; S1; S0; S1], S0, []))
               = Some (StA, ([], S1, [S1; S0; S0; S1])).
Proof. reflexivity. Qed.

Lemma Ufin : wsteps true false tm_9 1 (StD, ([], S0, [S1]))
             = Some (StD, ([S1], S1, [])).
Proof. reflexivity. Qed.

Lemma phPokein : forall L,
  csteps tm_9 3 (StD, (L, S1, [])) = Some (StC, ([S1; S1; S0] ++ L, S0, [])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L Upokein). Qed.

Lemma phPseed : forall M R,
  csteps tm_9 4 (StC, ([S1; S1; S0; S1] ++ M, S0, R))
  = Some (StA, (M, S1, [S1; S0; S0; S1] ++ R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ M R Upseed). Qed.

Lemma phFin : forall L,
  csteps tm_9 1 (StD, (L, S0, [S1])) = Some (StD, ([S1] ++ L, S1, [])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L Ufin). Qed.

Lemma grr_zero : forall j, grr 0 j = rep [S0] (S (3 * j)) ++ [S1].
Proof.
  intros j. unfold grr.
  assert (Hg : gbn 0 j = repeat false j).
  { clear. induction j; [reflexivity | simpl; rewrite IHj; reflexivity]. }
  rewrite Hg, slotsf_repeat_false, rep000. reflexivity.
Qed.

Lemma poke_fold : forall b a,
  [S1;S0] ++ rep [S1;S0] b ++ [S1;S0] ++ rep [S0] a ++ [S0;S1;S0;S0;S1]
  = rep [S1;S0] (S (S b)) ++ rep [S0] (S a) ++ [S1;S0;S0;S1].
Proof.
  intros b a.
  rewrite (app_assoc (rep [S1;S0] b) [S1;S0]).
  rewrite <- (rep_snoc [S1;S0] b).
  rewrite (app_assoc [S1;S0] (rep [S1;S0] (S b))).
  change ([S1;S0] ++ rep [S1;S0] (S b)) with (rep [S1;S0] (S (S b))).
  f_equal.
  rewrite (rep_snoc [S0] a). rewrite <- app_assoc. reflexivity.
Qed.

Lemma poke9 : forall j, 1 <= j ->
  exists n, csteps tm_9 n (D9 j) = Some (g9 j (2 ^ j) (2 ^ j - 1)) /\ 0 < n.
Proof.
  intros j Hj. destruct j as [| j']; [lia |].
  assert (Hp2 : 2 <= 2 ^ S j').
  { rewrite Nat.pow_succ_r'.
    assert (0 < 2 ^ j') by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia). lia. }
  set (b := 2 ^ S j' - 2).
  assert (Hb : 2 ^ S j' = S (S b)) by (unfold b; lia).
  unfold D9, g9.
  rewrite grr_kg, Hb.
  replace (3 * S j' - 1) with (S (S (3 * j'))) by lia.
  replace (S (S b) - 1) with (S b) by lia.
  eexists. split.
  - eapply csteps_chain. { apply phPokein. }
    eapply csteps_chain. { apply phPseed. }
    eapply csteps_chain. { apply phdA1. }
    eapply csteps_chain. { apply (phDclr9 (3 * j')). }
    change (rep [S0;S1] (S b)) with ([S0;S1] ++ rep [S0;S1] b).
    eapply csteps_chain. { apply phdC1C0. }
    rewrite <- (app_nil_r (rep [S0;S1] b)).
    eapply csteps_chain. { apply (phUcol b []). }
    rewrite <- (poke_fold b (3 * j')).
    apply phMat9.
  - lia.
Qed.

Lemma odd_pow2_pred : forall k, Nat.odd (2 ^ S k - 1) = true.
Proof.
  intros k.
  assert (He : Nat.even (2 ^ S k) = true)
    by (rewrite (Nat.pow_succ_r' 2 k), Nat.even_mul; reflexivity).
  assert (0 < 2 ^ S k) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  rewrite <- Nat.negb_odd in He. apply negb_true_iff in He.
  replace (2 ^ S k) with (S (2 ^ S k - 1)) in He by lia.
  rewrite Nat.odd_succ, <- Nat.negb_odd in He.
  apply negb_false_iff in He. exact He.
Qed.

Lemma final9 : forall j, 1 <= j ->
  creach tm_9 (g9 j (2 ^ S j - 1) 0) (D9 (S j)).
Proof.
  intros j Hj.
  assert (Hp : 0 < 2 ^ j) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  unfold g9, D9. rewrite grr_zero.
  replace (2 ^ S j - 1) with (S (2 * (2 ^ j - 1))) by (rewrite Nat.pow_succ_r'; lia).
  replace (3 * S j - 1) with (S (S (3 * j))) by lia.
  rewrite (rep_snoc [S1; S0] (2 * (2 ^ j - 1))).
  rewrite <- app_assoc.
  eapply creach_csteps.
  eapply csteps_chain. { apply (phSpr9 (2 ^ j - 1) []). }
  rewrite app_nil_r.
  eapply csteps_chain. { apply phEnter9. }
  eapply csteps_chain. { apply (phDf9 (S (3 * j))). }
  apply phFin.
Qed.

Lemma iter9 : forall j, 1 <= j ->
  creach tm_9 (g9 j (2 ^ j) (2 ^ j - 1)) (g9 j (2 ^ S j - 1) 0).
Proof.
  intros j Hj.
  assert (Hp : 0 < 2 ^ j) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  pose (F := fun i => g9 j (2 ^ j + i) (2 ^ j - 1 - i)).
  assert (Hstep : forall i, i < 2 ^ j - 1 -> creach tm_9 (F i) (F (S i))).
  { intros i Hi. unfold F.
    replace (2 ^ j + S i) with (S (2 ^ j + i)) by lia.
    replace (2 ^ j - 1 - S i) with (2 ^ j - 1 - i - 1) by lia.
    apply minilap9.
    - lia.
    - lia.
    - lia.
    - replace (2 ^ j + i + (2 ^ j - 1 - i)) with (2 ^ S j - 1)
        by (rewrite Nat.pow_succ_r'; lia).
      apply odd_pow2_pred. }
  pose proof (creach_iter tm_9 F (2 ^ j - 1) Hstep) as Hit.
  unfold F in Hit.
  replace (2 ^ j + 0) with (2 ^ j) in Hit by lia.
  replace (2 ^ j - 1 - 0) with (2 ^ j - 1) in Hit by lia.
  replace (2 ^ j + (2 ^ j - 1)) with (2 ^ S j - 1) in Hit
    by (rewrite Nat.pow_succ_r'; lia).
  replace (2 ^ j - 1 - (2 ^ j - 1)) with 0 in Hit by lia.
  exact Hit.
Qed.

Lemma macro9 : forall j, 1 <= j ->
  exists m, csteps tm_9 m (D9 j) = Some (D9 (S j)) /\ 0 < m.
Proof.
  intros j Hj.
  destruct (poke9 j Hj) as (Np & Hpoke & HNp).
  assert (Hreach : creach tm_9 (g9 j (2 ^ j) (2 ^ j - 1)) (D9 (S j))).
  { eapply creach_trans; [apply (iter9 j Hj) | apply (final9 j Hj)]. }
  destruct (creach_pos tm_9 Np (D9 j) (g9 j (2 ^ j) (2 ^ j - 1)) (D9 (S j))
              Hpoke HNp Hreach) as (m & Hm & Hpos).
  exists m. split; assumption.
Qed.

Theorem nqh_1RB0LC_1RC0RD_1LA0LC_1RD0RA : NeverQuasiHaltsSt tm_9.
Proof.
  apply (glue_neverqh tm_9 (fun p => D9 (S (Pos.to_nat p))) 1).
  - change (S (Pos.to_nat 1)) with 2. exact boot_9.
  - intros p _.
    destruct (macro9 (S (Pos.to_nat p)) (le_n_S _ _ (Nat.le_0_l _)))
      as (m & Hm & Hpos).
    exists m, (D9 (S (S (Pos.to_nat p)))). split; [exact Hm | split; [| exact Hpos]].
    rewrite Pos2Nat.inj_succ. reflexivity.
  - intros p q _. apply vis_9.
Qed.
