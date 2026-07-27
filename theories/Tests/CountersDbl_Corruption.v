(** * CountersDbl_Corruption: negative controls for the double_counter #9.

    BBB corruption-test tradition: every computable ingredient of the
    proof must REJECT mutated inputs.  For #9
    (1RB0LC_1RC0RD_1LA0LC_1RD0RA) we cover:

    - unit mutation: a one-transition mutant ([C0] turns the wrong way)
      no longer realises the collapse cycle [Ucol], so the transported
      collapse phase would not hold;
    - wall discipline: the doubling poke digs into the RIGHT blank
      ([D1 = 0RA]), so with the right wall ON it must die (return
      [None]) rather than fabricate cells;
    - bootstrap anchor: distinct anchors [D9 2]/[D9 3] are separated by
      [ceqb], the genuine boot lands on [D9 2] at exactly 47 steps, and
      a wrong step count does not.

    #32 (1RB1LD_1RC0RB_1LA0RC_0LD0LA) follows in its own section at the
    end of the file.

    Everything is decided by [vm_compute]/[reflexivity]/[discriminate];
    a regression that made any of these pass would be a soundness
    alarm. *)

From Coq Require Import Arith Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape.
From BBB4.Machines.Counters Require Import Double_9 Double_32.
Import ListNotations.

(** ** Unit mutation *)

(** A mutant that turns [C0] the wrong way (rightward instead of
    leftward). *)
Definition tm_9_mut : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StC
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S0 DR StD
  | StC, S0 => mk S1 DR StA | StC, S1 => mk S0 DL StC
  | StD, S0 => mk S1 DR StD | StD, S1 => mk S0 DR StA
  end.

(** The genuine collapse cycle unit. *)
Example ok_Ucol : wsteps true true tm_9 2 (StA, ([S0; S1], S1, []))
                  = Some (StA, ([], S1, [S1; S0])).
Proof. reflexivity. Qed.

(** The mutant does NOT realise it. *)
Example mut_Ucol : wsteps true true tm_9_mut 2 (StA, ([S0; S1], S1, []))
                   <> Some (StA, ([], S1, [S1; S0])).
Proof. vm_compute. discriminate. Qed.

(** ** Wall discipline *)

(** The doubling poke [D1 = 0RA] digs into the right blank; the genuine
    run declares [br = false] ([Upokein]).  With the right wall ON it
    dies rather than fabricating the seed. *)
Example wall_poke_right : wsteps true true tm_9 3 (StD, ([], S1, [])) = None.
Proof. reflexivity. Qed.

(** The genuine poke (right wall OFF) succeeds. *)
Example ok_poke : wsteps true false tm_9 3 (StD, ([], S1, []))
                  = Some (StC, ([S1; S1; S0], S0, [])).
Proof. reflexivity. Qed.

(** ** Bootstrap anchor *)

(** Distinct anchors are distinguished by [ceqb]. *)
Example boot_anchor_distinct : ceqb (D9 2) (D9 3) = false.
Proof. reflexivity. Qed.

(** The boot really reaches [D9 2] from the blank tape at 47 steps. *)
Example boot_reaches : match csteps tm_9 47 c0 with
                       | Some c => ceqb c (D9 2)
                       | None => false
                       end = true.
Proof. vm_compute. reflexivity. Qed.

(** A wrong boot step count does not land on the anchor. *)
Example boot_wrong_index : match csteps tm_9 46 c0 with
                           | Some c => ceqb c (D9 2)
                           | None => false
                           end = false.
Proof. vm_compute. reflexivity. Qed.

(** * double #32 -- 1RB1LD_1RC0RB_1LA0RC_0LD0LA

    The comb counter.  What is NOT free here is different from #9's:
    there is no wall to test, but there are four exact constants (the
    boot index, and the three rule step counts that add up to the lap)
    and two load-bearing side conditions on the block word.  Read at
    the LEFT RECORD the whole proof is [Cf32 a --lapn a--> Cf32
    (next32 a)], so every control below is a [ceqb]/[discriminate] on
    an anchor. *)

(** ** The boot constant is exact *)

Example dbl32_boot :
  match csteps tm_32 24 c0 with
  | Some c => ceqb c (Cf32 a0_32) | None => false end = true.
Proof. vm_compute. reflexivity. Qed.

Example dbl32_boot_not_23 :
  match csteps tm_32 23 c0 with
  | Some c => ceqb c (Cf32 a0_32) | None => false end = false.
Proof. vm_compute. reflexivity. Qed.

Example dbl32_boot_not_25 :
  match csteps tm_32 25 c0 with
  | Some c => ceqb c (Cf32 a0_32) | None => false end = false.
Proof. vm_compute. reflexivity. Qed.

(** ** The lap is exact, and grows the comb by exactly one

    [lapn (1, [(1,4)]) = 24*1 + 2*4 + 29 = 61]. *)

Example dbl32_lap :
  csteps tm_32 61 (Cf32 (1, [(1,4)])) = Some (Cf32 (2, [(1,6)])).
Proof. vm_compute. reflexivity. Qed.

Example dbl32_lap_not_60 :
  csteps tm_32 60 (Cf32 (1, [(1,4)])) <> Some (Cf32 (2, [(1,6)])).
Proof. vm_compute. discriminate. Qed.

(** One lap is ONE comb block, not two -- the macro [a -> 2a] doubling
    is what three of these add up to, never a single step. *)
Example dbl32_comb_grows_by_one :
  csteps tm_32 61 (Cf32 (1, [(1,4)])) <> Some (Cf32 (3, [(1,6)])).
Proof. vm_compute. discriminate. Qed.

(** ...and with a block following the lead: [24*3 + 2*4 + 29 = 109]. *)
Example dbl32_lap_tail :
  csteps tm_32 109 (Cf32 (3, [(1,4); (2,2)])) = Some (Cf32 (4, [(1,8)])).
Proof. vm_compute. reflexivity. Qed.

Example dbl32_lap_tail_not_108 :
  csteps tm_32 108 (Cf32 (3, [(1,4); (2,2)])) <> Some (Cf32 (4, [(1,8)])).
Proof. vm_compute. discriminate. Qed.

(** ** The three rule step counts are exact, and so are their windows *)

(** R1 at [j = 1, m = 4]: [8*1 + 2*4 + 5 = 21]. *)
Example dbl32_R1 :
  csteps tm_32 21 (Cf32 (1, [(1,4)])) = Some (Cf32 (1, [(6,2)])).
Proof. vm_compute. reflexivity. Qed.

(** R1 eats exactly TWO blanks off the block after the lead ([dec2]),
    not one: at [j = 3] the tail [(2,2)] must come out [(0,2)]. *)
Example dbl32_R1_eats_two :
  csteps tm_32 37 (Cf32 (3, [(1,4); (2,2)]))
  = Some (Cf32 (3, [(6,2); (0,2)])).
Proof. vm_compute. reflexivity. Qed.

Example dbl32_R1_not_one :
  csteps tm_32 37 (Cf32 (3, [(1,4); (2,2)]))
  <> Some (Cf32 (3, [(6,2); (1,2)])).
Proof. vm_compute. discriminate. Qed.

(** R2 at [j = 1]: [8*1 + 5 = 13], and it drops THREE zeros, not two.
    The third is the extra comb block of run-up before the turnaround;
    an [0^(a-2)] reading is the off-by-one this family hides. *)
Example dbl32_R2 :
  csteps tm_32 13 (Cf32 (1, [(6,2)])) = Some (Cf32 (2, [(0,1); (3,2)])).
Proof. vm_compute. reflexivity. Qed.

Example dbl32_R2_not_minus_two :
  csteps tm_32 13 (Cf32 (1, [(6,2)])) <> Some (Cf32 (2, [(0,1); (4,2)])).
Proof. vm_compute. discriminate. Qed.

(** R3 at [j = 2]: [8*2 + 11 = 27], again [0^(b-3)] and not [0^(b-2)]. *)
Example dbl32_R3 :
  csteps tm_32 27 (Cf32 (2, [(0,1); (3,2)])) = Some (Cf32 (2, [(1,6)])).
Proof. vm_compute. reflexivity. Qed.

Example dbl32_R3_not_minus_two :
  csteps tm_32 27 (Cf32 (2, [(0,1); (3,2)]))
  <> Some (Cf32 (2, [(1,4); (1,2)])).
Proof. vm_compute. discriminate. Qed.

(** ** The invariant's size conditions are load-bearing

    [m >= 4] is R3's [b >= 3] and [p >= 2] is R1's bite.  Neither is
    decoration: with either violated the lap identity fails outright,
    at the step count [lapn] prescribes. *)

Example dbl32_needs_m4 :
  csteps tm_32 81 (Cf32 (2, [(1,2)])) <> Some (Cf32 (3, [(1,6)])).
Proof. vm_compute. discriminate. Qed.

Example dbl32_needs_p2 :
  csteps tm_32 109 (Cf32 (3, [(1,4); (1,2)])) <> Some (Cf32 (4, [(1,8)])).
Proof. vm_compute. discriminate. Qed.

(** ** Unit mutation: break the comb traversal

    [tm_32] with [B1] re-routed to StC instead of StB.  That is exactly
    the step [rc5] uses to cross a comb block's [1], so the [8j]
    traversal dies -- while [bt4], which never reads a [1] in StB,
    still holds.  A mutant this local is the sharpest test that the
    [8j] is really [rc5] iterated and not a fitted constant. *)
Definition tm_32_mut : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StD
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S0 DR StC
  | StC, S0 => mk S1 DL StA | StC, S1 => mk S0 DR StC
  | StD, S0 => mk S0 DL StD | StD, S1 => mk S0 DL StA
  end.

Example dbl32_mut_breaks_rc5 :
  csteps tm_32_mut 5 (StA, ([S1;S0;S1], S0, [S1;S0;S1;S0;S0;S0;S1]))
  <> Some (StA, ([S1;S0;S1;S1;S0;S1], S0, [S1;S0;S0;S1])).
Proof. vm_compute. discriminate. Qed.

(** The genuine [rc5] does hold on the same window... *)
Example dbl32_genuine_rc5 :
  csteps tm_32 5 (StA, ([S1;S0;S1], S0, [S1;S0;S1;S0;S0;S0;S1]))
  = Some (StA, ([S1;S0;S1;S1;S0;S1], S0, [S1;S0;S0;S1])).
Proof. reflexivity. Qed.

(** ...and the mutation is local enough that [bt4] survives it, so the
    failure above is [rc5]'s and not a blanket break. *)
Example dbl32_mut_keeps_bt4 :
  csteps tm_32_mut 4 (StA, ([S1;S0;S1], S0, [S0;S1;S0;S0;S0;S1]))
  = Some (StA, ([S1;S1;S1;S0;S1], S0, [S1;S0;S0;S1])).
Proof. reflexivity. Qed.

(** ** [la2] consumes TWO cells from the left, not one

    Same shape as [lc3]: the explicit [S1] plus one more through
    [chd]/[ctl].  Reading it as a one-cell step is the trap that makes
    the return sweep's [3j] come out [2j]. *)
Example dbl32_la2_two_cells :
  csteps tm_32 2 (StA, ([S1;S0;S1;S1], S1, []))
  = Some (StA, ([S1;S1], S0, [S0;S1])).
Proof. reflexivity. Qed.

Example dbl32_la2_not_one_cell :
  csteps tm_32 2 (StA, ([S1;S0;S1;S1], S1, []))
  <> Some (StA, ([S0;S1;S1], S1, [S0;S1])).
Proof. vm_compute. discriminate. Qed.
