(** * BCtr_13: 1RB0RB_1LC1RA_1RA0LD_0LB0LD never quasihalts.

    BBB [blockdbl_counter] certificate #13, and the machine
    docs/BOUNCER_COUNTER_READING.md read off a spacetime diagram as
    "surely a bouncer counter".  It is -- the same one as #11:

      sigma(tm_11) = tm_13   for   sigma = (StA StC StB)

    i.e. StA -> StC, StB -> StA, StC -> StB, StD -> StD.  That
    bijection MOVES the start state, so it is not a [Mirror]/[TM_swap]
    transport and the two machines really do have different orbits
    from the blank tape (boots 34 vs 28, gap offsets 3 vs 2) -- but
    every lap gadget transcribes, exactly as [Wave_24] transcribed
    [Wave_6].  Sampled at StC on the leftmost visited cell:

      C(0) 1 0^(3v+2) 1 <binary counter of value v, low digit first>

    and one bouncer sweep is a complete lap,

      S(v) -->+ S(v+1)   in   12v + 4*carry(v) + 23 steps.

    Validated cell-for-cell against the raw simulator for all 512
    counter words of length <= 8, plus the sigma-image check above,
    before any Coq was written.

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import LapGlue BCtrCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB0RB_1LC1RA_1RA0LD_0LB0LD *)
Definition tm_13 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DR StB
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StA
  | StC, S0 => mk S1 DR StA | StC, S1 => mk S0 DL StD
  | StD, S0 => mk S0 DL StB | StD, S1 => mk S0 DL StD
  end.

(** ** The ten gadgets, [sigma]-transcribed from BCtr_11. *)

Lemma g_zip : forall L Y,
  csteps tm_13 3 (StC, (L, S0, S1 :: S0 :: Y))
  = Some (StC, (S1 :: L, S0, S1 :: Y)).
Proof. reflexivity. Qed.

Lemma g_entry : forall L Y,
  csteps tm_13 3 (StC, (L, S0, S1 :: S1 :: Y))
  = Some (StA, (S1 :: S0 :: S1 :: L, chd Y, ctl Y)).
Proof. reflexivity. Qed.

Lemma g_walk1 : forall L Y,
  csteps tm_13 2 (StA, (L, S0, S1 :: Y))
  = Some (StA, (S1 :: S1 :: L, chd Y, ctl Y)).
Proof. reflexivity. Qed.

Lemma g_walk0 : forall L Y,
  csteps tm_13 2 (StA, (L, S0, S0 :: Y)) = Some (StC, (L, S1, S1 :: Y)).
Proof. reflexivity. Qed.

Lemma g_walk0e : forall L,
  csteps tm_13 2 (StA, (L, S0, [])) = Some (StC, (L, S1, [S1])).
Proof. reflexivity. Qed.

Lemma g_turn : forall L R,
  csteps tm_13 1 (StC, (S1 :: L, S1, R)) = Some (StD, (L, S1, S0 :: R)).
Proof. reflexivity. Qed.

Lemma g_d11 : forall L R,
  csteps tm_13 1 (StD, (S1 :: L, S1, R)) = Some (StD, (L, S1, S0 :: R)).
Proof. reflexivity. Qed.

Lemma g_d10 : forall L R,
  csteps tm_13 1 (StD, (S0 :: L, S1, R)) = Some (StD, (L, S0, S0 :: R)).
Proof. reflexivity. Qed.

Lemma g_ret5 : forall M E,
  csteps tm_13 5 (StD, (S1 :: M, S0, S0 :: E))
  = Some (StD, (M, S1, S0 :: S1 :: E)).
Proof. reflexivity. Qed.

Lemma g_ret3 : forall R,
  csteps tm_13 3 (StD, ([], S1, R))
  = Some (StC, ([], S0, S1 :: S0 :: S0 :: R)).
Proof. reflexivity. Qed.

(** ** The anchor family and the closer instance *)

Notation A13 := (anchor StC 2).
Notation G13 := (gap 2).

Definition ze_13 := zip_end tm_13 StC 2 g_zip.
Definition ce_13 := ctr_end tm_13 StC StA StC StD 2
  g_zip g_entry g_walk1 g_walk0 g_walk0e g_turn g_d11 g_d10.

(** ** Boot and visits *)

Lemma boot_13 : exists t0,
  stepn tm_13 t0 InitES = Some (lift (Cc StC 2 1)).
Proof.
  exists 28.
  assert (H : match csteps tm_13 28 c0 with
              | Some c => ceqb c (Cc StC 2 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_13 28 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

Lemma vis_13 : forall w q,
  exists k c, csteps tm_13 k (A13 w) = Some c /\ fst c = q.
Proof.
  intros w q. destruct q.
  - exists (3 * G13 w + 1). eexists. split.
    + rewrite csteps_add, ze_13. reflexivity.
    + reflexivity.
  - exists (3 * G13 w + 2). eexists. split.
    + rewrite csteps_add, ze_13. reflexivity.
    + reflexivity.
  - exists 0. eexists. split; reflexivity.
  - exists (3 * G13 w + (3 + (4 * carry w + 4))). eexists. split.
    + rewrite ce_13. reflexivity.
    + reflexivity.
Qed.

(** #13 never quasihalts: bbchallenge 1RB0RB_1LC1RA_1RA0LD_0LB0LD. *)
Theorem nqh_1RB0RB_1LC1RA_1RA0LD_0LB0LD : NeverQuasiHaltsSt tm_13.
Proof.
  apply (bc_neverqh tm_13 StC StA StC StD 2
           g_zip g_entry g_walk1 g_walk0 g_walk0e g_turn g_d11 g_d10
           g_ret5 g_ret3 boot_13 vis_13).
Qed.

Theorem tm_13_nonhalt : NonHalt tm_13.
Proof. apply never_qh_nonhalt, nqh_1RB0RB_1LC1RA_1RA0LD_0LB0LD. Qed.
