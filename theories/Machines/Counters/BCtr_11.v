(** * BCtr_11: 1RB0LD_1RC0RC_1LA1RB_0LC0LD never quasihalts.

    BBB's certificate family for this machine is [blockdbl_counter]
    (results/counter11.cert): a solid block doubling, modelled at the
    macro anchor

      D(n) = 1^(3*2^n+1) 0 1^(2n+1) 0,   head on the last 0, StB,

    one macro lap of which costs 18*4^n + 22*2^n - 2 steps and turns
    around Theta(2^n) times.  Read that way the proof needs a nested
    lap -- which is why docs/HOLDOUTS_WAVE14.md filed it as needing
    MeasureGlue-style nesting, and why it stayed unproven.

    mxdys' reading is different and much cheaper: it is a plain
    BOUNCER COUNTER.  Sampled at StA on the leftmost visited cell the
    tape is

      A(0) 1 0^(3v+3) 1 <binary counter of value v, low digit first>

    -- a bouncer of length 3v+3 (affine in the counter's VALUE) with
    the counter beyond it, low digit adjacent.  The doubling BBB sees
    is just what one counter overflow does to the bouncer; it never
    has to be modelled, because ONE BOUNCER SWEEP is already a
    complete lap:

      S(v) -->+ S(v+1)   in   12v + 4*carry(v) + 27 steps.

    That is mxdys' "fully predictable forward behaviour": the anchor
    family is a function of v alone, and each transition's usage count
    over one lap is affine in v and in the carry length.

    Everything below was validated cell-for-cell against the raw
    simulator for all 1024 counter words of length <= 9 before any Coq
    was written; the kernel re-checks it here.  The ten gadget lemmas
    are the only per-machine content -- [BCtrCounter] derives the lap.

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import LapGlue BCtrCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB0LD_1RC0RC_1LA1RB_0LC0LD *)
Definition tm_11 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StD
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S0 DR StC
  | StC, S0 => mk S1 DL StA | StC, S1 => mk S1 DR StB
  | StD, S0 => mk S0 DL StC | StD, S1 => mk S0 DL StD
  end.

(** ** The ten gadgets.  Each is a plain [csteps] reflexivity:
    [CTape.cstep] materialises blanks through [chd]/[ctl], so no
    windowed transport is needed anywhere. *)

Lemma g_zip : forall L Y,
  csteps tm_11 3 (StA, (L, S0, S1 :: S0 :: Y))
  = Some (StA, (S1 :: L, S0, S1 :: Y)).
Proof. reflexivity. Qed.

Lemma g_entry : forall L Y,
  csteps tm_11 3 (StA, (L, S0, S1 :: S1 :: Y))
  = Some (StB, (S1 :: S0 :: S1 :: L, chd Y, ctl Y)).
Proof. reflexivity. Qed.

Lemma g_walk1 : forall L Y,
  csteps tm_11 2 (StB, (L, S0, S1 :: Y))
  = Some (StB, (S1 :: S1 :: L, chd Y, ctl Y)).
Proof. reflexivity. Qed.

Lemma g_walk0 : forall L Y,
  csteps tm_11 2 (StB, (L, S0, S0 :: Y)) = Some (StA, (L, S1, S1 :: Y)).
Proof. reflexivity. Qed.

Lemma g_walk0e : forall L,
  csteps tm_11 2 (StB, (L, S0, [])) = Some (StA, (L, S1, [S1])).
Proof. reflexivity. Qed.

Lemma g_turn : forall L R,
  csteps tm_11 1 (StA, (S1 :: L, S1, R)) = Some (StD, (L, S1, S0 :: R)).
Proof. reflexivity. Qed.

Lemma g_d11 : forall L R,
  csteps tm_11 1 (StD, (S1 :: L, S1, R)) = Some (StD, (L, S1, S0 :: R)).
Proof. reflexivity. Qed.

Lemma g_d10 : forall L R,
  csteps tm_11 1 (StD, (S0 :: L, S1, R)) = Some (StD, (L, S0, S0 :: R)).
Proof. reflexivity. Qed.

Lemma g_ret5 : forall M E,
  csteps tm_11 5 (StD, (S1 :: M, S0, S0 :: E))
  = Some (StD, (M, S1, S0 :: S1 :: E)).
Proof. reflexivity. Qed.

Lemma g_ret3 : forall R,
  csteps tm_11 3 (StD, ([], S1, R))
  = Some (StA, ([], S0, S1 :: S0 :: S0 :: R)).
Proof. reflexivity. Qed.

(** ** The anchor family and the closer instance *)

Notation A11 := (anchor StA 3).
Notation G11 := (gap 3).

Definition ze_11 := zip_end tm_11 StA 3 g_zip.
Definition ce_11 := ctr_end tm_11 StA StB StA StD 3
  g_zip g_entry g_walk1 g_walk0 g_walk0e g_turn g_d11 g_d10.

(** ** Boot and visits *)

Lemma boot_11 : exists t0,
  stepn tm_11 t0 InitES = Some (lift (Cc StA 3 1)).
Proof.
  exists 34.
  assert (H : match csteps tm_11 34 c0 with
              | Some c => ceqb c (Cc StA 3 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_11 34 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

(** All four states inside one lap, so none of them ever goes quiet. *)
Lemma vis_11 : forall w q,
  exists k c, csteps tm_11 k (A11 w) = Some c /\ fst c = q.
Proof.
  intros w q. destruct q.
  - exists 0. eexists. split; reflexivity.
  - exists (3 * G11 w + 1). eexists. split.
    + rewrite csteps_add, ze_11. reflexivity.
    + reflexivity.
  - exists (3 * G11 w + 2). eexists. split.
    + rewrite csteps_add, ze_11. reflexivity.
    + reflexivity.
  - exists (3 * G11 w + (3 + (4 * carry w + 4))). eexists. split.
    + rewrite ce_11. reflexivity.
    + reflexivity.
Qed.

(** #11 never quasihalts: bbchallenge 1RB0LD_1RC0RC_1LA1RB_0LC0LD. *)
Theorem nqh_1RB0LD_1RC0RC_1LA1RB_0LC0LD : NeverQuasiHaltsSt tm_11.
Proof.
  apply (bc_neverqh tm_11 StA StB StA StD 3
           g_zip g_entry g_walk1 g_walk0 g_walk0e g_turn g_d11 g_d10
           g_ret5 g_ret3 boot_11 vis_11).
Qed.

Theorem tm_11_nonhalt : NonHalt tm_11.
Proof. apply never_qh_nonhalt, nqh_1RB0LD_1RC0RC_1LA1RB_0LC0LD. Qed.
