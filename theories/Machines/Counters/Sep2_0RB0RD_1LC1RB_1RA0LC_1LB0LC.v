(** * Sep2_0RB0RD_1LC1RB_1RA0LC_1LB0LC: a separator-2 bouncer counter.

    bbchallenge 0RB0RD_1LC1RB_1RA0LC_1LB0LC, one of the two
    [SEP2_EARLY_ONLY] rows of the undecided core
    (tools/counter_encodings.tsv; tools/closeout/core_rows.txt).

    From the blank tape the machine reaches, after 94 steps,

      0 1 1 [D:1] 1 0^(2*v+2) 1 1 <v in binary, low digit first,
                                   one cell per digit>

    at [v = 1], and every lap takes [v] to [v+1]: the head crosses the
    zipper gap left-to-right turning it into ones (5 steps per cell),
    steps over the marker and the two separator cells, walks the
    counter's low digit-1s and sets the first digit-0 (the blank past
    the top digit is the same rule, so overflow needs no special case),
    sweeps all the way back left blanking as it goes, rebuilds the
    separator, and lays a fresh wall two cells further out.  The gap
    therefore grows by exactly 2 per lap, which is the counter
    incrementing.  Since [v] grows forever and every lap starts by
    visiting all four states, the machine never quasihalts.

    All of the above is [theories/Counters/Sep2Counter.v]; this file
    only discharges that closer's eight gadget runs (each a windowed
    [reflexivity]), the bootstrap, and the visit witnesses.

    Lap length: [6*(2*v+2) + 2*carry(v) + 36] steps, checked
    differentially against the raw simulator for [v = 1..300]. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue BCtrCounter Sep2Counter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 0RB0RD_1LC1RB_1RA0LC_1LB0LC *)
Definition tm_sep2a : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S0 DR StD
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S1 DR StA | StC, S1 => mk S0 DL StC
  | StD, S0 => mk S1 DL StB | StD, S1 => mk S0 DL StC
  end.

(** ** The windowed unit runs *)

(** W1: the prelude across the wall marker. *)
Lemma W1 : wsteps true true tm_sep2a 2 (StD, ([S0], S1, []))
           = Some (StA, ([S1], S0, [])).
Proof. reflexivity. Qed.

(** W2: one zipper cell -- a gap blank becomes a one. *)
Lemma W2 : wsteps true true tm_sep2a 5 (StA, ([], S0, [S1; S0]))
           = Some (StA, ([S1], S0, [S1])).
Proof. reflexivity. Qed.

(** W3: the turnaround rebuilding the two separator cells. *)
Lemma W3 : wsteps true true tm_sep2a 8 (StC, ([], S0, [S0; S0; S0]))
           = Some (StC, ([], S1, [S0; S1; S1])).
Proof. reflexivity. Qed.

(** W4: off the left end -- the new wall and marker. *)
Lemma W4 : wsteps false true tm_sep2a 14 (StC, ([], S0, [S0; S0; S0]))
           = Some (StD, ([S0; S1; S1], S1, [S1])).
Proof. reflexivity. Qed.

(** ** The closer's gadget list *)

Lemma Gpre : forall L R,
  csteps tm_sep2a 2 (StD, (S0 :: L, S1, R)) = Some (StA, (S1 :: L, S0, R)).
Proof.
  intros L R.
  exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R W1).
Qed.

Lemma Gzip : forall L Y,
  csteps tm_sep2a 5 (StA, (L, S0, S1 :: S0 :: Y))
  = Some (StA, (S1 :: L, S0, S1 :: Y)).
Proof.
  intros L Y.
  exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L Y W2).
Qed.

Lemma Gentry : forall L Y,
  csteps tm_sep2a 4 (StA, (L, S0, S1 :: S1 :: S1 :: Y))
  = Some (StB, (S1 :: S1 :: S1 :: S0 :: L, chd Y, ctl Y)).
Proof. reflexivity. Qed.

Lemma Gone : forall L Y,
  csteps tm_sep2a 1 (StB, (L, S1, Y)) = Some (StB, (S1 :: L, chd Y, ctl Y)).
Proof. reflexivity. Qed.

Lemma Gzero : forall L Y,
  csteps tm_sep2a 1 (StB, (L, S0, Y)) = Some (StC, (ctl L, chd L, S1 :: Y)).
Proof. reflexivity. Qed.

Lemma Gclr : forall L R,
  csteps tm_sep2a 1 (StC, (L, S1, R)) = Some (StC, (ctl L, chd L, S0 :: R)).
Proof. reflexivity. Qed.

Lemma Gturn : forall L R,
  csteps tm_sep2a 8 (StC, (L, S0, S0 :: S0 :: S0 :: R))
  = Some (StC, (L, S1, S0 :: S1 :: S1 :: R)).
Proof.
  intros L R.
  exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R W3).
Qed.

Lemma Gtail : forall R,
  csteps tm_sep2a 14 (StC, ([], S0, S0 :: S0 :: S0 :: R))
  = Some (StD, ([S0; S1; S1], S1, S1 :: R)).
Proof.
  intros R.
  exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R W4).
Qed.

(** ** Bootstrap, visits, and the theorem *)

Lemma boot_sep2a :
  exists t0, stepn tm_sep2a t0 InitES = Some (lift (Cc StD 1)).
Proof.
  exists 94.
  assert (H : match csteps tm_sep2a 94 c0 with
              | Some c => ceqb c (Cc StD 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_sep2a 94 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

(** Every anchor visits all four states in its first four steps:
    [D], then [C], [A], [B]. *)
Lemma vis_sep2a : forall q Y,
  exists k c, csteps tm_sep2a k (StD, ([S0; S1; S1], S1, S1 :: S0 :: Y))
              = Some c /\ fst c = q.
Proof.
  intros q Y. destruct q.
  - exists 2. eexists. split; reflexivity.
  - exists 3. eexists. split; reflexivity.
  - exists 1. eexists. split; reflexivity.
  - exists 0. eexists. split; reflexivity.
Qed.

(** 0RB0RD_1LC1RB_1RA0LC_1LB0LC never quasihalts. *)
Theorem nqh_0RB0RD_1LC1RB_1RA0LC_1LB0LC : NeverQuasiHaltsSt tm_sep2a.
Proof.
  apply (s2_neverqh tm_sep2a StA StB StC StD
           Gpre Gzip Gentry Gone Gzero Gclr Gturn Gtail).
  - exact boot_sep2a.
  - exact vis_sep2a.
Qed.

Theorem tm_sep2a_nonhalt : NonHalt tm_sep2a.
Proof. apply never_qh_nonhalt, nqh_0RB0RD_1LC1RB_1RA0LC_1LB0LC. Qed.
