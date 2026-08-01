(** * LinC_1RB0LD_0LC0RB_1LA1RC_0RC1LD: a spacer linear-search counter.

    bbchallenge 1RB0LD_0LC0RB_1LA1RC_0RC1LD, one of the undecided core
    rows (tools/closeout/core_rows.txt), classified QUAD/QUAD under the
    [Kp] alphabet by tools/closeout/residue_map.tsv.

    Again the tape left of the head is a base-2 counter, low digit
    nearest the head -- but one blank SPACER cell sits between the
    counter and the head, so the word on the tape reads [2*v] and its low
    cell is never a digit:

      anchor p :  <Kp p, low digit adjacent>  0  [B:0]

      t=10    100 [0]      p = 2
      t=14    110 [0]      p = 3
      t=28    1000 [0]     p = 4
      t=32    1010 [0]     p = 5      ...

    One lap is one increment.  [B] and [C] cross the spacer; [A] then
    opens a HOLE at the low digit, and each [D]/[C] round trip drives
    that hole one cell deeper into the carry run, refilling behind
    itself.  When the hole reaches the stop digit (a blank past the top
    digit is a digit-0, so overflow needs no separate rule) that digit is
    set and [B] blanks the finished run in a single sweep on the way out:

      anchor p -> anchor (p+1)   in   j^2+3*j+4 steps, j = carry length.

    [Theta(j)] excursions per lap, so no single LapDecider chain reaches
    it at any framing.  [Counters/LinCarry.v] section [Spacer] does the
    induction; here it is only instantiated.  The mirror customer of the
    same section is 1RB1LA_1LC0RD_0RA0LC_0LA1RD.

    Since the counter grows without bound and every anchor with a
    non-empty carry run visits all four states, the machine never
    quasihalts. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter KpCounter LinCarry.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).

(** 1RB0LD_0LC0RB_1LA1RC_0RC1LD *)
Definition tm_sp : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StD
  | StB, S0 => mk S0 DL StC | StB, S1 => mk S0 DR StB
  | StC, S0 => mk S1 DL StA | StC, S1 => mk S1 DR StC
  | StD, S0 => mk S0 DR StC | StD, S1 => mk S1 DL StD
  end.

(** The blank tape reaches the anchor at [p = 2] in ten steps. *)
Lemma boot_sp : exists t0,
  stepn tm_sp t0 InitES = Some (lift (SCf StB 2)).
Proof.
  exists 10.
  assert (H : match csteps tm_sp 10 c0 with
              | Some c => ceqb c (SCf StB 2)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_sp 10 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

(** 1RB0LD_0LC0RB_1LA1RC_0RC1LD never quasihalts. *)
Theorem nqh_1RB0LD_0LC0RB_1LA1RC_0RC1LD : NeverQuasiHaltsSt tm_sp.
Proof.
  apply (S_neverqh tm_sp StA StB StC StD) with (p0 := 2%positive);
    try (intros; reflexivity).
  - intros q; destruct q; auto.
  - exact boot_sp.
Qed.

Theorem tm_sp_nonhalt : NonHalt tm_sp.
Proof. apply never_qh_nonhalt, nqh_1RB0LD_0LC0RB_1LA1RC_0RC1LD. Qed.
