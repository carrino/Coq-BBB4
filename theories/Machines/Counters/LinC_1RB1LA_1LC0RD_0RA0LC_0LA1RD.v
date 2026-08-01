(** * LinC_1RB1LA_1LC0RD_0RA0LC_0LA1RD: the spacer counter, mirrored.

    bbchallenge 1RB1LA_1LC0RD_0RA0LC_0LA1RD, one of the undecided core
    rows (tools/closeout/core_rows.txt), classified QUAD/QUAD under the
    [Kp] alphabet by tools/closeout/residue_map.tsv.

    This machine's counter grows to the RIGHT of the head:

      anchor p :  [C:0]  0  <Kp p, low digit adjacent>

      t=11    [0] 001     p = 2
      t=15    [0] 011     p = 3
      t=29    [0] 0001    p = 4
      t=33    [0] 0101    p = 5      ...

    Mirrored, that is exactly the spacer counter of
    1RB0LD_0LC0RB_1LA1RC_0RC1LD -- [mirror_tm] of this table is that
    machine with its states renamed [A B C D |-> B C A D], and the two
    orbits agree step for step from the second step on.  They are still
    two rows, not one: the renaming moves the START state, so neither is
    reachable from the other by the census's mirror/swap orbit, and each
    needs its own boot.

    Every lemma below runs on the MIRRORED table, where the counter grows
    leftward and [Counters/LinCarry.v] section [Spacer] applies verbatim
    at [(qA,qB,qC,qD) := (B,C,A,D)]; [Mirror.mirror_never_qh] transfers
    the conclusion back.  Lap [j^2+3*j+4] steps for a carry run of
    length [j], one [D]/[C] round trip per digit. *)

From Coq Require Import Arith Lia Bool List PArith.
From Coq Require Import FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From BBB4.Counters Require Import WTape LapGlue MonoCounter KpCounter LinCarry.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).

(** 1RB1LA_1LC0RD_0RA0LC_0LA1RD -- the real machine (its counter grows RIGHT). *)
Definition tm_mr : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StA
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DR StD
  | StC, S0 => mk S0 DR StA | StC, S1 => mk S0 DL StC
  | StD, S0 => mk S0 DL StA | StD, S1 => mk S1 DR StD
  end.

(** Its mirror 1LB1RA_1RC0LD_0LA0RC_0RA1LD: the same counter grown
    leftward.  This is 1RB0LD_0LC0RB_1LA1RC_0RC1LD under [A B C D |-> B C A D]. *)
Definition tmm_mr : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => mk S1 DR StA
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S0 DL StD
  | StC, S0 => mk S0 DL StA | StC, S1 => mk S0 DR StC
  | StD, S0 => mk S0 DR StA | StD, S1 => mk S1 DL StD
  end.

Lemma mirror_ok_mr : mirror_tm tm_mr = tmm_mr.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

(** The blank tape reaches the mirrored anchor at [p = 1] in three steps. *)
Lemma boot_mr : exists t0,
  stepn tmm_mr t0 InitES = Some (lift (SCf StC 1)).
Proof.
  exists 3.
  assert (H : match csteps tmm_mr 3 c0 with
              | Some c => ceqb c (SCf StC 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tmm_mr 3 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

Lemma nqh_tmm_mr : NeverQuasiHaltsSt tmm_mr.
Proof.
  apply (S_neverqh tmm_mr StB StC StA StD) with (p0 := 1%positive);
    try (intros; reflexivity).
  - intros q; destruct q; auto.
  - exact boot_mr.
Qed.

(** 1RB1LA_1LC0RD_0RA0LC_0LA1RD never quasihalts. *)
Theorem nqh_1RB1LA_1LC0RD_0RA0LC_0LA1RD : NeverQuasiHaltsSt tm_mr.
Proof.
  apply mirror_never_qh. rewrite mirror_ok_mr. exact nqh_tmm_mr.
Qed.

Theorem tm_mr_nonhalt : NonHalt tm_mr.
Proof. apply never_qh_nonhalt, nqh_1RB1LA_1LC0RD_0RA0LC_0LA1RD. Qed.
