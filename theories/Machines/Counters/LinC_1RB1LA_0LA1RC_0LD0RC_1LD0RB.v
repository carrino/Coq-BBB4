(** * LinC_1RB1LA_0LA1RC_0LD0RC_1LD0RB: a linear-search-carry counter.

    bbchallenge 1RB1LA_0LA1RC_0LD0RC_1LD0RB, one of the undecided core
    rows (tools/closeout/core_rows.txt), classified QUAD/QUAD under the
    [Kp] alphabet by tools/closeout/residue_map.tsv.

    The tape left of the head IS the counter, base 2, low digit adjacent
    to the head and nothing between the bits; the head sits on the blank
    just past it in state [B]:

      anchor p :  <Kp p, low digit adjacent>  [B:0]

      t=1     1 [0]        p = 1
      t=7     10 [0]       p = 2
      t=9     11 [0]       p = 3
      t=21    100 [0]      p = 4      ...

    One lap is one increment.  [B] turns the head around; [A] walks left
    over the carry run and SETS the stop digit (a blank past the top
    digit is a digit-0, so overflow needs no separate rule); then the run
    is cleared by [C]/[D] ROUND TRIPS, one per digit, each two steps
    shorter than the last -- which is why the lap is quadratic in the
    carry length,

      anchor p -> anchor (p+1)   in   (j+1)*(j+2) steps, j = carry length,

    and why no single LapDecider chain reaches it: [Theta(j)] excursions,
    not a bounded number.  [Counters/LinCarry.v] section [Plain] does the
    induction; here it is only instantiated.

    Since the counter grows without bound and every anchor with a
    non-empty carry run visits all four states, the machine never
    quasihalts. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter KpCounter LinCarry.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).

(** 1RB1LA_0LA1RC_0LD0RC_1LD0RB *)
Definition tm_lp : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StA
  | StB, S0 => mk S0 DL StA | StB, S1 => mk S1 DR StC
  | StC, S0 => mk S0 DL StD | StC, S1 => mk S0 DR StC
  | StD, S0 => mk S1 DL StD | StD, S1 => mk S0 DR StB
  end.

(** The blank tape reaches the anchor at [p = 1] in one step. *)
Lemma boot_lp : exists t0,
  stepn tm_lp t0 InitES = Some (lift (PCf StB 1)).
Proof.
  exists 1.
  assert (H : match csteps tm_lp 1 c0 with
              | Some c => ceqb c (PCf StB 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_lp 1 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

(** 1RB1LA_0LA1RC_0LD0RC_1LD0RB never quasihalts. *)
Theorem nqh_1RB1LA_0LA1RC_0LD0RC_1LD0RB : NeverQuasiHaltsSt tm_lp.
Proof.
  apply (P_neverqh tm_lp StA StB StC StD) with (p0 := 1%positive);
    try (intros; reflexivity).
  - intros q; destruct q; auto.
  - exact boot_lp.
Qed.

Theorem tm_lp_nonhalt : NonHalt tm_lp.
Proof. apply never_qh_nonhalt, nqh_1RB1LA_0LA1RC_0LD0RC_1LD0RB. Qed.
