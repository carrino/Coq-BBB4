(** * T3D_1RB1RC_1LA0LB_1LD0RD_1LB0RC: the machine never quasihalts.

    A core row of the residue, and [tools/closeout/residue_map.tsv]'s
    [EXP3] / [Ip] / "no interior chain".  [docs/LADDER_NOFAM.md] measures it
    at [1 1 1 3 3 9 9 27] distinct strings per width -- ratio 3 -- and stops
    there; [docs/LADDER_PLAN.md] section 4w locates the anchor and reads the
    counter off it.

    It is a BASE-THREE wall counter, at

      Cc t = (StA, ([], S1, S1 :: Wf t))
      Wf   = Tw [S0;S0] [S1;S0] [S1;S1] []        (TernCounter, no terminator)

    -- the head on the wall, one fixed marker cell, then 2-cell digits with
    the LOW digit next to the marker and the top digit truncated.
    [tools/counters/ter3_probe.py] decodes 75,006 consecutive anchor visits
    to [0, 1, 2, ..., 75005] with zero prefix and zero consecutive-value
    failures, and [tools/counters/ter3_scan.py] confirms base 3 is the only
    radix that reads this row at any blank-side anchor or prefix.

    The alphabet and the increment are already in the tree: the digits are
    [Counters/Ter3WallB.v]'s digit for digit and the increment is
    [TernCounter.tsucc], whose overflow writes a fresh digit 1.  So the whole
    counter side is [Ter3WallB.ter_stepB_nil], reused verbatim, and this
    board is [Counters/Ter3WallD.v]'s closer plus two [vm_compute] facts.

    ** Why it is NOT the [iqh] its three-state siblings carry

    The [Ter3Wall*] rows have an undefined [StA] that nothing targets, so
    [StA] fires once and they genuinely quasihalt.  Here [StA] is the target
    of [StB]'s [S0] transition and is the anchor's own state: all four states
    recur at every anchor -- measured, every one of 37,502 laps contains all
    four -- so the theorem is [NeverQuasiHaltsSt] and the closer is
    [Counters/LapGlueNeverIx.glue_neverqh_ix].

    The lap is affine in the carry length [c] (the run of trailing 2s), in
    the trichotomy's three cases:

      stop digit 0    6c + 4
      stop digit 1    6c + 6
      overflow        6c + 4

    checked against the probe over 50,003 consecutive laps with zero
    mismatches before any of it was written in Coq.

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Counters Require Import WTape LapGlueNeverIx TernCounter.
From BBB4.Counters Require Ter3WallB Ter3WallD.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).

(** 1RB1RC_1LA0LB_1LD0RD_1LB0RC *)
Definition tm_1RB1RC_1LA0LB_1LD0RD_1LB0RC : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB       | StA, S1 => mk S1 DR StC
  | StB, S0 => mk S1 DL StA       | StB, S1 => mk S0 DL StB
  | StC, S0 => mk S1 DL StD       | StC, S1 => mk S0 DR StD
  | StD, S0 => mk S1 DL StB       | StD, S1 => mk S0 DR StC end.
Local Notation tm := tm_1RB1RC_1LA0LB_1LD0RD_1LB0RC.

Definition i0_1RB1RC_1LA0LB_1LD0RD_1LB0RC : tern := tE.
Definition Wf_1RB1RC_1LA0LB_1LD0RD_1LB0RC : tern -> list Sym :=
  Tw [S0;S0] [S1;S0] [S1;S1] [].

(** The counter is at 0 after two steps: the blank tape's first move sets the
    wall, the second sets the marker and returns the head to it. *)
Lemma boot_1RB1RC_1LA0LB_1LD0RD_1LB0RC :
  stepn tm 2 InitES
    = Some (lift (Ter3WallD.Cc StA Wf_1RB1RC_1LA0LB_1LD0RD_1LB0RC
                    i0_1RB1RC_1LA0LB_1LD0RD_1LB0RC)).
Proof.
  assert (H : match csteps tm 2 c0 with
              | Some c => ceqb c (Ter3WallD.Cc StA
                                    Wf_1RB1RC_1LA0LB_1LD0RD_1LB0RC
                                    i0_1RB1RC_1LA0LB_1LD0RD_1LB0RC)
              | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 2 c0) as [c|] eqn:E; [| discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

Theorem nqh_1RB1RC_1LA0LB_1LD0RD_1LB0RC : NeverQuasiHaltsSt tm.
Proof.
  exact (Ter3WallD.ter3walld_nqh tm StA StB StC StD 2
           i0_1RB1RC_1LA0LB_1LD0RD_1LB0RC
           eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
           ltac:(intro q; destruct q; auto)
           Wf_1RB1RC_1LA0LB_1LD0RD_1LB0RC tsucc Ter3WallB.ter_stepB_nil
           boot_1RB1RC_1LA0LB_1LD0RD_1LB0RC).
Qed.

Theorem nonhalt_1RB1RC_1LA0LB_1LD0RD_1LB0RC : NonHalt tm.
Proof. apply (never_qh_nonhalt tm nqh_1RB1RC_1LA0LB_1LD0RD_1LB0RC). Qed.
