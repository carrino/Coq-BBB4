(** * B2L_1RB1LC_1LC1RA_0LC0LD_0RA0RD: the machine never quasihalts.

    A core row of the residue, and [tools/closeout/residue_map.tsv]'s
    [EXP3] / [Alph_11_00_1].  [docs/LADDER_PLAN.md] section 4y measured it as
    BASE TWO -- the [EXP3] label is about the LAP, not the radix -- and
    section 4z pins the anchor and boards it.

    It is a BINARY counter at

      Cf p = (StD, ([], S0, Wp p))

    with [MonoCounter.Wp] VERBATIM: two cells a digit, LSB nearest the head,
    the even pad cell [Wp] already carries.
    [tools/counters/bin3lap.py] checks the right word against [Wp] CELL FOR
    CELL over 1,395 consecutive anchor visits with zero mismatches, values
    [1, 2, 3, ...] with no offset -- so [Cf : positive -> cconf] fits and the
    closer is the PLAIN [LapGlue.glue_neverqh].

    The lap is GEOMETRIC, [3^(c+1) + 2c + 1] in the carry length [c], which
    no ladder arm reaches; [LapGlue]'s lap premise existentially quantifies
    the step count, so [Counters/Bin3Lap.v] never writes it down.

    ** Why it is NEVER-quasihalting

    All four states occur in EVERY lap -- measured, every one of 1,394 laps
    of this row -- which is [glue_neverqh]'s [Hvis] premise.

    ** The one thing this row does not share with its partner

    [1RB1LC_1LB1RA_0LC0LD_0RA0RD] differs only in [B0]: [1LC] here, [1LB]
    there.  Every [B]-on-[S0] event of either row has an [S1] to its left
    (measured, 3,000,000 steps, 250,006 events here, zero exceptions), and
    from that shape both rows run the same composite

      (qB, (S1::L, S0, R))  ->  (qD, (ctl L, chd L, S0::S1::R))

    this row in TWO steps ([B0] hands straight to [qC], which clears the set
    cell) and its partner in four.  That is [Bin3Lap]'s [Hbc], discharged
    here by [Bin3Lap.bc_toC]; nothing downstream sees the difference, so one
    closer serves both rows and the whole lap gap rides inside the
    existential.

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Bin3Lap.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).

(** 1RB1LC_1LC1RA_0LC0LD_0RA0RD *)
Definition tm_1RB1LC_1LC1RA_0LC0LD_0RA0RD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB       | StA, S1 => mk S1 DL StC
  | StB, S0 => mk S1 DL StC       | StB, S1 => mk S1 DR StA
  | StC, S0 => mk S0 DL StC       | StC, S1 => mk S0 DL StD
  | StD, S0 => mk S0 DR StA       | StD, S1 => mk S0 DR StD end.
Local Notation tm := tm_1RB1LC_1LC1RA_0LC0LD_0RA0RD.

(** The counter reads 1 after three steps -- two fewer than its partner,
    which is exactly the composite's two-step saving. *)
Lemma boot_1RB1LC_1LC1RA_0LC0LD_0RA0RD :
  stepn tm 3 InitES = Some (lift (Bin3Lap.Cf StD 1)).
Proof.
  assert (H : match csteps tm 3 c0 with
              | Some c => ceqb c (Bin3Lap.Cf StD 1)
              | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 3 c0) as [c|] eqn:E; [| discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

Lemma hbc_1RB1LC_1LC1RA_0LC0LD_0RA0RD : forall L R, exists n, 0 < n /\
  csteps tm n (StB,(S1::L,S0,R)) = Some (StD,(ctl L,chd L,S0::S1::R)).
Proof. apply (Bin3Lap.bc_toC tm StB StC StD); reflexivity. Qed.

Lemma hbcC_1RB1LC_1LC1RA_0LC0LD_0RA0RD : forall L R, exists k c,
  csteps tm k (StB,(S1::L,S0,R)) = Some c /\ fst c = StC.
Proof. apply (Bin3Lap.bcC_toC tm StB StC); reflexivity. Qed.

Theorem nqh_1RB1LC_1LC1RA_0LC0LD_0RA0RD : NeverQuasiHaltsSt tm.
Proof.
  exact (Bin3Lap.bin3_nqh tm StA StB StC StD
           eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
           hbc_1RB1LC_1LC1RA_0LC0LD_0RA0RD
           hbcC_1RB1LC_1LC1RA_0LC0LD_0RA0RD
           ltac:(intro q; destruct q; auto)
           1%positive
           (ex_intro _ 3 boot_1RB1LC_1LC1RA_0LC0LD_0RA0RD)).
Qed.

Theorem nonhalt_1RB1LC_1LC1RA_0LC0LD_0RA0RD : NonHalt tm.
Proof. apply (never_qh_nonhalt tm nqh_1RB1LC_1LC1RA_0LC0LD_0RA0RD). Qed.
