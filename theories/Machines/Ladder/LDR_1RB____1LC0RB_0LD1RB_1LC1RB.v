(** * LDR_1RB____1LC0RB_0LD1RB_1LC1RB: machine 1RB---_1LC0RB_0LD1RB_1LC1RB, boarded by the LAZY FIBONACCI ladder.

    Emitted by [tools/ladder/emit_lazyfib.py] (UNTRUSTED); every line below is
    re-checked by the kernel.

    The counter reads in the kernel's own fibonacci numeration -- the digit at
    index [i] carries weight [1, 1, 2, 3, 5, 8, ...] -- and stands on its LAZY
    representative: LSB-first, [d0 = 1], NO TWO ZEROS ADJACENT, top digit [1].
    That is a different canonical form from [LadderCheck] section 3c's, not a
    different numeration; LADDER_PLAN 4v and 4w measured it twice, by
    independent routes, over 23,614 values of this row.

    The board is [LadderCheck.boardL_iqh] (section 12).  This row QUASIHALTS:
    [StA] fires once, at step 0, and is the target of no transition, so the
    theorem is the [iqh] triple and not [NeverQuasiHaltsSt].

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Counters Require Import WTape LapGlueQuiet.
From BBB4.Checkers Require Import LapDecider LapAvoid LadderKernel LadderFam.
From BBB4.Checkers Require Import LadderCheck.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB---_1LC0RB_0LD1RB_1LC1RB *)
Definition tm_1RB____1LC0RB_0LD1RB_1LC1RB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB
  | StA, S1 => None
  | StB, S0 => mk S1 DL StC
  | StB, S1 => mk S0 DR StB
  | StC, S0 => mk S0 DL StD
  | StC, S1 => mk S1 DR StB
  | StD, S0 => mk S1 DL StC
  | StD, S1 => mk S1 DR StB end.
Local Notation tm := tm_1RB____1LC0RB_0LD1RB_1LC1RB.

(** ** The family, as DATA

    One cell per digit, no prefix, no terminator, the counter on the RIGHT
    with an empty far side, code [FibL] and step 1.  [fm_fills] is EMPTY: at
    [FibL] the fill is [lazfill], a function of the width, so there is no
    [Fill] record to carry and the family is one-phase whatever the width
    does.  [fam_fill] falls through to [carry_fill], whose [f_to] is 0, which
    is the only field [fam_succ] still reads. *)
Definition fam_1RB____1LC0RB_0LD1RB_1LC1RB : Fam :=
  mkFam 2 [[S0];[S1]] [] [[]] FibL 1 [] StC S1 false [].
Local Notation FAM := fam_1RB____1LC0RB_0LD1RB_1LC1RB.

(** ** The ladder, as DATA

    Empty: every arm below derives from the machine's own window, cycle and
    rotation steps, with no earlier rule invoked. *)
Definition lad_1RB____1LC0RB_0LD1RB_1LC1RB : list (LRule * list rstep) := [].
Local Notation lad := lad_1RB____1LC0RB_0LD1RB_1LC1RB.

Definition rules_1RB____1LC0RB_0LD1RB_1LC1RB : list LRule := map fst lad.
Local Notation rules := rules_1RB____1LC0RB_0LD1RB_1LC1RB.

Lemma ladder_ok_1RB____1LC0RB_0LD1RB_1LC1RB : check_ladder tm [] lad = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rules_sound_1RB____1LC0RB_0LD1RB_1LC1RB : Forall (RuleSound tm false false) rules.
Proof. apply rule_sound_nil. exact ladder_ok_1RB____1LC0RB_0LD1RB_1LC1RB. Qed.

Definition iarm0_0_1RB____1LC0RB_0LD1RB_1LC1RB : LRule :=
  mkLRule (mkC StC (mkS [] [] 0 0 []) S1 (mkS [S0] [] 0 0 []))
          (mkC StC (mkS [] [] 0 0 []) S1 (mkS [S1] [] 0 0 [])) 0 2.
Definition ch_iarm0_0_1RB____1LC0RB_0LD1RB_1LC1RB : list rstep := [RB (SWin 2)].
Lemma ok_iarm0_0_1RB____1LC0RB_0LD1RB_1LC1RB :
  check_arm tm (negb false) false rules iarm0_0_1RB____1LC0RB_0LD1RB_1LC1RB
            ch_iarm0_0_1RB____1LC0RB_0LD1RB_1LC1RB = true.
Proof. vm_compute. reflexivity. Qed.

Definition iarm0_1_1RB____1LC0RB_0LD1RB_1LC1RB : LRule :=
  mkLRule (mkC StC (mkS [] [] 0 0 []) S1 (mkS [S1;S1] [S1;S1] 1 0 [S0]))
          (mkC StC (mkS [] [] 0 0 []) S1 (mkS [S1;S0] [S1;S0] 1 0 [S1])) 4 6.
Definition ch_iarm0_1_1RB____1LC0RB_0LD1RB_1LC1RB : list rstep := [RB (SWin 2);RB (SCycR 2);RB (SWin 2);RB (SCycL 2 0);RB (SWin 2)].
Lemma ok_iarm0_1_1RB____1LC0RB_0LD1RB_1LC1RB :
  check_arm tm (negb false) false rules iarm0_1_1RB____1LC0RB_0LD1RB_1LC1RB
            ch_iarm0_1_1RB____1LC0RB_0LD1RB_1LC1RB = true.
Proof. vm_compute. reflexivity. Qed.

Definition iarm1_0_1RB____1LC0RB_0LD1RB_1LC1RB : LRule :=
  mkLRule (mkC StC (mkS [] [] 0 0 []) S1 (mkS [S1;S0] [] 0 0 []))
          (mkC StC (mkS [] [] 0 0 []) S1 (mkS [S1;S1] [] 0 0 [])) 0 6.
Definition ch_iarm1_0_1RB____1LC0RB_0LD1RB_1LC1RB : list rstep := [RB (SWin 6)].
Lemma ok_iarm1_0_1RB____1LC0RB_0LD1RB_1LC1RB :
  check_arm tm (negb false) false rules iarm1_0_1RB____1LC0RB_0LD1RB_1LC1RB
            ch_iarm1_0_1RB____1LC0RB_0LD1RB_1LC1RB = true.
Proof. vm_compute. reflexivity. Qed.

Definition iarm1_1_1RB____1LC0RB_0LD1RB_1LC1RB : LRule :=
  mkLRule (mkC StC (mkS [] [] 0 0 []) S1 (mkS [S1;S1;S1] [S1;S1] 1 0 [S0]))
          (mkC StC (mkS [] [] 0 0 []) S1 (mkS [S1;S1;S0] [S1;S0] 1 0 [S1])) 4 10.
Definition ch_iarm1_1_1RB____1LC0RB_0LD1RB_1LC1RB : list rstep := [RB (SWin 3);RB (SCycR 2);RB (SWin 2);RB (SCycL 2 0);RB (SWin 5)].
Lemma ok_iarm1_1_1RB____1LC0RB_0LD1RB_1LC1RB :
  check_arm tm (negb false) false rules iarm1_1_1RB____1LC0RB_0LD1RB_1LC1RB
            ch_iarm1_1_1RB____1LC0RB_0LD1RB_1LC1RB = true.
Proof. vm_compute. reflexivity. Qed.

Definition farm1_1RB____1LC0RB_0LD1RB_1LC1RB : LRule :=
  mkLRule (mkC StC (mkS [] [] 0 0 []) S1 (mkS [] [S1;S1] 1 0 [S1]))
          (mkC StC (mkS [] [] 0 0 []) S1 (mkS [S1] [S1;S0] 1 0 [S1])) 4 6.
Definition ch_farm1_1RB____1LC0RB_0LD1RB_1LC1RB : list rstep := [RB (SRotR 1);RB (SWin 1);RB (SCycR 2);RB (SWinR 2);RB (SCycL 2 0);RB (SWin 3)].
Lemma ok_farm1_1RB____1LC0RB_0LD1RB_1LC1RB :
  check_arm tm true true rules farm1_1RB____1LC0RB_0LD1RB_1LC1RB ch_farm1_1RB____1LC0RB_0LD1RB_1LC1RB = true.
Proof. vm_compute. reflexivity. Qed.

Definition farm2_1RB____1LC0RB_0LD1RB_1LC1RB : LRule :=
  mkLRule (mkC StC (mkS [] [] 0 0 []) S1 (mkS [] [S1;S1] 1 0 [S1;S1]))
          (mkC StC (mkS [] [] 0 0 []) S1 (mkS [] [S1;S0] 1 0 [S1;S0;S1])) 4 6.
Definition ch_farm2_1RB____1LC0RB_0LD1RB_1LC1RB : list rstep := [RB (SRotR 1);RB (SWin 1);RB (SCycR 2);RB (SWin 1);RB (SWinR 3);RB (SCycL 2 0);RB (SWin 1);RB (SUnrotR 1)].
Lemma ok_farm2_1RB____1LC0RB_0LD1RB_1LC1RB :
  check_arm tm true true rules farm2_1RB____1LC0RB_0LD1RB_1LC1RB ch_farm2_1RB____1LC0RB_0LD1RB_1LC1RB = true.
Proof. vm_compute. reflexivity. Qed.

(** ** The arms, as DATA

    Two interior classes (section 3d's, split on the PARITY of the low run of
    ones) at threshold 1 stride 1, and one fill arm per WIDTH
    index at threshold 1 stride 2 -- the stride the parity pins. *)
Definition iarm_1RB____1LC0RB_0LD1RB_1LC1RB (i r : nat) : LRule :=
  match i, r with
  | 0, 0 => iarm0_0_1RB____1LC0RB_0LD1RB_1LC1RB
  | 0, 1 => iarm0_1_1RB____1LC0RB_0LD1RB_1LC1RB
  | 1, 0 => iarm1_0_1RB____1LC0RB_0LD1RB_1LC1RB
  | 1, 1 => iarm1_1_1RB____1LC0RB_0LD1RB_1LC1RB
  | _, _ => iarm0_0_1RB____1LC0RB_0LD1RB_1LC1RB   (* unreachable: i < 2 and r < N0i + sti *)
  end.

Definition farm_1RB____1LC0RB_0LD1RB_1LC1RB (r : nat) : LRule :=
  match r with
  | 1 => farm1_1RB____1LC0RB_0LD1RB_1LC1RB
  | 2 => farm2_1RB____1LC0RB_0LD1RB_1LC1RB
  | _ => farm1_1RB____1LC0RB_0LD1RB_1LC1RB   (* unreachable: 1 <= r < N0f + 2 *)
  end.

Definition fw1_1RB____1LC0RB_0LD1RB_1LC1RB (r : nat) : nat := match r with | 1 => 0 | 2 => 0 | _ => 0 end.
Definition fw2_1RB____1LC0RB_0LD1RB_1LC1RB (r : nat) : nat := match r with | 1 => 1 | 2 => 2 | _ => 0 end.
Definition fm1_1RB____1LC0RB_0LD1RB_1LC1RB (r : nat) : nat := match r with | 1 => 0 | 2 => 0 | _ => 0 end.
Definition fm2_1RB____1LC0RB_0LD1RB_1LC1RB (r : nat) : nat := match r with | 1 => 0 | 2 => 1 | _ => 0 end.

(** One chain per state per fill arm.  [vis_of_run] turns each into a visit
    and [topsL_cofinal] says the tops keep coming, which is all the liveness
    needs. *)
Definition vis_1RB____1LC0RB_0LD1RB_1LC1RB (r : nat) (q : St) : list lstep :=
  match r, q with
  | 1, StB => [SRotR 1;SWin 1]
  | 1, StC => []
  | 1, StD => [SRotR 1;SWin 1;SCycR 2;SWinR 2;SCycL 2 0;SWin 1]
  | 2, StB => [SRotR 1;SWin 1]
  | 2, StC => []
  | 2, StD => [SRotR 1;SWin 1;SCycR 2;SWinR 4]
  | _, _ => []
  end.

Lemma iarm_sound_1RB____1LC0RB_0LD1RB_1LC1RB : forall i r,
  i < 2 -> r < 1 + 1 ->
  RuleSound tm (negb (fm_left FAM)) (fm_left FAM) (iarm_1RB____1LC0RB_0LD1RB_1LC1RB i r).
Proof.
  intros i r Hi Hr.
  destruct i as [|i].
  {
    destruct r as [|r].
    { eapply arm_sound; [exact rules_sound_1RB____1LC0RB_0LD1RB_1LC1RB | exact ok_iarm0_0_1RB____1LC0RB_0LD1RB_1LC1RB]. }
    destruct r as [|r].
    { eapply arm_sound; [exact rules_sound_1RB____1LC0RB_0LD1RB_1LC1RB | exact ok_iarm0_1_1RB____1LC0RB_0LD1RB_1LC1RB]. }
    exfalso; lia.
  }
  destruct i as [|i].
  {
    destruct r as [|r].
    { eapply arm_sound; [exact rules_sound_1RB____1LC0RB_0LD1RB_1LC1RB | exact ok_iarm1_0_1RB____1LC0RB_0LD1RB_1LC1RB]. }
    destruct r as [|r].
    { eapply arm_sound; [exact rules_sound_1RB____1LC0RB_0LD1RB_1LC1RB | exact ok_iarm1_1_1RB____1LC0RB_0LD1RB_1LC1RB]. }
    exfalso; lia.
  }
  exfalso; lia.
Qed.

Lemma iarm_lhs_1RB____1LC0RB_0LD1RB_1LC1RB : forall i r, i < 2 -> r < 1 + 1 ->
  lr_lhs (iarm_1RB____1LC0RB_0LD1RB_1LC1RB i r)
    = cls_conf FAM (cls_sideW FAM (cw_u (flc i)) (cw_t (flc i)) r
                      (astride 1 1 r) (cw_w (flc i))).
Proof.
  intros i r Hi Hr.
  destruct i as [|i].
  {
    destruct r as [|r].
    { vm_compute; reflexivity. }
    destruct r as [|r].
    { vm_compute; reflexivity. }
    exfalso; lia.
  }
  destruct i as [|i].
  {
    destruct r as [|r].
    { vm_compute; reflexivity. }
    destruct r as [|r].
    { vm_compute; reflexivity. }
    exfalso; lia.
  }
  exfalso; lia.
Qed.

Lemma iarm_rhs_1RB____1LC0RB_0LD1RB_1LC1RB : forall i r, i < 2 -> r < 1 + 1 ->
  lr_rhs (iarm_1RB____1LC0RB_0LD1RB_1LC1RB i r)
    = cls_conf FAM (cls_sideW FAM (cw_u' (flc i)) (cw_t' (flc i)) r
                      (astride 1 1 r) (cw_w' (flc i))).
Proof.
  intros i r Hi Hr.
  destruct i as [|i].
  {
    destruct r as [|r].
    { vm_compute; reflexivity. }
    destruct r as [|r].
    { vm_compute; reflexivity. }
    exfalso; lia.
  }
  destruct i as [|i].
  {
    destruct r as [|r].
    { vm_compute; reflexivity. }
    destruct r as [|r].
    { vm_compute; reflexivity. }
    exfalso; lia.
  }
  exfalso; lia.
Qed.

Lemma iarm_cb_1RB____1LC0RB_0LD1RB_1LC1RB : forall i r, i < 2 -> r < 1 + 1 ->
  0 < lr_cb (iarm_1RB____1LC0RB_0LD1RB_1LC1RB i r).
Proof.
  intros i r Hi Hr.
  destruct i as [|i].
  {
    destruct r as [|r].
    { vm_compute; lia. }
    destruct r as [|r].
    { vm_compute; lia. }
    exfalso; lia.
  }
  destruct i as [|i].
  {
    destruct r as [|r].
    { vm_compute; lia. }
    destruct r as [|r].
    { vm_compute; lia. }
    exfalso; lia.
  }
  exfalso; lia.
Qed.

Lemma farm_sound_1RB____1LC0RB_0LD1RB_1LC1RB : forall r, 1 <= r -> r < 1 + 2 ->
  RuleSound tm true true (farm_1RB____1LC0RB_0LD1RB_1LC1RB r).
Proof.
  intros r H1 Hr.
  destruct r as [|r].
  { exfalso; lia. }
  destruct r as [|r].
  { eapply arm_sound; [exact rules_sound_1RB____1LC0RB_0LD1RB_1LC1RB | exact ok_farm1_1RB____1LC0RB_0LD1RB_1LC1RB]. }
  destruct r as [|r].
  { eapply arm_sound; [exact rules_sound_1RB____1LC0RB_0LD1RB_1LC1RB | exact ok_farm2_1RB____1LC0RB_0LD1RB_1LC1RB]. }
  exfalso; lia.
Qed.

Lemma farm_lhs_1RB____1LC0RB_0LD1RB_1LC1RB : forall r, 1 <= r -> r < 1 + 2 ->
  lr_lhs (farm_1RB____1LC0RB_0LD1RB_1LC1RB r)
    = cls_conf FAM (run_sideW FAM [1] (fw1_1RB____1LC0RB_0LD1RB_1LC1RB r)
                      (astride 1 2 r) (fw2_1RB____1LC0RB_0LD1RB_1LC1RB r) 0 [] []).
Proof.
  intros r H1 Hr.
  destruct r as [|r].
  { exfalso; lia. }
  destruct r as [|r].
  { vm_compute; reflexivity. }
  destruct r as [|r].
  { vm_compute; reflexivity. }
  exfalso; lia.
Qed.

Lemma farm_rhs_1RB____1LC0RB_0LD1RB_1LC1RB : forall r, 1 <= r -> r < 1 + 2 ->
  lr_rhs (farm_1RB____1LC0RB_0LD1RB_1LC1RB r)
    = cls_conf FAM (run_sideW FAM [1;0] (fm1_1RB____1LC0RB_0LD1RB_1LC1RB r)
                      (Nat.div2 (astride 1 2 r)) (fm2_1RB____1LC0RB_0LD1RB_1LC1RB r) 0
                      (if Nat.even r then [] else [1]) [1]).
Proof.
  intros r H1 Hr.
  destruct r as [|r].
  { exfalso; lia. }
  destruct r as [|r].
  { vm_compute; reflexivity. }
  destruct r as [|r].
  { vm_compute; reflexivity. }
  exfalso; lia.
Qed.

Lemma farm_cb_1RB____1LC0RB_0LD1RB_1LC1RB : forall r, 1 <= r -> r < 1 + 2 ->
  0 < lr_cb (farm_1RB____1LC0RB_0LD1RB_1LC1RB r).
Proof.
  intros r H1 Hr.
  destruct r as [|r].
  { exfalso; lia. }
  destruct r as [|r].
  { vm_compute; lia. }
  destruct r as [|r].
  { vm_compute; lia. }
  exfalso; lia.
Qed.

Lemma fw_1RB____1LC0RB_0LD1RB_1LC1RB : forall r, 1 <= r -> r < 1 + 2 ->
  fw1_1RB____1LC0RB_0LD1RB_1LC1RB r + fw2_1RB____1LC0RB_0LD1RB_1LC1RB r = r.
Proof.
  intros r H1 Hr.
  destruct r as [|r].
  { exfalso; lia. }
  destruct r as [|r].
  { vm_compute; lia. }
  destruct r as [|r].
  { vm_compute; lia. }
  exfalso; lia.
Qed.

Lemma fm_1RB____1LC0RB_0LD1RB_1LC1RB : forall r, 1 <= r -> r < 1 + 2 ->
  fm1_1RB____1LC0RB_0LD1RB_1LC1RB r + fm2_1RB____1LC0RB_0LD1RB_1LC1RB r = Nat.div2 r.
Proof.
  intros r H1 Hr.
  destruct r as [|r].
  { exfalso; lia. }
  destruct r as [|r].
  { vm_compute; lia. }
  destruct r as [|r].
  { vm_compute; lia. }
  exfalso; lia.
Qed.

Lemma boot_1RB____1LC0RB_0LD1RB_1LC1RB :
  csteps tm 2 c0 = Some (fam_cfg FAM ([1], 0, 0)).
Proof. vm_compute. reflexivity. Qed.

Lemma vis_ok_1RB____1LC0RB_0LD1RB_1LC1RB : forall r q, q <> StA -> 1 <= r ->
  r < 1 + 2 ->
  srun_st tm true true (vis_1RB____1LC0RB_0LD1RB_1LC1RB r q) (lr_lhs (farm_1RB____1LC0RB_0LD1RB_1LC1RB r)) = Some q.
Proof.
  intros r q Hq H1 Hr.
  destruct r as [|r].
  { exfalso; lia. }
  destruct r as [|r].
  { destruct q; try (exfalso; apply Hq; reflexivity); vm_compute; reflexivity. }
  destruct r as [|r].
  { destruct q; try (exfalso; apply Hq; reflexivity); vm_compute; reflexivity. }
  exfalso; lia.
Qed.

(** *** The arms avoid the quiet state

    Recomputed from the SAME chains the kernel already replays: a chain whose
    trace touches [StA] evaluates to [false] and this file fails to
    compile. *)
Lemma av_iarm0_0_1RB____1LC0RB_0LD1RB_1LC1RB :
  RuleAvoid tm (negb (fm_left FAM)) (fm_left FAM) StA iarm0_0_1RB____1LC0RB_0LD1RB_1LC1RB.
Proof. eapply arm_avoid; [exact ok_iarm0_0_1RB____1LC0RB_0LD1RB_1LC1RB | vm_compute; reflexivity]. Qed.

Lemma av_iarm0_1_1RB____1LC0RB_0LD1RB_1LC1RB :
  RuleAvoid tm (negb (fm_left FAM)) (fm_left FAM) StA iarm0_1_1RB____1LC0RB_0LD1RB_1LC1RB.
Proof. eapply arm_avoid; [exact ok_iarm0_1_1RB____1LC0RB_0LD1RB_1LC1RB | vm_compute; reflexivity]. Qed.

Lemma av_iarm1_0_1RB____1LC0RB_0LD1RB_1LC1RB :
  RuleAvoid tm (negb (fm_left FAM)) (fm_left FAM) StA iarm1_0_1RB____1LC0RB_0LD1RB_1LC1RB.
Proof. eapply arm_avoid; [exact ok_iarm1_0_1RB____1LC0RB_0LD1RB_1LC1RB | vm_compute; reflexivity]. Qed.

Lemma av_iarm1_1_1RB____1LC0RB_0LD1RB_1LC1RB :
  RuleAvoid tm (negb (fm_left FAM)) (fm_left FAM) StA iarm1_1_1RB____1LC0RB_0LD1RB_1LC1RB.
Proof. eapply arm_avoid; [exact ok_iarm1_1_1RB____1LC0RB_0LD1RB_1LC1RB | vm_compute; reflexivity]. Qed.

Lemma av_farm1_1RB____1LC0RB_0LD1RB_1LC1RB :
  RuleAvoid tm true true StA farm1_1RB____1LC0RB_0LD1RB_1LC1RB.
Proof. eapply arm_avoid; [exact ok_farm1_1RB____1LC0RB_0LD1RB_1LC1RB | vm_compute; reflexivity]. Qed.

Lemma av_farm2_1RB____1LC0RB_0LD1RB_1LC1RB :
  RuleAvoid tm true true StA farm2_1RB____1LC0RB_0LD1RB_1LC1RB.
Proof. eapply arm_avoid; [exact ok_farm2_1RB____1LC0RB_0LD1RB_1LC1RB | vm_compute; reflexivity]. Qed.


Lemma iarm_avoid_1RB____1LC0RB_0LD1RB_1LC1RB : forall i r,
  i < 2 -> r < 1 + 1 ->
  RuleAvoid tm (negb (fm_left FAM)) (fm_left FAM) StA (iarm_1RB____1LC0RB_0LD1RB_1LC1RB i r).
Proof.
  intros i r Hi Hr.
  destruct i as [|i].
  {
    destruct r as [|r].
    { exact av_iarm0_0_1RB____1LC0RB_0LD1RB_1LC1RB. }
    destruct r as [|r].
    { exact av_iarm0_1_1RB____1LC0RB_0LD1RB_1LC1RB. }
    exfalso; lia.
  }
  destruct i as [|i].
  {
    destruct r as [|r].
    { exact av_iarm1_0_1RB____1LC0RB_0LD1RB_1LC1RB. }
    destruct r as [|r].
    { exact av_iarm1_1_1RB____1LC0RB_0LD1RB_1LC1RB. }
    exfalso; lia.
  }
  exfalso; lia.
Qed.

Lemma farm_avoid_1RB____1LC0RB_0LD1RB_1LC1RB : forall r, 1 <= r -> r < 1 + 2 ->
  RuleAvoid tm true true StA (farm_1RB____1LC0RB_0LD1RB_1LC1RB r).
Proof.
  intros r H1 Hr.
  destruct r as [|r].
  { exfalso; lia. }
  destruct r as [|r].
  { exact av_farm1_1RB____1LC0RB_0LD1RB_1LC1RB. }
  destruct r as [|r].
  { exact av_farm2_1RB____1LC0RB_0LD1RB_1LC1RB. }
  exfalso; lia.
Qed.

(** *** The quiet state's last visit, and the window from it to the anchor *)
Lemma qvis_1RB____1LC0RB_0LD1RB_1LC1RB : VisitsAt tm StA 0.
Proof. apply bootvis_chk_sound. vm_compute. reflexivity. Qed.

Lemma qwin_1RB____1LC0RB_0LD1RB_1LC1RB : forall n c, 0 < n < 2 ->
  stepn tm n InitES = Some c -> fst c <> StA.
Proof.
  intros n c Hn Hstep.
  exact (bootquiet_chk_sound tm StA 1 1
           ltac:(vm_compute; reflexivity) n c ltac:(lia) Hstep).
Qed.

(** The machine-level theorem.  The counter laps forever over the lazy
    fibonacci numeration and every state but [StA] recurs; [StA] stops
    firing after index 0 -- it is entered once, at step 0, and is the
    target of no transition.  [boardL_iqh] returns the exact bound and it is
    weakened to the census tier's 2000. *)
Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.

Theorem iqh_1RB____1LC0RB_0LD1RB_1LC1RB : iqh tm.
Proof.
  assert (H : NonHalt tm /\ QHBound (S 0) tm /\ QuasiHaltsSt tm).
  { apply (boardL_iqh tm FAM iarm_1RB____1LC0RB_0LD1RB_1LC1RB 1 1
                      farm_1RB____1LC0RB_0LD1RB_1LC1RB 1
                      fw1_1RB____1LC0RB_0LD1RB_1LC1RB fw2_1RB____1LC0RB_0LD1RB_1LC1RB fm1_1RB____1LC0RB_0LD1RB_1LC1RB fm2_1RB____1LC0RB_0LD1RB_1LC1RB
                      [1] 2 StA 0 vis_1RB____1LC0RB_0LD1RB_1LC1RB).
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - repeat constructor.
    - vm_compute; lia.
    - vm_compute; reflexivity.
    - exact boot_1RB____1LC0RB_0LD1RB_1LC1RB.
    - lia.
    - exact iarm_sound_1RB____1LC0RB_0LD1RB_1LC1RB.
    - exact iarm_lhs_1RB____1LC0RB_0LD1RB_1LC1RB.
    - exact iarm_rhs_1RB____1LC0RB_0LD1RB_1LC1RB.
    - exact iarm_cb_1RB____1LC0RB_0LD1RB_1LC1RB.
    - lia.
    - exact fw_1RB____1LC0RB_0LD1RB_1LC1RB.
    - exact fm_1RB____1LC0RB_0LD1RB_1LC1RB.
    - exact farm_sound_1RB____1LC0RB_0LD1RB_1LC1RB.
    - exact farm_lhs_1RB____1LC0RB_0LD1RB_1LC1RB.
    - exact farm_rhs_1RB____1LC0RB_0LD1RB_1LC1RB.
    - exact farm_cb_1RB____1LC0RB_0LD1RB_1LC1RB.
    - exact iarm_avoid_1RB____1LC0RB_0LD1RB_1LC1RB.
    - exact farm_avoid_1RB____1LC0RB_0LD1RB_1LC1RB.
    - exact vis_ok_1RB____1LC0RB_0LD1RB_1LC1RB.
    - exact qvis_1RB____1LC0RB_0LD1RB_1LC1RB.
    - exact qwin_1RB____1LC0RB_0LD1RB_1LC1RB. }
  destruct H as (Hn & Hb & Hq).
  split; [exact Hn | split; [| exact Hq]].
  apply (qhbound_mono (S 0) 2000); [lia | exact Hb].
Qed.
