(** * ILK_1RB0LD_0LC1LA_0RC1LA_1RC0LD: the first PLAIN-counter board.

    Machine 1RB0LD_0LC1LA_0RC1LA_1RC0LD, never-quasihalting under
    [KpCounter.Kp] -- a binary counter with NOTHING between the bits.

    Human read: "wall on the right, msb on the left, normal counter."  Both
    halves are in the anchor:

      Cc p = (StC, (Kp p, S0, [S1]))

    [Kp p] is the plain base-2 word (LSB nearest the head, so MSB deepest =
    leftmost in tape order), and the far side [[S1]] is the right wall.

    This machine is a correction as much as a board.  It was in the bucket I
    had classified as DOUBLED-BIT ([DpCounter.Dp]) -- a doubled read of its
    tape does produce a consecutive decode at one anchor, so the automated
    scan accepted it.  It is not doubled: at the anchor above the word is
    plainly [Kp p], and only THIS reading makes both lap branches affine
    (interior and overflow both 6 + 2j, over 18,750 measured laps).  The
    merged `tools/counter_encodings.tsv` had it right as `KCOPY1`.  A decode
    being consecutive is necessary but nowhere near sufficient -- the lap
    profile is the arbiter.

    Lap: P1 . RIP^(j-1) . STP . RET^j, all one-cell units.  Like the [Dp]
    board the interior splits on whether there is a carry run at all, because
    the prologue consumes the cell nearest the head and that cell IS the low
    bit.

    Axiom footprint: [functional_extensionality_dep] (via CTape.lift). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter JpCounter KpCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).

(** 1RB0LD_0LC1LA_0RC1LA_1RC0LD *)
Definition tm_K : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StD
  | StB, S0 => mk S0 DL StC | StB, S1 => mk S1 DL StA
  | StC, S0 => mk S0 DR StC | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S1 DR StC | StD, S1 => mk S0 DL StD end.
Local Notation tm := tm_K.

Definition Cc (p : positive) : cconf := (StC, (Kp p, S0, [S1])).

(** ** Units

    The prologue never reads the cell it consumes, so it is uniform in it --
    which is what lets both interior branches share it. *)
Lemma phP1 : forall x L R, csteps tm 5 (StC,(x::L,S0,S1::R)) = Some (StD,(L,x,S0::S1::R)).
Proof. reflexivity. Qed.

(** All four states already appear inside that prologue. *)
Lemma phVA : forall x L R, csteps tm 2 (StC,(x::L,S0,S1::R)) = Some (StA,(x::L,S0,S1::R)).
Proof. reflexivity. Qed.
Lemma phVB : forall x L R, csteps tm 3 (StC,(x::L,S0,S1::R)) = Some (StB,(S1::x::L,S1,R)).
Proof. reflexivity. Qed.

Lemma U_RIP : wsteps true true tm 1 (StD,([S1],S1,[])) = Some (StD,([],S1,[S0])).
Proof. reflexivity. Qed.
Lemma U_STP : wsteps true true tm 2 (StD,([S0],S1,[])) = Some (StC,([S1],S0,[])).
Proof. reflexivity. Qed.
Lemma U_STP0 : wsteps true true tm 1 (StD,([],S0,[S0])) = Some (StC,([S1],S0,[])).
Proof. reflexivity. Qed.
(** The overflow stop runs off the deep end of the counter: left-open. *)
Lemma U_STPO : wsteps false true tm 2 (StD,([],S1,[])) = Some (StC,([S1],S0,[])).
Proof. reflexivity. Qed.
Lemma U_RET : wsteps true true tm 1 (StC,([],S0,[S0])) = Some (StC,([S0],S0,[])).
Proof. reflexivity. Qed.

(** ** Phases *)
Lemma phRIP : forall k L R,
  csteps tm k (StD,(rep [S1] k ++ L,S1,R)) = Some (StD,(L,S1,rep [S0] k ++ R)).
Proof.
  intros. pose proof (cycL _ _ _ _ _ _ _ U_RIP k L R) as H.
  cbn [app] in H. rewrite Nat.mul_1_l in H. exact H.
Qed.

Lemma phSTP : forall L R, csteps tm 2 (StD,(S0::L,S1,R)) = Some (StC,(S1::L,S0,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STP). Qed.

Lemma phSTP0 : forall L R, csteps tm 1 (StD,(L,S0,S0::R)) = Some (StC,(S1::L,S0,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STP0). Qed.

Lemma phSTPO : forall R, csteps tm 2 (StD,([],S1,R)) = Some (StC,([S1],S0,R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPO). Qed.

Lemma phRET : forall k L R,
  csteps tm k (StC,(L,S0,rep [S0] k ++ R)) = Some (StC,(rep [S0] k ++ L,S0,R)).
Proof.
  intros. pose proof (cycR _ _ _ _ _ _ U_RET k L R) as H.
  rewrite Nat.mul_1_l in H. exact H.
Qed.

Lemma zeros_snoc : forall k, rep [S0] k ++ [S0] = rep [S0] (S k).
Proof. intro k. cbn [rep]. rewrite rep_shift. reflexivity. Qed.

(** ** The lap *)

Lemma lap_int : forall p j q0, cview p = (j, Some q0) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p j q0 Ecv. unfold Cc.
  destruct (cview_some_K p j q0 Ecv) as (HKp & HKs).
  destruct j as [|j'].
  - do 2 eexists. split; [|split].
    + rewrite HKp. cbn [rep app].
      eapply csteps_chain. { apply phP1. }
      apply phSTP0.
    + rewrite HKs. cbn [rep app]. reflexivity.
    + lia.
  - do 2 eexists. split; [|split].
    + rewrite HKp. cbn [rep app].
      eapply csteps_chain. { apply phP1. }
      eapply csteps_chain. { apply (phRIP j'). }
      eapply csteps_chain. { apply phSTP. }
      change (rep [S0] j' ++ [S0;S1]) with (rep [S0] j' ++ [S0] ++ [S1]).
      rewrite app_assoc, zeros_snoc.
      apply (phRET (S j')).
    + rewrite HKs. reflexivity.
    + lia.
Qed.

Lemma lap_ov : forall p j', cview p = (S j', None) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p j' Ecv. unfold Cc.
  destruct (cview_none_K p j' Ecv) as (HKp & HKs).
  do 2 eexists. split; [|split].
  - rewrite HKp. cbn [rep app].
    eapply csteps_chain. { apply phP1. }
    rewrite <- (app_nil_r (rep [S1] j')).
    eapply csteps_chain. { apply (phRIP j'). }
    eapply csteps_chain. { apply phSTPO. }
    change (rep [S0] j' ++ [S0;S1]) with (rep [S0] j' ++ [S0] ++ [S1]).
    rewrite app_assoc, zeros_snoc.
    apply (phRET (S j')).
  - rewrite HKs. reflexivity.
  - lia.
Qed.

Lemma lap_exact : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - exact (lap_int p j q0 Ecv).
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv;
        [destruct (cview p); discriminate|discriminate|discriminate]. }
    exact (lap_ov p j' Ecv).
Qed.

Lemma lap_T : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (lap_exact p) as (n & c' & Hr & Hc & Hn).
  exists n, c'. split; [exact Hr | split; [rewrite Hc; reflexivity | exact Hn]].
Qed.

Lemma boot_T : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 7.
  assert (H : match csteps tm 7 c0 with Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 7 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** Every state fires inside the fixed 5-step prologue, so no trajectory
    induction is needed here at all. *)
Lemma vis_T : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q. destruct (Kp_nonnil p) as (x & w & Hw). unfold Cc. rewrite Hw.
  destruct q.
  - exists 2. eexists. split; [apply phVA | reflexivity].
  - exists 3. eexists. split; [apply phVB | reflexivity].
  - exists 0. eexists. split; reflexivity.
  - exists 5. eexists. split; [apply phP1 | reflexivity].
Qed.

Theorem nqh_1RB0LD_0LC1LA_0RC1LA_1RC0LD : NeverQuasiHaltsSt tm.
Proof.
  apply (glue_neverqh tm Cc 1).
  - exact boot_T.
  - intros p _. apply lap_T.
  - intros p q _. apply vis_T.
Qed.

Theorem tm_K_nonhalt : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_1RB0LD_0LC1LA_0RC1LA_1RC0LD. Qed.
