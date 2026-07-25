(** * ILD_1RB1RD_1LC0LB_1RA1LC_0RD1LB: the first DOUBLED-BIT counter board.

    Machine 1RB1RD_1LC0LB_1RA1LC_0RD1LB, proved never-quasihalting under
    [DpCounter.Dp] -- the encoding that writes each bit TWICE instead of
    separating bits with marker cells.

    Human read: "right wall and 2 copies of each bit."  Both halves are
    load-bearing and both are visible in the anchor:

      Cc p = (StD, (Dp p, S1, []))

    the head cell [S1] is the right wall (it is never consumed -- every lap
    starts and ends on it), and [Dp p] is the counter with every bit doubled,
    least significant nearest the head.

    Why no previous recognizer could see this machine: [Ip]/[Jp] put a MARKER
    cell between consecutive bits and every decoder in this project checks
    that the marker cells all hold [S1].  In a doubled-bit tape the cells at
    that parity ARE the data, so any counter value with a clear bit fails the
    marker test and the machine is reported as having no anchor family at all.
    It sat in the "no anchor" bucket, which was the largest unexplained bucket
    in the residue.

    The lap is the SAME single-sweep skeleton as the Ip/Jp boards, with
    one-CELL-wide ripple and return units (these machines sweep cell by cell,
    not pair by pair):

      interior lap  4 + 4j        overflow lap  4 + 4j

    The interior splits on whether there is a carry run at all -- with [j = 0]
    the prologue lands on [S0] and goes straight to the stop, with [j = S j']
    it lands on [S1] and ripples first.  That is the one structural difference
    from the Ip template, and it is forced: the prologue consumes the cell
    nearest the head, whose value IS the low bit.

    Axiom footprint: [functional_extensionality_dep] (via CTape.lift). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter JpCounter DpCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).

(** 1RB1RD_1LC0LB_1RA1LC_0RD1LB *)
Definition tm_D : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DR StD
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DL StB
  | StC, S0 => mk S1 DR StA | StC, S1 => mk S1 DL StC
  | StD, S0 => mk S0 DR StD | StD, S1 => mk S1 DL StB end.
Local Notation tm := tm_D.

Definition Cc (p : positive) : cconf := (StD, (Dp p, S1, [])).

(** ** The lap unit windows *)

(** The prologue does not read the cell it consumes, so it is uniform in it --
    which is what lets the [j = 0] and [j = S j'] branches share a prologue. *)
Lemma phP1 : forall x L R, csteps tm 1 (StD,(x::L,S1,R)) = Some (StB,(L,x,S1::R)).
Proof. reflexivity. Qed.

Lemma U_RIP : wsteps true true tm 1 (StB,([S1],S1,[])) = Some (StB,([],S1,[S0])).
Proof. reflexivity. Qed.
Lemma U_STP : wsteps true true tm 4 (StB,([S0;S0],S1,[])) = Some (StD,([S1;S1],S0,[])).
Proof. reflexivity. Qed.
Lemma U_STP0 : wsteps true true tm 3 (StB,([S0],S0,[S1])) = Some (StD,([S1;S1],S1,[])).
Proof. reflexivity. Qed.
(** The overflow stop runs off the DEEP end of the counter, so it is left-open. *)
Lemma U_STPO : wsteps false true tm 4 (StB,([],S1,[])) = Some (StD,([S1;S1],S0,[])).
Proof. reflexivity. Qed.
Lemma U_RET : wsteps true true tm 1 (StD,([],S0,[S0])) = Some (StD,([S0],S0,[])).
Proof. reflexivity. Qed.
Lemma U_FIN : wsteps true true tm 1 (StD,([],S0,[S1])) = Some (StD,([S0],S1,[])).
Proof. reflexivity. Qed.
Lemma U_VC : wsteps false true tm 2 (StB,([],S1,[])) = Some (StC,([],S0,[S1;S0])).
Proof. reflexivity. Qed.
Lemma U_VA : wsteps false true tm 3 (StB,([],S1,[])) = Some (StA,([S1],S1,[S0])).
Proof. reflexivity. Qed.

(** ** Transported phases *)

Lemma phRIP : forall k L R,
  csteps tm k (StB,(rep [S1] k ++ L,S1,R)) = Some (StB,(L,S1,rep [S0] k ++ R)).
Proof.
  intros. pose proof (cycL _ _ _ _ _ _ _ U_RIP k L R) as H.
  cbn [app] in H. rewrite Nat.mul_1_l in H. exact H.
Qed.

Lemma phSTP : forall L R, csteps tm 4 (StB,(S0::S0::L,S1,R)) = Some (StD,(S1::S1::L,S0,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STP). Qed.

Lemma phSTP0 : forall L R, csteps tm 3 (StB,(S0::L,S0,S1::R)) = Some (StD,(S1::S1::L,S1,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STP0). Qed.

Lemma phSTPO : forall R, csteps tm 4 (StB,([],S1,R)) = Some (StD,([S1;S1],S0,R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPO). Qed.

Lemma phRET : forall k L R,
  csteps tm k (StD,(L,S0,rep [S0] k ++ R)) = Some (StD,(rep [S0] k ++ L,S0,R)).
Proof.
  intros. pose proof (cycR _ _ _ _ _ _ U_RET k L R) as H.
  rewrite Nat.mul_1_l in H. exact H.
Qed.

Lemma phFIN : forall L R, csteps tm 1 (StD,(L,S0,S1::R)) = Some (StD,(S0::L,S1,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FIN). Qed.

Lemma phVC : forall R, csteps tm 2 (StB,([],S1,R)) = Some (StC,([],S0,S1::S0::R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_VC). Qed.

Lemma phVA : forall R, csteps tm 3 (StB,([],S1,R)) = Some (StA,([S1],S1,S0::R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_VA). Qed.

(** ** Rep algebra: an all-ones run of doubled bits, peeled one cell at a time *)

Lemma ones_peel : forall j, rep [S1;S1] (S j) = S1 :: rep [S1] (S (2*j)).
Proof.
  intro j. rewrite rep_dbl. replace (2 * S j) with (S (S (2*j))) by lia.
  reflexivity.
Qed.

Lemma zeros_fold : forall j, S0 :: rep [S0] (S (2*j)) = rep [S0;S0] (S j).
Proof.
  intro j. rewrite rep_dbl. replace (2 * S j) with (S (S (2*j))) by lia.
  reflexivity.
Qed.

(** ** The lap *)

Lemma lap_int : forall p j q0, cview p = (j, Some q0) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p j q0 Ecv. unfold Cc.
  destruct (cview_some_D p j q0 Ecv) as (HDp & HDs).
  destruct j as [|j'].
  - (* no carry run: the prologue lands on S0 and the stop fires at once *)
    do 2 eexists. split; [|split].
    + rewrite HDp. cbn [rep app].
      eapply csteps_chain. { apply phP1. }
      apply phSTP0.
    + rewrite HDs. cbn [rep app]. reflexivity.
    + lia.
  - (* carry run of length S j': ripple 2j'+1 cells after the prologue *)
    do 2 eexists. split; [|split].
    + rewrite HDp, ones_peel.
      eapply csteps_chain. { apply phP1. }
      eapply csteps_chain. { apply (phRIP (S (2*j'))). }
      eapply csteps_chain. { apply phSTP. }
      eapply csteps_chain. { apply (phRET (S (2*j'))). }
      apply phFIN.
    + rewrite HDs, <- zeros_fold. reflexivity.
    + lia.
Qed.

Lemma lap_ov : forall p j', cview p = (S j', None) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p j' Ecv. unfold Cc.
  destruct (cview_none_D p j' Ecv) as (HDp & HDs).
  do 2 eexists. split; [|split].
  - rewrite HDp, ones_peel.
    eapply csteps_chain. { apply phP1. }
    (* the counter is consumed entirely here, so spell out the empty rest *)
    rewrite <- (app_nil_r (rep [S1] (S (2*j')))).
    eapply csteps_chain. { apply (phRIP (S (2*j'))). }
    eapply csteps_chain. { apply phSTPO. }
    eapply csteps_chain. { apply (phRET (S (2*j'))). }
    apply phFIN.
  - rewrite HDs, <- zeros_fold. reflexivity.
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
  exists 5.
  assert (H : match csteps tm 5 c0 with Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 5 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    [StC] and [StA] fire only inside a stop, at a depth that depends on the
    carry length, so no bounded anchor prefix reaches them.  Both are
    witnessed from one landmark -- the configuration the OVERFLOW stop starts
    from, where the counter has been fully consumed and the left list is
    empty -- reached by well-founded induction on [tovf]. *)
Lemma reach_deep : forall p, exists k R, csteps tm k (Cc p) = Some (StB,([],S1,R)).
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }
    destruct (lap_int p j q0 Ecv) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia))
                 (Pos.succ p) eq_refl) as (k & R & Hk).
    exists (n + k), R. rewrite csteps_add, Hrun. exact Hk.
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv;
        [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_D p j' Ecv) as (HDp & _).
    unfold Cc. eexists. eexists.
    rewrite HDp, ones_peel.
    eapply csteps_chain. { apply phP1. }
    rewrite <- (app_nil_r (rep [S1] (S (2*j')))).
    apply (phRIP (S (2*j'))).
Qed.

Lemma vis_T : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q. destruct q.
  - (* StA : three steps into the overflow stop *)
    destruct (reach_deep p) as (k & R & Hk).
    exists (k + 3). eexists. rewrite csteps_add, Hk.
    split; [apply phVA | reflexivity].
  - (* StB : one step from the anchor, whatever the low bit is *)
    destruct (Dp_pair p) as (x & w & Hw). unfold Cc.
    exists 1. eexists. rewrite Hw. split; [apply phP1 | reflexivity].
  - (* StC : two steps into the overflow stop *)
    destruct (reach_deep p) as (k & R & Hk).
    exists (k + 2). eexists. rewrite csteps_add, Hk.
    split; [apply phVC | reflexivity].
  - (* StD : the anchor state *)
    exists 0. eexists. split; reflexivity.
Qed.

Theorem nqh_1RB1RD_1LC0LB_1RA1LC_0RD1LB : NeverQuasiHaltsSt tm.
Proof.
  apply (glue_neverqh tm Cc 1).
  - exact boot_T.
  - intros p _. apply lap_T.
  - intros p q _. apply vis_T.
Qed.

Theorem tm_D_nonhalt : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_1RB1RD_1LC0LB_1RA1LC_0RD1LB. Qed.
