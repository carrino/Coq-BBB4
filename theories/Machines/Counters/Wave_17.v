(** * Wave_17: the wave_counter machine #17, 1RB0RD_0LB1LC_1RA1LB_1RA1RD.

    WORK IN PROGRESS (wave track).  Edge state D, side R, poff 0,
    boot_vector [1;1;2;3] (cert results/counter17.cert).  The event
    config is the block word (frontier-first, lead dropped as the
    implicit trailing 1):

      Cf(front) = (StD, (1^{B_m} 0 1^{B_{m-1}} 0 ... 0 1^{B_1} 0 1, S0, [])),

    head one cell past the frontier.  The abstract pass [nextf 0] and
    its safety invariant [WInv 0] live in [WaveCounter]; this file
    carries the machine and the per-pass CONCRETE run (P1): a frontier
    turnaround, a leftward carry wave of parity-alternating run
    crossings ([cross_run] -- the crux, DONE below), a deposit, and a
    rightward reconstruction sweep.  No axioms beyond
    [functional_extensionality_dep]. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape WaveCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).

(** 1RB0RD_0LB1LC_1RA1LB_1RA1RD *)
Definition tm_17 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DR StD
  | StB, S0 => mk S0 DL StB | StB, S1 => mk S1 DL StC
  | StC, S0 => mk S1 DR StA | StC, S1 => mk S1 DL StB
  | StD, S0 => mk S1 DR StA | StD, S1 => mk S1 DR StD
  end.

(** ** The crux: crossing a run of ones leftward.

    From the frontier-turnaround the head sits on the top one of a run
    in state B; it walks left over the run (B and C alternating), and
    the state on reaching the separator encodes the run's parity -- B
    (continue the wave) if the run length is odd, C (stop and deposit)
    if even.  The [S k] ones (head plus [k] in the left list) are
    re-deposited on the right. *)
Definition stB (k : nat) : St := if Nat.even k then StC else StB.

Lemma cross_run : forall k rest R,
  csteps tm_17 (S k) (StB, (rep [S1] k ++ S0 :: rest, S1, R))
  = Some (stB k, (rest, S0, rep [S1] (S k) ++ R)).
Proof.
  intro k. pattern k. apply (well_founded_ind lt_wf). clear k.
  intros k IH rest R. destruct k as [|[|k']].
  - reflexivity.
  - reflexivity.
  - change (rep [S1] (S (S k'))) with (S1 :: S1 :: rep [S1] k').
    eapply csteps_chain with
      (n1 := 2) (n2 := S k')
      (c1 := (StB, (rep [S1] k' ++ S0 :: rest, S1, S1 :: S1 :: R))).
    + reflexivity.
    + rewrite (IH k' ltac:(lia) rest (S1 :: S1 :: R)).
      unfold stB. rewrite Nat.even_succ, Nat.odd_succ.
      f_equal. f_equal. f_equal.
      change (S1 :: S1 :: R) with (rep [S1] 2 ++ R).
      rewrite app_assoc, <- rep_add.
      replace (S k' + 2) with (S (S (S k'))) by lia. reflexivity.
Qed.

(** ** The block-word encoding *)

Fixpoint wbody (front : list nat) : list Sym :=
  match front with
  | [] => [S1]
  | b :: r => rep [S1] b ++ S0 :: wbody r
  end.

Definition Cf17 (front : list nat) : cconf := (StD, (wbody front, S0, [])).

(** ** Generic phase units (all reflexivity via [wsteps] + transport) *)

(** Frontier turnaround: never reads the left, materialises blanks right. *)
Lemma ph_FT : forall L, csteps tm_17 3 (StD, (L, S0, [])) = Some (StB, (S1 :: L, S1, [S0])).
Proof.
  intro L.
  pose proof (wsteps_frame_r tm_17 3 StD [] S0 [] StB [S1] S1 [S0] L) as H.
  cbn [app] in H. apply H. reflexivity.
Qed.

(** Separator-continue: at a separator [S0] in state B, step onto the next
    block's top one, still in state B. *)
Lemma ph_sepB : forall rest R,
  csteps tm_17 1 (StB, (S1 :: rest, S0, R)) = Some (StB, (rest, S1, S0 :: R)).
Proof.
  intros rest R.
  pose proof (wsteps_frame tm_17 1 StB [S1] S0 [] StB [] S1 [S0] rest R) as H.
  cbn [app] in H. apply H. reflexivity.
Qed.

(** Deposit: at a separator [S0] in state C with a swept one on the right,
    write [S1] (grow the block) and turn to a rightward sweep in A. *)
Lemma ph_dep : forall X R,
  csteps tm_17 1 (StC, (X, S0, S1 :: R)) = Some (StA, (S1 :: X, S1, R)).
Proof.
  intros X R.
  pose proof (wsteps_frame tm_17 1 StC [] S0 [S1] StA [S1] S1 [] X R) as H.
  cbn [app] in H. apply H. reflexivity.
Qed.

(** Spawn: at the lead's separator the head crosses the lead into the left
    blank and deposits a new leftmost block. *)
Lemma ph_spawn : forall R,
  csteps tm_17 3 (StB, ([S1], S0, R)) = Some (StA, ([S1], S1, S0 :: R)).
Proof. reflexivity. Qed.

(** ** The leftward carry wave (fold, mirrors [carry]).

    [outL]/[outR] give the deposit-turnaround config (state A, ready to
    sweep right).  [po] tracks "deposit here" as in [carry]; the wave
    crosses even blocks (run onto the right), deposits at the first odd
    block, or spawns past the lead. *)
Fixpoint outL (po : bool) (blocks : list nat) : list Sym :=
  match blocks with
  | [] => [S1]
  | b :: r => if po then S1 :: wbody (b :: r) else outL (Nat.odd b) r
  end.

Fixpoint outR (po : bool) (blocks : list nat) (R : list Sym) : list Sym :=
  match blocks with
  | [] => S0 :: R
  | b :: r => if po then tl R else outR (Nat.odd b) r (rep [S1] b ++ S0 :: R)
  end.

Lemma wave_L : forall blocks po R,
  carry_ok po blocks = true ->
  Forall (fun x => 1 <= x) blocks ->
  (po = true -> exists R', R = S1 :: R') ->
  wreach tm_17 (if po then StC else StB, (wbody blocks, S0, R))
              (StA, (outL po blocks, S1, outR po blocks R)).
Proof.
  induction blocks as [|b r IH]; intros po R Hok Hpos HR.
  - destruct po; simpl in Hok; [discriminate|].
    simpl. apply wreach_csteps with (n := 3). apply ph_spawn.
  - inversion Hpos as [|? ? Hb Hr]; subst.
    destruct po.
    + destruct (HR eq_refl) as (R' & ->). simpl.
      apply wreach_csteps with (n := 1). apply ph_dep.
    + simpl in Hok |- *.
      destruct b as [|b']; [lia|].
      eapply wreach_trans.
      { apply wreach_csteps with (n := 1).
        change (wbody (S b' :: r)) with (S1 :: (rep [S1] b' ++ S0 :: wbody r)).
        apply ph_sepB. }
      eapply wreach_trans.
      { apply wreach_csteps with (n := S b'). apply cross_run. }
      replace (stB b') with (if Nat.odd (S b') then StC else StB);
        [| unfold stB; rewrite Nat.odd_succ; reflexivity].
      cbn [outL outR]. apply IH.
      * exact Hok.
      * exact Hr.
      * intro Hodd. exists (rep [S1] b' ++ S0 :: R). reflexivity.
Qed.

(** ** The rightward reconstruction sweep (return_R fold).

    [sw cs] is the swept region (run-lengths [cs], deepest-first, each
    followed by a single separator).  The return sweeps right in state D:
    [run_to_sep] re-lays a run up to its separator (an A1 start plus a D1
    sweep, [Dsweep]), then a D0/A1 gadget FILLS the separator (the swept
    run gains one) and BORROWS one from the next run (its first 1 becomes
    the new separator).  Net over [cs]: the deepest run +1 (restoring the
    deposit-eaten block), the frontier -1 (removing the FT scratch), the
    interior unchanged -- captured by [relaid]. *)

Lemma repS1_slide : forall k L, rep [S1] k ++ S1 :: L = rep [S1] (S k) ++ L.
Proof. intros. symmetry. change (rep [S1] (S k)) with (S1 :: rep [S1] k). apply rep_slide. Qed.

Lemma Dsweep : forall k L R,
  csteps tm_17 (S k) (StD, (L, S1, rep [S1] k ++ S0 :: R))
  = Some (StD, (rep [S1] (S k) ++ L, S0, R)).
Proof.
  induction k as [|k IH]; intros L R.
  - reflexivity.
  - change (rep [S1] (S k) ++ S0 :: R) with (S1 :: (rep [S1] k ++ S0 :: R)).
    eapply csteps_chain with (n1:=1) (n2:=S k)
      (c1 := (StD, (S1 :: L, S1, rep [S1] k ++ S0 :: R))).
    + reflexivity.
    + rewrite (IH (S1 :: L) R), repS1_slide. reflexivity.
Qed.

Lemma run_to_sep : forall c L R,
  wreach tm_17 (StA, (L, S1, rep [S1] c ++ S0 :: R)) (StD, (rep [S1] c ++ S0 :: L, S0, R)).
Proof.
  intros [|c] L R.
  - apply wreach_csteps with (n:=1). reflexivity.
  - eapply wreach_trans.
    + apply wreach_csteps with (n:=1).
      instantiate (1 := (StD, (S0 :: L, S1, rep [S1] c ++ S0 :: R))). reflexivity.
    + apply wreach_csteps with (n := S c). apply Dsweep.
Qed.

Fixpoint sw (cs : list nat) : list Sym :=
  match cs with [] => [] | c :: r => rep [S1] c ++ S0 :: sw r end.
Definition dec1 (cs : list nat) : list nat :=
  match cs with [] => [] | c :: r => pred c :: r end.
Fixpoint relaid_b (b : nat) (cs : list nat) : list Sym :=
  match cs with
  | [] => []
  | [c] => rep [S1] (c - b)
  | c :: rest => relaid_b 1 rest ++ S0 :: rep [S1] (S (c - b))
  end.
Definition relaid (cs : list nat) : list Sym := relaid_b 0 cs.

Lemma relaid_b_dec : forall b cs, relaid_b (S b) cs = relaid_b b (dec1 cs).
Proof.
  intros b cs. destruct cs as [|c [|c2 rest']]; simpl; try reflexivity;
    replace (c - S b) with (pred c - b) by lia; reflexivity.
Qed.

Lemma relaid_dec : forall c rest, rest <> [] ->
  relaid (c :: rest) = relaid (dec1 rest) ++ S0 :: rep [S1] (S c).
Proof.
  intros c rest Hne. unfold relaid.
  destruct rest as [|c2 rest']; [congruence|].
  simpl relaid_b. rewrite Nat.sub_0_r.
  f_equal. f_equal. apply (relaid_b_dec 0 (c2 :: rest')).
Qed.

Lemma return_R_aux : forall n cs L,
  length cs <= n -> cs <> [] -> Forall (fun c => 1 <= c) (tl cs) ->
  wreach tm_17 (StA, (L, S1, sw cs)) (StD, (relaid cs ++ S0 :: L, S0, [])).
Proof.
  induction n as [|n IH]; intros cs L Hlen Hne Htl.
  - destruct cs; [congruence | simpl in Hlen; lia].
  - destruct cs as [|c rest]; [congruence|].
    destruct rest as [|c2 rest'].
    + simpl sw. unfold relaid; simpl relaid_b. rewrite Nat.sub_0_r.
      pose proof (run_to_sep c L []) as H. simpl in H. exact H.
    + inversion Htl as [|? ? Hc2 Htl2]; subst.
      destruct c2 as [|c2']; [lia|].
      rewrite (relaid_dec c (S c2' :: rest') ltac:(discriminate)).
      eapply wreach_trans.
      { apply (run_to_sep c L (sw (S c2' :: rest'))). }
      eapply wreach_trans.
      { apply wreach_csteps with (n:=1).
        simpl sw.
        change (rep [S1] (S c2') ++ S0 :: sw rest') with (S1 :: (rep [S1] c2' ++ S0 :: sw rest')).
        instantiate (1 := (StA, (S1 :: rep [S1] c ++ S0 :: L, S1, rep [S1] c2' ++ S0 :: sw rest'))).
        reflexivity. }
      replace (S1 :: rep [S1] c ++ S0 :: L) with (rep [S1] (S c) ++ S0 :: L)
        by (change (rep [S1] (S c)) with (S1 :: rep [S1] c); reflexivity).
      replace (rep [S1] c2' ++ S0 :: sw rest') with (sw (c2' :: rest')) by reflexivity.
      change (dec1 (S c2' :: rest')) with (c2' :: rest').
      rewrite <- app_assoc. cbn [app].
      apply (IH (c2' :: rest')).
      * simpl in Hlen |- *; lia.
      * discriminate.
      * exact Htl2.
Qed.

Lemma return_R : forall cs L,
  cs <> [] -> Forall (fun c => 1 <= c) (tl cs) ->
  wreach tm_17 (StA, (L, S1, sw cs)) (StD, (relaid cs ++ S0 :: L, S0, [])).
Proof. intros cs L. apply (return_R_aux (length cs) cs L). apply le_n. Qed.
