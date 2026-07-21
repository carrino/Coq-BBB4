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

(** ** The wave/return bridge, boot, visits, and the theorem.

    [bcs]/[dsuffix] connect the leftward wave's output ([outL]/[outR]) to
    the return's input ([sw]/[relaid]): the swept region is [sw (bcs ...)]
    and the deposit-turnaround left list is [wbody (dsuffix ...)].
    [bridge_l] is the telescoping identity that makes the return re-lay
    exactly onto [wbody (nextf 0 front)]. *)

Fixpoint bcs (po:bool) (blocks:list nat) (base:list nat) : list nat :=
  match blocks with
  | [] => 0 :: base
  | b :: r => if po then dec1 base else bcs (Nat.odd b) r (b :: base)
  end.
(* dsuffix: the deposit-and-below suffix (outL = wbody dsuffix). *)
Fixpoint dsuffix (po:bool) (blocks:list nat) : list nat :=
  match blocks with
  | [] => []
  | b :: r => if po then S b :: r else dsuffix (Nat.odd b) r
  end.

Lemma outL_wbody : forall blocks po, outL po blocks = wbody (dsuffix po blocks).
Proof.
  induction blocks as [|b r IH]; intros po; [reflexivity|].
  simpl. destruct po; [reflexivity | apply IH].
Qed.

Lemma outR_sw : forall blocks po base,
  Forall (fun x => 1 <= x) blocks -> Forall (fun x => 1 <= x) base ->
  outR po blocks (sw base) = sw (bcs po blocks base).
Proof.
  induction blocks as [|b r IH]; intros po base Hbl Hb.
  - reflexivity.
  - inversion Hbl as [|? ? Hb1 Hr]; subst. simpl. destruct po.
    + destruct base as [|c base']; [reflexivity|].
      inversion Hb; subst. destruct c as [|c']; [lia|]. reflexivity.
    + change (rep [S1] b ++ S0 :: sw base) with (sw (b :: base)).
      apply IH; [exact Hr | constructor; assumption].
Qed.

Lemma bridge_l : forall blocks po base,
  Forall (fun x => 1 <= x) blocks -> carry_ok po blocks = true ->
  base <> [] -> Forall (fun x => 1 <= x) base ->
  relaid (bcs po blocks base) ++ S0 :: wbody (dsuffix po blocks)
  = relaid (dec1 base) ++ S0 :: wbody (carry po blocks).
Proof.
  induction blocks as [|b r IH]; intros po base Hbl Hok Hne Hb.
  - destruct po; simpl in Hok; [discriminate|].
    simpl bcs. simpl dsuffix. simpl carry.
    rewrite (relaid_dec 0 base Hne), <- app_assoc.
    cbn [rep app wbody]. reflexivity.
  - inversion Hbl as [|? ? Hb1 Hr]; subst.
    destruct po.
    + reflexivity.
    + destruct b as [|b']; [lia|].
      cbn [bcs dsuffix carry carry_ok] in Hok |- *.
      rewrite (IH (Nat.odd (S b')) (S b' :: base) Hr Hok ltac:(discriminate)
                  (Forall_cons _ Hb1 Hb)).
      change (dec1 (S b' :: base)) with (b' :: base).
      rewrite (relaid_dec b' base Hne).
      cbn [wbody]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma bcs_nonnil : forall blocks po base, base <> [] -> bcs po blocks base <> [].
Proof.
  induction blocks as [|b r IH]; intros po base Hne; [discriminate|].
  simpl. destruct po.
  - destruct base; [congruence | discriminate].
  - apply IH. discriminate.
Qed.
Lemma bcs_tl_pos : forall blocks po base,
  Forall (fun x => 1 <= x) blocks -> Forall (fun x => 1 <= x) base -> base <> [] ->
  Forall (fun c => 1 <= c) (tl (bcs po blocks base)).
Proof.
  induction blocks as [|b r IH]; intros po base Hbl Hbase Hne.
  - simpl. exact Hbase.
  - inversion Hbl as [|? ? Hb1 Hr]; subst. simpl. destruct po.
    + destruct base as [|c base']; [congruence|]. simpl. inversion Hbase; assumption.
    + apply IH; [assumption | constructor; assumption | discriminate].
Qed.


(* ---- assembly ---- *)
Lemma post_FT_eq : forall b0 r0,
  S1 :: wbody (b0 :: r0) = rep [S1] (S b0) ++ S0 :: wbody r0.
Proof. intros. reflexivity. Qed.

Lemma nqh_lap : forall front, WInv 0 front ->
  exists n c', csteps tm_17 n (Cf17 front) = Some c' /\
               lift c' = lift (Cf17 (nextf 0 front)) /\ 0 < n.
Proof.
  intros front (Hfp & Hpos & Hne).
  destruct front as [|b0 r0]; [congruence|].
  assert (Hr0 : Forall (fun x => 1 <= x) r0) by (inversion Hpos; assumption).
  assert (Hok : carry_ok (Nat.odd b0) r0 = true).
  { pose proof (WInv_no_leadstop 0 b0 r0 (conj Hfp (conj Hpos Hne))) as H.
    rewrite Nat.add_0_r in H. exact H. }
  eapply wreach_lap with (n := 3) (c1 := (StB, (S1 :: wbody (b0 :: r0), S1, [S0]))).
  - apply ph_FT.
  - lia.
  - rewrite post_FT_eq.
    eapply wreach_trans.
    { apply wreach_csteps with (n := S (S b0)). apply cross_run. }
    replace (stB (S b0)) with (if Nat.odd b0 then StC else StB);
      [| unfold stB; rewrite Nat.even_succ; destruct (Nat.odd b0); reflexivity].
    eapply wreach_trans.
    { change (rep [S1] (S (S b0)) ++ [S0]) with (sw [S (S b0)]).
      apply (wave_L r0 (Nat.odd b0) (sw [S (S b0)])).
      - exact Hok.
      - exact Hr0.
      - intro Hodd. exists (rep [S1] (S b0) ++ [S0]). reflexivity. }
    rewrite (outR_sw r0 (Nat.odd b0) [S (S b0)] Hr0 ltac:(constructor; [lia | constructor])).
    eapply wreach_trans.
    { apply (return_R (bcs (Nat.odd b0) r0 [S (S b0)]) (outL (Nat.odd b0) r0)).
      - apply bcs_nonnil. discriminate.
      - apply bcs_tl_pos; [exact Hr0 | constructor; [lia | constructor] | discriminate]. }
    rewrite outL_wbody.
    rewrite (bridge_l r0 (Nat.odd b0) [S (S b0)] Hr0 Hok ltac:(discriminate)
                      ltac:(constructor; [lia | constructor])).
    change (dec1 [S (S b0)]) with [S b0].
    change (relaid [S b0]) with (rep [S1] (S b0)).
    replace (rep [S1] (S b0) ++ S0 :: wbody (carry (Nat.odd b0) r0))
      with (wbody (nextf 0 (b0 :: r0))).
    2:{ unfold nextf. rewrite Nat.add_0_r. reflexivity. }
    apply wreach_refl.
Qed.

Lemma boot_17 : exists t0, stepn tm_17 t0 InitES = Some (lift (Cf17 [3;2;1])).
Proof.
  exists 49.
  assert (H : match csteps tm_17 49 CTape.c0 with
              | Some c => ceqb c (Cf17 [3;2;1]) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm_17 49 CTape.c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

Lemma vis_17 : forall p q, WInv 0 p ->
  exists k c, csteps tm_17 k (Cf17 p) = Some c /\ fst c = q.
Proof.
  intros p q (Hfp & Hpos & Hne). destruct p as [|b0 r0]; [congruence|].
  destruct q.
  - exists 1. eexists. split; reflexivity.
  - exists 2. eexists. split; reflexivity.
  - exists 4. eexists. split; reflexivity.
  - exists 0. eexists. split; reflexivity.
Qed.

Theorem nqh_1RB0RD_0LB1LC_1RA1LB_1RA1RD : NeverQuasiHaltsSt tm_17.
Proof.
  apply (wglue_neverqh tm_17 (list nat) (nextf 0) (WInv 0) Cf17 [3;2;1]).
  - split; [reflexivity | split; [repeat constructor; lia | discriminate]].
  - intros a Ha. apply WInv_preserved; exact Ha.
  - exact boot_17.
  - exact nqh_lap.
  - exact vis_17.
Qed.
