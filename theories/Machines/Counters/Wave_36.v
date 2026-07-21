(** * Wave_36: the wave_counter machine #36, 1RB1RA_1LC0RA_0LC1LD_1RB1LC.

    Edge state A, side R, poff 1, boot_vector [1;1;2;4] (cert
    results/counter36.cert).  This is the #27 machine
    (Wave_27.v, 1RB1LC_1LC0RD_0LC1LA_1RB1RD) under the state relabelling
    A<->D: the transition structure, the abstract orbit ([nextf 1]) and
    the safety invariant ([WInv 1]) are identical, only the concrete edge
    and gadget states are swapped.  So this file is Wave_27.v with A/D
    exchanged throughout; the proofs transcribe verbatim.

    Gadget states (#27 -> #36, A<->D):
    - edge/return-sweep state D -> A (Cf36 = (StA, ...); sweep A1/1R>A);
    - deposit state A -> D (deposit D0/1R>B); cross-pair C/A -> C/D
      ([cross_run36] starts in C, [stC k = if even k then StD else StC]);
    - FT [A0/1R>B B0/1L>C], scratch [S1] (no trailing frontier separator,
      [sw36] / [run_to_end36]); return start [B1/0R>A], junction
      [A0/1R>B]; frontier-cross exit parity [odd(b0+1)].

    No axioms beyond [functional_extensionality_dep]. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape WaveCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).

(** 1RB1RA_1LC0RA_0LC1LD_1RB1LC *)
Definition tm_36 : TM := fun q s =>
  match q, s with
  | StD, S0 => mk S1 DR StB | StD, S1 => mk S1 DL StC
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DR StA
  | StC, S0 => mk S0 DL StC | StC, S1 => mk S1 DL StD
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DR StA
  end.

(** ** The crux: crossing a run of ones leftward (states C/A alternate).

    From the frontier-turnaround the head sits on the top one of a run in
    state C; it walks left over the run (C and A alternating), and the
    state on reaching the separator encodes the run's parity -- A (deposit,
    stop) if the run length is even, C (continue) if odd. *)
Definition stC (k : nat) : St := if Nat.even k then StD else StC.

Lemma cross_run36 : forall k rest R,
  csteps tm_36 (S k) (StC, (rep [S1] k ++ S0 :: rest, S1, R))
  = Some (stC k, (rest, S0, rep [S1] (S k) ++ R)).
Proof.
  intro k. pattern k. apply (well_founded_ind lt_wf). clear k.
  intros k IH rest R. destruct k as [|[|k']].
  - reflexivity.
  - reflexivity.
  - change (rep [S1] (S (S k'))) with (S1 :: S1 :: rep [S1] k').
    eapply csteps_chain with
      (n1 := 2) (n2 := S k')
      (c1 := (StC, (rep [S1] k' ++ S0 :: rest, S1, S1 :: S1 :: R))).
    + reflexivity.
    + rewrite (IH k' ltac:(lia) rest (S1 :: S1 :: R)).
      unfold stC. rewrite Nat.even_succ, Nat.odd_succ.
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

Definition Cf36 (front : list nat) : cconf := (StA, (wbody front, S0, [])).

(** ** Generic phase units (all reflexivity via [wsteps] + transport) *)

(** Frontier turnaround: 2 steps, never reads the left (D0 writes the +1,
    B0 consumes it as head and lays a [S1] scratch), turns to left C-sweep. *)
Lemma ph_FT36 : forall L, csteps tm_36 2 (StA, (L, S0, [])) = Some (StC, (L, S1, [S1])).
Proof.
  intro L.
  pose proof (wsteps_frame_r tm_36 2 StA [] S0 [] StC [] S1 [S1] L) as H.
  cbn [app] in H. apply H. reflexivity.
Qed.

(** Separator-continue: at a separator [S0] in state C, step onto the next
    block's top one, still in state C. *)
Lemma ph_sepC : forall rest R,
  csteps tm_36 1 (StC, (S1 :: rest, S0, R)) = Some (StC, (rest, S1, S0 :: R)).
Proof.
  intros rest R.
  pose proof (wsteps_frame tm_36 1 StC [S1] S0 [] StC [] S1 [S0] rest R) as H.
  cbn [app] in H. apply H. reflexivity.
Qed.

(** Deposit: at a separator [S0] in state A with a swept one on the right,
    write [S1] (grow the block) and turn to a rightward sweep in B. *)
Lemma ph_dep36 : forall X R,
  csteps tm_36 1 (StD, (X, S0, S1 :: R)) = Some (StB, (S1 :: X, S1, R)).
Proof.
  intros X R.
  pose proof (wsteps_frame tm_36 1 StD [] S0 [S1] StB [S1] S1 [] X R) as H.
  cbn [app] in H. apply H. reflexivity.
Qed.

(** Spawn: at the lead's separator the head crosses the lead into the left
    blank and deposits a new leftmost block. *)
Lemma ph_spawn36 : forall R,
  csteps tm_36 3 (StC, ([S1], S0, R)) = Some (StB, ([S1], S1, S0 :: R)).
Proof. reflexivity. Qed.

(** ** The leftward carry wave (fold, mirrors [carry]). *)
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

Lemma wave_L36 : forall blocks po R,
  carry_ok po blocks = true ->
  Forall (fun x => 1 <= x) blocks ->
  (po = true -> exists R', R = S1 :: R') ->
  wreach tm_36 (if po then StD else StC, (wbody blocks, S0, R))
              (StB, (outL po blocks, S1, outR po blocks R)).
Proof.
  induction blocks as [|b r IH]; intros po R Hok Hpos HR.
  - destruct po; simpl in Hok; [discriminate|].
    simpl. apply wreach_csteps with (n := 3). apply ph_spawn36.
  - inversion Hpos as [|? ? Hb Hr]; subst.
    destruct po.
    + destruct (HR eq_refl) as (R' & ->). simpl.
      apply wreach_csteps with (n := 1). apply ph_dep36.
    + simpl in Hok |- *.
      destruct b as [|b']; [lia|].
      eapply wreach_trans.
      { apply wreach_csteps with (n := 1).
        change (wbody (S b' :: r)) with (S1 :: (rep [S1] b' ++ S0 :: wbody r)).
        apply ph_sepC. }
      eapply wreach_trans.
      { apply wreach_csteps with (n := S b'). apply cross_run36. }
      replace (stC b') with (if Nat.odd (S b') then StD else StC);
        [| unfold stC; rewrite Nat.odd_succ; reflexivity].
      cbn [outL outR]. apply IH.
      * exact Hok.
      * exact Hr.
      * intro Hodd. exists (rep [S1] b' ++ S0 :: R). reflexivity.
Qed.

(** ** The rightward reconstruction sweep (return_R36 fold).

    [sw36 cs] is the swept region (run-lengths [cs], nearest-first, each
    followed by a single separator EXCEPT the last -- the frontier run is
    bare because #36's FT scratch is a [S1], not a separator).  The return
    sweeps right in state D, re-laying each run (a [B1] start plus a [D1]
    sweep [Dsweep36]) and, at each interior separator, a [D0/1R>B]-[B1/0R>D]
    borrow gadget; the frontier run walks off into the blank
    ([run_to_end36]).  Net: the deepest run -1 (removing the FT scratch),
    interior unchanged -- captured by [relaid]. *)

Lemma repS1_slide : forall k L, rep [S1] k ++ S1 :: L = rep [S1] (S k) ++ L.
Proof. intros. symmetry. change (rep [S1] (S k)) with (S1 :: rep [S1] k). apply rep_slide. Qed.

Lemma Dsweep36 : forall k L R,
  csteps tm_36 (S k) (StA, (L, S1, rep [S1] k ++ S0 :: R))
  = Some (StA, (rep [S1] (S k) ++ L, S0, R)).
Proof.
  induction k as [|k IH]; intros L R.
  - reflexivity.
  - change (rep [S1] (S k) ++ S0 :: R) with (S1 :: (rep [S1] k ++ S0 :: R)).
    eapply csteps_chain with (n1:=1) (n2:=S k)
      (c1 := (StA, (S1 :: L, S1, rep [S1] k ++ S0 :: R))).
    + reflexivity.
    + rewrite (IH (S1 :: L) R), repS1_slide. reflexivity.
Qed.

Lemma Dsweep_blank36 : forall k L,
  csteps tm_36 (S k) (StA, (L, S1, rep [S1] k))
  = Some (StA, (rep [S1] (S k) ++ L, S0, [])).
Proof.
  induction k as [|k IH]; intros L.
  - reflexivity.
  - change (rep [S1] (S k)) with (S1 :: rep [S1] k).
    eapply csteps_chain with (n1:=1) (n2:=S k)
      (c1 := (StA, (S1 :: L, S1, rep [S1] k))).
    + reflexivity.
    + rewrite (IH (S1 :: L)), repS1_slide. reflexivity.
Qed.

(** Re-lay a run ending on an interior separator (state B start). *)
Lemma run_to_sep36 : forall c L R,
  wreach tm_36 (StB, (L, S1, rep [S1] c ++ S0 :: R)) (StA, (rep [S1] c ++ S0 :: L, S0, R)).
Proof.
  intros [|c] L R.
  - apply wreach_csteps with (n:=1). reflexivity.
  - eapply wreach_trans.
    + apply wreach_csteps with (n:=1).
      instantiate (1 := (StA, (S0 :: L, S1, rep [S1] c ++ S0 :: R))). reflexivity.
    + apply wreach_csteps with (n := S c). apply Dsweep36.
Qed.

(** Re-lay the deepest (frontier) run, walking off into the blank. *)
Lemma run_to_end36 : forall c L,
  wreach tm_36 (StB, (L, S1, rep [S1] c)) (StA, (rep [S1] c ++ S0 :: L, S0, [])).
Proof.
  intros [|c] L.
  - apply wreach_csteps with (n:=1). reflexivity.
  - eapply wreach_trans.
    + apply wreach_csteps with (n:=1).
      instantiate (1 := (StA, (S0 :: L, S1, rep [S1] c))). reflexivity.
    + apply wreach_csteps with (n := S c). apply Dsweep_blank36.
Qed.

Fixpoint sw36 (cs : list nat) : list Sym :=
  match cs with
  | [] => []
  | [c] => rep [S1] c
  | c :: rest => rep [S1] c ++ S0 :: sw36 rest
  end.

Lemma sw36_slide : forall c rest, sw36 (S c :: rest) = S1 :: sw36 (c :: rest).
Proof. intros c [|c2 rest]; reflexivity. Qed.

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

Lemma return_R36_aux : forall n cs L,
  length cs <= n -> cs <> [] -> Forall (fun c => 1 <= c) (tl cs) ->
  wreach tm_36 (StB, (L, S1, sw36 cs)) (StA, (relaid cs ++ S0 :: L, S0, [])).
Proof.
  induction n as [|n IH]; intros cs L Hlen Hne Htl.
  - destruct cs; [congruence | simpl in Hlen; lia].
  - destruct cs as [|c rest]; [congruence|].
    destruct rest as [|c2 rest'].
    + simpl sw36. unfold relaid; simpl relaid_b. rewrite Nat.sub_0_r.
      apply (run_to_end36 c L).
    + inversion Htl as [|? ? Hc2 Htl2]; subst.
      destruct c2 as [|c2']; [lia|].
      rewrite (relaid_dec c (S c2' :: rest') ltac:(discriminate)).
      eapply wreach_trans.
      { change (sw36 (c :: S c2' :: rest'))
          with (rep [S1] c ++ S0 :: sw36 (S c2' :: rest')).
        apply (run_to_sep36 c L (sw36 (S c2' :: rest'))). }
      eapply wreach_trans.
      { apply wreach_csteps with (n:=1).
        rewrite sw36_slide.
        instantiate (1 := (StB, (S1 :: rep [S1] c ++ S0 :: L, S1, sw36 (c2' :: rest')))).
        reflexivity. }
      replace (S1 :: rep [S1] c ++ S0 :: L) with (rep [S1] (S c) ++ S0 :: L)
        by (change (rep [S1] (S c)) with (S1 :: rep [S1] c); reflexivity).
      change (dec1 (S c2' :: rest')) with (c2' :: rest').
      rewrite <- app_assoc. cbn [app].
      apply (IH (c2' :: rest')).
      * simpl in Hlen |- *; lia.
      * discriminate.
      * exact Htl2.
Qed.

Lemma return_R36 : forall cs L,
  cs <> [] -> Forall (fun c => 1 <= c) (tl cs) ->
  wreach tm_36 (StB, (L, S1, sw36 cs)) (StA, (relaid cs ++ S0 :: L, S0, [])).
Proof. intros cs L. apply (return_R36_aux (length cs) cs L). apply le_n. Qed.

(** ** The wave/return bridge, boot, visits, and the theorem. *)

Fixpoint bcs (po:bool) (blocks:list nat) (base:list nat) : list nat :=
  match blocks with
  | [] => 0 :: base
  | b :: r => if po then dec1 base else bcs (Nat.odd b) r (b :: base)
  end.
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

Lemma outR_sw36 : forall blocks po base,
  Forall (fun x => 1 <= x) blocks -> Forall (fun x => 1 <= x) base -> base <> [] ->
  outR po blocks (sw36 base) = sw36 (bcs po blocks base).
Proof.
  induction blocks as [|b r IH]; intros po base Hbl Hb Hne.
  - simpl. destruct base as [|c base']; [congruence|]. reflexivity.
  - inversion Hbl as [|? ? Hb1 Hr]; subst. simpl. destruct po.
    + destruct base as [|c base']; [congruence|].
      inversion Hb; subst. destruct c as [|c']; [lia|].
      rewrite sw36_slide. reflexivity.
    + replace (rep [S1] b ++ S0 :: sw36 base) with (sw36 (b :: base)).
      2:{ destruct base; [congruence | reflexivity]. }
      apply IH; [exact Hr | constructor; assumption | discriminate].
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
Lemma nqh_lap36 : forall front, WInv 1 front ->
  exists n c', csteps tm_36 n (Cf36 front) = Some c' /\
               lift c' = lift (Cf36 (nextf 1 front)) /\ 0 < n.
Proof.
  intros front (Hfp & Hpos & Hne).
  destruct front as [|b0 r0]; [congruence|].
  assert (Hr0 : Forall (fun x => 1 <= x) r0) by (inversion Hpos; assumption).
  assert (Hok : carry_ok (Nat.odd (b0 + 1)) r0 = true).
  { apply (WInv_no_leadstop 1 b0 r0 (conj Hfp (conj Hpos Hne))). }
  eapply wreach_lap with (n := 2) (c1 := (StC, (wbody (b0 :: r0), S1, [S1]))).
  - apply ph_FT36.
  - lia.
  - change (wbody (b0 :: r0)) with (rep [S1] b0 ++ S0 :: wbody r0).
    eapply wreach_trans.
    { apply wreach_csteps with (n := S b0). apply cross_run36. }
    replace (stC b0) with (if Nat.odd (b0 + 1) then StD else StC);
      [| unfold stC; replace (b0 + 1) with (S b0) by lia;
         rewrite Nat.odd_succ; reflexivity].
    replace (rep [S1] (S b0) ++ [S1]) with (sw36 [S (S b0)]);
      [| cbn [sw36]; change [S1] with (rep [S1] 1);
         rewrite <- rep_add; f_equal; lia ].
    eapply wreach_trans.
    { apply (wave_L36 r0 (Nat.odd (b0 + 1)) (sw36 [S (S b0)])).
      - exact Hok.
      - exact Hr0.
      - intro Hodd. exists (rep [S1] (S b0)). reflexivity. }
    rewrite (outR_sw36 r0 (Nat.odd (b0 + 1)) [S (S b0)]
               Hr0 ltac:(constructor; [lia | constructor]) ltac:(discriminate)).
    eapply wreach_trans.
    { apply (return_R36 (bcs (Nat.odd (b0 + 1)) r0 [S (S b0)]) (outL (Nat.odd (b0 + 1)) r0)).
      - apply bcs_nonnil. discriminate.
      - apply bcs_tl_pos; [exact Hr0 | constructor; [lia | constructor] | discriminate]. }
    rewrite outL_wbody.
    rewrite (bridge_l r0 (Nat.odd (b0 + 1)) [S (S b0)] Hr0 Hok ltac:(discriminate)
                      ltac:(constructor; [lia | constructor])).
    change (dec1 [S (S b0)]) with [S b0].
    change (relaid [S b0]) with (rep [S1] (S b0)).
    replace (rep [S1] (S b0) ++ S0 :: wbody (carry (Nat.odd (b0 + 1)) r0))
      with (wbody (nextf 1 (b0 :: r0))).
    2:{ unfold nextf. reflexivity. }
    apply wreach_refl.
Qed.

Lemma boot_36 : exists t0, stepn tm_36 t0 InitES = Some (lift (Cf36 [4;2;1])).
Proof.
  exists 50.
  assert (H : match csteps tm_36 50 CTape.c0 with
              | Some c => ceqb c (Cf36 [4;2;1]) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm_36 50 CTape.c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

Lemma vis_36 : forall p q, WInv 1 p ->
  exists k c, csteps tm_36 k (Cf36 p) = Some c /\ fst c = q.
Proof.
  intros p q (Hfp & Hpos & Hne). destruct p as [|b0 r0]; [congruence|].
  destruct q.
  - exists 0. eexists. split; reflexivity.
  - exists 1. eexists. split; reflexivity.
  - exists 2. eexists. split; reflexivity.
  - exists 3. eexists. split; reflexivity.
Qed.

Theorem nqh_1RB1RA_1LC0RA_0LC1LD_1RB1LC : NeverQuasiHaltsSt tm_36.
Proof.
  apply (wglue_neverqh tm_36 (list nat) (nextf 1) (WInv 1) Cf36 [4;2;1]).
  - split; [reflexivity | split; [repeat constructor; lia | discriminate]].
  - intros a Ha. apply WInv_preserved; exact Ha.
  - exact boot_36.
  - exact nqh_lap36.
  - exact vis_36.
Qed.
