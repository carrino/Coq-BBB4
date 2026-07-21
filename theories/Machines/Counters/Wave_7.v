(** * Wave_7: the wave_counter machine #7, 1RB0LC_1LA1RD_1LA1LC_0RD1RB.

    Edge state A, side L, poff 1, boot_vector [1;1;2;4] (cert
    results/counter7.cert).  Side L, so this is boarded through
    [Mirror.mirror_never_qh]: we prove [NeverQuasiHaltsSt (mirror_tm tm_7)],
    where [mirror_tm tm_7 = tm_7m = 1LB0RC_1RA1LD_1RA1RC_0LD1LB] is a
    side-R wave odometer (edge A, same [nextf 1]/[WInv 1] orbit), then
    apply the mirror lemma.

    Deltas from #17/#27 (all Compute-validated; probe tools/counters/probe7m.py):
    - the frontier turnaround is a SINGLE step [A0/1L>B]: it writes the +1
      increment and lands the head straight on the frontier top in state B,
      laying a [S1] scratch.  So the swept frontier is [S b0] (one less than
      #27's [S(S b0)]), and the RETURN CONSERVES every run count: its
      terminal [C0/1R>A] WRITES a one, so [relaid7] does NOT decrement the
      deepest run ([relaid7_b]'s [[c]] case is [rep[S1](S(c-b))], one more
      than #27's [rep[S1](c-b)]);
    - the leftward cross alternates B/D; because the FT lands in the
      deposit-state B while the sep-continue lands in the continue-state D,
      there are TWO cross lemmas: [cross_run7B] (frontier, start B) and
      [cross_run7] (interior, start D);
    - return: sweep [C1/1R>C] ([Csweep7]), start [A1/0R>C], junction
      [C0/1R>A]; state A is the edge (Cf7 = (StA, ...)).
    [sw7], [bcs], [dsuffix], [outL]/[outR], [bridge7]'s SHAPE, and the whole
    [WaveCounter] layer are reused from the #27 template.

    No axioms beyond [functional_extensionality_dep]. *)

From Coq Require Import Arith Lia Bool List PArith FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From BBB4.Counters Require Import WTape WaveCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).

(** The genuine side-L machine #7, and its side-R mirror we actually board. *)
Definition tm_7 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StC
  | StB, S0 => mk S1 DL StA | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S1 DL StA | StC, S1 => mk S1 DL StC
  | StD, S0 => mk S0 DR StD | StD, S1 => mk S1 DR StB
  end.

(** 1LB0RC_1RA1LD_1RA1RC_0LD1LB (= mirror_tm tm_7) *)
Definition tm_7m : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => mk S0 DR StC
  | StB, S0 => mk S1 DR StA | StB, S1 => mk S1 DL StD
  | StC, S0 => mk S1 DR StA | StC, S1 => mk S1 DR StC
  | StD, S0 => mk S0 DL StD | StD, S1 => mk S1 DL StB
  end.

Lemma mirror_ok : mirror_tm tm_7 = tm_7m.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro s; destruct q, s; reflexivity.
Qed.

(** ** The crux: crossing a run of ones leftward (states B/D alternate).

    Two entry points: the frontier is entered in the deposit-state B (from
    the 1-step FT), each interior block in the continue-state D (from the
    sep-continue).  The exit state at the separator encodes the run parity. *)
Definition stB7 (k : nat) : St := if Nat.even k then StD else StB.
Definition stD7 (k : nat) : St := if Nat.even k then StB else StD.

Lemma cross_run7B : forall k rest R,
  csteps tm_7m (S k) (StB, (rep [S1] k ++ S0 :: rest, S1, R))
  = Some (stB7 k, (rest, S0, rep [S1] (S k) ++ R)).
Proof.
  intro k. pattern k. apply (well_founded_ind lt_wf). clear k.
  intros k IH rest R. destruct k as [|[|k']].
  - reflexivity.
  - reflexivity.
  - change (rep [S1] (S (S k'))) with (S1 :: S1 :: rep [S1] k').
    eapply csteps_chain with (n1 := 2) (n2 := S k')
      (c1 := (StB, (rep [S1] k' ++ S0 :: rest, S1, S1 :: S1 :: R))).
    + reflexivity.
    + rewrite (IH k' ltac:(lia) rest (S1 :: S1 :: R)).
      unfold stB7. rewrite Nat.even_succ, Nat.odd_succ.
      f_equal. f_equal. f_equal.
      change (S1 :: S1 :: R) with (rep [S1] 2 ++ R).
      rewrite app_assoc, <- rep_add.
      replace (S k' + 2) with (S (S (S k'))) by lia. reflexivity.
Qed.

Lemma cross_run7 : forall k rest R,
  csteps tm_7m (S k) (StD, (rep [S1] k ++ S0 :: rest, S1, R))
  = Some (stD7 k, (rest, S0, rep [S1] (S k) ++ R)).
Proof.
  intro k. pattern k. apply (well_founded_ind lt_wf). clear k.
  intros k IH rest R. destruct k as [|[|k']].
  - reflexivity.
  - reflexivity.
  - change (rep [S1] (S (S k'))) with (S1 :: S1 :: rep [S1] k').
    eapply csteps_chain with (n1 := 2) (n2 := S k')
      (c1 := (StD, (rep [S1] k' ++ S0 :: rest, S1, S1 :: S1 :: R))).
    + reflexivity.
    + rewrite (IH k' ltac:(lia) rest (S1 :: S1 :: R)).
      unfold stD7. rewrite Nat.even_succ, Nat.odd_succ.
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

Definition Cf7 (front : list nat) : cconf := (StA, (wbody front, S0, [])).

(** ** Generic phase units (reflexivity via direct [cstep]) *)

(** Frontier turnaround: 1 step [A0/1L>B], moves onto the frontier top. *)
Lemma ph_FT7 : forall L, csteps tm_7m 1 (StA, (S1 :: L, S0, [])) = Some (StB, (L, S1, [S1])).
Proof. reflexivity. Qed.

(** Separator-continue [D0/0L>D]. *)
Lemma ph_sepD7 : forall rest R,
  csteps tm_7m 1 (StD, (S1 :: rest, S0, R)) = Some (StD, (rest, S1, S0 :: R)).
Proof. reflexivity. Qed.

(** Deposit [B0/1R>A]. *)
Lemma ph_dep7 : forall X R,
  csteps tm_7m 1 (StB, (X, S0, S1 :: R)) = Some (StA, (S1 :: X, S1, R)).
Proof. reflexivity. Qed.

(** Spawn: cross the lead into the left blank, deposit a new leftmost block. *)
Lemma ph_spawn7 : forall R,
  csteps tm_7m 3 (StD, ([S1], S0, R)) = Some (StA, ([S1], S1, S0 :: R)).
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

Lemma wave_L7 : forall blocks po R,
  carry_ok po blocks = true ->
  Forall (fun x => 1 <= x) blocks ->
  (po = true -> exists R', R = S1 :: R') ->
  wreach tm_7m (if po then StB else StD, (wbody blocks, S0, R))
              (StA, (outL po blocks, S1, outR po blocks R)).
Proof.
  induction blocks as [|b r IH]; intros po R Hok Hpos HR.
  - destruct po; simpl in Hok; [discriminate|].
    simpl. apply wreach_csteps with (n := 3). apply ph_spawn7.
  - inversion Hpos as [|? ? Hb Hr]; subst.
    destruct po.
    + destruct (HR eq_refl) as (R' & ->). simpl.
      apply wreach_csteps with (n := 1). apply ph_dep7.
    + simpl in Hok |- *.
      destruct b as [|b']; [lia|].
      eapply wreach_trans.
      { apply wreach_csteps with (n := 1).
        change (wbody (S b' :: r)) with (S1 :: (rep [S1] b' ++ S0 :: wbody r)).
        apply ph_sepD7. }
      eapply wreach_trans.
      { apply wreach_csteps with (n := S b'). apply cross_run7. }
      replace (stD7 b') with (if Nat.odd (S b') then StB else StD);
        [| unfold stD7; rewrite Nat.odd_succ; reflexivity].
      cbn [outL outR]. apply IH.
      * exact Hok.
      * exact Hr.
      * intro Hodd. exists (rep [S1] b' ++ S0 :: R). reflexivity.
Qed.

(** ** The rightward reconstruction sweep (return_R7 fold, state C).

    [sw7] is the swept region (last run bare, as #27).  The return sweeps
    right in state C: [Csweep7] re-lays a run, the junction [C0/1R>A]
    borrows one from the next run, and the deepest run walks off with a
    TERMINAL [C0/1R>A] that WRITES a one -- so [relaid7] conserves counts
    (no decrement, unlike #27). *)

Lemma repS1_slide : forall k L, rep [S1] k ++ S1 :: L = rep [S1] (S k) ++ L.
Proof. intros. symmetry. change (rep [S1] (S k)) with (S1 :: rep [S1] k). apply rep_slide. Qed.

Lemma Csweep7 : forall k L R,
  csteps tm_7m (S k) (StC, (L, S1, rep [S1] k ++ S0 :: R))
  = Some (StC, (rep [S1] (S k) ++ L, S0, R)).
Proof.
  induction k as [|k IH]; intros L R.
  - reflexivity.
  - change (rep [S1] (S k) ++ S0 :: R) with (S1 :: (rep [S1] k ++ S0 :: R)).
    eapply csteps_chain with (n1:=1) (n2:=S k)
      (c1 := (StC, (S1 :: L, S1, rep [S1] k ++ S0 :: R))).
    + reflexivity.
    + rewrite (IH (S1 :: L) R), repS1_slide. reflexivity.
Qed.

Lemma Csweep_blank7 : forall k L,
  csteps tm_7m (S k) (StC, (L, S1, rep [S1] k))
  = Some (StC, (rep [S1] (S k) ++ L, S0, [])).
Proof.
  induction k as [|k IH]; intros L.
  - reflexivity.
  - change (rep [S1] (S k)) with (S1 :: rep [S1] k).
    eapply csteps_chain with (n1:=1) (n2:=S k)
      (c1 := (StC, (S1 :: L, S1, rep [S1] k))).
    + reflexivity.
    + rewrite (IH (S1 :: L)), repS1_slide. reflexivity.
Qed.

(** Re-lay an interior run, landing on its separator (state C). *)
Lemma run_to_sep7 : forall c L R,
  wreach tm_7m (StA, (L, S1, rep [S1] c ++ S0 :: R)) (StC, (rep [S1] c ++ S0 :: L, S0, R)).
Proof.
  intros [|c] L R.
  - apply wreach_csteps with (n:=1). reflexivity.
  - eapply wreach_trans.
    + apply wreach_csteps with (n:=1).
      instantiate (1 := (StC, (S0 :: L, S1, rep [S1] c ++ S0 :: R))). reflexivity.
    + apply wreach_csteps with (n := S c). apply Csweep7.
Qed.

(** Re-lay the deepest (frontier) run: walk off, the TERMINAL writes a one. *)
Lemma run_to_end7 : forall c L,
  wreach tm_7m (StA, (L, S1, rep [S1] c)) (StA, (rep [S1] (S c) ++ S0 :: L, S0, [])).
Proof.
  intros [|c] L.
  - eapply wreach_trans.
    + apply wreach_csteps with (n:=1). instantiate (1 := (StC, (S0 :: L, S0, []))). reflexivity.
    + apply wreach_csteps with (n:=1). reflexivity.
  - eapply wreach_trans.
    + apply wreach_csteps with (n:=1). instantiate (1 := (StC, (S0 :: L, S1, rep [S1] c))). reflexivity.
    + eapply wreach_trans.
      * apply wreach_csteps with (n := S c). apply Csweep_blank7.
      * apply wreach_csteps with (n:=1). reflexivity.
Qed.

Fixpoint sw7 (cs : list nat) : list Sym :=
  match cs with
  | [] => []
  | [c] => rep [S1] c
  | c :: rest => rep [S1] c ++ S0 :: sw7 rest
  end.

Lemma sw7_slide : forall c rest, sw7 (S c :: rest) = S1 :: sw7 (c :: rest).
Proof. intros c [|c2 rest]; reflexivity. Qed.

Definition dec1 (cs : list nat) : list nat :=
  match cs with [] => [] | c :: r => pred c :: r end.
Fixpoint relaid7_b (b : nat) (cs : list nat) : list Sym :=
  match cs with
  | [] => []
  | [c] => rep [S1] (S (c - b))
  | c :: rest => relaid7_b 1 rest ++ S0 :: rep [S1] (S (c - b))
  end.
Definition relaid7 (cs : list nat) : list Sym := relaid7_b 0 cs.

Lemma relaid7_b_dec : forall b cs, relaid7_b (S b) cs = relaid7_b b (dec1 cs).
Proof.
  intros b cs. destruct cs as [|c [|c2 rest']]; simpl; try reflexivity;
    replace (c - S b) with (pred c - b) by lia; reflexivity.
Qed.

Lemma relaid7_dec : forall c rest, rest <> [] ->
  relaid7 (c :: rest) = relaid7 (dec1 rest) ++ S0 :: rep [S1] (S c).
Proof.
  intros c rest Hne. unfold relaid7.
  destruct rest as [|c2 rest']; [congruence|].
  simpl relaid7_b. rewrite Nat.sub_0_r.
  f_equal. f_equal. apply (relaid7_b_dec 0 (c2 :: rest')).
Qed.

Lemma return_R7_aux : forall n cs L,
  length cs <= n -> cs <> [] -> Forall (fun c => 1 <= c) (tl cs) ->
  wreach tm_7m (StA, (L, S1, sw7 cs)) (StA, (relaid7 cs ++ S0 :: L, S0, [])).
Proof.
  induction n as [|n IH]; intros cs L Hlen Hne Htl.
  - destruct cs; [congruence | simpl in Hlen; lia].
  - destruct cs as [|c rest]; [congruence|].
    destruct rest as [|c2 rest'].
    + simpl sw7. unfold relaid7; simpl relaid7_b. rewrite Nat.sub_0_r.
      apply (run_to_end7 c L).
    + inversion Htl as [|? ? Hc2 Htl2]; subst.
      destruct c2 as [|c2']; [lia|].
      rewrite (relaid7_dec c (S c2' :: rest') ltac:(discriminate)).
      eapply wreach_trans.
      { change (sw7 (c :: S c2' :: rest'))
          with (rep [S1] c ++ S0 :: sw7 (S c2' :: rest')).
        apply (run_to_sep7 c L (sw7 (S c2' :: rest'))). }
      eapply wreach_trans.
      { apply wreach_csteps with (n:=1).
        rewrite sw7_slide.
        instantiate (1 := (StA, (S1 :: rep [S1] c ++ S0 :: L, S1, sw7 (c2' :: rest')))).
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

Lemma return_R7 : forall cs L,
  cs <> [] -> Forall (fun c => 1 <= c) (tl cs) ->
  wreach tm_7m (StA, (L, S1, sw7 cs)) (StA, (relaid7 cs ++ S0 :: L, S0, [])).
Proof. intros cs L. apply (return_R7_aux (length cs) cs L). apply le_n. Qed.

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

Lemma outR_sw7 : forall blocks po base,
  Forall (fun x => 1 <= x) blocks -> Forall (fun x => 1 <= x) base -> base <> [] ->
  outR po blocks (sw7 base) = sw7 (bcs po blocks base).
Proof.
  induction blocks as [|b r IH]; intros po base Hbl Hb Hne.
  - simpl. destruct base as [|c base']; [congruence|]. reflexivity.
  - inversion Hbl as [|? ? Hb1 Hr]; subst. simpl. destruct po.
    + destruct base as [|c base']; [congruence|].
      inversion Hb; subst. destruct c as [|c']; [lia|].
      rewrite sw7_slide. reflexivity.
    + replace (rep [S1] b ++ S0 :: sw7 base) with (sw7 (b :: base)).
      2:{ destruct base; [congruence | reflexivity]. }
      apply IH; [exact Hr | constructor; assumption | discriminate].
Qed.

Lemma bridge7 : forall blocks po base,
  Forall (fun x => 1 <= x) blocks -> carry_ok po blocks = true ->
  base <> [] -> Forall (fun x => 1 <= x) base ->
  relaid7 (bcs po blocks base) ++ S0 :: wbody (dsuffix po blocks)
  = relaid7 (dec1 base) ++ S0 :: wbody (carry po blocks).
Proof.
  induction blocks as [|b r IH]; intros po base Hbl Hok Hne Hb.
  - destruct po; simpl in Hok; [discriminate|].
    simpl bcs. simpl dsuffix. simpl carry.
    rewrite (relaid7_dec 0 base Hne), <- app_assoc.
    cbn [rep app wbody]. reflexivity.
  - inversion Hbl as [|? ? Hb1 Hr]; subst.
    destruct po.
    + reflexivity.
    + destruct b as [|b']; [lia|].
      cbn [bcs dsuffix carry carry_ok] in Hok |- *.
      rewrite (IH (Nat.odd (S b')) (S b' :: base) Hr Hok ltac:(discriminate)
                  (Forall_cons _ Hb1 Hb)).
      change (dec1 (S b' :: base)) with (b' :: base).
      rewrite (relaid7_dec b' base Hne).
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

(** Reach the deposit-turnaround (state A, head [S1]) from the post-FT config. *)
Lemma reach_depA7 : forall b0' r0,
  carry_ok (Nat.odd (S b0' + 1)) r0 = true -> Forall (fun x => 1 <= x) r0 ->
  wreach tm_7m (StB, (rep [S1] b0' ++ S0 :: wbody r0, S1, [S1]))
    (StA, (outL (Nat.odd (S b0' + 1)) r0, S1,
           outR (Nat.odd (S b0' + 1)) r0 (sw7 [S (S b0')]))).
Proof.
  intros b0' r0 Hok Hr0.
  eapply wreach_trans.
  { apply wreach_csteps with (n := S b0'). apply cross_run7B. }
  replace (stB7 b0') with (if Nat.odd (S b0' + 1) then StB else StD);
    [| unfold stB7; replace (S b0' + 1) with (S (S b0')) by lia;
       rewrite Nat.odd_succ, Nat.even_succ, <- Nat.negb_odd;
       destruct (Nat.odd b0'); reflexivity].
  replace (rep [S1] (S b0') ++ [S1]) with (sw7 [S (S b0')]);
    [| cbn [sw7]; change [S1] with (rep [S1] 1); rewrite <- rep_add; f_equal; lia].
  apply (wave_L7 r0 (Nat.odd (S b0' + 1)) (sw7 [S (S b0')])).
  - exact Hok.
  - exact Hr0.
  - intro Hodd. exists (rep [S1] (S b0')). reflexivity.
Qed.

Lemma nqh_lap7m : forall front, WInv 1 front ->
  exists n c', csteps tm_7m n (Cf7 front) = Some c' /\
               lift c' = lift (Cf7 (nextf 1 front)) /\ 0 < n.
Proof.
  intros front (Hfp & Hpos & Hne).
  destruct front as [|b0 r0]; [congruence|].
  assert (Hr0 : Forall (fun x => 1 <= x) r0) by (inversion Hpos; assumption).
  assert (Hok : carry_ok (Nat.odd (b0 + 1)) r0 = true).
  { apply (WInv_no_leadstop 1 b0 r0 (conj Hfp (conj Hpos Hne))). }
  assert (Hb0 : 1 <= b0) by (inversion Hpos; assumption).
  destruct b0 as [|b0']; [lia|].
  eapply wreach_lap with (n := 1)
    (c1 := (StB, (rep [S1] b0' ++ S0 :: wbody r0, S1, [S1]))).
  - change (Cf7 (S b0' :: r0)) with (StA, (S1 :: (rep [S1] b0' ++ S0 :: wbody r0), S0, @nil Sym)).
    apply ph_FT7.
  - lia.
  - eapply wreach_trans.
    { apply (reach_depA7 b0' r0 Hok Hr0). }
    rewrite (outR_sw7 r0 (Nat.odd (S b0' + 1)) [S (S b0')] Hr0
               ltac:(constructor; [lia | constructor]) ltac:(discriminate)).
    eapply wreach_trans.
    { apply (return_R7 (bcs (Nat.odd (S b0' + 1)) r0 [S (S b0')])
                       (outL (Nat.odd (S b0' + 1)) r0)).
      - apply bcs_nonnil. discriminate.
      - apply bcs_tl_pos; [exact Hr0 | constructor; [lia | constructor] | discriminate]. }
    rewrite outL_wbody.
    rewrite (bridge7 r0 (Nat.odd (S b0' + 1)) [S (S b0')] Hr0 Hok ltac:(discriminate)
                     ltac:(constructor; [lia | constructor])).
    change (dec1 [S (S b0')]) with [S b0'].
    change (relaid7 [S b0']) with (rep [S1] (S (S b0'))).
    replace (rep [S1] (S (S b0')) ++ S0 :: wbody (carry (Nat.odd (S b0' + 1)) r0))
      with (wbody (nextf 1 (S b0' :: r0))).
    2:{ unfold nextf. reflexivity. }
    apply wreach_refl.
Qed.

Lemma boot_7m : exists t0, stepn tm_7m t0 InitES = Some (lift (Cf7 [4;2;1])).
Proof.
  exists 42.
  assert (H : match csteps tm_7m 42 CTape.c0 with
              | Some c => ceqb c (Cf7 [4;2;1]) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm_7m 42 CTape.c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** State C is not in the frontier gadget; reach it via the deposit turnaround. *)
Lemma reach_C7 : forall b0 r0, WInv 1 (b0 :: r0) ->
  exists k c, csteps tm_7m k (Cf7 (b0 :: r0)) = Some c /\ fst c = StC.
Proof.
  intros b0 r0 (Hfp & Hpos & Hne).
  assert (Hr0 : Forall (fun x => 1 <= x) r0) by (inversion Hpos; assumption).
  assert (Hok : carry_ok (Nat.odd (b0 + 1)) r0 = true).
  { apply (WInv_no_leadstop 1 b0 r0 (conj Hfp (conj Hpos Hne))). }
  assert (Hb0 : 1 <= b0) by (inversion Hpos; assumption).
  destruct b0 as [|b0']; [lia|].
  assert (Hw : wreach tm_7m (Cf7 (S b0' :: r0))
    (StC, (S0 :: outL (Nat.odd (S b0' + 1)) r0,
           chd (outR (Nat.odd (S b0' + 1)) r0 (sw7 [S (S b0')])),
           ctl (outR (Nat.odd (S b0' + 1)) r0 (sw7 [S (S b0')]))))).
  { eapply wreach_trans.
    { apply wreach_csteps with (n:=1).
      change (Cf7 (S b0' :: r0)) with (StA, (S1 :: (rep [S1] b0' ++ S0 :: wbody r0), S0, @nil Sym)).
      apply ph_FT7. }
    eapply wreach_trans.
    { apply (reach_depA7 b0' r0 Hok Hr0). }
    apply wreach_csteps with (n:=1). reflexivity. }
  destruct Hw as (k & Hk). eexists. eexists. split; [exact Hk | reflexivity].
Qed.

Lemma vis_7m : forall p q, WInv 1 p ->
  exists k c, csteps tm_7m k (Cf7 p) = Some c /\ fst c = q.
Proof.
  intros p q Hinv. pose proof Hinv as (Hfp & Hpos & Hne).
  destruct p as [|b0 r0]; [congruence|].
  assert (Hb0 : 1 <= b0) by (inversion Hpos; assumption).
  destruct q.
  - exists 0. eexists. split; reflexivity.
  - destruct b0 as [|b0']; [lia|]. exists 1. eexists. split; reflexivity.
  - apply (reach_C7 b0 r0 Hinv).
  - destruct b0 as [|b0']; [lia|]. exists 2. eexists. split; reflexivity.
Qed.

Lemma nqh_7m : NeverQuasiHaltsSt tm_7m.
Proof.
  apply (wglue_neverqh tm_7m (list nat) (nextf 1) (WInv 1) Cf7 [4;2;1]).
  - split; [reflexivity | split; [repeat constructor; lia | discriminate]].
  - intros a Ha. apply WInv_preserved; exact Ha.
  - exact boot_7m.
  - exact nqh_lap7m.
  - exact vis_7m.
Qed.

Theorem nqh_1RB0LC_1LA1RD_1LA1LC_0RD1RB : NeverQuasiHaltsSt tm_7.
Proof.
  apply (mirror_never_qh tm_7). rewrite mirror_ok. exact nqh_7m.
Qed.
