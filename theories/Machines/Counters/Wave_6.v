(** * Wave_6: the wave_counter machine #6, 1RB0LB_0LB0RC_1LD1RC_1LA1RB.

    Edge state C, side R, poff 1, boot_vector [1;1;2;4] (cert
    results/counter6.cert).  The abstract parity-odometer orbit
    ([nextf 1]) and its safety invariant ([WInv 1]) are the ones
    already proven for #17/#27/#36/#7 and live in [WaveCounter]; this
    file carries only the machine and its per-pass CONCRETE run.

    Deltas from #27 (the "hard 4-step 0-writing cross" the wave
    hand-off flagged), all read off tools/counters/probe6.py and
    differentially validated by tools/counters/lap6.py (units ALL OK,
    300 orbit laps ALL OK):

    - the frontier turnaround [ph_FT6] is FIVE steps and consumes the
      frontier's top one (#27's is two and is generic in the left);
    - the leftward cross [ph_XC6] is a 4-step cycle that crosses TWO
      cells at a time and rewrites both as ones, so the run parity is
      carried by WHERE the walk stops rather than by an exit state;
    - crossing a separator is its own 5-step gadget [ph_BT6] (with an
      edge form [ph_BTe6] at the lead, which is the SPAWN);
    - THE SIMPLIFICATION: the rightward return leaves the tape
      byte-for-byte unchanged ([ph_RSW6] rewrites a one as a one,
      [ph_RSEP6] writes 1 at x, 1 at x-1, then 0 back at x).  So #6
      needs none of #27's relaid/bridge_l borrow algebra -- the
      leftward wave alone lands the tape on [wbody (nextf 1 front)]
      and the return is a pure traversal back to the frontier blank.

    Read concretely, [WaveCounter.carry] says: a run entered at offset
    0 deposits iff it is even, a run entered at offset 1 deposits iff
    it is odd, and a non-depositing run always hands the next one over
    at offset 1.

    No axioms beyond [functional_extensionality_dep]. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape WaveCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).

(** 1RB0LB_0LB0RC_1LD1RC_1LA1RB *)
Definition tm_6 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StB
  | StB, S0 => mk S0 DL StB | StB, S1 => mk S0 DR StC
  | StC, S0 => mk S1 DL StD | StC, S1 => mk S1 DR StC
  | StD, S0 => mk S1 DL StA | StD, S1 => mk S1 DR StB
  end.

(** ** The block-word encoding (identical to #17/#27) *)

Fixpoint wbody (front : list nat) : list Sym :=
  match front with
  | [] => [S1]
  | b :: r => rep [S1] b ++ S0 :: wbody r
  end.

Definition Cf6 (front : list nat) : cconf := (StC, (wbody front, S0, [])).

Lemma wbody_S : forall b r, wbody (S b :: r) = S1 :: wbody (b :: r).
Proof. reflexivity. Qed.

Lemma odd_2k : forall k, Nat.odd (2 * k) = false.
Proof. intro k. rewrite Nat.odd_mul. reflexivity. Qed.

Lemma odd_2k1 : forall k, Nat.odd (2 * k + 1) = true.
Proof. intro k. rewrite Nat.odd_add, odd_2k. reflexivity. Qed.

Lemma rep_one_end : forall k, rep [S1] k ++ [S1] = rep [S1] (S k).
Proof. intro k. apply (rep_shift [S1] k). Qed.

Lemma rep_two_end : forall k, rep [S1] k ++ [S1; S1] = rep [S1] (S (S k)).
Proof.
  intro k. change [S1; S1] with ([S1] ++ [S1]).
  rewrite app_assoc, rep_one_end, rep_one_end. reflexivity.
Qed.

Lemma repS1_slide : forall k L, rep [S1] k ++ S1 :: L = rep [S1] (S k) ++ L.
Proof.
  intros. symmetry. change (rep [S1] (S k)) with (S1 :: rep [S1] k).
  apply rep_slide.
Qed.

(** ** The gadget units

    Every one is a plain [csteps] reflexivity: [CTape.cstep] already
    materialises blanks with [chd]/[ctl], so no windowed transport is
    needed even where the run walks off the written extent. *)

(** FT: the frontier turnaround.  Writes the +1 past the frontier, lays a
    second one beyond it, and comes back onto the frontier's top cell in
    the leftward-wave state A. *)
Lemma ph_FT6 : forall L,
  csteps tm_6 5 (StC, (S1 :: L, S0, [])) = Some (StA, (L, S1, [S1; S1])).
Proof. reflexivity. Qed.

(** XC: the cross cycle.  Two cells per four steps, both rewritten as ones;
    the cell two below the head becomes the new head whatever it is. *)
Lemma ph_XC6 : forall c L R,
  csteps tm_6 4 (StA, (S1 :: c :: L, S1, R)) = Some (StA, (L, c, S1 :: S1 :: R)).
Proof. reflexivity. Qed.

(** BT: crossing a separator into the next run.  The separator effectively
    moves one cell frontier-ward and the walk resumes at offset 1. *)
Lemma ph_BT6 : forall c L R,
  csteps tm_6 5 (StA, (S0 :: S1 :: c :: L, S1, R))
  = Some (StA, (L, c, S1 :: S1 :: S0 :: R)).
Proof. reflexivity. Qed.

(** BT at the lead: the cell past the lead is the blank, so the walk lands
    on it and the following deposit SPAWNS a new leftmost block. *)
Lemma ph_BTe6 : forall R,
  csteps tm_6 5 (StA, ([S0; S1], S1, R))
  = Some (StA, ([], S0, S1 :: S1 :: S0 :: R)).
Proof. reflexivity. Qed.

(** DEP: the deposit -- write the carry's +1 at the separator and turn. *)
Lemma ph_DEP6 : forall L R,
  csteps tm_6 1 (StA, (L, S0, R)) = Some (StB, (S1 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

(** RS: the return start -- lay the new separator and enter the sweep. *)
Lemma ph_RS6 : forall L R,
  csteps tm_6 1 (StB, (L, S1, R)) = Some (StC, (S0 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

(** RSW: the return sweep over a one (rewrites it as a one). *)
Lemma ph_RSW6 : forall L R,
  csteps tm_6 1 (StC, (L, S1, R)) = Some (StC, (S1 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

(** RSEP: the return over a separator -- three steps that restore every
    cell they touch. *)
Lemma ph_RSEP6 : forall L R,
  csteps tm_6 3 (StC, (S1 :: L, S0, R)) = Some (StC, (S0 :: S1 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

(** ** The cross fold: [m] cycles cross [2m] cells *)

Lemma xc_run : forall m L R,
  csteps tm_6 (4 * m) (StA, (rep [S1] (2 * m) ++ L, S1, R))
  = Some (StA, (L, S1, rep [S1] (2 * m) ++ R)).
Proof.
  induction m as [|m IH]; intros L R.
  - reflexivity.
  - replace (4 * S m) with (4 + 4 * m) by lia.
    replace (2 * S m) with (S (S (2 * m))) by lia.
    change (rep [S1] (S (S (2 * m)))) with (S1 :: S1 :: rep [S1] (2 * m)).
    eapply csteps_chain with (n1 := 4) (n2 := 4 * m)
      (c1 := (StA, (rep [S1] (2 * m) ++ L, S1, S1 :: S1 :: R))).
    + rewrite <- app_comm_cons, <- app_comm_cons. apply ph_XC6.
    + rewrite (IH L (S1 :: S1 :: R)).
      rewrite repS1_slide, repS1_slide. reflexivity.
Qed.

(** ** The rightward return

    [rbody cs] is the not-yet-traversed word (runs [cs], nearest-first,
    single separators between them, none after the last).  [retl cs L]
    is the same word folded onto the left as the traversal consumes it.
    The traversal changes nothing, so this is pure bookkeeping. *)

Fixpoint rbody (cs : list nat) : list Sym :=
  match cs with
  | [] => []
  | [c] => rep [S1] c
  | c :: r => rep [S1] c ++ S0 :: rbody r
  end.

Fixpoint retl (cs : list nat) (L : list Sym) : list Sym :=
  match cs with
  | [] => L
  | [c] => rep [S1] c ++ L
  | c :: r => retl r (S0 :: rep [S1] c ++ L)
  end.

Lemma rbody_chd : forall c cs, 1 <= c -> chd (rbody (c :: cs)) = S1.
Proof. intros c cs Hc. destruct c as [|k]; [lia|]. destruct cs; reflexivity. Qed.

Lemma rbody_ctl : forall c cs, 1 <= c -> ctl (rbody (c :: cs)) = rbody (pred c :: cs).
Proof. intros c cs Hc. destruct c as [|k]; [lia|]. destruct cs; reflexivity. Qed.

Lemma ret_sw : forall k L R,
  csteps tm_6 (S k) (StC, (L, S1, rep [S1] k ++ R))
  = Some (StC, (rep [S1] (S k) ++ L, chd R, ctl R)).
Proof.
  induction k as [|k IH]; intros L R.
  - apply ph_RSW6.
  - change (rep [S1] (S k) ++ R) with (S1 :: (rep [S1] k ++ R)).
    eapply csteps_chain with (n1 := 1) (n2 := S k)
      (c1 := (StC, (S1 :: L, S1, rep [S1] k ++ R))).
    + apply ph_RSW6.
    + rewrite (IH (S1 :: L) R), repS1_slide. reflexivity.
Qed.

Lemma ret_sep : forall k L R,
  csteps tm_6 (S k + 3) (StC, (L, S1, rep [S1] k ++ S0 :: R))
  = Some (StC, (S0 :: rep [S1] (S k) ++ L, chd R, ctl R)).
Proof.
  intros k L R.
  eapply csteps_chain with (n1 := S k) (n2 := 3)
    (c1 := (StC, (rep [S1] (S k) ++ L, S0, R))).
  - rewrite (ret_sw k L (S0 :: R)). reflexivity.
  - change (rep [S1] (S k) ++ L) with (S1 :: (rep [S1] k ++ L)).
    apply ph_RSEP6.
Qed.

Lemma ret_end : forall k L,
  csteps tm_6 (S k) (StC, (L, S1, rep [S1] k))
  = Some (StC, (rep [S1] (S k) ++ L, S0, [])).
Proof.
  intros k L. rewrite <- (app_nil_r (rep [S1] k)).
  rewrite (ret_sw k L []). reflexivity.
Qed.

Lemma ret_fold : forall cs L,
  cs <> [] -> Forall (fun c => 1 <= c) cs ->
  wreach tm_6 (StC, (L, chd (rbody cs), ctl (rbody cs)))
              (StC, (retl cs L, S0, [])).
Proof.
  induction cs as [|c rest IH]; intros L Hne Hpos; [congruence|].
  inversion Hpos as [|? ? Hc Hrest]; subst.
  destruct c as [|k]; [lia|].
  destruct rest as [|c2 rest'].
  - (* the last (frontier) run: walk off into the blank *)
    apply wreach_csteps with (n := S k).
    change (rbody [S k]) with (rep [S1] (S k)).
    change (rep [S1] (S k)) with (S1 :: rep [S1] k).
    cbn [chd ctl]. apply ret_end.
  - (* an interior run, then its separator *)
    eapply wreach_trans.
    + apply wreach_csteps with (n := S k + 3).
      change (rbody (S k :: c2 :: rest'))
        with (rep [S1] (S k) ++ S0 :: rbody (c2 :: rest')).
      change (rep [S1] (S k) ++ S0 :: rbody (c2 :: rest'))
        with (S1 :: (rep [S1] k ++ S0 :: rbody (c2 :: rest'))).
      cbn [chd ctl]. apply ret_sep.
    + apply IH; [discriminate | exact Hrest].
Qed.

(** ** The leftward wave

    [dsufL po blocks] is the still-untouched lead-ward word at the moment
    the carry deposits; [wcs po blocks base] is the run-length list of the
    material the wave laid down behind it (nearest-first), on top of the
    frontier run [base]. *)

Definition mat (po : bool) (x : nat) : nat := if po then S x else x.

Definition dec1 (cs : list nat) : list nat :=
  match cs with [] => [] | c :: r => pred c :: r end.

Definition decp (po : bool) (cs : list nat) : list nat :=
  if po then dec1 cs else cs.

Lemma decp_mat : forall po x, decp po [mat po x] = [x].
Proof. intros [] x; reflexivity. Qed.

Fixpoint dsufL (po : bool) (blocks : list nat) : list Sym :=
  match blocks with
  | [] => []
  | b :: r => if po then wbody (b :: r) else dsufL (Nat.odd b) r
  end.

Fixpoint wcs (po : bool) (blocks : list nat) (base : list nat) : list nat :=
  match blocks with
  | [] => 2 :: base
  | b :: r => if po then base
              else wcs (Nat.odd b) r (mat (Nat.odd b) b :: base)
  end.

Definition wentry (po : bool) (blocks : list nat) (R : list Sym) : cconf :=
  if po then (StA, (wbody blocks, S0, R))
        else (StA, (S0 :: wbody blocks, S1, R)).

Lemma rbody_cons : forall c base, base <> [] ->
  rbody (c :: base) = rep [S1] c ++ S0 :: rbody base.
Proof. intros c [|x base'] H; [congruence | reflexivity]. Qed.

Lemma wave_L6 : forall blocks po base,
  carry_ok po blocks = true ->
  Forall (fun x => 1 <= x) blocks ->
  base <> [] ->
  wreach tm_6 (wentry po blocks (rbody base))
              (StA, (dsufL po blocks, S0, rbody (wcs po blocks base))).
Proof.
  induction blocks as [|b r IH]; intros po base Hok Hpos Hne.
  - (* the lead: SPAWN *)
    destruct po; simpl in Hok; [discriminate|].
    unfold wentry. cbn [wbody dsufL wcs].
    rewrite (rbody_cons 2 base Hne).
    apply wreach_csteps with (n := 5).
    change (rep [S1] 2 ++ S0 :: rbody base) with (S1 :: S1 :: S0 :: rbody base).
    apply ph_BTe6.
  - inversion Hpos as [|? ? Hb Hr]; subst.
    destruct po.
    + (* the carry deposits right here *)
      unfold wentry. cbn [dsufL wcs]. apply wreach_refl.
    + cbn [carry_ok] in Hok. unfold wentry. cbn [dsufL wcs].
      destruct b as [|[|d]]; [lia | |].
      * (* b = 1: BT lands straight on the next separator *)
        change (wbody (1 :: r)) with (S1 :: S0 :: wbody r).
        eapply wreach_trans.
        { apply wreach_csteps with (n := 5).
          apply (ph_BT6 S0 (wbody r) (rbody base)). }
        change (Nat.odd 1) with true. cbn [mat].
        replace (S1 :: S1 :: S0 :: rbody base) with (rbody (2 :: base))
          by (rewrite (rbody_cons 2 base Hne); reflexivity).
        exact (IH true (2 :: base) Hok Hr ltac:(discriminate)).
      * (* b = S (S d): BT then d/2 cross cycles *)
        change (wbody (S (S d) :: r))
          with (rep [S1] (S (S d)) ++ S0 :: wbody r).
        change (rep [S1] (S (S d)) ++ S0 :: wbody r)
          with (S1 :: S1 :: (rep [S1] d ++ S0 :: wbody r)).
        eapply wreach_trans.
        { apply wreach_csteps with (n := 5).
          apply (ph_BT6 S1 (rep [S1] d ++ S0 :: wbody r) (rbody base)). }
        destruct (Nat.even d) eqn:Ed.
        -- (* d = 2m, so b = S (S d) is even: continue *)
           apply Nat.even_spec in Ed. destruct Ed as (m & Hm). subst d.
           eapply wreach_trans.
           { apply wreach_csteps with (n := 4 * m).
             apply (xc_run m (S0 :: wbody r) (S1 :: S1 :: S0 :: rbody base)). }
           assert (Hodd : Nat.odd (S (S (2 * m))) = false).
           { replace (S (S (2 * m))) with (2 * S m) by lia. apply odd_2k. }
           rewrite Hodd in Hok |- *. cbn [mat].
           replace (rep [S1] (2 * m) ++ S1 :: S1 :: S0 :: rbody base)
             with (rbody (S (S (2 * m)) :: base))
             by (rewrite (rbody_cons (S (S (2 * m))) base Hne),
                         repS1_slide, repS1_slide; reflexivity).
           exact (IH false (S (S (2 * m)) :: base) Hok Hr ltac:(discriminate)).
        -- (* d = 2m+1, so b = S (S d) is odd: one extra cycle, then deposit *)
           assert (Hodd_d : Nat.odd d = true)
             by (rewrite <- Nat.negb_even, Ed; reflexivity).
           apply Nat.odd_spec in Hodd_d. destruct Hodd_d as (m & Hm). subst d.
           eapply wreach_trans.
           { apply wreach_csteps with (n := 4 * m).
             replace (rep [S1] (2 * m + 1) ++ S0 :: wbody r)
               with (rep [S1] (2 * m) ++ (S1 :: S0 :: wbody r))
               by (rewrite rep_add, <- app_assoc; reflexivity).
             apply (xc_run m (S1 :: S0 :: wbody r)
                             (S1 :: S1 :: S0 :: rbody base)). }
           eapply wreach_trans.
           { apply wreach_csteps with (n := 4).
             apply (ph_XC6 S0 (wbody r)
                     (rep [S1] (2 * m) ++ S1 :: S1 :: S0 :: rbody base)). }
           assert (Hodd : Nat.odd (S (S (2 * m + 1))) = true).
           { replace (S (S (2 * m + 1))) with (2 * S m + 1) by lia.
             apply odd_2k1. }
           rewrite Hodd in Hok |- *. cbn [mat].
           replace (S1 :: S1 :: rep [S1] (2 * m) ++ S1 :: S1 :: S0 :: rbody base)
             with (rbody (S (S (S (2 * m + 1))) :: base)).
           2:{ rewrite (rbody_cons (S (S (S (2 * m + 1)))) base Hne).
               replace (S (S (S (2 * m + 1)))) with (S (S (S (S (2 * m)))))
                 by lia.
               change (rep [S1] (S (S (S (S (2 * m))))) ++ S0 :: rbody base)
                 with (S1 :: S1 :: (rep [S1] (S (S (2 * m))) ++ S0 :: rbody base)).
               rewrite repS1_slide, repS1_slide. reflexivity. }
           exact (IH true (S (S (S (2 * m + 1))) :: base) Hok Hr
                     ltac:(discriminate)).
Qed.

(** ** The bridge: the wave's bookkeeping IS [carry] *)

Lemma retl_cons : forall c base L, base <> [] ->
  retl (c :: base) L = retl base (S0 :: rep [S1] c ++ L).
Proof. intros c [|x base'] L H; [congruence | reflexivity]. Qed.

Lemma bridge6 : forall blocks po base,
  carry_ok po blocks = true ->
  Forall (fun x => 1 <= x) blocks ->
  base <> [] ->
  retl (dec1 (wcs po blocks base)) (S0 :: S1 :: dsufL po blocks)
  = retl (decp po base) (S0 :: wbody (carry po blocks)).
Proof.
  induction blocks as [|b r IH]; intros po base Hok Hpos Hne.
  - destruct po; simpl in Hok; [discriminate|].
    cbn [wcs dsufL dec1 decp carry].
    rewrite (retl_cons 1 base _ Hne). cbn [wbody rep app]. reflexivity.
  - inversion Hpos as [|? ? Hb Hr]; subst.
    destruct po.
    + cbn [wcs dsufL decp carry]. rewrite wbody_S. reflexivity.
    + cbn [carry_ok] in Hok. cbn [wcs dsufL decp carry].
      rewrite (IH (Nat.odd b) (mat (Nat.odd b) b :: base) Hok Hr
                  ltac:(discriminate)).
      replace (decp (Nat.odd b) (mat (Nat.odd b) b :: base)) with (b :: base)
        by (destruct (Nat.odd b); reflexivity).
      rewrite (retl_cons b base _ Hne).
      cbn [wbody]. reflexivity.
Qed.

Lemma wcs_wf : forall blocks po base,
  carry_ok po blocks = true ->
  Forall (fun x => 1 <= x) blocks ->
  base <> [] ->
  Forall (fun x => 1 <= x) (decp po base) ->
  dec1 (wcs po blocks base) <> []
  /\ Forall (fun x => 1 <= x) (dec1 (wcs po blocks base)).
Proof.
  induction blocks as [|b r IH]; intros po base Hok Hpos Hne Hdec.
  - destruct po; simpl in Hok; [discriminate|].
    cbn [wcs dec1]. cbn [decp] in Hdec.
    split; [discriminate | constructor; [lia | exact Hdec]].
  - inversion Hpos as [|? ? Hb Hr]; subst.
    destruct po.
    + cbn [wcs]. cbn [decp] in Hdec.
      split; [destruct base; [congruence | discriminate] | exact Hdec].
    + cbn [carry_ok] in Hok. cbn [wcs]. cbn [decp] in Hdec.
      apply (IH (Nat.odd b) (mat (Nat.odd b) b :: base) Hok Hr
                ltac:(discriminate)).
      replace (decp (Nat.odd b) (mat (Nat.odd b) b :: base)) with (b :: base)
        by (destruct (Nat.odd b); reflexivity).
      constructor; [exact Hb | exact Hdec].
Qed.

(** ** Assembly *)

Lemma nqh_lap6 : forall front, WInv 1 front ->
  exists n c', csteps tm_6 n (Cf6 front) = Some c' /\
               lift c' = lift (Cf6 (nextf 1 front)) /\ 0 < n.
Proof.
  intros front (Hfp & Hpos & Hne).
  destruct front as [|b0 r0]; [congruence|].
  assert (Hr0 : Forall (fun x => 1 <= x) r0) by (inversion Hpos; assumption).
  assert (Hb0 : 1 <= b0) by (inversion Hpos; assumption).
  assert (Hok : carry_ok (Nat.odd (b0 + 1)) r0 = true)
    by (apply (WInv_no_leadstop 1 b0 r0 (conj Hfp (conj Hpos Hne)))).
  destruct b0 as [|b0']; [lia|].
  (* the frontier turnaround *)
  eapply wreach_lap with (n := 5)
    (c1 := (StA, (rep [S1] b0' ++ S0 :: wbody r0, S1, [S1; S1]))).
  - change (Cf6 (S b0' :: r0))
      with (StC, (S1 :: (rep [S1] b0' ++ S0 :: wbody r0), S0, @nil Sym)).
    apply ph_FT6.
  - lia.
  - (* cross the frontier run, then the wave, deposit, and return *)
    set (po0 := Nat.odd (S b0' + 1)).
    set (base := [mat po0 (S (S b0'))]).
    (* Step 1: reach [wentry po0 r0 (rbody base)]. *)
    assert (Hfront : wreach tm_6
              (StA, (rep [S1] b0' ++ S0 :: wbody r0, S1, [S1; S1]))
              (wentry po0 r0 (rbody base))).
    { destruct (Nat.even b0') eqn:Eb.
      - (* b0' even => S b0' odd => po0 = false: land at offset 1 of r0 *)
        apply Nat.even_spec in Eb. destruct Eb as (m & Hm). subst b0'.
        assert (Hpo : po0 = false).
        { unfold po0. replace (S (2 * m) + 1) with (2 * S m) by lia.
          apply odd_2k. }
        eapply wreach_trans.
        { apply wreach_csteps with (n := 4 * m).
          apply (xc_run m (S0 :: wbody r0) [S1; S1]). }
        unfold wentry. rewrite Hpo.
        unfold base. rewrite Hpo. cbn [mat rbody].
        replace (rep [S1] (S (S (2 * m)))) with (rep [S1] (2 * m) ++ [S1; S1])
          by (apply rep_two_end).
        apply wreach_refl.
      - (* b0' odd => S b0' even => po0 = true: land on r0's separator *)
        assert (Hodd : Nat.odd b0' = true)
          by (rewrite <- Nat.negb_even, Eb; reflexivity).
        apply Nat.odd_spec in Hodd. destruct Hodd as (m & Hm). subst b0'.
        assert (Hpo : po0 = true).
        { unfold po0. replace (S (2 * m + 1) + 1) with (2 * S m + 1) by lia.
          apply odd_2k1. }
        eapply wreach_trans.
        { apply wreach_csteps with (n := 4 * m).
          replace (rep [S1] (2 * m + 1) ++ S0 :: wbody r0)
            with (rep [S1] (2 * m) ++ (S1 :: S0 :: wbody r0))
            by (rewrite rep_add, <- app_assoc; reflexivity).
          apply (xc_run m (S1 :: S0 :: wbody r0) [S1; S1]). }
        eapply wreach_trans.
        { apply wreach_csteps with (n := 4).
          apply (ph_XC6 S0 (wbody r0) (rep [S1] (2 * m) ++ [S1; S1])). }
        unfold wentry. rewrite Hpo.
        unfold base. rewrite Hpo. cbn [mat rbody].
        replace (rep [S1] (S (S (S (2 * m + 1)))))
          with (S1 :: S1 :: rep [S1] (2 * m) ++ [S1; S1]).
        2:{ rewrite rep_two_end.
            replace (S (S (S (2 * m + 1)))) with (S (S (S (S (2 * m))))) by lia.
            reflexivity. }
        apply wreach_refl. }
    eapply wreach_trans; [exact Hfront | clear Hfront].
    (* Step 2: the wave *)
    assert (Hbase : base <> []) by (unfold base; discriminate).
    assert (Hok0 : carry_ok po0 r0 = true) by (unfold po0; exact Hok).
    eapply wreach_trans.
    { apply (wave_L6 r0 po0 base Hok0 Hr0 Hbase). }
    (* Step 3: deposit + return start *)
    set (cs := wcs po0 r0 base).
    assert (Hwf : dec1 cs <> [] /\ Forall (fun x => 1 <= x) (dec1 cs)).
    { unfold cs. apply (wcs_wf r0 po0 base Hok0 Hr0 Hbase).
      unfold base. rewrite decp_mat. constructor; [lia | constructor]. }
    destruct Hwf as (Hdne & Hdpos).
    destruct cs as [|c cs'] eqn:Ecs; [cbn in Hdne; congruence|].
    assert (Hc : 1 <= c).
    { cbn [dec1] in Hdpos. inversion Hdpos; lia. }
    eapply wreach_trans.
    { apply wreach_csteps with (n := 1).
      apply (ph_DEP6 (dsufL po0 r0) (rbody (c :: cs'))). }
    rewrite (rbody_chd c cs' Hc), (rbody_ctl c cs' Hc).
    eapply wreach_trans.
    { apply wreach_csteps with (n := 1).
      apply (ph_RS6 (S1 :: dsufL po0 r0) (rbody (pred c :: cs'))). }
    (* Step 4: the return traversal *)
    eapply wreach_trans.
    { apply (ret_fold (pred c :: cs') (S0 :: S1 :: dsufL po0 r0)
               ltac:(discriminate) Hdpos). }
    (* Step 5: the bridge *)
    change (pred c :: cs') with (dec1 (c :: cs')). rewrite <- Ecs. unfold cs.
    rewrite (bridge6 r0 po0 base Hok0 Hr0 Hbase).
    unfold base. rewrite decp_mat.
    change (Cf6 (nextf 1 (S b0' :: r0)))
      with (StC, (wbody (S (S b0') :: carry (Nat.odd (S b0' + 1)) r0), S0,
                  @nil Sym)).
    cbn [retl wbody]. apply wreach_refl.
Qed.

Lemma boot_6 : exists t0, stepn tm_6 t0 InitES = Some (lift (Cf6 [4; 2; 1])).
Proof.
  exists 74.
  assert (H : match csteps tm_6 74 CTape.c0 with
              | Some c => ceqb c (Cf6 [4; 2; 1]) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm_6 74 CTape.c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

Lemma vis_6 : forall p q, WInv 1 p ->
  exists k c, csteps tm_6 k (Cf6 p) = Some c /\ fst c = q.
Proof.
  intros p q (Hfp & Hpos & Hne). destruct p as [|b0 r0]; [congruence|].
  assert (Hb0 : 1 <= b0) by (inversion Hpos; assumption).
  destruct b0 as [|b0']; [lia|].
  change (Cf6 (S b0' :: r0))
    with (StC, (S1 :: (rep [S1] b0' ++ S0 :: wbody r0), S0, @nil Sym)).
  destruct q.
  - exists 5. eexists. split; reflexivity.
  - exists 2. eexists. split; reflexivity.
  - exists 0. eexists. split; reflexivity.
  - exists 1. eexists. split; reflexivity.
Qed.

Theorem nqh_1RB0LB_0LB0RC_1LD1RC_1LA1RB : NeverQuasiHaltsSt tm_6.
Proof.
  apply (wglue_neverqh tm_6 (list nat) (nextf 1) (WInv 1) Cf6 [4; 2; 1]).
  - split; [reflexivity | split; [repeat constructor; lia | discriminate]].
  - intros a Ha. apply WInv_preserved; exact Ha.
  - exact boot_6.
  - exact nqh_lap6.
  - exact vis_6.
Qed.
