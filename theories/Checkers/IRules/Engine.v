(** * IRules.Engine: the symbolic replay engine, one op at a time.

    The v1 engine of BBB docs/irules.md "Engine ops", ops 1 and 2:

    - **Concrete step**: fire the head transition; the written cell
      merges onto the departed side's nearest run; the head pops one
      cell from the approached side (a symbolic count decrements
      only when it provably stays >= 1 under the bounds [lo]).
    - **Chain hop**: entering a run [(s, e)] in state [q] whose
      transition keeps the state and the direction crosses all [e]
      copies in [e] steps, rewriting the run onto the departed side.

    [eng_step] performs one concrete step together with all chain
    hops it triggers (the C verifier's [iv_step]).  Its soundness
    theorem instantiates any valuation [nu >= lo]: the denoted
    abstract configurations are connected by [Reach], which packages
    [stepn], the *fired-transition cover* (every intermediate
    configuration is about to fire a listed transition) and the
    *firing witness* (every listed transition actually fires).  The
    cover gives quietness of unlisted states, the witness gives
    recurrence -- the two directions of the N/F/I classification of
    docs/irules.md "Meta-cycle and induction". *)

From Coq Require Import Arith ZArith Lia Bool List Setoid FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers.IRules Require Import Expr RLE.
Import ListNotations.
Open Scope Z_scope.

(** ** Transitions and reachability with fired-set tracking *)

Definition Tr : Set := (St * Sym)%type.

Definition tr_eqb (a b : Tr) : bool :=
  st_eqb (fst a) (fst b) && sym_eqb (snd a) (snd b).

Lemma tr_eqb_spec : forall a b, tr_eqb a b = true <-> a = b.
Proof.
  intros [qa sa] [qb sb]; unfold tr_eqb; simpl; split; intro H.
  - apply andb_prop in H as [H1 H2].
    apply st_eqb_spec in H1; apply sym_eqb_spec in H2. congruence.
  - injection H as -> ->.
    apply andb_true_intro; split;
      [apply st_eqb_spec | apply sym_eqb_spec]; reflexivity.
Qed.

(** The transition the configuration is about to fire. *)
Definition trans_of (c : ExecState) : Tr := (fst c, t_head (snd c)).

(** [Reach tm F n a b]: [n] steps from [a] to [b], every
    intermediate configuration fires a transition in [F], and every
    transition in [F] fires at least once. *)
Definition Covers (tm : TM) (F : list Tr) (n : nat) (a : ExecState)
  : Prop :=
  forall m, (m < n)%nat ->
  exists cm, stepn tm m a = Some cm /\ In (trans_of cm) F.

Definition Fires (tm : TM) (F : list Tr) (n : nat) (a : ExecState)
  : Prop :=
  forall t, In t F ->
  exists m cm, (m < n)%nat /\ stepn tm m a = Some cm /\ trans_of cm = t.

Definition Reach (tm : TM) (F : list Tr) (n : nat) (a b : ExecState)
  : Prop :=
  stepn tm n a = Some b /\ Covers tm F n a /\ Fires tm F n a.

Lemma Reach_refl : forall tm a, Reach tm [] 0 a a.
Proof.
  intros. split; [reflexivity|]. split.
  - intros m Hm; lia.
  - intros t Ht; destruct Ht.
Qed.

Lemma Reach_compose : forall tm F1 n1 F2 n2 a b c,
  Reach tm F1 n1 a b -> Reach tm F2 n2 b c ->
  Reach tm (F1 ++ F2) (n1 + n2) a c.
Proof.
  intros tm F1 n1 F2 n2 a b c (S1 & C1 & X1) (S2 & C2 & X2).
  split; [|split].
  - rewrite stepn_add, S1. exact S2.
  - intros m Hm.
    destruct (Nat.lt_ge_cases m n1) as [Hlt | Hge].
    + destruct (C1 m Hlt) as (cm & Hcm & Hin).
      exists cm. split; [assumption | apply in_or_app; auto].
    + destruct (C2 (m - n1)%nat ltac:(lia)) as (cm & Hcm & Hin).
      exists cm. split; [| apply in_or_app; auto].
      replace m with (n1 + (m - n1))%nat by lia.
      rewrite stepn_add, S1. exact Hcm.
  - intros t Ht. apply in_app_or in Ht as [Ht | Ht].
    + destruct (X1 t Ht) as (m & cm & Hm & Hcm & Htr).
      exists m, cm. split; [lia | auto].
    + destruct (X2 t Ht) as (m & cm & Hm & Hcm & Htr).
      exists (n1 + m)%nat, cm. split; [lia|].
      rewrite stepn_add, S1. auto.
Qed.

(** One step whose start configuration fires [t]. *)
Lemma Reach_one : forall tm a b,
  step tm a = Some b -> Reach tm [trans_of a] 1 a b.
Proof.
  intros tm a b H. split; [|split].
  - simpl. rewrite H. reflexivity.
  - intros m Hm. destruct m; [|lia].
    exists a. split; [reflexivity | left; reflexivity].
  - intros t [<- | []].
    exists O, a. split; [lia | split; reflexivity].
Qed.

(** ** Direction plumbing *)

Definition dir_eqb (a b : Dir) : bool :=
  match a, b with DL, DL | DR, DR => true | _, _ => false end.

Lemma dir_eqb_spec : forall a b, dir_eqb a b = true <-> a = b.
Proof. destruct a, b; simpl; split; congruence. Qed.

(** Is [(q, s)] a chain transition in direction [mv]? *)
Definition chainable (tm : TM) (q : St) (s : Sym) (mv : Dir) : bool :=
  match tm q s with
  | Some tr => st_eqb (t_next tr) q && dir_eqb (t_dir tr) mv
  | None => false
  end.

(** Reassemble an SCfg from loop coordinates: [dep] is the departed
    side (behind the head move direction [mv]), [app] the approached
    side. *)
Definition assemble (q : St) (h : Sym) (mv : Dir) (dep app : list SRun)
  : SCfg :=
  match mv with
  | DR => mkSCfg q h dep app
  | DL => mkSCfg q h app dep
  end.

(** The abstract mid-loop configuration: the head has just moved in
    direction [mv]; the departed runs are [dep], the approached
    half-tape (whose first cell the head now scans) is [app]. *)
Definition lsem (nu : nat -> Z) (q : St) (mv : Dir)
    (dep app : list SRun) : ExecState :=
  let df := lift_side (dside nu dep) in
  let af := lift_side (dside nu app) in
  match mv with
  | DR => (q, mkTape df (af O) (tail_side af))
  | DL => (q, mkTape (tail_side af) (af O) df)
  end.

Lemma tail_push : forall s f, tail_side (push_side s f) = f.
Proof.
  intros. apply functional_extensionality; intro n. reflexivity.
Qed.

(** ** Concrete chain-crossing runs *)

Section Chain.
Variable tm : TM.

Lemma repeat_shift : forall (x : Sym) n (l : list Sym),
  repeat x n ++ x :: l = x :: repeat x n ++ l.
Proof.
  intros. change (x :: l) with ([x] ++ l).
  rewrite app_assoc, <- repeat_cons. reflexivity.
Qed.

Lemma csteps_S : forall n c c1,
  cstep tm c = Some c1 -> csteps tm (S n) c = csteps tm n c1.
Proof. intros n c c1 H. simpl. rewrite H. reflexivity. Qed.

(** Right-moving crossing of [S c] copies (the head scans the first;
    [c] more follow): intermediate configurations... *)
Lemma chain_cc_R_mid : forall q s w,
  tm q s = Some (mkTrans w DR q) ->
  forall m c lc rc, (m <= c)%nat ->
  csteps tm m (q, (lc, s, repeat s c ++ rc)) =
  Some (q, (repeat w m ++ lc, s, repeat s (c - m) ++ rc)).
Proof.
  intros q s w Htr.
  induction m; intros c lc rc Hm.
  - simpl. rewrite Nat.sub_0_r. reflexivity.
  - destruct c as [|c']; [lia|].
    rewrite (csteps_S m (q, (lc, s, repeat s (S c') ++ rc))
               (q, (w :: lc, s, repeat s c' ++ rc)))
      by (simpl; rewrite Htr; reflexivity).
    rewrite (IHm c' (w :: lc) rc ltac:(lia)).
    rewrite repeat_shift.
    replace (S c' - S m)%nat with (c' - m)%nat by lia.
    reflexivity.
Qed.

(** ... and the full crossing. *)
Lemma chain_cc_R_end : forall q s w,
  tm q s = Some (mkTrans w DR q) ->
  forall c lc rc,
  csteps tm (S c) (q, (lc, s, repeat s c ++ rc)) =
  Some (q, (repeat w (S c) ++ lc, chd rc, ctl rc)).
Proof.
  intros q s w Htr.
  induction c; intros lc rc.
  - simpl. rewrite Htr. reflexivity.
  - rewrite (csteps_S (S c) (q, (lc, s, repeat s (S c) ++ rc))
               (q, (w :: lc, s, repeat s c ++ rc)))
      by (simpl; rewrite Htr; reflexivity).
    rewrite (IHc (w :: lc) rc).
    rewrite repeat_shift.
    reflexivity.
Qed.

(** Left-moving twins. *)
Lemma chain_cc_L_mid : forall q s w,
  tm q s = Some (mkTrans w DL q) ->
  forall m c lc rc, (m <= c)%nat ->
  csteps tm m (q, (repeat s c ++ lc, s, rc)) =
  Some (q, (repeat s (c - m) ++ lc, s, repeat w m ++ rc)).
Proof.
  intros q s w Htr.
  induction m; intros c lc rc Hm.
  - simpl. rewrite Nat.sub_0_r. reflexivity.
  - destruct c as [|c']; [lia|].
    rewrite (csteps_S m (q, (repeat s (S c') ++ lc, s, rc))
               (q, (repeat s c' ++ lc, s, w :: rc)))
      by (simpl; rewrite Htr; reflexivity).
    rewrite (IHm c' lc (w :: rc) ltac:(lia)).
    rewrite repeat_shift.
    replace (S c' - S m)%nat with (c' - m)%nat by lia.
    reflexivity.
Qed.

Lemma chain_cc_L_end : forall q s w,
  tm q s = Some (mkTrans w DL q) ->
  forall c lc rc,
  csteps tm (S c) (q, (repeat s c ++ lc, s, rc)) =
  Some (q, (ctl lc, chd lc, repeat w (S c) ++ rc)).
Proof.
  intros q s w Htr.
  induction c; intros lc rc.
  - simpl. rewrite Htr. reflexivity.
  - rewrite (csteps_S (S c) (q, (repeat s (S c) ++ lc, s, rc))
               (q, (repeat s c ++ lc, s, w :: rc)))
      by (simpl; rewrite Htr; reflexivity).
    rewrite (IHc lc (w :: rc)).
    rewrite repeat_shift.
    reflexivity.
Qed.

End Chain.

(** ** The engine loop: cross chainable runs, then set the head *)

Fixpoint eng_cross (tm : TM) (lo : list Z) (q : St) (mv : Dir)
    (app dep : list SRun)
  : option (list SRun * list SRun * Sym * list Tr) :=
  match app with
  | [] =>
      (* reading blanks: a chain transition on blank spins out *)
      if chainable tm q S0 mv then None else Some ([], dep, S0, [])
  | (s, e) :: rest =>
      if chainable tm q s mv then
        match tm q s with
        | Some tr =>
            if expr_ge lo e 1 then
              match push lo (t_write tr) e dep with
              | Some dep' =>
                  match eng_cross tm lo q mv rest dep' with
                  | Some (app', dep'', h, F) =>
                      Some (app', dep'', h, (q, s) :: F)
                  | None => None
                  end
              | None => None
              end
            else None
        | None => None (* unreachable: chainable implies defined *)
        end
      else if eeqb e (econst 1) then Some (rest, dep, s, [])
      else if expr_ge lo e 2 then
        Some ((s, eaddc e (-1)) :: rest, dep, s, [])
      else None
  end.

(** One engine op: the concrete step plus its chain hops. *)
Definition eng_step (tm : TM) (lo : list Z) (c : SCfg)
  : option (SCfg * list Tr) :=
  match tm (s_st c) (s_hs c) with
  | None => None
  | Some tr =>
      let q1 := t_next tr in
      let '(dep0, app0) :=
        match t_dir tr with
        | DR => (s_L c, s_R c)
        | DL => (s_R c, s_L c)
        end in
      match push lo (t_write tr) (econst 1) dep0 with
      | None => None
      | Some dep =>
          match eng_cross tm lo q1 (t_dir tr) app0 dep with
          | Some (app', dep', h, F) =>
              Some (assemble q1 h (t_dir tr) dep' app',
                    (s_st c, s_hs c) :: F)
          | None => None
          end
      end
  end.

(** ** Soundness *)

Lemma lift_cc : forall q l h r,
  lift (q, (l, h, r)) = (q, mkTape (lift_side l) h (lift_side r)).
Proof. reflexivity. Qed.


(** The mid-loop configuration, concretely: the head scans the first
    cell of the approached side's denotation. *)
Lemma lsem_concrete_R : forall nu q dep app,
  lsem nu q DR dep app =
  lift (q, (dside nu dep, chd (dside nu app), ctl (dside nu app))).
Proof.
  intros. unfold lsem.
  rewrite lift_cc, lift_side_tl, lift_side_hd. reflexivity.
Qed.

Lemma lsem_concrete_L : forall nu q dep app,
  lsem nu q DL dep app =
  lift (q, (ctl (dside nu app), chd (dside nu app), dside nu dep)).
Proof.
  intros. unfold lsem.
  rewrite lift_cc, lift_side_tl, lift_side_hd. reflexivity.
Qed.

Lemma eng_cross_sound : forall tm lo q mv app dep app' dep' h F,
  eng_cross tm lo q mv app dep = Some (app', dep', h, F) ->
  forall nu, bge lo nu ->
  exists n,
    Reach tm F n (lsem nu q mv dep app)
                 (asem nu (assemble q h mv dep' app')).
Proof.
  intros tm lo q mv app.
  induction app as [|[s e] rest IH]; intros dep app' dep' h F H nu Hb;
    simpl in H.
  - (* empty approached side: n = 0, blank head *)
    destruct (chainable tm q S0 mv) eqn:Hch; [discriminate|].
    injection H as <- <- <- <-.
    exists O.
    assert (Heq : lsem nu q mv dep [] =
                  asem nu (assemble q S0 mv dep [])).
    { destruct mv; [rewrite lsem_concrete_L | rewrite lsem_concrete_R];
        reflexivity. }
    setoid_rewrite Heq. apply Reach_refl.
  - destruct (chainable tm q s mv) eqn:Hch.
    + (* chain hop over (s, e) *)
      unfold chainable in Hch.
      destruct (tm q s) as [tr|] eqn:Htr; [|discriminate].
      apply andb_prop in Hch as [Hnx Hdir].
      apply st_eqb_spec in Hnx. apply dir_eqb_spec in Hdir.
      destruct (expr_ge lo e 1) eqn:Hge; [|discriminate].
      destruct (push lo (t_write tr) e dep) as [depP|] eqn:Hpush;
        [|discriminate].
      destruct (eng_cross tm lo q mv rest depP)
        as [[[[appX depX] hX] FX]|] eqn:Hrec; [|discriminate].
      injection H as <- <- <- <-.
      destruct (IH depP appX depX hX FX Hrec nu Hb) as (n2 & HR2).
      pose proof (expr_ge_sound lo e 1 nu Hge Hb) as He1.
      assert (Hsplit : exists n0, cnt nu e = S n0).
      { unfold cnt. exists (Z.to_nat (eval nu e) - 1)%nat. lia. }
      destruct Hsplit as [n0 Hn1].
      destruct tr as [w d q'].
      simpl in Hnx, Hdir. subst d q'.
      pose proof (push_den lo w e dep depP nu Hpush Hb) as Hpden.
      rewrite Hn1 in Hpden.
      assert (HR1 : Reach tm [(q, s)] (S n0)
                (lsem nu q mv dep ((s, e) :: rest))
                (lsem nu q mv depP rest)).
      { destruct mv.
        - (* DL *)
          assert (Hstart : lsem nu q DL dep ((s, e) :: rest) =
            lift (q, (repeat s n0 ++ dside nu rest, s, dside nu dep))).
          { rewrite lsem_concrete_L, dside_cons, Hn1. reflexivity. }
          assert (Hlend :
            lift (q, (ctl (dside nu rest), chd (dside nu rest),
                      repeat w (S n0) ++ dside nu dep)) =
            lsem nu q DL depP rest).
          { rewrite lsem_concrete_L, !lift_cc, Hpden. reflexivity. }
          split; [|split].
          + rewrite Hstart, <- Hlend.
            apply csteps_lift.
            apply chain_cc_L_end; exact Htr.
          + intros m Hm.
            rewrite Hstart.
            eexists. split.
            * apply csteps_lift.
              apply (chain_cc_L_mid tm q s w Htr m n0 (dside nu rest)
                       (dside nu dep) ltac:(lia)).
            * left. reflexivity.
          + intros t [<- | []].
            exists O. eexists. split; [lia|]. split; [reflexivity|].
            rewrite Hstart. reflexivity.
        - (* DR *)
          assert (Hstart : lsem nu q DR dep ((s, e) :: rest) =
            lift (q, (dside nu dep, s, repeat s n0 ++ dside nu rest))).
          { rewrite lsem_concrete_R, dside_cons, Hn1. reflexivity. }
          assert (Hlend :
            lift (q, (repeat w (S n0) ++ dside nu dep,
                      chd (dside nu rest), ctl (dside nu rest))) =
            lsem nu q DR depP rest).
          { rewrite lsem_concrete_R, !lift_cc, Hpden. reflexivity. }
          split; [|split].
          + rewrite Hstart, <- Hlend.
            apply csteps_lift.
            apply chain_cc_R_end; exact Htr.
          + intros m Hm.
            rewrite Hstart.
            eexists. split.
            * apply csteps_lift.
              apply (chain_cc_R_mid tm q s w Htr m n0 (dside nu dep)
                       (dside nu rest) ltac:(lia)).
            * left. reflexivity.
          + intros t [<- | []].
            exists O. eexists. split; [lia|]. split; [reflexivity|].
            rewrite Hstart. reflexivity. }
      exists (S n0 + n2)%nat.
      change ((q, s) :: FX) with ([(q, s)] ++ FX).
      exact (Reach_compose _ _ _ _ _ _ _ _ HR1 HR2).
    + (* non-chain: the head lands on this run *)
      destruct (eeqb e (econst 1)) eqn:He1.
      * injection H as <- <- <- <-.
        exists O.
        assert (Hc1 : cnt nu e = 1%nat).
        { unfold cnt. rewrite (eeqb_eval _ _ nu He1), eval_econst.
          reflexivity. }
        assert (Heq : lsem nu q mv dep ((s, e) :: rest) =
                      asem nu (assemble q s mv dep rest)).
        { destruct mv;
            [rewrite lsem_concrete_L | rewrite lsem_concrete_R];
            rewrite dside_cons, Hc1; reflexivity. }
        setoid_rewrite Heq. apply Reach_refl.
      * destruct (expr_ge lo e 2) eqn:Hge2; [|discriminate].
        injection H as <- <- <- <-.
        exists O.
        pose proof (expr_ge_sound lo e 2 nu Hge2 Hb) as He2.
        assert (Hcs : cnt nu e = S (cnt nu (eaddc e (-1)))).
        { unfold cnt. rewrite eval_eaddc. lia. }
        assert (Heq : lsem nu q mv dep ((s, e) :: rest) =
                      asem nu (assemble q s mv dep
                                 ((s, eaddc e (-1)) :: rest))).
        { destruct mv;
            [rewrite lsem_concrete_L | rewrite lsem_concrete_R];
            rewrite dside_cons, Hcs; reflexivity. }
        setoid_rewrite Heq. apply Reach_refl.
Qed.

Theorem eng_step_sound : forall tm lo c c' F,
  eng_step tm lo c = Some (c', F) ->
  forall nu, bge lo nu ->
  exists n, (1 <= n)%nat /\ Reach tm F n (asem nu c) (asem nu c').
Proof.
  intros tm lo c c' F H nu Hb.
  unfold eng_step in H.
  destruct (tm (s_st c) (s_hs c)) as [tr|] eqn:Htr; [|discriminate].
  destruct (t_dir tr) eqn:Hdir.
  - (* DL: departed side is R *)
    destruct (push lo (t_write tr) (econst 1) (s_R c)) as [dep|]
      eqn:Hpush; [|discriminate].
    destruct (eng_cross tm lo (t_next tr) DL (s_L c) dep)
      as [[[[app' dep'] h] F']|] eqn:Hcr; [|discriminate].
    injection H as <- <-.
    destruct (eng_cross_sound tm lo (t_next tr) DL (s_L c) dep
                app' dep' h F' Hcr nu Hb) as (n2 & HR2).
    assert (Hdep : lift_side (dside nu dep) =
                   push_side (t_write tr) (lift_side (dside nu (s_R c)))).
    { rewrite (push_den lo (t_write tr) (econst 1) (s_R c) dep nu
                 Hpush Hb).
      change (cnt nu (econst 1)) with 1%nat.
      apply lift_side_cons. }
    assert (Hstep : step tm (asem nu c) =
                    Some (lsem nu (t_next tr) DL dep (s_L c))).
    { unfold asem, dcfg. rewrite lift_cc.
      unfold step. cbn [t_head fst snd]. rewrite Htr, Hdir.
      unfold lsem, tape_move.
      rewrite Hdep. reflexivity. }
    assert (HR1 : Reach tm [(s_st c, s_hs c)] 1 (asem nu c)
                    (lsem nu (t_next tr) DL dep (s_L c))).
    { pose proof (Reach_one tm _ _ Hstep) as HRo.
      replace (trans_of (asem nu c)) with (s_st c, s_hs c) in HRo;
        [exact HRo | reflexivity]. }
    exists (1 + n2)%nat. split; [lia|].
    change ((s_st c, s_hs c) :: F') with ([(s_st c, s_hs c)] ++ F').
    exact (Reach_compose _ _ _ _ _ _ _ _ HR1 HR2).
  - (* DR: departed side is L *)
    destruct (push lo (t_write tr) (econst 1) (s_L c)) as [dep|]
      eqn:Hpush; [|discriminate].
    destruct (eng_cross tm lo (t_next tr) DR (s_R c) dep)
      as [[[[app' dep'] h] F']|] eqn:Hcr; [|discriminate].
    injection H as <- <-.
    destruct (eng_cross_sound tm lo (t_next tr) DR (s_R c) dep
                app' dep' h F' Hcr nu Hb) as (n2 & HR2).
    assert (Hdep : lift_side (dside nu dep) =
                   push_side (t_write tr) (lift_side (dside nu (s_L c)))).
    { rewrite (push_den lo (t_write tr) (econst 1) (s_L c) dep nu
                 Hpush Hb).
      change (cnt nu (econst 1)) with 1%nat.
      apply lift_side_cons. }
    assert (Hstep : step tm (asem nu c) =
                    Some (lsem nu (t_next tr) DR dep (s_R c))).
    { unfold asem, dcfg. rewrite lift_cc.
      unfold step. cbn [t_head fst snd]. rewrite Htr, Hdir.
      unfold lsem, tape_move.
      rewrite Hdep. reflexivity. }
    assert (HR1 : Reach tm [(s_st c, s_hs c)] 1 (asem nu c)
                    (lsem nu (t_next tr) DR dep (s_R c))).
    { pose proof (Reach_one tm _ _ Hstep) as HRo.
      replace (trans_of (asem nu c)) with (s_st c, s_hs c) in HRo;
        [exact HRo | reflexivity]. }
    exists (1 + n2)%nat. split; [lia|].
    change ((s_st c, s_hs c) :: F') with ([(s_st c, s_hs c)] ++ F').
    exact (Reach_compose _ _ _ _ _ _ _ _ HR1 HR2).
Qed.
