(** * NGram: the n-gram CPS instance of the closure engine.

    The BBB harness's [neverqh_ngram] certificate (docs/neverqh.md;
    verifier [nq_succ] in src/verify.c), reformulated head-relatively:

    - An abstract node is a *context* [(q, (lw, s, rw))]: state, head
      symbol, and the [n] tape cells on each side of the head
      (nearest first).  We reuse the [cconf] pair type; windows have
      length exactly [n] by construction.

    - Two *gram sets* [lset]/[rset] over-approximate the deep tape:
      the covering invariant says every n-window of a half-tape at
      depth >= 1 (offsets [d..d+n-1], d >= 1) belongs to the set.
      Note depth 1 overlaps the context window in n-1 cells -- this
      matches the C construction, where a right move consumes the
      right window at depth 1 (branching over its one unknown far
      cell) and donates the current LEFT window to [lset] (it becomes
      the new depth-1 left window).

    - A move consumes a depth-1 gram on the approached side (the
      unknown far cell [x] is branched over the alphabet, keeping the
      branches whose window is in the set) and requires the departed
      side's current window to be in its set ([ng_succs] returns
      [None] otherwise, which fails [closed_b] -- donation is a
      closure obligation, exactly the C fixpoint's set growth).

    The gram sets are *parameters* of the abstraction: an untrusted
    two-level fixpoint ([ng_grow]) mirrors the C prover to find them,
    then the trusted engine re-checks everything against the final
    sets, plus a seed check ([ng_seed_ok]) that the configuration at
    step [t] is covered.  With plain-acyclicity liveness (the
    engine's ranks), this is certificate-compatible with upstream
    [neverqh_ngram]'s [(t, n)] parameters.

    Representation ([PosEnc]): gram sets are Patricia tries keyed by
    the window encoding [syms_enc], and the engine's node identity is
    [cconf_enc] -- every membership test the closure performs is a
    trie lookup, so large-[n] certificates (gram sets of size up to
    2^n) check without the quadratic list scans of the first cut.
    Note the abstraction needs no injectivity for the gram sets:
    [ng_covers] is *defined* through [gmem], so any computable set
    would be sound -- injectivity is only load-bearing for the
    engine's node pool. *)

From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement CTape PosEnc PattCount Closure.
From BBB4.Checkers Require Import Cycle ExactClosure.
Import ListNotations.

(** ** Windows *)

Definition win (f : nat -> Sym) (d n : nat) : list Sym := map f (seq d n).

Lemma win_push_S : forall w f d n, win (push_side w f) (S d) n = win f d n.
Proof.
  intros. unfold win. rewrite <- seq_shift, map_map. reflexivity.
Qed.

Lemma win_tail : forall f d n, win (tail_side f) d n = win f (S d) n.
Proof.
  intros. unfold win. rewrite <- seq_shift, map_map. reflexivity.
Qed.

Lemma win_cons : forall f d n, win f d (S n) = f d :: win f (S d) n.
Proof. reflexivity. Qed.

Lemma win_snoc : forall f d n, win f d (S n) = win f d n ++ [f (d + n)].
Proof.
  intros. unfold win. rewrite seq_S, map_app. reflexivity.
Qed.

Lemma win_removelast : forall f d n, removelast (win f d (S n)) = win f d n.
Proof.
  intros. rewrite win_snoc. apply removelast_last.
Qed.

Lemma win_tl : forall f d n, tl (win f d (S n)) = win f (S d) n.
Proof. intros. rewrite win_cons. reflexivity. Qed.

Lemma win_chd : forall f d n, chd (win f d (S n)) = f d.
Proof. intros. rewrite win_cons. reflexivity. Qed.

(** Shifting the near window outward by one cell gives the depth-1
    window. *)
Lemma win_shift_out : forall f m,
  tl (win f 0 (S m)) ++ [f (S m)] = win f 1 (S m).
Proof.
  intros. rewrite win_tl, win_snoc. reflexivity.
Qed.

Lemma win_blank : forall l d n,
  length l <= d -> win (lift_side l) d n = repeat S0 n.
Proof.
  intros l d n. revert d. induction n; intros d H.
  - reflexivity.
  - rewrite win_cons. simpl. f_equal.
    + unfold lift_side, nthb. apply nth_overflow. assumption.
    + apply IHn. lia.
Qed.

(** ** Gram sets: tries of window encodings *)

Definition gset : Type := PositiveSet.t.

Definition gempty : gset := PositiveSet.empty.

Definition gmem (w : list Sym) (s : gset) : bool :=
  PositiveSet.mem (syms_enc w) s.

Definition gadd (g : list Sym) (s : gset) : gset :=
  PositiveSet.add (syms_enc g) s.

(** ** The abstraction *)

Definition ng_covers (n : nat) (lset rset : gset)
    (a : cconf) (c : ExecState) : Prop :=
  let '(q, (lw, s, rw)) := a in
  fst c = q /\
  t_head (snd c) = s /\
  lw = win (t_left (snd c)) 0 n /\
  rw = win (t_right (snd c)) 0 n /\
  (forall d, 1 <= d -> gmem (win (t_left (snd c)) d n) lset = true) /\
  (forall d, 1 <= d -> gmem (win (t_right (snd c)) d n) rset = true).


(** Successor branches as named definitions: keeps them opaque to
    whole-hypothesis [cbv] reductions, so the membership lemmas below
    can target their exact shape. *)

Definition ng_brR (rset : gset) (q' : St) (w : Sym)
    (lw rw : list Sym) (x : Sym) : list cconf :=
  if gmem (tl rw ++ [x]) rset
  then [(q', (w :: removelast lw, chd rw, tl rw ++ [x]))]
  else [].

Definition ng_brL (lset : gset) (q' : St) (w : Sym)
    (lw rw : list Sym) (x : Sym) : list cconf :=
  if gmem (tl lw ++ [x]) lset
  then [(q', (tl lw ++ [x], chd lw, w :: removelast rw))]
  else [].

Definition ng_succs (tm : TM) (lset rset : gset)
    (a : cconf) : option (list cconf) :=
  let '(q, (lw, s, rw)) := a in
  match tm q s with
  | None => None
  | Some tr =>
      match t_dir tr with
      | DR =>
          if gmem lw lset
          then Some (ng_brR rset (t_next tr) (t_write tr) lw rw S0
                     ++ ng_brR rset (t_next tr) (t_write tr) lw rw S1)
          else None
      | DL =>
          if gmem rw rset
          then Some (ng_brL lset (t_next tr) (t_write tr) lw rw S0
                     ++ ng_brL lset (t_next tr) (t_write tr) lw rw S1)
          else None
      end
  end.

Lemma in_ng_brR : forall rset q' w lw rw x,
  gmem (tl rw ++ [x]) rset = true ->
  In (q', (w :: removelast lw, chd rw, tl rw ++ [x]))
     (ng_brR rset q' w lw rw S0 ++ ng_brR rset q' w lw rw S1).
Proof.
  intros rset q' w lw rw x H.
  destruct x; unfold ng_brR;
    [apply in_or_app; left | apply in_or_app; right];
    rewrite H; left; reflexivity.
Qed.

Lemma in_ng_brL : forall lset q' w lw rw x,
  gmem (tl lw ++ [x]) lset = true ->
  In (q', (tl lw ++ [x], chd lw, w :: removelast rw))
     (ng_brL lset q' w lw rw S0 ++ ng_brL lset q' w lw rw S1).
Proof.
  intros lset q' w lw rw x H.
  destruct x; unfold ng_brL;
    [apply in_or_app; left | apply in_or_app; right];
    rewrite H; left; reflexivity.
Qed.

Lemma ng_covers_state : forall n lset rset a c,
  ng_covers n lset rset a c -> ec_state a = fst c.
Proof.
  intros n lset rset [q [[lw s] rw]] c (Hq & _).
  unfold ec_state; simpl. congruence.
Qed.

(** Halt-freeness: a context with successors covers no halting
    configuration. *)
Lemma ng_succs_nohalt : forall tm lset rset n a c sl,
  ng_covers n lset rset a c ->
  ng_succs tm lset rset a = Some sl ->
  step tm c = None -> False.
Proof.
  intros tm lset rset n [q [[lw s] rw]] [qc [L h R]] sl Hcov Esucc Estep.
  destruct Hcov as (Hq & Hh & _).
  simpl in Hq, Hh. subst qc h.
  unfold ng_succs in Esucc.
  unfold step in Estep; simpl in Estep.
  destruct (tm q s); discriminate.
Qed.

(** The step-coverage lemma: the heart of the instance. *)
Lemma ng_succs_sound_some : forall tm n lset rset a c sl c',
  1 <= n ->
  ng_covers n lset rset a c ->
  ng_succs tm lset rset a = Some sl ->
  step tm c = Some c' ->
  exists a', In a' sl /\ ng_covers n lset rset a' c'.
Proof.
  intros tm n lset rset a c sl c' Hn Hcov Esucc Estep.
  destruct a as [q [[lw s] rw]].
  destruct c as [qc [L h R]].
  destruct Hcov as (Hq & Hh & Hlw & Hrw & HL & HR).
  simpl in Hq, Hh. subst qc h lw rw.
  cbn [t_left t_right t_head snd fst] in *.
  destruct n as [|m]; [lia|].
  unfold ng_succs in Esucc.
  destruct (tm q s) as [tr|] eqn:Etr; [|discriminate].
  destruct (t_dir tr) eqn:Ed.
  - (* left move *)
    destruct (gmem (win R 0 (S m)) rset) eqn:Egr; [|discriminate].
    injection Esucc as <-.
    assert (Estep' : step tm (q, mkTape L s R)
                     = Some (t_next tr,
                             mkTape (tail_side L) (L 0)
                                    (push_side (t_write tr) R))).
    { unfold step; simpl. rewrite Etr, Ed. reflexivity. }
    rewrite Estep' in Estep. injection Estep as <-.
    (* the true far-left cell selects the branch *)
    exists (t_next tr,
            (tl (win L 0 (S m)) ++ [L (S m)],
             chd (win L 0 (S m)),
             t_write tr :: removelast (win R 0 (S m)))).
    split.
    + apply in_ng_brL.
      rewrite win_shift_out. apply HL. lia.
    + cbn [ng_covers t_left t_right t_head snd fst].
      rewrite win_chd.
      repeat split.
      * (* new left window *)
        rewrite win_shift_out, win_tail. reflexivity.
      * (* new right window *)
        rewrite win_removelast.
        rewrite win_cons, win_push_S. reflexivity.
      * (* left grams *)
        intros d Hd. rewrite win_tail. apply HL. lia.
      * (* right grams *)
        intros d Hd.
        destruct d as [|d']; [lia|].
        rewrite win_push_S.
        destruct d' as [|d''].
        -- exact Egr.
        -- apply HR. lia.
  - (* right move *)
    destruct (gmem (win L 0 (S m)) lset) eqn:Egl; [|discriminate].
    injection Esucc as <-.
    assert (Estep' : step tm (q, mkTape L s R)
                     = Some (t_next tr,
                             mkTape (push_side (t_write tr) L) (R 0)
                                    (tail_side R))).
    { unfold step; simpl. rewrite Etr, Ed. reflexivity. }
    rewrite Estep' in Estep. injection Estep as <-.
    exists (t_next tr,
            (t_write tr :: removelast (win L 0 (S m)),
             chd (win R 0 (S m)),
             tl (win R 0 (S m)) ++ [R (S m)])).
    split.
    + apply in_ng_brR.
      rewrite win_shift_out. apply HR. lia.
    + cbn [ng_covers t_left t_right t_head snd fst].
      rewrite win_chd.
      repeat split.
      * rewrite win_removelast.
        rewrite win_cons, win_push_S. reflexivity.
      * rewrite win_shift_out, win_tail. reflexivity.
      * intros d Hd.
        destruct d as [|d']; [lia|].
        rewrite win_push_S.
        destruct d' as [|d''].
        -- exact Egl.
        -- apply HL. lia.
      * intros d Hd. rewrite win_tail. apply HR. lia.
Qed.

(** Repackage in the engine's match shape. *)
Lemma ng_succs_sound : forall tm n lset rset a c,
  1 <= n ->
  ng_covers n lset rset a c ->
  match ng_succs tm lset rset a, step tm c with
  | Some l, Some c' => exists a', In a' l /\ ng_covers n lset rset a' c'
  | Some _, None => False
  | None, _ => True
  end.
Proof.
  intros tm n lset rset a c Hn Hcov.
  destruct (ng_succs tm lset rset a) as [sl|] eqn:Esucc; [|exact I].
  destruct (step tm c) as [c'|] eqn:Estep.
  - eapply ng_succs_sound_some; eauto.
  - eapply ng_succs_nohalt; eauto.
Qed.

(** ** Seeding: covering the configuration at step t *)

Definition ng_start (n : nat) (cc : cconf) : cconf :=
  let '(q, (l, h, r)) := cc in
  (q, (win (lift_side l) 0 n, h, win (lift_side r) 0 n)).

Definition seed_ok_side (n : nat) (l : list Sym)
    (set : gset) : bool :=
  forallb (fun d => gmem (win (lift_side l) d n) set)
          (seq 1 (length l + 1)).

Lemma seed_ok_side_sound : forall n l set,
  seed_ok_side n l set = true ->
  forall d, 1 <= d -> gmem (win (lift_side l) d n) set = true.
Proof.
  intros n l set H d Hd.
  unfold seed_ok_side in H. rewrite forallb_forall in H.
  destruct (le_lt_dec d (length l)) as [Hle | Hgt].
  - apply H. apply in_seq. lia.
  - rewrite win_blank by lia.
    rewrite <- (win_blank l (length l + 1) n) by lia.
    apply H. apply in_seq. lia.
Qed.

Definition ng_seed_ok (n : nat) (lset rset : gset)
    (cc : cconf) : bool :=
  let '(q, (l, h, r)) := cc in
  seed_ok_side n l lset && seed_ok_side n r rset.

Lemma ng_start_covers : forall n lset rset cc,
  ng_seed_ok n lset rset cc = true ->
  ng_covers n lset rset (ng_start n cc) (lift cc).
Proof.
  intros n lset rset [q [[l h] r]] H.
  apply andb_prop in H as [Hl Hr].
  simpl. repeat split.
  - intros d Hd. apply seed_ok_side_sound; assumption.
  - intros d Hd. apply seed_ok_side_sound; assumption.
Qed.

(** ** Untrusted gram-set search (the C prover's two-level fixpoint) *)

Definition ng_seed_side (n : nat) (l : list Sym) : list (list Sym) :=
  map (fun d => win (lift_side l) d n) (seq 1 (length l + 1)).

Definition gadds (gs : list (list Sym)) (s : gset) : gset :=
  fold_left (fun acc g => gadd g acc) gs s.

(** Explore reachable contexts under fixed sets, skipping (rather
    than failing on) contexts whose successors are blocked -- their
    donations feed the next round.  [sp] mirrors [seen] as a trie of
    [cconf_enc] keys. *)
Fixpoint ng_explore (tm : TM) (lset rset : gset)
    (fuel : nat) (seen : list cconf) (sp : PositiveSet.t)
    (todo : list cconf) : list cconf :=
  match fuel with
  | 0 => seen
  | S f =>
      match todo with
      | [] => seen
      | a :: todo' =>
          if pset_mem cconf cconf_enc a sp
          then ng_explore tm lset rset f seen sp todo'
          else let sp' := pset_add cconf cconf_enc a sp in
               match ng_succs tm lset rset a with
               | None => ng_explore tm lset rset f (a :: seen) sp' todo'
               | Some l => ng_explore tm lset rset f (a :: seen) sp'
                                      (l ++ todo')
               end
      end
  end.

Definition ng_harvest (tm : TM) (a : cconf)
  : (list (list Sym) * list (list Sym)) :=
  let '(q, (lw, s, rw)) := a in
  match tm q s with
  | Some tr => match t_dir tr with
               | DR => ([lw], [])
               | DL => ([], [rw])
               end
  | None => ([], [])
  end.

Fixpoint ng_grow (tm : TM) (a0 : cconf) (fuel rounds : nat)
    (lset rset : gset) : (gset * gset) :=
  match rounds with
  | 0 => (lset, rset)
  | S k =>
      let ctxs := ng_explore tm lset rset fuel [] PositiveSet.empty [a0] in
      let sets' :=
        fold_left (fun p a =>
                     let '(ls, rs) := p in
                     let '(hl, hr) := ng_harvest tm a in
                     (gadds hl ls, gadds hr rs))
                  ctxs (lset, rset) in
      let '(lset', rset') := sets' in
      if (PositiveSet.cardinal lset' =? PositiveSet.cardinal lset)
         && (PositiveSet.cardinal rset' =? PositiveSet.cardinal rset)
      then (lset, rset)
      else ng_grow tm a0 fuel k lset' rset'
  end.

(** ** The checker *)

Definition ngram_check_neverqh (tm : TM) (n t fuel rounds : nat) : bool :=
  (1 <=? n) &&
  match csteps tm t c0 with
  | Some cc =>
      let '(q, (l, h, r)) := cc in
      let lset0 := gadds (ng_seed_side n l) gempty in
      let rset0 := gadds (ng_seed_side n r) gempty in
      let a0 := ng_start n cc in
      let '(lset, rset) := ng_grow tm a0 fuel rounds lset0 rset0 in
      ng_seed_ok n lset rset cc &&
      closure_check_neverqh tm cconf cconf_enc ec_state
        (ng_succs tm lset rset) t fuel a0
  | None => false
  end.

Theorem ngram_check_neverqh_sound : forall tm n t fuel rounds,
  ngram_check_neverqh tm n t fuel rounds = true -> NeverQuasiHaltsSt tm.
Proof.
  intros tm n t fuel rounds H.
  unfold ngram_check_neverqh in H.
  apply andb_prop in H as [Hn H].
  apply Nat.leb_le in Hn.
  destruct (csteps tm t c0) as [[q [[l h] r]]|] eqn:Et; [|discriminate].
  match type of H with
  | (let '(_, _) := ?G in _) = true => destruct G as [lset rset] eqn:Eg
  end.
  cbv beta iota zeta in H.
  apply andb_prop in H as [Hseed Hcheck].
  apply (closure_check_neverqh_sound tm cconf cconf_enc ec_state
           (ng_succs tm lset rset) (ng_covers n lset rset)) in Hcheck;
    [assumption | | | |].
  - exact cconf_enc_inj.
  - intros a c Hc. eapply ng_covers_state; eauto.
  - intros a c Hc. apply ng_succs_sound; assumption.
  - intros ct' Hct'. rewrite Et in Hct'. injection Hct' as <-.
    apply ng_start_covers. exact Hseed.
Qed.

(** ** Ranking measures: counts of nonblank cells

    The canonical rank-rule measures (docs/neverqh.md): the number of
    1s on the whole tape / strictly left / strictly right of the
    head.  Values are computed on the computable configuration;
    deltas are read off the abstract context (the write, the old
    head, and the nearest cell of the approached window). *)

Fixpoint count1 (l : list Sym) : nat :=
  match l with
  | [] => 0
  | S1 :: t => S (count1 t)
  | S0 :: t => count1 t
  end.

Definition zc1 (s : Sym) : Z := match s with S1 => 1%Z | S0 => 0%Z end.
Definition nc1 (s : Sym) : nat := match s with S1 => 1 | S0 => 0 end.

Lemma count1_cons : forall x t, count1 (x :: t) = nc1 x + count1 t.
Proof. destruct x; reflexivity. Qed.

Lemma count1_ctl : forall r,
  Z.of_nat (count1 (ctl r)) = (Z.of_nat (count1 r) - zc1 (chd r))%Z.
Proof.
  destruct r as [|x t]; [reflexivity|].
  destruct x; cbn [count1 ctl chd zc1]; lia.
Qed.

Inductive ngmeas : Type := MAll | MLeft | MRight.

Definition ngm_val (m : ngmeas) (cc : cconf) : nat :=
  let '(q, (l, h, r)) := cc in
  match m with
  | MAll => count1 l + nc1 h + count1 r
  | MLeft => count1 l
  | MRight => count1 r
  end.

Definition ngm_delta (tm : TM) (m : ngmeas) (a a' : cconf) : Z :=
  let '(q, (lw, s, rw)) := a in
  match tm q s with
  | None => 0%Z
  | Some tr =>
      match m, t_dir tr with
      | MAll, _ => (zc1 (t_write tr) - zc1 s)%Z
      | MLeft, DR => zc1 (t_write tr)
      | MLeft, DL => (- zc1 (chd lw))%Z
      | MRight, DR => (- zc1 (chd rw))%Z
      | MRight, DL => zc1 (t_write tr)
      end
  end.

Lemma ngm_exact : forall tm n lset rset m a cc a' cc',
  1 <= n ->
  ng_covers n lset rset a (lift cc) ->
  cstep tm cc = Some cc' ->
  Z.of_nat (ngm_val m cc') = (Z.of_nat (ngm_val m cc) + ngm_delta tm m a a')%Z.
Proof.
  intros tm n lset rset m [q [[lw s] rw]] [qc [[l h] r]] a' cc' Hn Hcov Hstep.
  destruct Hcov as (Hq & Hh & Hlw & Hrw & _).
  simpl in Hq, Hh. subst qc h lw rw.
  cbn [snd t_left t_right t_head lift lift_tape] in *.
  destruct n as [|k]; [lia|].
  unfold cstep in Hstep.
  destruct (tm q s) as [tr|] eqn:Etr; [|discriminate].
  injection Hstep as <-.
  assert (Hcl : chd (win (lift_side l) 0 (S k)) = chd l).
  { rewrite win_chd. symmetry. apply lift_side_hd. }
  assert (Hcr : chd (win (lift_side r) 0 (S k)) = chd r).
  { rewrite win_chd. symmetry. apply lift_side_hd. }
  unfold ngm_delta. rewrite Etr.
  destruct (t_dir tr) eqn:Ed; destruct m; cbn [ngm_val ctape_move];
    rewrite ?Hcl, ?Hcr;
    destruct l as [|x1 t1]; destruct r as [|x2 t2];
    destruct (t_write tr); destruct s;
    try destruct x1; try destruct x2;
    cbn [count1 nc1 zc1 ctl chd]; lia.
Qed.

(** ** Pattern measures: the full [rkv_delta] vocabulary

    The C verifier's rank measures (src/verify.c, [rkv_delta]) are
    *pattern counts*: a word [p] over the alphabet (containing at
    least one nonblank) counted over the whole tape ([RgA]) or over
    the half-tape strictly left/right of the head ([RgL]/[RgR]).
    The [ngmeas] measures above are the special case [p = [S1]].

    Values are counted on the computable configuration's text padded
    with [|p|-1] blanks on the open ends, so occurrences straddling
    the written region are counted exactly once.  Deltas are read off
    the abstract context alone:

    - a step rewrites one interior cell of the whole-tape text, so
      the [RgA] delta is the count difference over the fixed
      [2|p|-1]-cell window around the head ([occ_update]);
    - a step pushes/pops one cell at the near end of each half-tape,
      so the [RgL]/[RgR] deltas are prefix-occurrence indicators.
      Left-of-head counts use the *reversed* pattern against the
      nearest-first left list, keeping every half-tape edit at the
      head of a list.

    Window-coverage constraints (checked by [pm_ok], weaker than the
    C verifier's): [|p| - 1 <= n] for [RgA], [|p| <= n] for L/R. *)

Inductive ngreg : Type := RgA | RgL | RgR.

Definition pm_pad (p : list Sym) : list Sym := repeat S0 (length p - 1).

Definition pm_val (p : list Sym) (rg : ngreg) (cc : cconf) : nat :=
  let '(_, (l, h, r)) := cc in
  match rg with
  | RgA => occ p (pm_pad p ++ rev l ++ h :: (r ++ pm_pad p))
  | RgL => occ (rev p) (l ++ pm_pad p)
  | RgR => occ p (r ++ pm_pad p)
  end.

Definition zind (b : bool) : Z := if b then 1%Z else 0%Z.

Definition pm_delta (tm : TM) (p : list Sym) (rg : ngreg)
    (a a' : cconf) : Z :=
  let '(q, (lw, s, rw)) := a in
  match tm q s with
  | None => 0%Z
  | Some tr =>
      let w := t_write tr in
      let p1 := length p - 1 in
      match rg, t_dir tr with
      | RgA, _ =>
          (Z.of_nat (occ p (rev (firstn p1 lw) ++ w :: firstn p1 rw))
           - Z.of_nat (occ p (rev (firstn p1 lw) ++ s :: firstn p1 rw)))%Z
      | RgL, DR => zind (syms_eqb (rev p) (w :: firstn p1 lw))
      | RgL, DL => (- zind (syms_eqb (rev p) (firstn (length p) lw)))%Z
      | RgR, DR => (- zind (syms_eqb p (firstn (length p) rw)))%Z
      | RgR, DL => zind (syms_eqb p (w :: firstn p1 rw))
      end
  end.

(** *** Windows of lifted sides vs. padded lists *)

Lemma win_firstn : forall f k d n,
  k <= n -> firstn k (win f d n) = win f d k.
Proof.
  intros f k. induction k as [|k IH]; intros d n H.
  - reflexivity.
  - destruct n as [|n']; [lia|].
    rewrite !win_cons. simpl firstn. f_equal. apply IH. lia.
Qed.

Lemma firstn_lift : forall l j k,
  k <= length l + j ->
  firstn k (l ++ repeat S0 j) = win (lift_side l) 0 k.
Proof.
  induction l as [|x l' IH]; intros j k H; simpl in H.
  - simpl app. rewrite pc_firstn_repeat, Nat.min_l by lia.
    symmetry. apply win_blank. simpl. lia.
  - destruct k as [|k'].
    + reflexivity.
    + simpl app. simpl firstn.
      rewrite IH by lia.
      rewrite lift_side_cons, win_cons, win_push_S.
      reflexivity.
Qed.

Lemma firstn_lift_win : forall l j k n,
  k <= n -> k <= length l + j ->
  firstn k (l ++ repeat S0 j) = firstn k (win (lift_side l) 0 n).
Proof.
  intros. rewrite firstn_lift, win_firstn by assumption. reflexivity.
Qed.

(** *** Half-tape edits *)

Lemma occ_side_push : forall p u x n,
  1 <= length p -> length p <= n ->
  occ p ((x :: u) ++ pm_pad p)
  = (if syms_eqb p (x :: firstn (length p - 1) (win (lift_side u) 0 n))
     then 1 else 0)
    + occ p (u ++ pm_pad p).
Proof.
  intros p u x n H1 Hn.
  simpl app. rewrite occ_cons. unfold prefix_eqb.
  rewrite firstn_S_pred by assumption.
  unfold pm_pad.
  rewrite (firstn_lift_win u (length p - 1) (length p - 1) n) by lia.
  reflexivity.
Qed.

Lemma occ_side_pop : forall p u n,
  In S1 p -> length p <= n ->
  occ p (u ++ pm_pad p)
  = (if syms_eqb p (firstn (length p) (win (lift_side u) 0 n))
     then 1 else 0)
    + occ p (ctl u ++ pm_pad p).
Proof.
  intros p u n H1 Hn.
  assert (Hlen : 1 <= length p)
    by (destruct p; [destruct H1 | simpl; lia]).
  destruct u as [|c u'].
  - cbn [ctl]. rewrite win_blank by (simpl; lia).
    rewrite pc_firstn_repeat, Nat.min_l by lia.
    rewrite syms_eqb_repeat_S0 by assumption.
    reflexivity.
  - cbn [ctl]. simpl app. rewrite occ_cons. unfold prefix_eqb, pm_pad.
    change (c :: u' ++ repeat S0 (length p - 1))
      with ((c :: u') ++ repeat S0 (length p - 1)).
    rewrite (firstn_lift_win (c :: u') (length p - 1) (length p) n)
      by (simpl; lia).
    reflexivity.
Qed.

(** *** Whole-tape cell rewrite *)

Lemma occ_full_update : forall p l s w r n,
  length p - 1 <= n ->
  occ p (pm_pad p ++ rev l ++ w :: (r ++ pm_pad p))
    + occ p (rev (firstn (length p - 1) (win (lift_side l) 0 n))
             ++ s :: firstn (length p - 1) (win (lift_side r) 0 n))
  = occ p (pm_pad p ++ rev l ++ s :: (r ++ pm_pad p))
    + occ p (rev (firstn (length p - 1) (win (lift_side l) 0 n))
             ++ w :: firstn (length p - 1) (win (lift_side r) 0 n)).
Proof.
  intros p l s w r n Hn.
  assert (HmidW : firstn (length p - 1) (l ++ pm_pad p)
                  = firstn (length p - 1) (win (lift_side l) 0 n)).
  { unfold pm_pad. apply firstn_lift_win; lia. }
  assert (HfpW : firstn (length p - 1) (r ++ pm_pad p)
                 = firstn (length p - 1) (win (lift_side r) 0 n)).
  { unfold pm_pad. apply firstn_lift_win; lia. }
  rewrite <- HmidW, <- HfpW.
  assert (Hsplit : pm_pad p ++ rev l
                   = rev (skipn (length p - 1) (l ++ pm_pad p))
                     ++ rev (firstn (length p - 1) (l ++ pm_pad p))).
  { rewrite <- rev_app_distr, firstn_skipn, rev_app_distr.
    f_equal. unfold pm_pad. symmetry. apply pc_rev_repeat. }
  rewrite !app_assoc, Hsplit, <- !app_assoc.
  apply occ_update.
  rewrite rev_length, firstn_length, app_length.
  unfold pm_pad. rewrite repeat_length. lia.
Qed.

(** *** Normalizing the stepped whole-tape text *)

Local Ltac app_norm :=
  repeat first [rewrite <- app_assoc | progress simpl app].

Lemma normA_push : forall p l w r,
  In S1 p ->
  occ p (pm_pad p ++ rev (w :: l) ++ chd r :: (ctl r ++ pm_pad p))
  = occ p (pm_pad p ++ rev l ++ w :: (r ++ pm_pad p)).
Proof.
  intros p l w r H1.
  destruct r as [|c r']; cbn [chd ctl rev]; unfold pm_pad.
  - transitivity
      (occ p ((repeat S0 (length p - 1) ++ rev l ++ [w])
              ++ repeat S0 (length p - 1) ++ [S0])).
    { f_equal. app_norm.
      rewrite (pc_repeat_shift S0 (length p - 1)). reflexivity. }
    rewrite occ_app_blank by assumption.
    f_equal. app_norm. reflexivity.
  - f_equal. app_norm. reflexivity.
Qed.

Lemma normA_pop : forall p l w r,
  In S1 p ->
  occ p (pm_pad p ++ rev (ctl l) ++ chd l :: ((w :: r) ++ pm_pad p))
  = occ p (pm_pad p ++ rev l ++ w :: (r ++ pm_pad p)).
Proof.
  intros p l w r H1.
  destruct l as [|c l']; cbn [chd ctl rev]; unfold pm_pad.
  - transitivity
      (occ p (S0 :: (repeat S0 (length p - 1)
                     ++ w :: r ++ repeat S0 (length p - 1)))).
    { f_equal. app_norm.
      rewrite pad_rotate. reflexivity. }
    rewrite occ_cons_blank;
      [| assumption
       | apply (firstn_pad_app (length p - 1)
                               (w :: r ++ repeat S0 (length p - 1)))].
    reflexivity.
  - f_equal. app_norm. reflexivity.
Qed.

Lemma pm_pad_rev : forall p, pm_pad (rev p) = pm_pad p.
Proof.
  intros p. unfold pm_pad. rewrite rev_length. reflexivity.
Qed.

(** *** Exactness *)

Lemma pm_exact : forall tm n lset rset p rg a cc a' cc',
  In S1 p ->
  (match rg with RgA => length p - 1 <= n | _ => length p <= n end) ->
  ng_covers n lset rset a (lift cc) ->
  cstep tm cc = Some cc' ->
  Z.of_nat (pm_val p rg cc')
  = (Z.of_nat (pm_val p rg cc) + pm_delta tm p rg a a')%Z.
Proof.
  intros tm n lset rset p rg [q [[lw s] rw]] [qc [[l h] r]] a' cc'
         Hp Hbound Hcov Hstep.
  assert (Hlen : 1 <= length p)
    by (destruct p; [destruct Hp | simpl; lia]).
  assert (Hprev : In S1 (rev p)) by (apply in_rev in Hp; exact Hp).
  destruct Hcov as (Hq & Hh & Hlw & Hrw & _).
  simpl in Hq, Hh. subst qc h lw rw.
  cbn [snd t_left t_right t_head lift lift_tape] in *.
  unfold cstep in Hstep.
  destruct (tm q s) as [tr|] eqn:Etr; [|discriminate].
  injection Hstep as <-.
  unfold pm_delta. rewrite Etr.
  destruct (t_dir tr) eqn:Ed; destruct rg; cbn [pm_val ctape_move].
  - (* DL, RgA *)
    rewrite normA_pop by assumption.
    pose proof (occ_full_update p l s (t_write tr) r n Hbound) as HU.
    lia.
  - (* DL, RgL *)
    rewrite <- (pm_pad_rev p).
    rewrite (occ_side_pop (rev p) l n Hprev)
      by (rewrite rev_length; assumption).
    rewrite rev_length.
    destruct (syms_eqb (rev p)
                (firstn (length p) (win (lift_side l) 0 n)));
      cbn [zind]; lia.
  - (* DL, RgR *)
    rewrite (occ_side_push p r (t_write tr) n Hlen Hbound).
    destruct (syms_eqb p
                (t_write tr
                 :: firstn (length p - 1) (win (lift_side r) 0 n)));
      cbn [zind]; lia.
  - (* DR, RgA *)
    rewrite normA_push by assumption.
    pose proof (occ_full_update p l s (t_write tr) r n Hbound) as HU.
    lia.
  - (* DR, RgL *)
    rewrite <- (pm_pad_rev p).
    rewrite (occ_side_push (rev p) l (t_write tr) n)
      by (rewrite rev_length; assumption).
    rewrite rev_length.
    destruct (syms_eqb (rev p)
                (t_write tr
                 :: firstn (length p - 1) (win (lift_side l) 0 n)));
      cbn [zind]; lia.
  - (* DR, RgR *)
    rewrite (occ_side_pop p r n Hp Hbound).
    destruct (syms_eqb p (firstn (length p) (win (lift_side r) 0 n)));
      cbn [zind]; lia.
Qed.

(** ** Certificate syntax and denotation *)

Inductive ngcomp : Type :=
| NgRank (phi : list (cconf * nat))
| NgMeas (m : ngmeas) (K : nat) (phi : list (cconf * nat))
         (gate : list cconf)
| NgRankE (phi : list (positive * nat))
| NgPattE (p : list Sym) (rg : ngreg) (K : nat)
          (phi : list (positive * nat)) (gate : list positive).

(** Certificate tables stay lists of [(context, value)] pairs in the
    generated [.v] files; the denotation compiles each into a
    [PositiveMap]/[PositiveSet] ONCE (the [let] is strict under
    [vm_compute], so the trie is shared across every edge lookup).
    The values need no soundness story: [lex_ok] re-checks every
    edge against whatever function comes out. *)

(** Encoded-key tables: bulk-generated certificates carry
    [cconf_enc]-encoded keys directly (a [positive] literal is ~5x
    smaller than a context term).  The data is untrusted -- the
    engine re-checks every edge against whatever function comes out
    -- so no correspondence between the emitted keys and real
    contexts needs proving; a wrong key merely fails the check. *)

Definition pmape_of (tbl : list (positive * nat)) : PositiveMap.tree nat :=
  fold_left (fun m e => PositiveMap.add (fst e) (snd e) m) tbl
            (PositiveMap.empty nat).

Definition pmape_get (m : PositiveMap.tree nat) (a : cconf) : nat :=
  match PositiveMap.find (cconf_enc a) m with
  | Some v => v
  | None => 0
  end.

Definition psete_of (l : list positive) : PositiveSet.t :=
  fold_left (fun s x => PositiveSet.add x s) l PositiveSet.empty.

(** The pattern-measure side conditions, checked computationally
    (a failing pattern denotes a sound no-op component). *)
Definition pm_ok (n : nat) (p : list Sym) (rg : ngreg) : bool :=
  existsb (fun x => sym_eqb x S1) p &&
  match rg with
  | RgA => length p - 1 <=? n
  | _ => length p <=? n
  end.

Definition ng_comp_denote (tm : TM) (n : nat) (c : ngcomp) : lexcomp cconf :=
  match c with
  | NgRank phi =>
      let pm := pmap_of cconf cconf_enc phi in
      LexRank cconf (pmap_get cconf cconf_enc pm)
  | NgMeas m K phi gate =>
      let pm := pmap_of cconf cconf_enc phi in
      let gs := pset_of cconf cconf_enc gate in
      LexMeas cconf (ngm_val m) (ngm_delta tm m) K
              (pmap_get cconf cconf_enc pm)
              (fun a => pset_mem cconf cconf_enc a gs)
  | NgRankE phi =>
      let pm := pmape_of phi in
      LexRank cconf (pmape_get pm)
  | NgPattE p rg K phi gate =>
      if pm_ok n p rg then
        let pm := pmape_of phi in
        let gs := psete_of gate in
        LexMeas cconf (pm_val p rg) (pm_delta tm p rg) K
                (pmape_get pm)
                (fun a => PositiveSet.mem (cconf_enc a) gs)
      else LexRank cconf (fun _ => 0)
  end.

Definition ngram_check_neverqh_lex (tm : TM) (n t fuel rounds : nat)
    (cert : St -> list ngcomp) : bool :=
  (1 <=? n) &&
  match csteps tm t c0 with
  | Some cc =>
      let '(q, (l, h, r)) := cc in
      let lset0 := gadds (ng_seed_side n l) gempty in
      let rset0 := gadds (ng_seed_side n r) gempty in
      let a0 := ng_start n cc in
      let '(lset, rset) := ng_grow tm a0 fuel rounds lset0 rset0 in
      ng_seed_ok n lset rset cc &&
      closure_check_neverqh_lex tm cconf cconf_enc ec_state
        (ng_succs tm lset rset) t fuel a0
        (fun q => map (ng_comp_denote tm n) (cert q))
  | None => false
  end.

(** the lex check with the gram sets supplied by the caller (e.g. the
    rank tier, which already grew them for its certificate closure):
    identical validation -- [ng_seed_ok] + the closure check re-derive
    everything from the given sets, so soundness does not depend on
    where they came from -- without re-running [ng_grow]. *)
Definition ngram_check_neverqh_lex_with (tm : TM) (n t fuel : nat)
    (lset rset : gset) (cert : St -> list ngcomp) : bool :=
  (1 <=? n) &&
  match csteps tm t c0 with
  | Some cc =>
      let a0 := ng_start n cc in
      ng_seed_ok n lset rset cc &&
      closure_check_neverqh_lex tm cconf cconf_enc ec_state
        (ng_succs tm lset rset) t fuel a0
        (fun q => map (ng_comp_denote tm n) (cert q))
  | None => false
  end.

Theorem ngram_check_neverqh_lex_with_sound :
  forall tm n t fuel lset rset cert,
  ngram_check_neverqh_lex_with tm n t fuel lset rset cert = true ->
  NeverQuasiHaltsSt tm.
Proof.
  intros tm n t fuel lset rset cert H.
  unfold ngram_check_neverqh_lex_with in H.
  apply andb_prop in H as [Hn H].
  apply Nat.leb_le in Hn.
  destruct (csteps tm t c0) as [cc|] eqn:Et; [|discriminate].
  apply andb_prop in H as [Hseed Hcheck].
  apply (closure_check_neverqh_lex_sound tm cconf cconf_enc ec_state
           (ng_succs tm lset rset) (ng_covers n lset rset)) in Hcheck;
    [assumption | | | | |].
  - exact cconf_enc_inj.
  - intros a c Hc. eapply ng_covers_state; eauto.
  - intros a c Hc. apply ng_succs_sound; assumption.
  - intros ct' Hct'. rewrite Et in Hct'. injection Hct' as <-.
    apply ng_start_covers. exact Hseed.
  - intros q0. apply Forall_forall. intros comp Hin.
    apply in_map_iff in Hin. destruct Hin as (c & <- & _).
    destruct c as [phi | m K phi gate | phi | pp rg K phi gate]; simpl.
    + exact I.
    + intros a cc' a' cc'' sl Hca Hca' Hstep Es HInl.
      eapply ngm_exact; eauto.
    + exact I.
    + destruct (pm_ok n pp rg) eqn:Epm; [|exact I].
      apply andb_prop in Epm as [He Hb].
      intros a cc' a' cc'' sl Hca Hca' Hstep Es HInl.
      eapply pm_exact; eauto.
      * apply existsb_exists in He as (x & Hx & Hx1).
        apply sym_eqb_spec in Hx1. subst x. assumption.
      * destruct rg; apply Nat.leb_le; assumption.
Qed.

Theorem ngram_check_neverqh_lex_sound : forall tm n t fuel rounds cert,
  ngram_check_neverqh_lex tm n t fuel rounds cert = true ->
  NeverQuasiHaltsSt tm.
Proof.
  intros tm n t fuel rounds cert H.
  unfold ngram_check_neverqh_lex in H.
  apply andb_prop in H as [Hn H].
  apply Nat.leb_le in Hn.
  destruct (csteps tm t c0) as [[q [[l h] r]]|] eqn:Et; [|discriminate].
  match type of H with
  | (let '(_, _) := ?G in _) = true => destruct G as [lset rset] eqn:Eg
  end.
  cbv beta iota zeta in H.
  apply andb_prop in H as [Hseed Hcheck].
  apply (closure_check_neverqh_lex_sound tm cconf cconf_enc ec_state
           (ng_succs tm lset rset) (ng_covers n lset rset)) in Hcheck;
    [assumption | | | | |].
  - exact cconf_enc_inj.
  - intros a c Hc. eapply ng_covers_state; eauto.
  - intros a c Hc. apply ng_succs_sound; assumption.
  - intros ct' Hct'. rewrite Et in Hct'. injection Hct' as <-.
    apply ng_start_covers. exact Hseed.
  - intros q0. apply Forall_forall. intros comp Hin.
    apply in_map_iff in Hin. destruct Hin as (c & <- & _).
    destruct c as [phi | m K phi gate | phi | pp rg K phi gate]; simpl.
    + exact I.
    + intros a cc a' cc' sl Hca Hca' Hstep Es HInl.
      eapply ngm_exact; eauto.
    + exact I.
    + destruct (pm_ok n pp rg) eqn:Epm; [|exact I].
      apply andb_prop in Epm as [He Hb].
      intros a cc a' cc' sl Hca Hca' Hstep Es HInl.
      eapply pm_exact; eauto.
      * apply existsb_exists in He as (x & Hx & Hx1).
        apply sym_eqb_spec in Hx1. subst x. assumption.
      * destruct rg; apply Nat.leb_le; assumption.
Qed.
