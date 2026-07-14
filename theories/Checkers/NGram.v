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
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure.
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

(** ** Certificate syntax and denotation *)

Inductive ngcomp : Type :=
| NgRank (phi : list (cconf * nat))
| NgMeas (m : ngmeas) (K : nat) (phi : list (cconf * nat))
         (gate : list cconf).

(** Certificate tables stay lists of [(context, value)] pairs in the
    generated [.v] files; the denotation compiles each into a
    [PositiveMap]/[PositiveSet] ONCE (the [let] is strict under
    [vm_compute], so the trie is shared across every edge lookup).
    The values need no soundness story: [lex_ok] re-checks every
    edge against whatever function comes out. *)

Definition ng_comp_denote (tm : TM) (c : ngcomp) : lexcomp cconf :=
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
        (fun q => map (ng_comp_denote tm) (cert q))
  | None => false
  end.

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
    destruct c as [phi | m K phi gate]; simpl; [exact I|].
    intros a cc a' cc' sl Hca Hca' Hstep Es HInl.
    eapply ngm_exact; eauto.
Qed.
