(** * NGramHist: the HISTORY-AUGMENTED n-gram instance of the closure engine.

    The gap this closes (docs/NGHIST_WAVE5.md): BBB4's [NGram] is mxdys'
    plain NGramCPS (impl2).  mxdys' impl1 augments each tape cell with a
    bounded record of the last [k] [(state,read)] updates ([TM.v]
    [Sigma_history := Sigma * list (St*Sigma)], written
    [(o, firstn k ((s,i0)::i1))]).  Over that richer alphabet the n-gram
    closure de-merges carry phases and FINITIZES for machines plain
    n-gram cannot close (measured: the counter tail closes at [k=2]).

    The augmentation is pure decoration -- it never changes the machine's
    behaviour (projected away by the cell's [fst]).  So we realise it as a
    NEW INSTANCE of the [Closure.v] engine over the ORIGINAL machine [tm]:

    - an augmented cell [hsym := Sym * list (St*Sym)] (truncated to [k]);
      an augmented computable config [hcconf]; an augmented step [hcstep]
      writing the updated cell; a projection [hproj : hcconf -> cconf]
      (drop histories).  [hproj] COMMUTES with [cstep] and halting matches
      -- THIS is the new soundness proof for the augmented-alphabet
      abstraction ([hcstep_proj]).

    - a node [hctx] = augmented n-gram context over [hsym] windows;
      [ha_state = St] (history is NOT part of the state, so the reused
      liveness gates see the ORIGINAL machine's states);
      [covers a c := exists hc, lift (hproj hc) = c /\ hng_abstracts a hc]
      -- an existential over the augmented config.  [succs_sound] steps the
      witness under [hcstep] and re-abstracts (an [hsym] fork of
      [NGram.ng_succs_sound_some]); the gram sets are over [hsym] windows,
      so the far-cell branch is history-constrained -- the closure
      refinement.

    Then [Closure.v]'s [live_ok]/[rank_ok]/[lex_ok] gates and the
    [closure_check_neverqh_lex_sound] theorem are REUSED VERBATIM.  Count /
    pattern measures read the bit projection, so [comp_exact] reduces to
    [NGram.ngm_exact]/[pm_exact].

    SAFETY != LIVENESS: a finite closed augmented set proves NonHalt only;
    never-QH comes from the liveness gates over the augmented closure. *)

From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement CTape PosEnc PattCount Closure.
From BBB4.Checkers Require Import Cycle ExactClosure NGram.
Import ListNotations.

(** ** The augmented alphabet *)

(** A history record: bounded list of the last-k [(state,read)] updates. *)
Definition hrec : Type := list (St * Sym).
Definition hsym : Type := (Sym * hrec)%type.

Definition hbit (x : hsym) : Sym := fst x.
Definition hblank : hsym := (S0, []).

(** Augmented computable config: like [cconf] but cells carry history. *)
Definition hctape : Type := (list hsym * hsym * list hsym)%type.
Definition hcconf : Type := (St * hctape)%type.

Definition hchd (l : list hsym) : hsym :=
  match l with [] => hblank | x :: _ => x end.
Definition hctl (l : list hsym) : list hsym :=
  match l with [] => [] | _ :: t => t end.

Definition hctape_move (d : Dir) (w : hsym) (ct : hctape) : hctape :=
  let '(l, h, r) := ct in
  match d with
  | DR => (w :: l, hchd r, hctl r)
  | DL => (hctl l, hchd l, w :: r)
  end.

(** The augmented step: look up [tm q (hbit head)]; write the ORIGINAL
    write-symbol tagged with the pushed, truncated history. *)
Definition hcstep (tm : TM) (k : nat) (c : hcconf) : option hcconf :=
  let '(q, (l, h, r)) := c in
  match tm q (hbit h) with
  | None => None
  | Some tr =>
      let w : hsym := (t_write tr, firstn k ((q, hbit h) :: snd h)) in
      Some (t_next tr, hctape_move (t_dir tr) w (l, h, r))
  end.

Fixpoint hcsteps (tm : TM) (k n : nat) (c : hcconf) : option hcconf :=
  match n with
  | 0 => Some c
  | S m => match hcstep tm k c with
           | None => None
           | Some c' => hcsteps tm k m c'
           end
  end.

(** ** Projection to the plain config *)

Definition hproj_side (l : list hsym) : list Sym := map hbit l.

Definition hproj (c : hcconf) : cconf :=
  let '(q, (l, h, r)) := c in (q, (hproj_side l, hbit h, hproj_side r)).

Lemma hproj_hchd : forall l, chd (hproj_side l) = hbit (hchd l).
Proof. destruct l; reflexivity. Qed.

Lemma hproj_hctl : forall l, ctl (hproj_side l) = hproj_side (hctl l).
Proof. destruct l; reflexivity. Qed.

Lemma hproj_state : forall c, fst (hproj c) = fst c.
Proof. destruct c as [q [[l h] r]]; reflexivity. Qed.

Lemma hproj_head : forall c, let '(_, (_, h, _)) := c in
  t_head (snd (lift (hproj c))) = hbit h.
Proof. destruct c as [q [[l h] r]]; reflexivity. Qed.

(** THE simulation: the augmented step projects to the plain step. *)
Lemma hcstep_proj : forall tm k c,
  match hcstep tm k c, cstep tm (hproj c) with
  | Some c', Some d' => hproj c' = d'
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros tm k [q [[l h] r]]. cbn [hcstep hproj].
  destruct (tm q (hbit h)) as [tr|] eqn:E; cbn [cstep].
  - rewrite E. cbn [hctape_move ctape_move].
    destruct (t_dir tr); cbn [hproj hproj_side map fst snd].
    + rewrite hproj_hchd, hproj_hctl. reflexivity.
    + rewrite hproj_hchd, hproj_hctl. reflexivity.
  - rewrite E. reflexivity.
Qed.

Lemma hcstep_proj_some : forall tm k c c',
  hcstep tm k c = Some c' -> cstep tm (hproj c) = Some (hproj c').
Proof.
  intros tm k c c' H. pose proof (hcstep_proj tm k c) as HP.
  rewrite H in HP. destruct (cstep tm (hproj c)); [congruence | contradiction].
Qed.

Lemma hcstep_proj_none : forall tm k c,
  hcstep tm k c = None -> cstep tm (hproj c) = None.
Proof.
  intros tm k c H. pose proof (hcstep_proj tm k c) as HP.
  rewrite H in HP. destruct (cstep tm (hproj c)); [contradiction | reflexivity].
Qed.

Lemma hcstep_proj_some_rev : forall tm k c d',
  cstep tm (hproj c) = Some d' ->
  exists c', hcstep tm k c = Some c' /\ hproj c' = d'.
Proof.
  intros tm k c d' H. pose proof (hcstep_proj tm k c) as HP.
  destruct (hcstep tm k c) as [c'|] eqn:E.
  - rewrite H in HP. eauto.
  - rewrite (hcstep_proj_none tm k c E) in H. discriminate.
Qed.

Lemma hcsteps_proj : forall tm k n c c',
  hcsteps tm k n c = Some c' -> csteps tm n (hproj c) = Some (hproj c').
Proof.
  intros tm k n. induction n as [|n IH]; intros c c' H; cbn [hcsteps csteps] in *.
  - injection H as <-. reflexivity.
  - destruct (hcstep tm k c) as [c1|] eqn:E; [|discriminate].
    rewrite (hcstep_proj_some tm k c c1 E). apply IH. exact H.
Qed.

(** ** Injective encoding of augmented nodes *)

Definition hpair_app (p : St * Sym) (acc : positive) : positive :=
  st_app (fst p) (sym_app (snd p) acc).

Lemma hpair_app_inj : forall x y p q,
  hpair_app x p = hpair_app y q -> x = y /\ p = q.
Proof.
  intros [a b] [c d] p q H. unfold hpair_app in H. simpl in H.
  destruct (st_app_inj _ _ _ _ H) as [-> H1].
  destruct (sym_app_inj _ _ _ _ H1) as [-> ->]. auto.
Qed.

Fixpoint hrec_app (l : hrec) (acc : positive) : positive :=
  match l with
  | [] => xO acc
  | x :: t => xI (hpair_app x (hrec_app t acc))
  end.

Lemma hrec_app_inj : forall l1 l2 p q,
  hrec_app l1 p = hrec_app l2 q -> l1 = l2 /\ p = q.
Proof.
  induction l1 as [|x t IH]; destruct l2 as [|y u]; simpl; intros p q H;
    try (split; congruence).
  injection H as H.
  destruct (hpair_app_inj _ _ _ _ H) as [-> H2].
  destruct (IH _ _ _ H2) as [-> ->]. auto.
Qed.

Definition hsym_app (x : hsym) (acc : positive) : positive :=
  sym_app (fst x) (hrec_app (snd x) acc).

Lemma hsym_app_inj : forall x y p q,
  hsym_app x p = hsym_app y q -> x = y /\ p = q.
Proof.
  intros [a b] [c d] p q H. unfold hsym_app in H. simpl in H.
  destruct (sym_app_inj _ _ _ _ H) as [-> H1].
  destruct (hrec_app_inj _ _ _ _ H1) as [-> ->]. auto.
Qed.

Fixpoint hsyms_app (l : list hsym) (acc : positive) : positive :=
  match l with
  | [] => xO acc
  | x :: t => xI (hsym_app x (hsyms_app t acc))
  end.

Lemma hsyms_app_inj : forall l1 l2 p q,
  hsyms_app l1 p = hsyms_app l2 q -> l1 = l2 /\ p = q.
Proof.
  induction l1 as [|x t IH]; destruct l2 as [|y u]; simpl; intros p q H;
    try (split; congruence).
  injection H as H.
  destruct (hsym_app_inj _ _ _ _ H) as [-> H2].
  destruct (IH _ _ _ H2) as [-> ->]. auto.
Qed.

Definition hctx_enc (a : hcconf) : positive :=
  let '(q, (lw, s, rw)) := a in
  st_app q (hsym_app s (hsyms_app lw (hsyms_app rw xH))).

Lemma hctx_enc_inj : forall a b, hctx_enc a = hctx_enc b -> a = b.
Proof.
  intros [q1 [[l1 s1] r1]] [q2 [[l2 s2] r2]] H. unfold hctx_enc in H.
  destruct (st_app_inj _ _ _ _ H) as [-> H1].
  destruct (hsym_app_inj _ _ _ _ H1) as [-> H2].
  destruct (hsyms_app_inj _ _ _ _ H2) as [-> H3].
  destruct (hsyms_app_inj _ _ _ _ H3) as [-> _]. reflexivity.
Qed.

(** ** Decidable equality of augmented cells / windows *)

Definition stsym_eqb (p q : St * Sym) : bool :=
  st_eqb (fst p) (fst q) && sym_eqb (snd p) (snd q).

Lemma stsym_eqb_spec : forall p q, stsym_eqb p q = true <-> p = q.
Proof.
  intros [a b] [c d]. unfold stsym_eqb; simpl. split.
  - intro H. apply andb_prop in H as [H1 H2].
    apply st_eqb_spec in H1; apply sym_eqb_spec in H2; subst; reflexivity.
  - intro H. injection H as -> ->.
    rewrite (proj2 (st_eqb_spec c c) eq_refl), (proj2 (sym_eqb_spec d d) eq_refl).
    reflexivity.
Qed.

Fixpoint hrec_eqb (l1 l2 : hrec) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: t1, y :: t2 => stsym_eqb x y && hrec_eqb t1 t2
  | _, _ => false
  end.

Lemma hrec_eqb_spec : forall l1 l2, hrec_eqb l1 l2 = true <-> l1 = l2.
Proof.
  induction l1 as [|x t1 IH]; destruct l2 as [|y t2]; simpl; split;
    intro H; try reflexivity; try discriminate.
  - apply andb_prop in H as [H1 H2].
    apply stsym_eqb_spec in H1; apply IH in H2; subst; reflexivity.
  - injection H as -> ->.
    rewrite (proj2 (stsym_eqb_spec y y) eq_refl), (proj2 (IH t2) eq_refl).
    reflexivity.
Qed.

Definition hsym_eqb (x y : hsym) : bool :=
  sym_eqb (fst x) (fst y) && hrec_eqb (snd x) (snd y).

Lemma hsym_eqb_spec : forall x y, hsym_eqb x y = true <-> x = y.
Proof.
  intros [a b] [c d]. unfold hsym_eqb; simpl. split.
  - intro H. apply andb_prop in H as [H1 H2].
    apply sym_eqb_spec in H1; apply hrec_eqb_spec in H2; subst; reflexivity.
  - intro H. injection H as -> ->.
    rewrite (proj2 (sym_eqb_spec c c) eq_refl), (proj2 (hrec_eqb_spec d d) eq_refl).
    reflexivity.
Qed.

Fixpoint hlist_eqb (l1 l2 : list hsym) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: t1, y :: t2 => hsym_eqb x y && hlist_eqb t1 t2
  | _, _ => false
  end.

Lemma hlist_eqb_spec : forall l1 l2, hlist_eqb l1 l2 = true <-> l1 = l2.
Proof.
  induction l1 as [|x t1 IH]; destruct l2 as [|y t2]; simpl; split;
    intro H; try reflexivity; try discriminate.
  - apply andb_prop in H as [H1 H2].
    apply hsym_eqb_spec in H1; apply IH in H2; subst; reflexivity.
  - injection H as -> ->.
    rewrite (proj2 (hsym_eqb_spec y y) eq_refl), (proj2 (IH t2) eq_refl).
    reflexivity.
Qed.

Lemma hlist_eqb_refl : forall l, hlist_eqb l l = true.
Proof. intro l. apply hlist_eqb_spec. reflexivity. Qed.

(** ** Windows over the augmented alphabet (list-direct, no funext) *)

Definition hnthb (l : list hsym) (n : nat) : hsym := nth n l hblank.
Definition hlift_side (l : list hsym) : nat -> hsym := fun n => hnthb l n.
Definition hwin (f : nat -> hsym) (d n : nat) : list hsym := map f (seq d n).

Lemma hwin_cons : forall f d n, hwin f d (S n) = f d :: hwin f (S d) n.
Proof. reflexivity. Qed.

Lemma hwin_snoc : forall f d n, hwin f d (S n) = hwin f d n ++ [f (d + n)].
Proof. intros. unfold hwin. rewrite seq_S, map_app. reflexivity. Qed.

Lemma hwin_removelast : forall f d n, removelast (hwin f d (S n)) = hwin f d n.
Proof. intros. rewrite hwin_snoc. apply removelast_last. Qed.

Lemma hwin_tl : forall f d n, tl (hwin f d (S n)) = hwin f (S d) n.
Proof. intros. rewrite hwin_cons. reflexivity. Qed.

Lemma hwin_chd : forall f d n, hchd (hwin f d (S n)) = f d.
Proof. intros. rewrite hwin_cons. reflexivity. Qed.

Lemma hwin_shift_out : forall f m,
  tl (hwin f 0 (S m)) ++ [f (S m)] = hwin f 1 (S m).
Proof.
  intros. rewrite hwin_tl, (hwin_snoc f 1 m).
  replace (1 + m) with (S m) by lia. reflexivity.
Qed.

Lemma hnthb_ctl : forall l i, hnthb (hctl l) i = hnthb l (S i).
Proof. intros [|x t] i; destruct i; reflexivity. Qed.

Lemma hlift_side_hd : forall l, hchd l = hlift_side l 0.
Proof. destruct l; reflexivity. Qed.

Lemma hwin_lift_consS : forall w l d n,
  hwin (hlift_side (w :: l)) (S d) n = hwin (hlift_side l) d n.
Proof.
  intros. unfold hwin, hlift_side. rewrite <- seq_shift, map_map.
  apply map_ext. intro i. reflexivity.
Qed.

Lemma hwin_lift_tl : forall l d n,
  hwin (hlift_side (hctl l)) d n = hwin (hlift_side l) (S d) n.
Proof.
  intros. unfold hwin, hlift_side. rewrite <- seq_shift, map_map.
  apply map_ext. intro i. rewrite hnthb_ctl. reflexivity.
Qed.

Lemma hwin_blank : forall l d n,
  length l <= d -> hwin (hlift_side l) d n = repeat hblank n.
Proof.
  intros l d n. revert d. induction n as [|n IH]; intros d H.
  - reflexivity.
  - rewrite hwin_cons. simpl. f_equal.
    + unfold hlift_side, hnthb. apply nth_overflow. assumption.
    + apply IH. lia.
Qed.

Lemma hwin_firstn : forall f k d n, k <= n -> firstn k (hwin f d n) = hwin f d k.
Proof.
  intros f k. induction k as [|k IH]; intros d n H.
  - reflexivity.
  - destruct n as [|n']; [lia|].
    rewrite !hwin_cons. simpl firstn. f_equal. apply IH. lia.
Qed.

(** ** Gram sets over augmented windows (lists) *)

Definition hgset : Type := list (list hsym).
Definition hgmem (w : list hsym) (s : hgset) : bool := existsb (hlist_eqb w) s.

Lemma In_hgmem : forall w s, In w s -> hgmem w s = true.
Proof.
  intros w s H. unfold hgmem. apply existsb_exists. exists w.
  split; [exact H | apply hlist_eqb_refl].
Qed.

Lemma hgmem_In : forall w s, hgmem w s = true -> In w s.
Proof.
  intros w s H. unfold hgmem in H. apply existsb_exists in H as (g & Hin & He).
  apply hlist_eqb_spec in He. subst g. exact Hin.
Qed.

(** ** The augmented abstraction *)

Definition hng_covers (n : nat) (lset rset : hgset)
    (a : hcconf) (hc : hcconf) : Prop :=
  let '(q, (lw, s, rw)) := a in
  let '(qc, (l, h, r)) := hc in
  q = qc /\ h = s /\
  lw = hwin (hlift_side l) 0 n /\
  rw = hwin (hlift_side r) 0 n /\
  (forall d, 1 <= d -> In (hwin (hlift_side l) d n) lset) /\
  (forall d, 1 <= d -> In (hwin (hlift_side r) d n) rset).

Definition ha_state (a : hcconf) : St := fst a.

Lemma hng_covers_state : forall n lset rset a hc,
  hng_covers n lset rset a hc -> ha_state a = fst hc.
Proof.
  intros n lset rset [q [[lw s] rw]] [qc [[l h] r]] (Hq & _).
  unfold ha_state; simpl. congruence.
Qed.

(** Successor branches: iterate the gram set for the newly-revealed far
    cell (the depth-1 window on the approached side). *)
Definition hbrR (rset : hgset) (n : nat) (q' : St) (w : hsym)
    (lw rw : list hsym) : list hcconf :=
  map (fun g => (q', (w :: removelast lw, hchd rw, g)))
      (filter (fun g => (length g =? n) && hlist_eqb (hctl rw) (firstn (pred n) g))
              rset).

Definition hbrL (lset : hgset) (n : nat) (q' : St) (w : hsym)
    (lw rw : list hsym) : list hcconf :=
  map (fun g => (q', (g, hchd lw, w :: removelast rw)))
      (filter (fun g => (length g =? n) && hlist_eqb (hctl lw) (firstn (pred n) g))
              lset).

Definition hng_succs (tm : TM) (k n : nat) (lset rset : hgset)
    (a : hcconf) : option (list hcconf) :=
  let '(q, (lw, s, rw)) := a in
  match tm q (hbit s) with
  | None => None
  | Some tr =>
      let w : hsym := (t_write tr, firstn k ((q, hbit s) :: snd s)) in
      match t_dir tr with
      | DR => if hgmem lw lset then Some (hbrR rset n (t_next tr) w lw rw) else None
      | DL => if hgmem rw rset then Some (hbrL lset n (t_next tr) w lw rw) else None
      end
  end.

(** The step-coverage lemma: the heart of the augmented instance.  The
    successor abstracting the augmented-stepped config is among the
    gram-set branches (the true depth-1 window is in the set, so it is
    one of the iterated far cells). *)
Lemma hng_succs_sound_some : forall tm k n lset rset a hc sl hc',
  1 <= n ->
  hng_covers n lset rset a hc ->
  hng_succs tm k n lset rset a = Some sl ->
  hcstep tm k hc = Some hc' ->
  exists a', In a' sl /\ hng_covers n lset rset a' hc'.
Proof.
  intros tm k n lset rset [q [[lw s] rw]] [qc [[l h] r]] sl hc' Hn Hcov Es Estep.
  destruct Hcov as (Hq & Hh & Hlw & Hrw & HL & HR).
  simpl in Hq, Hh. subst qc s.
  destruct n as [|m]; [lia|].
  (* the augmented step *)
  cbn [hcstep] in Estep.
  destruct (tm q (hbit h)) as [tr|] eqn:Etr; [|discriminate].
  set (w := (t_write tr, firstn k ((q, hbit h) :: snd h)) : hsym) in *.
  cbn [hng_succs] in Es. rewrite Etr in Es.
  destruct (t_dir tr) eqn:Ed.
  - (* left move *)
    destruct (hgmem rw rset) eqn:Egr; [|discriminate].
    injection Es as <-.
    cbn [hctape_move] in Estep. injection Estep as <-.
    set (g := hwin (hlift_side l) 1 (S m)).
    exists (t_next tr, (g, hchd lw, w :: removelast rw)).
    assert (Hin : In g lset).
    { subst g. apply (HL 1). lia. }
    split.
    + unfold hbrL. rewrite in_map_iff. exists g. split; [reflexivity|].
      apply filter_In. split; [exact Hin|].
      apply andb_true_intro. split.
      * subst g. unfold hwin. rewrite map_length, seq_length. apply Nat.eqb_refl.
      * subst g. rewrite Hlw. cbn [pred].
        rewrite (hwin_firstn (hlift_side l) m 1 (S m)) by lia.
        assert (E : hctl (hwin (hlift_side l) 0 (S m)) = hwin (hlift_side l) 1 m).
        { rewrite hwin_cons. reflexivity. }
        rewrite E. apply hlist_eqb_refl.
    + cbn [hng_covers]. repeat split; try reflexivity.
      * (* new head = hchd l *)
        rewrite Hlw. rewrite hwin_chd. apply hlift_side_hd.
      * (* new left window = g = depth-1 left window *)
        subst g. rewrite (hwin_lift_tl l 0 (S m)). reflexivity.
      * (* new right window = w :: removelast rw *)
        rewrite Hrw. rewrite hwin_removelast.
        rewrite hwin_cons. rewrite hwin_lift_consS. reflexivity.
      * (* deep left of hc' (side hctl l) *)
        intros d Hd. rewrite hwin_lift_tl. apply HL. lia.
      * (* deep right of hc' (side w::r) *)
        intros d Hd. destruct d as [|d']; [lia|].
        rewrite hwin_lift_consS.
        destruct d' as [|d''].
        -- rewrite <- Hrw. apply hgmem_In. exact Egr.
        -- apply HR. lia.
  - (* right move *)
    destruct (hgmem lw lset) eqn:Egl; [|discriminate].
    injection Es as <-.
    cbn [hctape_move] in Estep. injection Estep as <-.
    set (g := hwin (hlift_side r) 1 (S m)).
    exists (t_next tr, (w :: removelast lw, hchd rw, g)).
    assert (Hin : In g rset).
    { subst g. apply (HR 1). lia. }
    split.
    + unfold hbrR. rewrite in_map_iff. exists g. split; [reflexivity|].
      apply filter_In. split; [exact Hin|].
      apply andb_true_intro. split.
      * subst g. unfold hwin. rewrite map_length, seq_length. apply Nat.eqb_refl.
      * subst g. rewrite Hrw. cbn [pred].
        rewrite (hwin_firstn (hlift_side r) m 1 (S m)) by lia.
        assert (E : hctl (hwin (hlift_side r) 0 (S m)) = hwin (hlift_side r) 1 m).
        { rewrite hwin_cons. reflexivity. }
        rewrite E. apply hlist_eqb_refl.
    + cbn [hng_covers]. repeat split; try reflexivity.
      * (* new head = hchd r *)
        rewrite Hrw. rewrite hwin_chd. apply hlift_side_hd.
      * (* new left window = w :: removelast lw *)
        rewrite Hlw. rewrite hwin_removelast.
        rewrite hwin_cons. rewrite hwin_lift_consS. reflexivity.
      * (* new right window = g = depth-1 right window *)
        subst g. rewrite (hwin_lift_tl r 0 (S m)). reflexivity.
      * (* deep left of hc' (side w::l) *)
        intros d Hd. destruct d as [|d']; [lia|].
        rewrite hwin_lift_consS.
        destruct d' as [|d''].
        -- rewrite <- Hlw. apply hgmem_In. exact Egl.
        -- apply HL. lia.
      * (* deep right of hc' (side hctl r) *)
        intros d Hd. rewrite hwin_lift_tl. apply HR. lia.
Qed.

(** ** The covering relation over the ORIGINAL machine's ExecState *)

Definition hcovers (n : nat) (lset rset : hgset)
    (a : hcconf) (c : ExecState) : Prop :=
  exists hc, lift (hproj hc) = c /\ hng_covers n lset rset a hc.

Lemma hcovers_state : forall n lset rset a c,
  hcovers n lset rset a c -> ha_state a = fst c.
Proof.
  intros n lset rset a c (hc & Hlift & Hcov).
  rewrite (hng_covers_state n lset rset a hc Hcov).
  subst c. rewrite lift_state, hproj_state. reflexivity.
Qed.

(** The engine's [succs_sound] shape, at the covers level. *)
Lemma hng_succs_sound : forall tm k n lset rset a c,
  1 <= n ->
  hcovers n lset rset a c ->
  match hng_succs tm k n lset rset a, step tm c with
  | Some l, Some c' => exists a', In a' l /\ hcovers n lset rset a' c'
  | Some _, None => False
  | None, _ => True
  end.
Proof.
  intros tm k n lset rset a c Hn (hc & Hlift & Hcov). subst c.
  destruct (hng_succs tm k n lset rset a) as [sl|] eqn:Es; [|exact I].
  destruct (step tm (lift (hproj hc))) as [c'|] eqn:Estep.
  - destruct (cstep_lift_rev tm (hproj hc) c' Estep) as (cc' & Hcc' & Hlc).
    destruct (hcstep_proj_some_rev tm k hc cc' Hcc') as (hc' & Hhc' & Hpr).
    destruct (hng_succs_sound_some tm k n lset rset a hc sl hc' Hn Hcov Es Hhc')
      as (a' & Hin & Hcov').
    exists a'. split; [exact Hin|].
    exists hc'. split; [| exact Hcov'].
    rewrite Hpr. exact Hlc.
  - exfalso.
    destruct a as [q [[lw s] rw]].
    cbn [hng_succs] in Es.
    destruct (tm q (hbit s)) as [tr|] eqn:Etr; [| discriminate Es].
    assert (Hcs : cstep tm (hproj hc) <> None).
    { destruct hc as [qc [[l h] r]]. destruct Hcov as (Hq & Hh & _).
      simpl in Hq, Hh. subst qc. subst h. cbn [cstep hproj].
      rewrite Etr. discriminate. }
    destruct (cstep tm (hproj hc)) as [cc'|] eqn:Ecs; [| now apply Hcs].
    pose proof (cstep_lift tm _ _ Ecs) as Hst. congruence.
Qed.

(** ** Seeding: the augmented config at step [t] *)

Definition hcconf0 : hcconf := (StA, ([], hblank, [])).

Lemma hproj_hcconf0 : hproj hcconf0 = c0.
Proof. reflexivity. Qed.

Definition hng_start (n : nat) (hc : hcconf) : hcconf :=
  let '(q, (l, h, r)) := hc in
  (q, (hwin (hlift_side l) 0 n, h, hwin (hlift_side r) 0 n)).

Definition hseed_ok_side (n : nat) (l : list hsym) (s : hgset) : bool :=
  forallb (fun d => hgmem (hwin (hlift_side l) d n) s) (seq 1 (length l + 1)).

Lemma hseed_ok_side_sound : forall n l s,
  hseed_ok_side n l s = true ->
  forall d, 1 <= d -> In (hwin (hlift_side l) d n) s.
Proof.
  intros n l s H d Hd.
  unfold hseed_ok_side in H. rewrite forallb_forall in H.
  destruct (le_lt_dec d (length l)) as [Hle | Hgt].
  - apply hgmem_In, H. apply in_seq. lia.
  - rewrite hwin_blank by lia.
    rewrite <- (hwin_blank l (length l + 1) n) by lia.
    apply hgmem_In, H. apply in_seq. lia.
Qed.

Definition hseed_ok (n : nat) (lset rset : hgset) (hc : hcconf) : bool :=
  let '(q, (l, h, r)) := hc in
  hseed_ok_side n l lset && hseed_ok_side n r rset.

Lemma hng_start_covers : forall n lset rset hc,
  hseed_ok n lset rset hc = true ->
  hng_covers n lset rset (hng_start n hc) hc.
Proof.
  intros n lset rset [q [[l h] r]] H.
  apply andb_prop in H as [Hl Hr].
  cbn [hng_start hng_covers]. repeat split.
  - intros d Hd. apply hseed_ok_side_sound; assumption.
  - intros d Hd. apply hseed_ok_side_sound; assumption.
Qed.

(** ** The never-QH checker (plain acyclicity rank gate) *)

Definition ngramhist_check_neverqh (tm : TM) (k n t fuel : nat)
    (lset rset : hgset) : bool :=
  (1 <=? n) &&
  match hcsteps tm k t hcconf0 with
  | Some hct =>
      hseed_ok n lset rset hct &&
      closure_check_neverqh tm hcconf hctx_enc ha_state
        (hng_succs tm k n lset rset) t fuel (hng_start n hct)
  | None => false
  end.

Theorem ngramhist_check_neverqh_sound : forall tm k n t fuel lset rset,
  ngramhist_check_neverqh tm k n t fuel lset rset = true -> NeverQuasiHaltsSt tm.
Proof.
  intros tm k n t fuel lset rset H.
  unfold ngramhist_check_neverqh in H.
  apply andb_prop in H as [Hn H].
  apply Nat.leb_le in Hn.
  destruct (hcsteps tm k t hcconf0) as [hct|] eqn:Eht; [|discriminate].
  apply andb_prop in H as [Hseed Hcheck].
  apply (closure_check_neverqh_sound tm hcconf hctx_enc ha_state
           (hng_succs tm k n lset rset) (hcovers n lset rset)) in Hcheck;
    [assumption | | | |].
  - exact hctx_enc_inj.
  - intros a c Hc. eapply hcovers_state; eauto.
  - intros a c Hc. apply hng_succs_sound; assumption.
  - intros ct' Hct'.
    (* the augmented step-t config witnesses the cover *)
    pose proof (hcsteps_proj tm k t hcconf0 hct Eht) as Hpr.
    rewrite hproj_hcconf0 in Hpr. rewrite Hct' in Hpr. injection Hpr as Hpr.
    exists hct. split.
    + rewrite Hpr. reflexivity.
    + apply hng_start_covers. exact Hseed.
Qed.

(** ** Lexicographic liveness: count measures over the augmented closure

    The measure VALUE reads the plain computable config; the DELTA is read
    off the node's bit projection.  [comp_exact] reduces to an [ng_start]
    form of [NGram.ngm_exact] via [hproj a = ng_start n cc]. *)

Lemma hbit_nthb_map : forall l i, nthb (map hbit l) i = hbit (hnthb l i).
Proof.
  induction l as [|x l IH]; intros i.
  - destruct i; reflexivity.
  - destruct i; [reflexivity | apply IH].
Qed.

Lemma map_hbit_hwin : forall l d n,
  map hbit (hwin (hlift_side l) d n) = win (lift_side (map hbit l)) d n.
Proof.
  intros l d n. unfold hwin, win. rewrite map_map. apply map_ext. intro i.
  unfold hlift_side, lift_side. symmetry. apply hbit_nthb_map.
Qed.

Lemma hproj_eq_ngstart : forall n lset rset a hc cc,
  hng_covers n lset rset a hc -> lift (hproj hc) = lift cc ->
  hproj a = ng_start n cc.
Proof.
  intros n lset rset [q [[Lw s] Rw]] [qc [[l h] r]] [cq [[cl ch] cr]] Hcov Hlift.
  destruct Hcov as (Hq & Hh & HLw & HRw & _). simpl in Hq, Hh. subst qc. subst s.
  unfold lift, hproj, lift_tape, hproj_side in Hlift.
  injection Hlift as HqE HlE HhE HrE.
  subst cq. subst ch.
  cbn [hproj hproj_side ng_start]. subst Lw. subst Rw.
  rewrite !map_hbit_hwin, HlE, HrE. reflexivity.
Qed.

Lemma ngm_start_exact : forall tm n m cc cc' a',
  1 <= n -> cstep tm cc = Some cc' ->
  Z.of_nat (ngm_val m cc')
  = (Z.of_nat (ngm_val m cc) + ngm_delta tm m (ng_start n cc) a')%Z.
Proof.
  intros tm n m [q [[l h] r]] cc' a' Hn Hstep.
  destruct n as [|kk]; [lia|].
  cbn [ng_start].
  unfold cstep in Hstep. destruct (tm q h) as [tr|] eqn:Etr; [|discriminate].
  injection Hstep as <-.
  assert (Hcl : chd (win (lift_side l) 0 (S kk)) = chd l).
  { rewrite win_chd. symmetry. apply lift_side_hd. }
  assert (Hcr : chd (win (lift_side r) 0 (S kk)) = chd r).
  { rewrite win_chd. symmetry. apply lift_side_hd. }
  unfold ngm_delta. rewrite Etr.
  destruct (t_dir tr) eqn:Ed; destruct m; cbn [ngm_val ctape_move];
    rewrite ?Hcl, ?Hcr;
    destruct l as [|x1 t1]; destruct r as [|x2 t2];
    destruct (t_write tr); destruct h;
    try destruct x1; try destruct x2;
    cbn [count1 nc1 zc1 ctl chd]; lia.
Qed.

(** ** The lex never-QH checker (count measures, phase-dependent potentials)

    Certificate components are keyed by the FULL augmented node
    ([hctx_enc]) -- so potentials/gates are phase-dependent, the liveness
    granularity history buys.  A [HMeas] count measure discharges the
    counter tail (pilot: [lex-Left]); [HRank] is a phase-dependent rank. *)

Definition hpmape_get (m : PositiveMap.tree nat) (a : hcconf) : nat :=
  match PositiveMap.find (hctx_enc a) m with Some v => v | None => 0 end.

Definition hpsete_mem (gate : list positive) (a : hcconf) : bool :=
  PositiveSet.mem (hctx_enc a) (psete_of gate).

Inductive hcomp : Type :=
| HRank (phi : list (positive * nat))
| HMeas (m : ngmeas) (K : nat) (phi : list (positive * nat)) (gate : list positive).

Definition hcomp_denote (tm : TM) (c : hcomp) : lexcomp hcconf :=
  match c with
  | HRank phi => LexRank hcconf (hpmape_get (pmape_of phi))
  | HMeas m K phi gate =>
      LexMeas hcconf (ngm_val m) (fun a a' => ngm_delta tm m (hproj a) (hproj a'))
              K (hpmape_get (pmape_of phi)) (hpsete_mem gate)
  end.

Definition ngramhist_check_neverqh_lex (tm : TM) (k n t fuel : nat)
    (lset rset : hgset) (cert : St -> list hcomp) : bool :=
  (1 <=? n) &&
  match hcsteps tm k t hcconf0 with
  | Some hct =>
      hseed_ok n lset rset hct &&
      closure_check_neverqh_lex tm hcconf hctx_enc ha_state
        (hng_succs tm k n lset rset) t fuel (hng_start n hct)
        (fun q => map (hcomp_denote tm) (cert q))
  | None => false
  end.

Theorem ngramhist_check_neverqh_lex_sound : forall tm k n t fuel lset rset cert,
  ngramhist_check_neverqh_lex tm k n t fuel lset rset cert = true ->
  NeverQuasiHaltsSt tm.
Proof.
  intros tm k n t fuel lset rset cert H.
  unfold ngramhist_check_neverqh_lex in H.
  apply andb_prop in H as [Hn H].
  apply Nat.leb_le in Hn.
  destruct (hcsteps tm k t hcconf0) as [hct|] eqn:Eht; [|discriminate].
  apply andb_prop in H as [Hseed Hcheck].
  apply (closure_check_neverqh_lex_sound tm hcconf hctx_enc ha_state
           (hng_succs tm k n lset rset) (hcovers n lset rset)) in Hcheck;
    [assumption | | | | |].
  - exact hctx_enc_inj.
  - intros a c Hc. eapply hcovers_state; eauto.
  - intros a c Hc. apply hng_succs_sound; assumption.
  - intros ct' Hct'.
    pose proof (hcsteps_proj tm k t hcconf0 hct Eht) as Hpr.
    rewrite hproj_hcconf0 in Hpr. rewrite Hct' in Hpr. injection Hpr as Hpr.
    exists hct. split; [rewrite Hpr; reflexivity | apply hng_start_covers; exact Hseed].
  - intros q0. apply Forall_forall. intros comp Hin.
    apply in_map_iff in Hin. destruct Hin as (c & <- & _).
    destruct c as [phi | m K phi gate]; simpl.
    + exact I.
    + intros a cc a' cc' sl (hc & Hlift & Hcov) Hca' Hstep Es HInl.
      rewrite (hproj_eq_ngstart n lset rset a hc cc Hcov Hlift).
      apply ngm_start_exact; [exact Hn | exact Hstep].
Qed.
