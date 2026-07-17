(** * RepWL: the general-block-L repeated-word-list abstraction.

    The Coq half of the design validated by tools/repwl_prover.py
    (106/106 neverqh_rwlrank holdouts at t=0): whole-tape abstract
    configurations

        (q, (litems, lbuf, h, rbuf, ritems))

    where [lbuf]/[rbuf] are raw cells nearest-first around the head
    (the "buffer": always whole L-blocks, |lbuf|+1+|rbuf| in
    {L, 2L, 3L}), and [litems]/[ritems] are run-length item lists,
    nearest item first, each item [(w, c, cap)] denoting the block
    word [w] repeated exactly [c] times ([cap] = false) or at least
    [c] times ([cap] = true; canonically c = T, but soundness never
    assumes the invariant).  A LEFT word's cells are stored
    nearest-first (mirror image), so both sides run the same code.
    Trailing blank infinity is implicit.

    One TM step: write, move; if the head stays inside the buffer
    nothing else happens.  Walking off one end folds the departed-end
    block into that side's item list when the buffer is full (3L
    cells; run-length merge saturating at the threshold [T], a blank
    block against an empty list absorbed by the blank infinity), then
    pops the arrival side's nearest item -- branching two ways on a
    capped item (count was exactly [c] / strictly more) -- and
    materializes it.  Every concrete step is covered by one abstract
    successor ([rw_succs_sound]); a zero-count item (unreachable, but
    not excluded by the covering) fails closed.

    Unlike the n-gram instance there are NO untrusted gram sets: the
    abstraction is self-contained, so the checker is just seed +
    engine closure + the per-state lexicographic gate, with the five
    measures of docs/neverqh.md "RepWL ranking liveness"
    (N/A, N/L, N/R nonblank counts; 0/l, 0/r interior blank counts),
    whose per-node deltas are exact because both cap branches share
    the physical step and witness bits never depend on capped
    counts. *)

From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement CTape PosEnc Records Closure.
Import ListNotations.

(** ** Items, configurations, denotation *)

Record ritem : Set := mkItem { it_w : list Sym; it_c : nat; it_cap : bool }.

Definition rtape : Type :=
  (list ritem * list Sym * Sym * list Sym * list ritem)%type.
Definition rconf : Type := (St * rtape)%type.

Definition rw_state (a : rconf) : St := fst a.

(** [w] repeated [k] times. *)
Definition wrep (w : list Sym) (k : nat) : list Sym :=
  concat (repeat w k).

Lemma wrep_S : forall w k, wrep w (S k) = w ++ wrep w k.
Proof. reflexivity. Qed.

Lemma wrep_0 : forall w, wrep w 0 = [].
Proof. reflexivity. Qed.

(** An item list's possible expansions. *)
Inductive items_den : list ritem -> list Sym -> Prop :=
| items_den_nil : items_den nil nil
| items_den_cons : forall (w : list Sym) (c : nat) (cap : bool)
                          (k : nat) (rest : list ritem) (ext : list Sym),
    (if cap then c <= k else k = c) ->
    items_den rest ext ->
    items_den (mkItem w c cap :: rest) (wrep w k ++ ext).

(** A half-tape function matches buffer cells, then some expansion,
    then blanks ([nthb] pads with [S0] for free). *)
Definition side_den (b : list Sym) (items : list ritem)
    (f : nat -> Sym) : Prop :=
  exists ext, items_den items ext /\ forall i, f i = nthb (b ++ ext) i.

Definition rw_covers (a : rconf) (c : ExecState) : Prop :=
  let '(q, (li, lb, h, rb, ri)) := a in
  fst c = q /\
  t_head (snd c) = h /\
  side_den lb li (t_left (snd c)) /\
  side_den rb ri (t_right (snd c)).

Lemma rw_covers_state : forall a c, rw_covers a c -> rw_state a = fst c.
Proof.
  intros [q [[[[li lb] h] rb] ri]] c (Hq & _). simpl. congruence.
Qed.

(** ** The step *)

Definition blankw (L : nat) : list Sym := repeat S0 L.

Definition word_blank (w : list Sym) : bool :=
  forallb (fun x => sym_eqb x S0) w.

Definition syms_eqb (a b : list Sym) : bool :=
  (length a =? length b) && forallb (fun p => sym_eqb (fst p) (snd p))
                                    (combine a b).

Lemma syms_eqb_spec : forall a b, syms_eqb a b = true <-> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b]; unfold syms_eqb; simpl;
    split; intro H; try reflexivity; try discriminate.
  - apply andb_prop in H as [Hl H].
    apply andb_prop in H as [Hx Hr].
    apply sym_eqb_spec in Hx. subst y.
    apply Nat.eqb_eq in Hl.
    f_equal. apply IH. unfold syms_eqb.
    apply andb_true_intro. split; [apply Nat.eqb_eq; lia | exact Hr].
  - injection H as -> ->.
    apply andb_true_intro. split; [apply Nat.eqb_eq; reflexivity |].
    apply andb_true_intro. split; [apply sym_eqb_spec; reflexivity |].
    specialize (IH b). destruct IH as [_ IH].
    specialize (IH eq_refl). unfold syms_eqb in IH.
    apply andb_prop in IH as [_ IH]. exact IH.
Qed.

(** Fold one departed block into a side list (nearest end): merge
    with the nearest item when the word matches (count saturating at
    [T], the cap flag STICKY so an already-at-least item stays
    at-least), absorb a blank block into the blank infinity when the
    list is empty. *)
Definition push_item (T : nat) (w : list Sym) (items : list ritem)
    : list ritem :=
  match items with
  | [] => if word_blank w then [] else [mkItem w 1 (1 =? T)]
  | mkItem w0 c0 cap0 :: rest =>
      if syms_eqb w0 w
      then let c1 := Nat.min (S c0) T in
           mkItem w0 c1 (cap0 || (c1 =? T)) :: rest
      else mkItem w 1 (1 =? T) :: items
  end.

(** Pop the arrival side's nearest item: the blank block when the
    list is empty; 1 result (exact count) or 2 (cap branch: count
    was strictly above [c0] / exactly [c0]).  [None] on a zero-count
    item: its expansion can be empty, so no single popped word is
    faithful -- fail closed (unreachable from any seed anyway). *)
Definition pop_item (L : nat) (items : list ritem)
    : option (list (list Sym * list ritem)) :=
  match items with
  | [] => Some [(blankw L, [])]
  | mkItem [] _ _ :: _ => None
  | mkItem w0 c0 cap0 :: rest =>
      match c0 with
      | 0 => None
      | S c0' =>
          let dec := match c0' with
                     | 0 => rest
                     | S _ => mkItem w0 c0' false :: rest
                     end in
          Some (if cap0
                then [(w0, mkItem w0 (S c0') cap0 :: rest); (w0, dec)]
                else [(w0, dec)])
      end
  end.

(** ** List-lookup helpers *)

Lemma nthb_app_l : forall a b i, i < length a -> nthb (a ++ b) i = nthb a i.
Proof. intros. unfold nthb. apply app_nth1. assumption. Qed.

Lemma nthb_app_r : forall a b i,
  length a <= i -> nthb (a ++ b) i = nthb b (i - length a).
Proof. intros. unfold nthb. apply app_nth2. assumption. Qed.

Lemma nthb_blank : forall L i, nthb (blankw L) i = S0.
Proof.
  unfold blankw. induction L as [|L IH]; intros [|i]; simpl;
    solve [reflexivity | apply IH].
Qed.

Lemma word_blank_nthb : forall w, word_blank w = true ->
  forall i, nthb w i = S0.
Proof.
  induction w as [|x w IH]; intros H [|i]; simpl;
    try reflexivity;
    unfold word_blank in H; simpl in H;
    apply andb_prop in H as [Hx Hw].
  - apply sym_eqb_spec in Hx. exact Hx.
  - apply IH. exact Hw.
Qed.

(** One abstract step: at most two successors. *)
Definition rw_succs (tm : TM) (L T : nat) (a : rconf)
    : option (list rconf) :=
  let '(q, (li, lb, h, rb, ri)) := a in
  match tm q h with
  | None => None
  | Some tr =>
      let w := t_write tr in
      let q2 := t_next tr in
      match t_dir tr with
      | DR =>
          match rb with
          | x :: rb' => Some [(q2, (li, w :: lb, x, rb', ri))]
          | [] =>
              let lb1 := w :: lb in
              let '(lb2, li2) :=
                if 3 * L <=? length lb1
                then (firstn (2 * L) lb1,
                      push_item T (skipn (2 * L) lb1) li)
                else (lb1, li) in
              match pop_item L ri with
              | None => None
              | Some ps =>
                  Some (map (fun p =>
                          (q2, (li2, lb2, hd S0 (fst p), tl (fst p),
                                snd p))) ps)
              end
          end
      | DL =>
          match lb with
          | x :: lb' => Some [(q2, (li, lb', x, w :: rb, ri))]
          | [] =>
              let rb1 := w :: rb in
              let '(rb2, ri2) :=
                if 3 * L <=? length rb1
                then (firstn (2 * L) rb1,
                      push_item T (skipn (2 * L) rb1) ri)
                else (rb1, ri) in
              match pop_item L li with
              | None => None
              | Some ps =>
                  Some (map (fun p =>
                          (q2, (snd p, tl (fst p), hd S0 (fst p), rb2,
                                ri2))) ps)
              end
          end
      end
  end.

(** ** Soundness of the step *)

(** Depositing the written cell on the departed side. *)
Lemma side_den_push : forall w b items f,
  side_den b items f ->
  side_den (w :: b) items (push_side w f).
Proof.
  intros w b items f (ext & Hden & Hf).
  exists ext. split; [exact Hden|].
  intros [|i]; simpl.
  - reflexivity.
  - apply Hf.
Qed.

(** Folding the departed-end block into the item list. *)
Lemma push_side_den : forall T b blk items f,
  side_den (b ++ blk) items f ->
  side_den b (push_item T blk items) f.
Proof.
  intros T b blk items f (ext & Hden & Hf).
  unfold push_item.
  destruct items as [| [w0 c0 cap0] rest].
  - inversion Hden; subst ext.
    destruct (word_blank blk) eqn:Eb.
    + exists []. split; [constructor|].
      intro i. rewrite Hf. rewrite !app_nil_r.
      destruct (le_lt_dec (length b) i) as [Hge | Hlt].
      * rewrite nthb_app_r by assumption.
        rewrite (word_blank_nthb blk Eb).
        unfold nthb. rewrite nth_overflow by assumption. reflexivity.
      * rewrite nthb_app_l by assumption. reflexivity.
    + exists (wrep blk 1 ++ []).
      split.
      * apply (items_den_cons blk 1 (1 =? T) 1 [] []);
          [destruct (1 =? T); [lia | reflexivity] | constructor].
      * intro i. rewrite Hf.
        unfold wrep; simpl. rewrite !app_nil_r.
        reflexivity.
  - inversion Hden as [| w c cap k rest' ext0 Hk Hrest]; subst.
    destruct (syms_eqb w0 blk) eqn:Ew.
    + apply syms_eqb_spec in Ew. subst blk.
      exists (wrep w0 (S k) ++ ext0).
      split.
      * apply (items_den_cons w0 (Nat.min (S c0) T)
                 (cap0 || (Nat.min (S c0) T =? T)) (S k) rest ext0);
          [| exact Hrest].
        destruct cap0; cbn -[Nat.min].
        -- pose proof (Nat.le_min_l (S c0) T). lia.
        -- destruct (Nat.min (S c0) T =? T) eqn:Ec; cbn -[Nat.min].
           ++ pose proof (Nat.le_min_l (S c0) T). lia.
           ++ apply Nat.eqb_neq in Ec.
              destruct (Nat.min_dec (S c0) T) as [Em | Em]; lia.
      * intro i. rewrite Hf.
        rewrite wrep_S, <- !app_assoc. reflexivity.
    + exists (wrep blk 1 ++ (wrep w0 k ++ ext0)).
      split.
      * apply (items_den_cons blk 1 (1 =? T) 1
                 (mkItem w0 c0 cap0 :: rest) (wrep w0 k ++ ext0));
          [destruct (1 =? T); [lia | reflexivity] |].
        apply (items_den_cons w0 c0 cap0 k rest ext0);
          [exact Hk | exact Hrest].
      * intro i. rewrite Hf.
        unfold wrep at 2; simpl. rewrite app_nil_r.
        rewrite <- !app_assoc. reflexivity.
Qed.

(** Popping the arrival side's nearest item: some branch is faithful
    to any expansion, and the popped word is never empty. *)
Lemma pop_den : forall L items ps ext,
  1 <= L ->
  pop_item L items = Some ps ->
  items_den items ext ->
  exists wd items' ext',
    In (wd, items') ps /\ wd <> [] /\ items_den items' ext' /\
    forall i, nthb ext i = nthb (wd ++ ext') i.
Proof.
  intros L items ps ext HL Hpop Hden.
  destruct items as [| [w0 c0 cap0] rest].
  - simpl in Hpop. injection Hpop as <-.
    inversion Hden; subst ext.
    exists (blankw L), [], [].
    repeat split.
    + left. reflexivity.
    + unfold blankw. destruct L; [lia | simpl; discriminate].
    + constructor.
    + intro i. rewrite app_nil_r, nthb_blank.
      unfold nthb. destruct i; reflexivity.
  - simpl in Hpop.
    destruct w0 as [|y w0']; [discriminate|].
    destruct c0 as [|c0']; [discriminate|].
    injection Hpop as <-.
    inversion Hden as [| w c cap k rest' ext0 Hk Hrest]; subst.
    destruct cap0.
    + (* capped: k >= S c0' *)
      destruct k as [|k']; [lia|].
      destruct (le_lt_dec (S c0') k') as [Hge | Hlt].
      * (* count was > S c0': item unchanged *)
        exists (y :: w0'), (mkItem (y :: w0') (S c0') true :: rest),
               (wrep (y :: w0') k' ++ ext0).
        repeat split.
        -- left. reflexivity.
        -- discriminate.
        -- apply (items_den_cons (y :: w0') (S c0') true k' rest ext0);
             [exact Hge | exact Hrest].
        -- intro i. rewrite wrep_S, <- app_assoc. reflexivity.
      * (* count was exactly S c0' *)
        assert (Hkc : k' = c0') by lia.
        subst k'.
        exists (y :: w0'),
               (match c0' with
                | 0 => rest
                | S _ => mkItem (y :: w0') c0' false :: rest
                end),
               (wrep (y :: w0') c0' ++ ext0).
        repeat split.
        -- right. left.
           destruct c0'; reflexivity.
        -- discriminate.
        -- destruct c0' as [|c0''].
           ++ unfold wrep. simpl. exact Hrest.
           ++ apply (items_den_cons (y :: w0') (S c0'') false (S c0'')
                       rest ext0); [reflexivity | exact Hrest].
        -- intro i. rewrite wrep_S, <- app_assoc. reflexivity.
    + (* exact count *)
      subst k.
      exists (y :: w0'),
             (match c0' with
              | 0 => rest
              | S _ => mkItem (y :: w0') c0' false :: rest
              end),
             (wrep (y :: w0') c0' ++ ext0).
      repeat split.
      * left. destruct c0'; reflexivity.
      * discriminate.
      * destruct c0' as [|c0''].
        -- unfold wrep. simpl. exact Hrest.
        -- apply (items_den_cons (y :: w0') (S c0'') false (S c0'')
                    rest ext0); [reflexivity | exact Hrest].
      * intro i. rewrite wrep_S, <- app_assoc. reflexivity.
Qed.

(** The step-coverage lemma: every concrete step out of a covered
    configuration lands on one of the abstract successors. *)
Lemma rw_succs_sound : forall tm L T a c,
  1 <= L ->
  rw_covers a c ->
  match rw_succs tm L T a, step tm c with
  | Some l, Some c' => exists a', In a' l /\ rw_covers a' c'
  | Some _, None => False
  | None, _ => True
  end.
Proof.
  intros tm L T [q [[[[li lb] h] rb] ri]] [qc tp] HL (Hq & Hh & Hl & Hr).
  simpl in Hq, Hh, Hl, Hr. subst qc.
  unfold rw_succs.
  destruct (tm q h) as [tr|] eqn:Etr; [| exact I].
  assert (Hstep : step tm (q, tp)
                  = Some (t_next tr, tape_move (t_dir tr) (t_write tr) tp)).
  { unfold step. rewrite Hh, Etr. reflexivity. }
  rewrite Hstep.
  destruct (t_dir tr) eqn:Ed; cbn [tape_move].
  - (* DL: left is the arrival side, right the departed one *)
    pose proof (side_den_push (t_write tr) rb ri (t_right tp) Hr) as Hr1.
    destruct lb as [|x lb'].
    + (* walked off the left end *)
      destruct Hl as (ext & Hden & Hf). cbn [app] in Hf.
      set (rb1 := t_write tr :: rb) in *.
      destruct (pop_item L li) as [ps|] eqn:Ep; cycle 1.
      { destruct (3 * L <=? length rb1); exact I. }
      destruct (pop_den L li ps ext HL Ep Hden)
        as (wd & li' & ext' & HIn & Hne & Hden' & Hpt).
      destruct wd as [|y wd']; [congruence|].
      assert (Hhd : t_left tp 0 = y).
      { rewrite Hf, (Hpt 0). reflexivity. }
      assert (Htl : side_den wd' li' (tail_side (t_left tp))).
      { exists ext'. split; [exact Hden'|].
        intro i. unfold tail_side. rewrite Hf, (Hpt (S i)). reflexivity. }
      destruct (3 * L <=? length rb1) eqn:Ef.
      * eexists. split.
        { apply in_map_iff. exists (y :: wd', li').
          split; [reflexivity | exact HIn]. }
        repeat split; cbn [t_left t_right t_head snd fst hd tl].
        -- exact Hhd.
        -- exact Htl.
        -- apply push_side_den.
           rewrite firstn_skipn. exact Hr1.
      * eexists. split.
        { apply in_map_iff. exists (y :: wd', li').
          split; [reflexivity | exact HIn]. }
        repeat split; cbn [t_left t_right t_head snd fst hd tl].
        -- exact Hhd.
        -- exact Htl.
        -- exact Hr1.
    + (* still inside the buffer *)
      destruct Hl as (ext & Hden & Hf).
      eexists. split; [left; reflexivity|].
      repeat split; cbn [t_left t_right t_head snd fst].
      * rewrite Hf. reflexivity.
      * exists ext. split; [exact Hden|].
        intro i. unfold tail_side. rewrite Hf. reflexivity.
      * exact Hr1.
  - (* DR: mirror image *)
    pose proof (side_den_push (t_write tr) lb li (t_left tp) Hl) as Hl1.
    destruct rb as [|x rb'].
    + destruct Hr as (ext & Hden & Hf). cbn [app] in Hf.
      set (lb1 := t_write tr :: lb) in *.
      destruct (pop_item L ri) as [ps|] eqn:Ep; cycle 1.
      { destruct (3 * L <=? length lb1); exact I. }
      destruct (pop_den L ri ps ext HL Ep Hden)
        as (wd & ri' & ext' & HIn & Hne & Hden' & Hpt).
      destruct wd as [|y wd']; [congruence|].
      assert (Hhd : t_right tp 0 = y).
      { rewrite Hf, (Hpt 0). reflexivity. }
      assert (Htl : side_den wd' ri' (tail_side (t_right tp))).
      { exists ext'. split; [exact Hden'|].
        intro i. unfold tail_side. rewrite Hf, (Hpt (S i)). reflexivity. }
      destruct (3 * L <=? length lb1) eqn:Ef.
      * eexists. split.
        { apply in_map_iff. exists (y :: wd', ri').
          split; [reflexivity | exact HIn]. }
        repeat split; cbn [t_left t_right t_head snd fst hd tl].
        -- exact Hhd.
        -- apply push_side_den.
           rewrite firstn_skipn. exact Hl1.
        -- exact Htl.
      * eexists. split.
        { apply in_map_iff. exists (y :: wd', ri').
          split; [reflexivity | exact HIn]. }
        repeat split; cbn [t_left t_right t_head snd fst hd tl].
        -- exact Hhd.
        -- exact Hl1.
        -- exact Htl.
    + destruct Hr as (ext & Hden & Hf).
      eexists. split; [left; reflexivity|].
      repeat split; cbn [t_left t_right t_head snd fst].
      * rewrite Hf. reflexivity.
      * exact Hl1.
      * exists ext. split; [exact Hden|].
        intro i. unfold tail_side. rewrite Hf. reflexivity.
Qed.

(** ** Injective encoding (self-delimiting bit streams, PosEnc style) *)

Fixpoint nat_app (n : nat) (p : positive) : positive :=
  match n with
  | 0 => xO p
  | S m => xI (nat_app m p)
  end.

Lemma nat_app_inj : forall n m p q,
  nat_app n p = nat_app m q -> n = m /\ p = q.
Proof.
  induction n as [|n IH]; intros [|m] p q H; simpl in H;
    try discriminate.
  - split; congruence.
  - injection H as H. destruct (IH m p q H). split; congruence.
Qed.

Definition bool_app (b : bool) (p : positive) : positive :=
  if b then xI p else xO p.

Lemma bool_app_inj : forall a b p q,
  bool_app a p = bool_app b q -> a = b /\ p = q.
Proof.
  destruct a, b; simpl; intros p q H; split; congruence.
Qed.

Definition item_app (it : ritem) (p : positive) : positive :=
  syms_app (it_w it) (nat_app (it_c it) (bool_app (it_cap it) p)).

Lemma item_app_inj : forall a b p q,
  item_app a p = item_app b q -> a = b /\ p = q.
Proof.
  intros [wa ca capa] [wb cb capb] p q H.
  unfold item_app in H; simpl in H.
  apply syms_app_inj in H as [Hw H].
  apply nat_app_inj in H as [Hc H].
  apply bool_app_inj in H as [Hcap Hp].
  split; congruence.
Qed.

Fixpoint items_app (l : list ritem) (p : positive) : positive :=
  match l with
  | [] => xO p
  | it :: t => xI (item_app it (items_app t p))
  end.

Lemma items_app_inj : forall l1 l2 p q,
  items_app l1 p = items_app l2 q -> l1 = l2 /\ p = q.
Proof.
  induction l1 as [|a t1 IH]; intros [|b t2] p q H; simpl in H;
    try discriminate.
  - split; congruence.
  - injection H as H.
    apply item_app_inj in H as [Hab H].
    destruct (IH t2 p q H).
    split; congruence.
Qed.

Definition rconf_enc (a : rconf) : positive :=
  let '(q, (li, lb, h, rb, ri)) := a in
  st_app q (sym_app h (syms_app lb (syms_app rb
    (items_app li (items_app ri xH))))).

Lemma rconf_enc_inj : forall a b, rconf_enc a = rconf_enc b -> a = b.
Proof.
  intros [q1 [[[[li1 lb1] h1] rb1] ri1]] [q2 [[[[li2 lb2] h2] rb2] ri2]] H.
  unfold rconf_enc in H.
  apply st_app_inj in H as [Hq H].
  apply sym_app_inj in H as [Hh H].
  apply syms_app_inj in H as [Hlb H].
  apply syms_app_inj in H as [Hrb H].
  apply items_app_inj in H as [Hli H].
  apply items_app_inj in H as [Hri _].
  congruence.
Qed.

(** ** Seeding: blocking the computable configuration at step t *)

Definition padw (L : nat) (w : list Sym) : list Sym :=
  w ++ repeat S0 (L - length w).

Lemma padw_length : forall L w, length w <= L -> length (padw L w) = L.
Proof.
  intros L w H. unfold padw. rewrite app_length, repeat_length. lia.
Qed.

Lemma nthb_padw : forall L w i, nthb (padw L w) i = nthb w i.
Proof.
  intros L w i. unfold padw.
  destruct (le_lt_dec (length w) i) as [Hge | Hlt].
  - rewrite nthb_app_r by assumption.
    unfold nthb at 2. rewrite nth_overflow by assumption.
    exact (nthb_blank (L - length w) (i - length w)).
  - rewrite nthb_app_l by assumption. reflexivity.
Qed.

Fixpoint chunk_go (gas L : nat) (l : list Sym) : list (list Sym) :=
  match gas, l with
  | _, [] => []
  | 0, _ => []
  | S g, _ => padw L (firstn L l) :: chunk_go g L (skipn L l)
  end.

Definition chunk (L : nat) (l : list Sym) : list (list Sym) :=
  chunk_go (length l) L l.

Lemma nthb_skipn : forall (l : list Sym) n i,
  nthb (skipn n l) i = nthb l (n + i).
Proof.
  induction l as [|x l IH]; intros [|n] i; simpl; try reflexivity.
  - destruct i; reflexivity.
  - apply IH.
Qed.

Lemma nthb_firstn : forall (l : list Sym) n i,
  i < n -> nthb (firstn n l) i = nthb l i.
Proof.
  induction l as [|x l IH]; intros [|n] [|i] H; simpl;
    try reflexivity; try lia.
  apply IH. lia.
Qed.

Lemma chunk_go_nthb : forall gas L l,
  1 <= L -> length l <= gas ->
  forall i, nthb (concat (chunk_go gas L l)) i = nthb l i.
Proof.
  induction gas as [|g IH]; intros L l HL Hlen i.
  - destruct l; simpl; [destruct i; reflexivity | simpl in Hlen; lia].
  - destruct l as [|x l']; [destruct i; reflexivity|].
    cbn [chunk_go concat].
    destruct (le_lt_dec L i) as [Hge | Hlt].
    + rewrite nthb_app_r
        by (rewrite padw_length by (apply firstn_le_length); assumption).
      rewrite padw_length by apply firstn_le_length.
      rewrite IH; [| assumption |].
      * rewrite nthb_skipn. f_equal. lia.
      * rewrite skipn_length.
        destruct L as [|L']; [lia|].
        simpl in Hlen; simpl. lia.
    + rewrite nthb_app_l
        by (rewrite padw_length by (apply firstn_le_length); assumption).
      rewrite nthb_padw. apply nthb_firstn. assumption.
Qed.

(** Run-length encode a nearest-first block list, counts saturating
    at [T], blank blocks adjacent to the blank infinity absorbed. *)
Fixpoint rle (T : nat) (blocks : list (list Sym)) : list ritem :=
  match blocks with
  | [] => []
  | b :: rest =>
      match rle T rest with
      | [] => if word_blank b then [] else [mkItem b 1 (1 =? T)]
      | mkItem w0 c0 cap0 :: tl0 =>
          if syms_eqb w0 b
          then let c1 := Nat.min (S c0) T in
               mkItem w0 c1 (cap0 || (c1 =? T)) :: tl0
          else mkItem b 1 (1 =? T) :: mkItem w0 c0 cap0 :: tl0
      end
  end.

Lemma nthb_app_pointwise : forall (b x y : list Sym),
  (forall j, nthb x j = nthb y j) ->
  forall i, nthb (b ++ x) i = nthb (b ++ y) i.
Proof.
  intros b x y H i.
  destruct (le_lt_dec (length b) i) as [Hge | Hlt].
  - rewrite !nthb_app_r by assumption. apply H.
  - rewrite !nthb_app_l by assumption. reflexivity.
Qed.

Lemma rle_den : forall T blocks,
  exists ext, items_den (rle T blocks) ext /\
  forall i, nthb (concat blocks) i = nthb ext i.
Proof.
  intros T. induction blocks as [|b rest IH].
  - exists []. split; [constructor | intro i; reflexivity].
  - destruct IH as (ext0 & Hden0 & Hpt0).
    cbn [rle concat].
    destruct (rle T rest) as [| [w0 c0 cap0] tl0] eqn:Er.
    + inversion Hden0; subst ext0.
      destruct (word_blank b) eqn:Eb.
      * exists []. split; [constructor|].
        intro i.
        destruct (le_lt_dec (length b) i) as [Hge | Hlt].
        -- rewrite nthb_app_r by assumption. rewrite Hpt0.
           rewrite !nthb_nil. reflexivity.
        -- rewrite nthb_app_l by assumption.
           rewrite (word_blank_nthb b Eb).
           rewrite nthb_nil. reflexivity.
      * exists (wrep b 1 ++ []).
        split.
        -- apply (items_den_cons b 1 (1 =? T) 1 [] []);
             [destruct (1 =? T); [lia | reflexivity] | constructor].
        -- intro i. unfold wrep; cbn [concat repeat].
           rewrite !app_nil_r.
           destruct (le_lt_dec (length b) i) as [Hge | Hlt].
           ++ rewrite nthb_app_r by assumption. rewrite Hpt0, nthb_nil.
              unfold nthb; rewrite nth_overflow by assumption.
              reflexivity.
           ++ rewrite nthb_app_l by assumption. reflexivity.
    + inversion Hden0 as [| w c cap k rest' ext1 Hk Hrest]; subst.
      destruct (syms_eqb w0 b) eqn:Ew.
      * apply syms_eqb_spec in Ew. subst b.
        exists (wrep w0 (S k) ++ ext1).
        split.
        -- apply (items_den_cons w0 (Nat.min (S c0) T)
                    (cap0 || (Nat.min (S c0) T =? T)) (S k) tl0 ext1);
             [| exact Hrest].
           destruct cap0; cbn -[Nat.min].
           ++ pose proof (Nat.le_min_l (S c0) T). lia.
           ++ destruct (Nat.min (S c0) T =? T) eqn:Ec; cbn -[Nat.min].
              ** pose proof (Nat.le_min_l (S c0) T). lia.
              ** apply Nat.eqb_neq in Ec.
                 destruct (Nat.min_dec (S c0) T) as [Em | Em]; lia.
        -- intro i. rewrite wrep_S, <- app_assoc.
           apply nthb_app_pointwise. exact Hpt0.
      * exists (wrep b 1 ++ (wrep w0 k ++ ext1)).
        split.
        -- apply (items_den_cons b 1 (1 =? T) 1
                    (mkItem w0 c0 cap0 :: tl0) (wrep w0 k ++ ext1));
             [destruct (1 =? T); [lia | reflexivity] |].
           apply (items_den_cons w0 c0 cap0 k tl0 ext1);
             [exact Hk | exact Hrest].
        -- intro i. unfold wrep at 1; cbn [concat repeat].
           rewrite app_nil_r.
           apply nthb_app_pointwise. exact Hpt0.
Qed.

(** The seed context and its covering. *)
Definition rw_seed (L T : nat) (cc : cconf) : rconf :=
  let '(q, (l, h, r)) := cc in
  (q, (rle T (chunk L l), [], h,
       padw (L - 1) (firstn (L - 1) r),
       rle T (chunk L (skipn (L - 1) r)))).

Lemma rw_seed_covers : forall L T cc,
  1 <= L ->
  rw_covers (rw_seed L T cc) (lift cc).
Proof.
  intros L T [q [[l h] r]] HL.
  cbn [rw_seed rw_covers lift lift_tape fst snd t_left t_right t_head].
  repeat split.
  - (* left side *)
    destruct (rle_den T (chunk L l)) as (ext & Hden & Hpt).
    exists ext. split; [exact Hden|].
    intro i. cbn [app].
    rewrite <- Hpt.
    unfold chunk. rewrite chunk_go_nthb by (assumption || lia).
    reflexivity.
  - (* right side *)
    destruct (rle_den T (chunk L (skipn (L - 1) r)))
      as (ext & Hden & Hpt).
    exists ext. split; [exact Hden|].
    intro i.
    destruct (le_lt_dec (L - 1) i) as [Hge | Hlt].
    + rewrite nthb_app_r
        by (rewrite padw_length by apply firstn_le_length; assumption).
      rewrite padw_length by apply firstn_le_length.
      rewrite <- Hpt.
      unfold chunk. rewrite chunk_go_nthb by (assumption || lia).
      rewrite nthb_skipn. unfold lift_side. f_equal. lia.
    + rewrite nthb_app_l
        by (rewrite padw_length by apply firstn_le_length; assumption).
      rewrite nthb_padw, nthb_firstn by assumption.
      reflexivity.
Qed.

(** ** Well-formed items

    The measure deltas below read "some nonblank strictly beyond"
    bits off the item lists; those bits are exact only when every
    item denotes at least one copy of a nonempty word.  All
    checker-constructed configurations satisfy this ([rw_seed_wf],
    [rw_succs_wf]), so the engine's covers relation is the
    conjunction [rw_covers'] below. *)

Definition item_wf (it : ritem) : Prop :=
  1 <= it_c it /\ (it_cap it = true -> 2 <= it_c it) /\ it_w it <> [].

Definition rw_wf (a : rconf) : Prop :=
  let '(_, (li, _, _, _, ri)) := a in
  Forall item_wf li /\ Forall item_wf ri.

Definition rw_covers' (a : rconf) (c : ExecState) : Prop :=
  rw_covers a c /\ rw_wf a.

Lemma newitem_wf : forall T w,
  2 <= T -> w <> [] -> item_wf (mkItem w 1 (1 =? T)).
Proof.
  intros T w HT Hw.
  split; [simpl; lia|].
  split; [| exact Hw].
  cbn [it_cap it_c].
  destruct (1 =? T) eqn:E1; [apply Nat.eqb_eq in E1; lia|].
  intro Hc; discriminate Hc.
Qed.

Lemma merge_wf : forall T c0 cap0,
  2 <= T -> 1 <= c0 -> (cap0 = true -> 2 <= c0) ->
  1 <= Nat.min (S c0) T /\
  (cap0 || (Nat.min (S c0) T =? T) = true -> 2 <= Nat.min (S c0) T).
Proof.
  intros T c0 cap0 HT Hc Hcap.
  split.
  - apply Nat.min_glb; lia.
  - intro Hor. apply orb_prop in Hor as [Hc0 | He].
    + specialize (Hcap Hc0). apply Nat.min_glb; lia.
    + apply Nat.eqb_eq in He. lia.
Qed.

Lemma push_item_wf : forall T w items,
  2 <= T -> w <> [] -> Forall item_wf items ->
  Forall item_wf (push_item T w items).
Proof.
  intros T w items HT Hw Hwf.
  unfold push_item.
  destruct items as [| [w0 c0 cap0] rest].
  - destruct (word_blank w); constructor;
      [apply newitem_wf; assumption | constructor].
  - inversion Hwf as [| ? ? Hit Hrest]; subst.
    destruct Hit as (Hc & Hcap & Hw0); simpl in Hc, Hcap, Hw0.
    destruct (syms_eqb w0 w).
    + constructor; [| exact Hrest].
      destruct (merge_wf T c0 cap0 HT Hc Hcap) as [H1 H2].
      split; [exact H1 | split; [exact H2 | exact Hw0]].
    + constructor; [apply newitem_wf; assumption |].
      constructor; [| exact Hrest].
      split; [exact Hc | split; [exact Hcap | exact Hw0]].
Qed.

Lemma pop_item_wf : forall L items ps,
  pop_item L items = Some ps ->
  Forall item_wf items ->
  forall wd items', In (wd, items') ps -> Forall item_wf items'.
Proof.
  intros L items ps Hpop Hwf wd items' HIn.
  destruct items as [| [w0 c0 cap0] rest].
  - simpl in Hpop. injection Hpop as <-.
    destruct HIn as [E | []]. injection E as <- <-. constructor.
  - simpl in Hpop.
    destruct w0 as [|y w0']; [discriminate|].
    destruct c0 as [|c0']; [discriminate|].
    injection Hpop as <-.
    inversion Hwf as [| ? ? Hit Hrest]; subst.
    assert (Hdec : Forall item_wf
              (match c0' with
               | 0 => rest
               | S _ => mkItem (y :: w0') c0' false :: rest
               end)).
    { destruct c0' as [|c0'']; [exact Hrest|].
      constructor; [| exact Hrest].
      split; [simpl; lia |].
      split; [simpl; intro Hb; discriminate | discriminate]. }
    destruct cap0.
    + destruct HIn as [E | [E | []]]; injection E as <- <-.
      * constructor; [exact Hit | exact Hrest].
      * exact Hdec.
    + destruct HIn as [E | []]. injection E as <- <-. exact Hdec.
Qed.

Lemma rw_succs_wf : forall tm L T a sl a',
  1 <= L -> 2 <= T ->
  rw_wf a ->
  rw_succs tm L T a = Some sl ->
  In a' sl ->
  rw_wf a'.
Proof.
  intros tm L T [q [[[[li lb] h] rb] ri]] sl a' HL HT [Hli Hri] Hs HIn.
  unfold rw_succs in Hs.
  destruct (tm q h) as [tr|]; [|discriminate].
  destruct (t_dir tr).
  - (* DL *)
    destruct lb as [|x lb'].
    + destruct (3 * L <=? length (t_write tr :: rb)) eqn:Ef.
      * destruct (pop_item L li) as [ps|] eqn:Ep; [|discriminate].
        injection Hs as <-.
        apply in_map_iff in HIn as ((wd & li2) & E & HInp).
        subst a'. simpl.
        split.
        -- exact (pop_item_wf L li ps Ep Hli wd li2 HInp).
        -- apply push_item_wf; [exact HT | | exact Hri].
           apply Nat.leb_le in Ef.
           intro Hcontra.
           pose proof (f_equal (@length Sym) Hcontra) as Hlen.
           rewrite skipn_length in Hlen.
           destruct L as [|L']; [lia | simpl in Ef, Hlen; lia].
      * destruct (pop_item L li) as [ps|] eqn:Ep; [|discriminate].
        injection Hs as <-.
        apply in_map_iff in HIn as ((wd & li2) & E & HInp).
        subst a'. simpl.
        split; [exact (pop_item_wf L li ps Ep Hli wd li2 HInp) | exact Hri].
    + injection Hs as <-.
      destruct HIn as [E | []]. subst a'. simpl.
      split; [exact Hli | exact Hri].
  - (* DR *)
    destruct rb as [|x rb'].
    + destruct (3 * L <=? length (t_write tr :: lb)) eqn:Ef.
      * destruct (pop_item L ri) as [ps|] eqn:Ep; [|discriminate].
        injection Hs as <-.
        apply in_map_iff in HIn as ((wd & ri2) & E & HInp).
        subst a'. simpl.
        split.
        -- apply push_item_wf; [exact HT | | exact Hli].
           apply Nat.leb_le in Ef.
           intro Hcontra.
           pose proof (f_equal (@length Sym) Hcontra) as Hlen.
           rewrite skipn_length in Hlen.
           destruct L as [|L']; [lia | simpl in Ef, Hlen; lia].
        -- exact (pop_item_wf L ri ps Ep Hri wd ri2 HInp).
      * destruct (pop_item L ri) as [ps|] eqn:Ep; [|discriminate].
        injection Hs as <-.
        apply in_map_iff in HIn as ((wd & ri2) & E & HInp).
        subst a'. simpl.
        split; [exact Hli | exact (pop_item_wf L ri ps Ep Hri wd ri2 HInp)].
    + injection Hs as <-.
      destruct HIn as [E | []]. subst a'. simpl.
      split; [exact Hli | exact Hri].
Qed.

Lemma rw_succs_sound' : forall tm L T a c,
  1 <= L -> 2 <= T ->
  rw_covers' a c ->
  match rw_succs tm L T a, step tm c with
  | Some l, Some c' => exists a', In a' l /\ rw_covers' a' c'
  | Some _, None => False
  | None, _ => True
  end.
Proof.
  intros tm L T a c HL HT [Hcov Hwf].
  pose proof (rw_succs_sound tm L T a c HL Hcov) as H.
  destruct (rw_succs tm L T a) as [sl|] eqn:Hs; [| exact I].
  destruct (step tm c) as [c'|]; [| exact H].
  destruct H as (a' & HIn & Hcov').
  exists a'. split; [exact HIn|].
  split; [exact Hcov' | exact (rw_succs_wf tm L T a sl a' HL HT Hwf Hs HIn)].
Qed.

(** ** Measures: values on the computable configuration, deltas on
    the node (docs/neverqh.md "RepWL ranking liveness") *)

Fixpoint countnb (l : list Sym) : nat :=
  match l with
  | [] => 0
  | S1 :: t => S (countnb t)
  | S0 :: t => countnb t
  end.

(** Interior blanks: blank cells with a nonblank strictly farther
    out on the same side. *)
Fixpoint ibc (l : list Sym) : nat :=
  match l with
  | [] => 0
  | x :: t =>
      (if sym_eqb x S0 && negb (word_blank t) then 1 else 0) + ibc t
  end.

Definition zc (s : Sym) : nat := match s with S1 => 1 | S0 => 0 end.
Definition zcz (s : Sym) : Z := match s with S1 => 1%Z | S0 => 0%Z end.
Definition zi (b : bool) : Z := if b then 1%Z else 0%Z.

Lemma countnb_cons : forall x t, countnb (x :: t) = zc x + countnb t.
Proof. destruct x; reflexivity. Qed.

Lemma countnb_hd : forall r, countnb r = zc (chd r) + countnb (ctl r).
Proof. destruct r as [|x t]; [reflexivity | destruct x; reflexivity]. Qed.

Lemma ibc_cons : forall x t,
  ibc (x :: t) = (if sym_eqb x S0 && negb (word_blank t) then 1 else 0)
                 + ibc t.
Proof. reflexivity. Qed.

Lemma ibc_hd : forall r,
  ibc r = (if sym_eqb (chd r) S0 && negb (word_blank (ctl r))
           then 1 else 0) + ibc (ctl r).
Proof. destruct r as [|x t]; reflexivity. Qed.

Lemma chd_nthb : forall l, chd l = nthb l 0.
Proof. destruct l; reflexivity. Qed.

Lemma ctl_nthb : forall l i, nthb (ctl l) i = nthb l (S i).
Proof. destruct l as [|x t]; intros [|i]; reflexivity. Qed.

(** *** Blankness correspondences *)

Lemma word_blank_app : forall a b,
  word_blank (a ++ b) = word_blank a && word_blank b.
Proof. intros. unfold word_blank. apply forallb_app. Qed.

Lemma wrep_blank : forall w k,
  word_blank w = true -> word_blank (wrep w k) = true.
Proof.
  intros w k Hw. induction k as [|k IH]; [reflexivity|].
  rewrite wrep_S, word_blank_app, Hw, IH. reflexivity.
Qed.

Lemma word_nonblank_ex : forall w,
  word_blank w = false -> exists j, j < length w /\ nthb w j = S1.
Proof.
  induction w as [|x t IH]; intro H; [discriminate|].
  unfold word_blank in H; simpl in H.
  apply andb_false_iff in H as [Hx | Ht].
  - exists 0. split; [simpl; lia|].
    destruct x; [discriminate | reflexivity].
  - destruct (IH Ht) as (j & Hj & Hs).
    exists (S j). split; [simpl; lia | exact Hs].
Qed.

Lemma all_blank_word : forall l,
  (forall i, nthb l i = S0) -> word_blank l = true.
Proof.
  induction l as [|x t IH]; intro H; [reflexivity|].
  unfold word_blank; simpl.
  apply andb_true_intro. split.
  - specialize (H 0). unfold nthb in H; simpl in H.
    rewrite H. reflexivity.
  - apply IH. intro i. exact (H (S i)).
Qed.

Definition items_nb (items : list ritem) : bool :=
  existsb (fun it => negb (word_blank (it_w it))) items.

Lemma items_nb_false : forall items ext,
  items_nb items = false -> items_den items ext ->
  forall i, nthb ext i = S0.
Proof.
  intros items ext Hnb Hden.
  induction Hden as [| w c cap k rest ext0 Hk Hden IH]; intro i.
  - apply nthb_nil.
  - unfold items_nb in Hnb; simpl in Hnb.
    apply orb_false_iff in Hnb as [Hw Hrest].
    apply negb_false_iff in Hw. simpl in Hw.
    destruct (le_lt_dec (length (wrep w k)) i) as [Hge | Hlt].
    + rewrite nthb_app_r by assumption. apply IH. exact Hrest.
    + rewrite nthb_app_l by assumption.
      apply word_blank_nthb. apply wrep_blank. exact Hw.
Qed.

Lemma items_nb_true : forall items ext,
  items_nb items = true -> Forall item_wf items -> items_den items ext ->
  exists i, nthb ext i = S1.
Proof.
  intros items ext Hnb Hwf Hden.
  induction Hden as [| w c cap k rest ext0 Hk Hden IH].
  - discriminate.
  - inversion Hwf as [| ? ? Hit Hrest]; subst.
    destruct Hit as (Hc & _ & _); simpl in Hc.
    unfold items_nb in Hnb; simpl in Hnb.
    apply orb_true_iff in Hnb as [Hw | Hr].
    + apply negb_true_iff in Hw. simpl in Hw.
      destruct (word_nonblank_ex w Hw) as (j & Hj & Hs).
      assert (Hk1 : 1 <= k) by (destruct cap; lia).
      destruct k as [|k']; [lia|].
      exists j.
      rewrite wrep_S, <- app_assoc.
      rewrite nthb_app_l by assumption.
      exact Hs.
    + destruct (IH Hr Hrest) as (i & Hs).
      exists (length (wrep w k) + i).
      rewrite nthb_app_r by lia.
      replace (length (wrep w k) + i - length (wrep w k)) with i by lia.
      exact Hs.
Qed.

(** A covered concrete side list is blank iff both the buffer and
    the item words are. *)
Lemma side_blank : forall b items ext (cl : list Sym),
  Forall item_wf items -> items_den items ext ->
  (forall i, nthb cl i = nthb (b ++ ext) i) ->
  word_blank cl = word_blank b && negb (items_nb items).
Proof.
  intros b items ext cl Hwf Hden Hpt.
  destruct (word_blank b) eqn:Hb; simpl.
  - destruct (items_nb items) eqn:Hnb; simpl.
    + destruct (items_nb_true items ext Hnb Hwf Hden) as (i & Hs).
      destruct (word_blank cl) eqn:Hcl; [| reflexivity].
      pose proof (word_blank_nthb cl Hcl (length b + i)) as H0.
      rewrite Hpt, nthb_app_r in H0 by lia.
      replace (length b + i - length b) with i in H0 by lia.
      congruence.
    + apply all_blank_word. intro i.
      rewrite Hpt.
      destruct (le_lt_dec (length b) i) as [Hge | Hlt].
      * rewrite nthb_app_r by assumption.
        apply (items_nb_false items ext Hnb Hden).
      * rewrite nthb_app_l by assumption.
        apply word_blank_nthb. exact Hb.
  - destruct (word_nonblank_ex b Hb) as (j & Hj & Hs).
    destruct (word_blank cl) eqn:Hcl; [| reflexivity].
    pose proof (word_blank_nthb cl Hcl j) as H0.
    rewrite Hpt, nthb_app_l in H0 by assumption.
    congruence.
Qed.

(** *** The arrival cell and the two witness bits, read off a side *)

Definition arr_s2 (b : list Sym) (items : list ritem) : Sym :=
  match b with
  | x :: _ => x
  | [] => match items with
          | it :: _ => hd S0 (it_w it)
          | [] => S0
          end
  end.

Definition arr_nbb (b : list Sym) (items : list ritem) : bool :=
  match b with
  | _ :: b' => negb (word_blank b') || items_nb items
  | [] => match items with
          | it :: rest =>
              negb (word_blank (tl (it_w it)))
              || ((2 <=? it_c it) || it_cap it)
                 && negb (word_blank (it_w it))
              || items_nb rest
          | [] => false
          end
  end.

Definition dep_nbb (b : list Sym) (items : list ritem) : bool :=
  negb (word_blank b) || items_nb items.

Lemma wrep_blank_pos : forall w k,
  1 <= k -> word_blank (wrep w k) = word_blank w.
Proof.
  intros w k Hk. destruct k as [|k]; [lia|].
  clear Hk. induction k as [|k IH].
  - unfold wrep; simpl. rewrite app_nil_r. reflexivity.
  - rewrite wrep_S, word_blank_app, IH.
    destruct (word_blank w); reflexivity.
Qed.

Lemma dep_nbb_eq : forall b items ext (cl : list Sym),
  Forall item_wf items -> items_den items ext ->
  (forall i, nthb cl i = nthb (b ++ ext) i) ->
  dep_nbb b items = negb (word_blank cl).
Proof.
  intros b items ext cl Hwf Hden Hpt.
  unfold dep_nbb.
  rewrite (side_blank b items ext cl Hwf Hden Hpt).
  destruct (word_blank b), (items_nb items); reflexivity.
Qed.

Lemma arr_s2_eq : forall b items ext (cl : list Sym),
  Forall item_wf items -> items_den items ext ->
  (forall i, nthb cl i = nthb (b ++ ext) i) ->
  arr_s2 b items = chd cl.
Proof.
  intros b items ext cl Hwf Hden Hpt.
  rewrite chd_nthb, Hpt.
  destruct b as [|x b']; [| reflexivity].
  cbn [app].
  destruct items as [| [w c cap] rest].
  - inversion Hden; subst. reflexivity.
  - inversion Hden as [| ? ? ? k ? ext0 Hk Hrest]; subst.
    inversion Hwf as [| ? ? Hit _]; subst.
    destruct Hit as (Hc & _ & Hw); simpl in Hc, Hw.
    assert (Hk1 : 1 <= k) by (destruct cap; lia).
    destruct k as [|k']; [lia|].
    rewrite wrep_S, <- app_assoc.
    destruct w as [|y w']; [congruence | reflexivity].
Qed.

Lemma arr_nbb_eq : forall b items ext (cl : list Sym),
  Forall item_wf items -> items_den items ext ->
  (forall i, nthb cl i = nthb (b ++ ext) i) ->
  arr_nbb b items = negb (word_blank (ctl cl)).
Proof.
  intros b items ext cl Hwf Hden Hpt.
  assert (Hpt' : forall i, nthb (ctl cl) i = nthb cl (S i))
    by (intro i; apply ctl_nthb).
  destruct b as [|x b'].
  - cbn [app] in Hpt.
    destruct items as [| [w c cap] rest].
    + inversion Hden; subst.
      cbn [arr_nbb].
      assert (Hbl : word_blank (ctl cl) = true).
      { apply all_blank_word. intro i.
        rewrite Hpt', Hpt. apply nthb_nil. }
      rewrite Hbl. reflexivity.
    + inversion Hden as [| ? ? ? k ? ext0 Hk Hrest]; subst.
      inversion Hwf as [| ? ? Hit Hwfr]; subst.
      destruct Hit as (Hc & Hcap & Hw); simpl in Hc, Hcap, Hw.
      assert (Hk1 : 1 <= k) by (destruct cap; lia).
      destruct k as [|k']; [lia|].
      destruct w as [|y w']; [congruence|].
      cbn [arr_nbb it_w it_c it_cap tl].
      assert (Hct : forall i,
        nthb (ctl cl) i = nthb ((w' ++ wrep (y :: w') k') ++ ext0) i).
      { intro i. rewrite Hpt', Hpt.
        rewrite wrep_S, <- app_assoc.
        cbn [app]. rewrite <- app_assoc. reflexivity. }
      rewrite (side_blank (w' ++ wrep (y :: w') k') rest ext0 (ctl cl)
                 Hwfr Hrest Hct).
      rewrite word_blank_app.
      destruct ((2 <=? c) || cap) eqn:Hbit.
      * assert (Hk2 : 1 <= k').
        { apply orb_prop in Hbit as [H2 | Hcp].
          - apply Nat.leb_le in H2. destruct cap; lia.
          - specialize (Hcap Hcp). subst cap. lia. }
        rewrite (wrep_blank_pos (y :: w') k' Hk2).
        destruct (word_blank w'), (word_blank (y :: w')),
                 (items_nb rest); reflexivity.
      * assert (Hk0 : k' = 0).
        { apply orb_false_iff in Hbit as [H2 Hcp].
          apply Nat.leb_gt in H2. subst cap. lia. }
        subst k'.
        rewrite wrep_0.
        destruct (word_blank w'), (items_nb rest); reflexivity.
  - cbn [arr_nbb].
    assert (Hct : forall i, nthb (ctl cl) i = nthb (b' ++ ext) i).
    { intro i. rewrite Hpt', Hpt. reflexivity. }
    rewrite (side_blank b' items ext (ctl cl) Hwf Hden Hct).
    destruct (word_blank b'), (items_nb items); reflexivity.
Qed.
