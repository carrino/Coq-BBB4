(** * ClosureIdx: the closure engine's checks on INTERNED node indices.

    Same soundness argument as [Closure.v], same closure search, but
    the verified half stops paying [a_enc] on every membership test.

    Measured motivation (docs/CENSUS_RUNTIME.md, 2026-08-05): one
    n-gram ladder catch spends ~37% of its time in
    [rank_ok]+[compute_ranks] and only ~4% exploring, because
    [closure_check_neverqh] recomputes [succs] and re-encodes every
    node once per state in [all_St] -- up to eight traversals of the
    successor relation per catch.  Memoising the edges under [cconf]
    keys does not help (measured 1.14x: encoding the key costs what
    recomputing [succs] costs).  What does help is giving each context
    a small INDEX:

    - one verified pass ([edges_of]) computes [succs] once per node,
      resolves every successor to its index, and fails if any
      successor is outside the pool -- so its success already IS
      closedness ([edges_closed]);
    - each edge carries its target's index AND state, so the rank
      checks need no lookup table and no faithfulness side-condition;
    - all four states' rank checks then run off that one edge list,
      keyed by short indices instead of context encodings.

    Everything search-like stays UNTRUSTED exactly as before: the
    closure list comes from [Closure.close], and the ranks are a
    PARAMETER here ([rnk]) rather than something this file computes,
    so a wrong rank assignment can only make the check fail.

    Soundness is not re-argued: [edges_of] success is converted to
    [closed_b] and [rank_ok] of [Closure.v], and the existing
    [closure_invariant] / [rank_find] lemmas finish the proof. *)

From Coq Require Import Arith Lia Bool List ZArith PArith.
From Coq Require Import FSets.FMapPositive.
From BBB4 Require Import BBB4_Statement CTape PosEnc Records Closure.
From BBB4.Checkers Require Import Cycle.
Import ListNotations.

(** ** The forward membership direction

    [PosEnc] proves only [pset_of_mem] (a trie hit is a list member),
    the direction the old checker needed.  Interning needs the
    converse, and it needs no injectivity. *)

Section PsetIntro.
  Variable A : Type.
  Variable enc : A -> positive.

  Lemma pset_fold_mono : forall l s k,
    PositiveSet.mem k s = true ->
    PositiveSet.mem k (fold_left (fun s a => pset_add A enc a s) l s) = true.
  Proof.
    induction l as [|x t IH]; simpl; intros s k H; [exact H|].
    apply IH. unfold pset_add.
    apply PositiveSet.mem_spec, PositiveSet.add_spec.
    right. apply PositiveSet.mem_spec, H.
  Qed.

  Lemma pset_of_intro_aux : forall l a s,
    In a l ->
    PositiveSet.mem (enc a) (fold_left (fun s x => pset_add A enc x s) l s)
    = true.
  Proof.
    induction l as [|x t IH]; simpl; intros a s Hin; [contradiction|].
    destruct Hin as [-> | Hin].
    - apply pset_fold_mono. unfold pset_add.
      apply PositiveSet.mem_spec, PositiveSet.add_spec. left. reflexivity.
    - apply IH. exact Hin.
  Qed.

  Lemma pset_of_intro : forall a l,
    In a l -> pset_mem A enc a (pset_of A enc l) = true.
  Proof. intros a l Hin. apply pset_of_intro_aux. exact Hin. Qed.
End PsetIntro.

(** ** Option-returning map *)

Fixpoint map_opt {B C : Type} (f : B -> option C) (l : list B)
  : option (list C) :=
  match l with
  | [] => Some []
  | x :: t =>
      match f x, map_opt f t with
      | Some y, Some r => Some (y :: r)
      | _, _ => None
      end
  end.

Lemma map_opt_in : forall (B C : Type) (f : B -> option C) l r x,
  map_opt f l = Some r -> In x l -> exists y, f x = Some y /\ In y r.
Proof.
  induction l as [|b t IH]; simpl; intros r x Hm Hin; [contradiction|].
  destruct (f b) as [y|] eqn:Ef; [|discriminate].
  destruct (map_opt f t) as [rt|] eqn:Et; [|discriminate].
  injection Hm as <-.
  destruct Hin as [-> | Hin].
  - exists y. split; [exact Ef | left; reflexivity].
  - destruct (IH rt x eq_refl Hin) as (z & Hz & Hinz).
    exists z. split; [exact Hz | right; exact Hinz].
Qed.

Section IdxEngine.

  Variable tm : TM.
  Variable A : Type.
  Variable a_enc : A -> positive.
  Variable a_state : A -> St.
  Variable succs : A -> option (list A).

  (** ** Interning: context encoding -> small index *)

  Definition imap : Type := PositiveMap.tree positive.

  Fixpoint build_imap_aux (l : list A) (i : positive) (m : imap) : imap :=
    match l with
    | [] => m
    | a :: t => build_imap_aux t (Pos.succ i) (PositiveMap.add (a_enc a) i m)
    end.

  Definition build_imap (l : list A) : imap :=
    build_imap_aux l 1%positive (PositiveMap.empty _).

  Definition idx_of (m : imap) (a : A) : option positive :=
    PositiveMap.find (a_enc a) m.

  (** Every key of the interning map comes from the interned list --
      the only fact soundness needs from the untrusted numbering. *)
  Lemma build_imap_aux_keys : forall l i m k v,
    PositiveMap.find k (build_imap_aux l i m) = Some v ->
    (exists a, In a l /\ a_enc a = k) \/ PositiveMap.find k m = Some v.
  Proof.
    induction l as [|x t IH]; simpl; intros i m k v H; [right; exact H|].
    destruct (IH _ _ _ _ H) as [(a & Hin & Ha) | H'].
    - left. exists a. split; [right; exact Hin | exact Ha].
    - destruct (Pos.eq_dec k (a_enc x)) as [-> | Hne].
      + left. exists x. split; [left; reflexivity | reflexivity].
      + right. rewrite PositiveMap.gso in H' by (intro C; apply Hne; congruence).
        exact H'.
  Qed.

  Hypothesis a_enc_inj : forall x y, a_enc x = a_enc y -> x = y.

  Lemma idx_of_In : forall pool a i,
    idx_of (build_imap pool) a = Some i -> In a pool.
  Proof.
    intros pool a i H. unfold idx_of, build_imap in H.
    destruct (build_imap_aux_keys pool 1%positive (PositiveMap.empty _)
                (a_enc a) i H) as [(b & Hin & Hb) | Hemp].
    - rewrite <- (a_enc_inj b a Hb). exact Hin.
    - rewrite PositiveMap.gempty in Hemp. discriminate.
  Qed.

  (** ** The one verified pass

      For every pool node: compute [succs] ONCE, resolve each
      successor to (index, state).  Failure to resolve = the successor
      escaped the pool = not closed. *)

  Definition erow : Type := (positive * St * list (positive * St))%type.

  Definition tag (m : imap) (a' : A) : option (positive * St) :=
    match idx_of m a' with
    | Some j => Some (j, a_state a')
    | None => None
    end.

  Definition edge_row (m : imap) (a : A) : option erow :=
    match idx_of m a with
    | None => None
    | Some i =>
        match succs a with
        | None => None
        | Some l =>
            match map_opt (tag m) l with
            | None => None
            | Some js => Some (i, a_state a, js)
            end
        end
    end.

  Definition edges_of (m : imap) (pool : list A) : option (list erow) :=
    map_opt (edge_row m) pool.

  (** Success of the pass is exactly closedness. *)
  Lemma edges_closed : forall pool rows,
    edges_of (build_imap pool) pool = Some rows ->
    closed_b A a_enc succs pool = true.
  Proof.
    intros pool rows H.
    unfold closed_b. apply forallb_forall. intros a Hin.
    destruct (map_opt_in A erow (edge_row (build_imap pool)) pool rows a H Hin)
      as (row & Hrow & _).
    unfold edge_row in Hrow.
    destruct (idx_of (build_imap pool) a) as [i|] eqn:Ei; [|discriminate].
    destruct (succs a) as [l|] eqn:Es; [|discriminate].
    destruct (map_opt (tag (build_imap pool)) l) as [js|] eqn:Ejs;
      [|discriminate].
    unfold node_ok. rewrite Es.
    apply forallb_forall. intros a' Hin'.
    destruct (map_opt_in A (positive * St) (tag (build_imap pool)) l js a'
                Ejs Hin') as (p & Hp & _).
    unfold tag in Hp.
    destruct (idx_of (build_imap pool) a') as [j|] eqn:Ej; [|discriminate].
    unfold apool. apply pset_of_intro. exact (idx_of_In pool a' j Ej).
  Qed.

  (** ** Rank checking off the edge list

      [rnk] is UNTRUSTED input: any assignment of naturals to indices.
      The check is per row, and every edge already carries its
      target's index and state, so nothing is looked up. *)

  Definition rmap : Type := PositiveMap.tree nat.

  Definition rank_at (r : rmap) (i : positive) : nat :=
    match PositiveMap.find i r with Some n => n | None => 0 end.

  Definition row_ok (q : St) (r : rmap) (row : erow) : bool :=
    let '(i, s, js) := row in
    if st_eqb s q then true
    else forallb (fun p =>
           implb (negb (st_eqb (snd p) q))
                 (rank_at r (fst p) <? rank_at r i)) js.

  Definition irank_ok (rows : list erow) (q : St) (r : rmap) : bool :=
    forallb (row_ok q r) rows.

  Definition row_state (row : erow) : St := snd (fst row).

  (** The rank function the pool sees: index, then rank. *)
  Definition rnk_of (m : imap) (r : rmap) (a : A) : nat :=
    match idx_of m a with
    | Some i => rank_at r i
    | None => 0
    end.

  (** [irank_ok] on the rows is [rank_ok] on the pool. *)
  Lemma irank_ok_rank_ok : forall pool rows q r,
    edges_of (build_imap pool) pool = Some rows ->
    irank_ok rows q r = true ->
    rank_ok A a_state succs pool q (rnk_of (build_imap pool) r) = true.
  Proof.
    intros pool rows q r Hrows Hok.
    unfold rank_ok. apply forallb_forall. intros a Hin.
    destruct (map_opt_in A erow (edge_row (build_imap pool)) pool rows a
                Hrows Hin) as (row & Hrow & Hinrow).
    assert (Hro : row_ok q r row = true).
    { unfold irank_ok in Hok. rewrite forallb_forall in Hok. auto. }
    unfold edge_row in Hrow.
    destruct (idx_of (build_imap pool) a) as [i|] eqn:Ei; [|discriminate].
    destruct (succs a) as [l|] eqn:Es; [|discriminate].
    destruct (map_opt (tag (build_imap pool)) l) as [js|] eqn:Ejs;
      [|discriminate].
    injection Hrow as <-.
    simpl in Hro.
    destruct (st_eqb (a_state a) q) eqn:Eq; [reflexivity|].
    apply forallb_forall. intros a' Hin'.
    destruct (map_opt_in A (positive * St) (tag (build_imap pool)) l js a'
                Ejs Hin') as (p & Hp & Hinp).
    assert (Hp' : p = (match idx_of (build_imap pool) a' with
                       | Some j => j | None => 1%positive end, a_state a')).
    { unfold tag in Hp.
      destruct (idx_of (build_imap pool) a') as [j|]; [|discriminate].
      injection Hp as <-. reflexivity. }
    rewrite forallb_forall in Hro. specialize (Hro p Hinp).
    unfold edge_ok, rnk_of. rewrite Ei.
    subst p. simpl in Hro.
    destruct (idx_of (build_imap pool) a') as [j|] eqn:Ej.
    - exact Hro.
    - (* impossible: the pass resolved every successor *)
      unfold tag in Hp. rewrite Ej in Hp. discriminate.
  Qed.

  (** ** Untrusted rank search on the edge list

      [Closure.compute_ranks]'s reverse-topological peeling, but over
      rows: a node is ready when all its q-avoiding successors are
      ranked, and every edge already names its target's index and
      state, so a pass touches no context and encodes nothing.
      Carries no soundness -- a bad assignment only fails [irank_ok]. *)

  Definition row_nonq (q : St) (row : erow) : list positive :=
    map fst (filter (fun p => negb (st_eqb (snd p) q)) (snd row)).

  Definition rranked (r : rmap) (i : positive) : bool :=
    match PositiveMap.find i r with Some _ => true | None => false end.

  Definition rpeel_pass (q : St) (st : rmap * list erow * bool)
      (rem : list erow) : rmap * list erow * bool :=
    fold_left (fun '(r, stuck, prog) row =>
      let sl := row_nonq q row in
      if forallb (rranked r) sl
      then (PositiveMap.add (fst (fst row))
              (match sl with
               | [] => 0
               | _ => S (fold_left Nat.max (map (rank_at r) sl) 0)
               end) r, stuck, true)
      else (r, row :: stuck, prog)) rem st.

  Fixpoint rpeel_iter (k : nat) (q : St) (r : rmap) (rem : list erow)
    : rmap :=
    match k, rem with
    | 0, _ | _, [] => r
    | S k', _ =>
        let '(r', stuck, prog) := rpeel_pass q (r, [], false) rem in
        if prog then rpeel_iter k' q r' stuck else r'
    end.

  Definition idx_ranks (rows : list erow) (q : St) : rmap :=
    rpeel_iter (S (length rows)) q (PositiveMap.empty nat)
      (filter (fun row => negb (st_eqb (row_state row) q)) rows).

  (** ** The checker

      Shape-for-shape [closure_check_neverqh], with the three
      re-traversals ([closed_b], the [apool] rebuild inside [mem], and
      the per-state [succs] recomputation) replaced by the single
      [edges_of] pass.  [mkr] is the untrusted rank search. *)

  Definition idx_check_neverqh (t fuel : nat) (a0 : A)
      (mkr : list erow -> St -> rmap) : bool :=
    match csteps tm t c0 with
    | Some ct =>
        match close A a_enc succs fuel [] PositiveSet.empty [a0] with
        | Some pool =>
            let m := build_imap pool in
            match edges_of m pool with
            | None => false
            | Some rows =>
                match idx_of m a0 with
                | None => false
                | Some _ =>
                    forallb (fun q =>
                      implb (cvisits tm c0 t q
                             || existsb (fun row => st_eqb (row_state row) q)
                                        rows)
                            (irank_ok rows q (mkr rows q))) all_St
                end
            end
        | None => false
        end
    | None => false
    end.

  (** ** ClosureIdx-lex: the same interning for lexicographic certificates

      [Closure.closure_check_neverqh_lex] pays, PER STATE of [all_St]:
      [succs] recomputed for every pool node, and -- inside
      [lex_edge_ok] -- one [a_enc] plus one big-key
      [PositiveMap.find] per certificate component per EDGE ENDPOINT.
      With [c] components over [e] edges that is [2*c*e] context
      encodings per state, four states deep, on top of four [succs]
      sweeps.

      Measured motivation (docs/CENSUS_RUNTIME.md, [ProbeRwWin]):
      interning the untrusted RepWL search sped its FAILING attempts
      up 2.33-4.4x but left WINNING attempts flat, because on a
      winning attempt the verified checker is ~43% of the cost and
      interning had not touched it.

      Interning the certificate closes that gap:

      - the graph is walked ONCE by [edges_of] above, so [succs] is
        computed once per node and every edge already names its
        target's index and state;
      - a component is presented with its tables keyed by [a_enc]
        ([epres]) -- exactly the shape the RepWL and n-gram searches
        already emit -- so [vals_of] encodes a node ONCE and reads
        every component's rank, gate and delta off that one key;
      - per state, one pass over the pool materialises those per-node
        values into a SMALL-key map ([vmap_of]).  The check itself
        then touches no context at all: two small-key lookups and
        integer arithmetic per edge.

      The certificate stays a parameter, so it still carries no
      soundness -- and [lex_check_idx] is proved EQUAL to
      [closure_check_neverqh_lex] on the denoted certificate, not
      merely sound relative to it, so no verdict anywhere can move. *)

  (** *** Components presented with [a_enc]-keyed tables *)

  Inductive epres : Type :=
  | ERank (phi : PositiveMap.tree nat)
  | EMeas (mval : cconf -> nat) (md : A -> Z) (K : nat)
          (phi : PositiveMap.tree nat) (gate : PositiveSet.t).

  Definition enat (m : PositiveMap.tree nat) (k : positive) : nat :=
    match PositiveMap.find k m with Some n => n | None => 0 end.

  Definition epres_denote (p : epres) : lexcomp A :=
    match p with
    | ERank phi => LexRank A (fun a => enat phi (a_enc a))
    | EMeas mval md K phi gate =>
        LexMeas A mval (fun a _ => md a) K
                (fun a => enat phi (a_enc a))
                (fun a => PositiveSet.mem (a_enc a) gate)
    end.

  (** *** One node's value for one component

      [VMeas] carries the SOURCE-side delta; that is all the RepWL and
      n-gram measures ever depend on, and [epres_denote] pins it by
      construction ([fun a _ => md a]). *)

  Inductive cval : Type :=
  | VRank (r : nat)
  | VMeas (K : nat) (g : bool) (p : nat) (d : Z).

  Definition cval_of (e : positive) (a : A) (p : epres) : cval :=
    match p with
    | ERank phi => VRank (enat phi e)
    | EMeas _ md K phi gate =>
        VMeas K (PositiveSet.mem e gate) (enat phi e) (md a)
    end.

  (** The single [a_enc] per node, shared by every component. *)
  Definition vals_of (ps : list epres) (a : A) : list cval :=
    let e := a_enc a in map (fun p => cval_of e a p) ps.

  (** *** The per-edge test, on values only

      Same boolean functions as [comp_strict] / [comp_noninc] /
      [lex_edge_ok], written with nested [if]s so a decided prefix
      does not evaluate the rest (Coq's [&&] and [||] are functions,
      so under call-by-value both arguments run -- the trap that cost
      the scan tier two quadratics). *)

  Definition vstrict (x y : cval) : bool :=
    match x, y with
    | VRank rx, VRank ry => ry <? rx
    | VMeas K gx px dx, VMeas _ gy py _ =>
        if gx then
          if gy
          then (Z.of_nat K * dx + Z.of_nat py - Z.of_nat px <=? -1)%Z
          else false
        else false
    | _, _ => false
    end.

  Definition vnoninc (x y : cval) : bool :=
    match x, y with
    | VRank rx, VRank ry => ry <=? rx
    | VMeas K gx px dx, VMeas _ gy py _ =>
        if gy then
          if gx
          then (Z.of_nat K * dx + Z.of_nat py - Z.of_nat px <=? 0)%Z
          else false
        else true
    | _, _ => false
    end.

  Fixpoint vlex_edge_ok (xs ys : list cval) : bool :=
    match xs, ys with
    | x :: xt, y :: yt =>
        if vstrict x y then true
        else if vnoninc x y then vlex_edge_ok xt yt else false
    | _, _ => false
    end.

  Lemma vstrict_spec : forall p a a',
    vstrict (cval_of (a_enc a) a p) (cval_of (a_enc a') a' p)
    = comp_strict A (epres_denote p) a a'.
  Proof.
    intros [phi | mval md K phi gate] a a'; simpl; [reflexivity|].
    destruct (PositiveSet.mem (a_enc a) gate);
      destruct (PositiveSet.mem (a_enc a') gate); reflexivity.
  Qed.

  Lemma vnoninc_spec : forall p a a',
    vnoninc (cval_of (a_enc a) a p) (cval_of (a_enc a') a' p)
    = comp_noninc A (epres_denote p) a a'.
  Proof.
    intros [phi | mval md K phi gate] a a'; simpl; [reflexivity|].
    destruct (PositiveSet.mem (a_enc a) gate);
      destruct (PositiveSet.mem (a_enc a') gate); reflexivity.
  Qed.

  Lemma vlex_edge_ok_spec : forall ps a a',
    vlex_edge_ok (vals_of ps a) (vals_of ps a')
    = lex_edge_ok A (map epres_denote ps) a a'.
  Proof.
    unfold vals_of. induction ps as [|p t IH]; intros a a'; [reflexivity|].
    cbn [map vlex_edge_ok lex_edge_ok].
    rewrite vstrict_spec, vnoninc_spec.
    destruct (comp_strict A (epres_denote p) a a'); [reflexivity|].
    cbn [orb]. destruct (comp_noninc A (epres_denote p) a a');
      [cbn [andb]; apply IH | reflexivity].
  Qed.

  (** *** Per-state materialisation into small keys *)

  Definition vmap : Type := PositiveMap.tree (list cval).

  Fixpoint zip_from (l : list A) (i : positive) : list (positive * A) :=
    match l with
    | [] => []
    | a :: t => (i, a) :: zip_from t (Pos.succ i)
    end.

  (** The pool paired with the indices [build_imap] hands out. *)
  Definition ipool (pool : list A) : list (positive * A) :=
    zip_from pool 1%positive.

  Definition vmap_of (ps : list epres) (ip : list (positive * A)) : vmap :=
    fold_left (fun m p => PositiveMap.add (fst p) (vals_of ps (snd p)) m)
              ip (PositiveMap.empty _).

  Definition vget (vm : vmap) (i : positive) : list cval :=
    match PositiveMap.find i vm with Some vs => vs | None => [] end.

  Definition vrow_ok (q : St) (vm : vmap) (row : erow) : bool :=
    let '(i, s, js) := row in
    if st_eqb s q then true
    else
      let xs := vget vm i in
      forallb (fun p => if st_eqb (snd p) q then true
                        else vlex_edge_ok xs (vget vm (fst p))) js.

  Definition vlex_ok (rows : list erow) (q : St) (vm : vmap) : bool :=
    forallb (vrow_ok q vm) rows.

  (** *** The checker *)

  Definition lex_check_idx (t fuel : nat) (a0 : A)
      (cert : St -> list epres) : bool :=
    match csteps tm t c0 with
    | Some ct =>
        match close A a_enc succs fuel [] PositiveSet.empty [a0] with
        | Some pool =>
            match edges_of (build_imap pool) pool with
            | None => false
            | Some rows =>
                let ip := ipool pool in
                forallb (fun q =>
                  implb (cvisits tm c0 t q
                         || existsb (fun row => st_eqb (row_state row) q) rows)
                        (vlex_ok rows q (vmap_of (cert q) ip))) all_St
            end
        | None => false
        end
    | None => false
    end.

  (** *** Structural transfer lemmas for [map_opt] *)

  Lemma map_opt_forallb : forall (B C : Type) (f : B -> option C)
      (P : C -> bool) (Q : B -> bool) l r,
    map_opt f l = Some r ->
    (forall b c, In b l -> f b = Some c -> P c = Q b) ->
    forallb P r = forallb Q l.
  Proof.
    intros B C f P Q. induction l as [|b t IH]; simpl; intros r Hm HPQ.
    - injection Hm as <-. reflexivity.
    - destruct (f b) as [c|] eqn:Ef; [|discriminate].
      destruct (map_opt f t) as [rt|] eqn:Et; [|discriminate].
      injection Hm as <-. simpl.
      rewrite (HPQ b c (or_introl eq_refl) Ef).
      rewrite (IH rt eq_refl); [reflexivity|].
      intros b' c' Hin Hf. apply HPQ; [right; exact Hin | exact Hf].
  Qed.

  Lemma map_opt_existsb : forall (B C : Type) (f : B -> option C)
      (P : C -> bool) (Q : B -> bool) l r,
    map_opt f l = Some r ->
    (forall b c, In b l -> f b = Some c -> P c = Q b) ->
    existsb P r = existsb Q l.
  Proof.
    intros B C f P Q. induction l as [|b t IH]; simpl; intros r Hm HPQ.
    - injection Hm as <-. reflexivity.
    - destruct (f b) as [c|] eqn:Ef; [|discriminate].
      destruct (map_opt f t) as [rt|] eqn:Et; [|discriminate].
      injection Hm as <-. simpl.
      rewrite (HPQ b c (or_introl eq_refl) Ef).
      rewrite (IH rt eq_refl); [reflexivity|].
      intros b' c' Hin Hf. apply HPQ; [right; exact Hin | exact Hf].
  Qed.

  Lemma map_opt_total : forall (B C : Type) (f : B -> option C) l,
    (forall x, In x l -> exists y, f x = Some y) ->
    exists r, map_opt f l = Some r.
  Proof.
    intros B C f. induction l as [|b t IH]; simpl; intros H;
      [exists []; reflexivity|].
    destruct (H b (or_introl eq_refl)) as (y & Hy).
    destruct (IH (fun x Hx => H x (or_intror Hx))) as (rt & Hrt).
    exists (y :: rt). rewrite Hy, Hrt. reflexivity.
  Qed.

  Lemma forallb_ext : forall (B : Type) (f g : B -> bool) l,
    (forall x, f x = g x) -> forallb f l = forallb g l.
  Proof.
    intros B f g. induction l as [|x t IH]; simpl; intros H; [reflexivity|].
    rewrite H, IH by assumption. reflexivity.
  Qed.

  (** *** The numbering [build_imap] hands out is [ipool]'s *)

  Lemma vmap_of_skip : forall ps l i0 m j,
    (j < i0)%positive ->
    PositiveMap.find j
      (fold_left (fun m p => PositiveMap.add (fst p) (vals_of ps (snd p)) m)
                 (zip_from l i0) m)
    = PositiveMap.find j m.
  Proof.
    intros ps. induction l as [|x t IH]; simpl; intros i0 m j Hlt;
      [reflexivity|].
    rewrite IH by lia. apply PositiveMap.gso. lia.
  Qed.

  Lemma vmap_of_find : forall ps l i0 m j a,
    In (j, a) (zip_from l i0) ->
    PositiveMap.find j
      (fold_left (fun m p => PositiveMap.add (fst p) (vals_of ps (snd p)) m)
                 (zip_from l i0) m)
    = Some (vals_of ps a).
  Proof.
    intros ps. induction l as [|x t IH]; simpl; intros i0 m j a Hin;
      [contradiction|].
    destruct Hin as [E | Hin].
    - injection E as <- <-. rewrite vmap_of_skip by lia.
      apply PositiveMap.gss.
    - apply IH. exact Hin.
  Qed.

  Lemma build_imap_aux_val : forall l i m k v,
    PositiveMap.find k (build_imap_aux l i m) = Some v ->
    (exists a, In (v, a) (zip_from l i) /\ a_enc a = k)
    \/ PositiveMap.find k m = Some v.
  Proof.
    induction l as [|x t IH]; simpl; intros i m k v H; [right; exact H|].
    destruct (IH _ _ _ _ H) as [(a & Hin & Ha) | H'].
    - left. exists a. split; [right; exact Hin | exact Ha].
    - destruct (Pos.eq_dec k (a_enc x)) as [-> | Hne].
      + rewrite PositiveMap.gss in H'. injection H' as ->.
        left. exists x. split; [left; reflexivity | reflexivity].
      + rewrite PositiveMap.gso in H' by (intro C; apply Hne; congruence).
        right. exact H'.
  Qed.

  Lemma build_imap_aux_mono : forall l i m k v,
    PositiveMap.find k m = Some v ->
    exists v', PositiveMap.find k (build_imap_aux l i m) = Some v'.
  Proof.
    induction l as [|x t IH]; simpl; intros i m k v H; [exists v; exact H|].
    destruct (Pos.eq_dec k (a_enc x)) as [-> | Hne].
    - apply (IH (Pos.succ i) _ _ i). apply PositiveMap.gss.
    - apply (IH (Pos.succ i) _ _ v).
      rewrite PositiveMap.gso by (intro C; apply Hne; congruence). exact H.
  Qed.

  Lemma build_imap_aux_hit : forall l a i m,
    In a l ->
    exists v, PositiveMap.find (a_enc a) (build_imap_aux l i m) = Some v.
  Proof.
    induction l as [|x t IH]; simpl; intros a i m Hin; [contradiction|].
    destruct Hin as [-> | Hin].
    - apply (build_imap_aux_mono t (Pos.succ i) _ (a_enc a) i).
      apply PositiveMap.gss.
    - apply IH. exact Hin.
  Qed.

  Lemma build_imap_hit : forall pool a,
    In a pool -> exists i, idx_of (build_imap pool) a = Some i.
  Proof.
    intros pool a Hin. unfold idx_of, build_imap.
    apply build_imap_aux_hit. exact Hin.
  Qed.

  Lemma idx_of_zip : forall pool a i,
    idx_of (build_imap pool) a = Some i -> In (i, a) (ipool pool).
  Proof.
    intros pool a i H. unfold idx_of, build_imap in H. unfold ipool.
    destruct (build_imap_aux_val pool 1%positive (PositiveMap.empty _)
                (a_enc a) i H) as [(b & Hin & Hb) | Hemp].
    - rewrite <- (a_enc_inj b a Hb). exact Hin.
    - rewrite PositiveMap.gempty in Hemp. discriminate.
  Qed.

  Lemma vget_pool : forall ps pool a i,
    idx_of (build_imap pool) a = Some i ->
    vget (vmap_of ps (ipool pool)) i = vals_of ps a.
  Proof.
    intros ps pool a i H. unfold vget, vmap_of, ipool.
    rewrite (vmap_of_find ps pool 1%positive _ i a (idx_of_zip pool a i H)).
    reflexivity.
  Qed.

  (** *** [edges_of] succeeds on any closed pool

      The converse of [edges_closed]: this is what makes the interned
      checker EQUAL to the old one rather than merely stronger. *)

  Lemma edges_of_closed : forall pool,
    closed_b A a_enc succs pool = true ->
    exists rows, edges_of (build_imap pool) pool = Some rows.
  Proof.
    intros pool Hcl. unfold edges_of. apply map_opt_total.
    intros a Hin.
    unfold closed_b in Hcl. rewrite forallb_forall in Hcl.
    specialize (Hcl a Hin). unfold node_ok in Hcl.
    destruct (succs a) as [l|] eqn:Es; [|discriminate].
    destruct (build_imap_hit pool a Hin) as (i & Hi).
    assert (Hjs : exists js, map_opt (tag (build_imap pool)) l = Some js).
    { apply map_opt_total. intros a' Hin'.
      rewrite forallb_forall in Hcl. specialize (Hcl a' Hin').
      unfold apool in Hcl.
      destruct (build_imap_hit pool a'
                  (pset_of_mem A a_enc a_enc_inj a' pool Hcl)) as (j & Hj).
      exists (j, a_state a'). unfold tag. rewrite Hj. reflexivity. }
    destruct Hjs as (js & Hjs).
    exists (i, a_state a, js). unfold edge_row.
    rewrite Hi, Es, Hjs. reflexivity.
  Qed.

  (** *** The interned lex check IS the old lex check *)

  Lemma vlex_ok_lex_ok : forall pool rows ps q,
    edges_of (build_imap pool) pool = Some rows ->
    vlex_ok rows q (vmap_of ps (ipool pool))
    = lex_ok A a_state succs pool q (map epres_denote ps).
  Proof.
    intros pool rows ps q Hrows. unfold vlex_ok, lex_ok.
    apply (map_opt_forallb A erow (edge_row (build_imap pool)) _ _ pool rows
             Hrows).
    intros a row Hin Hrow. unfold edge_row in Hrow.
    destruct (idx_of (build_imap pool) a) as [i|] eqn:Ei; [|discriminate].
    destruct (succs a) as [l|] eqn:Es; [|discriminate].
    destruct (map_opt (tag (build_imap pool)) l) as [js|] eqn:Ejs;
      [|discriminate].
    injection Hrow as <-. cbn [vrow_ok].
    destruct (st_eqb (a_state a) q); [reflexivity|].
    rewrite (vget_pool ps pool a i Ei).
    apply (map_opt_forallb A (positive * St) (tag (build_imap pool)) _ _
             l js Ejs).
    intros a' p Hin' Hp. unfold tag in Hp.
    destruct (idx_of (build_imap pool) a') as [j|] eqn:Ej; [|discriminate].
    injection Hp as <-. cbn [fst snd].
    destruct (st_eqb (a_state a') q); [reflexivity|].
    cbn [orb]. rewrite (vget_pool ps pool a' j Ej).
    apply vlex_edge_ok_spec.
  Qed.

  Lemma lex_check_idx_spec : forall t fuel a0 cert cert',
    (forall q, cert' q = map epres_denote (cert q)) ->
    lex_check_idx t fuel a0 cert
    = closure_check_neverqh_lex tm A a_enc a_state succs t fuel a0 cert'.
  Proof.
    intros t fuel a0 cert cert' Hc.
    unfold lex_check_idx, closure_check_neverqh_lex.
    destruct (csteps tm t c0) as [ct|]; [|reflexivity].
    destruct (close A a_enc succs fuel [] PositiveSet.empty [a0])
      as [pool|] eqn:Ecl; [|reflexivity].
    destruct (close_root_spec A a_enc succs a_enc_inj fuel a0 pool Ecl)
      as [_ Hcl].
    destruct (edges_of_closed pool Hcl) as (rows & Erow). rewrite Erow.
    apply forallb_ext. intros q.
    rewrite (map_opt_existsb A erow (edge_row (build_imap pool))
               (fun row => st_eqb (row_state row) q)
               (fun a => st_eqb (a_state a) q) pool rows Erow).
    - rewrite Hc. rewrite (vlex_ok_lex_ok pool rows (cert q) q Erow).
      reflexivity.
    - intros a row _ Hrow. unfold edge_row in Hrow.
      destruct (idx_of (build_imap pool) a); [|discriminate].
      destruct (succs a); [|discriminate].
      destruct (map_opt (tag (build_imap pool)) l); [|discriminate].
      injection Hrow as <-. reflexivity.
  Qed.

  (** ** Soundness

      Reuses [Closure.v] wholesale: the pass gives [closed_b], the
      index gives [In a0 pool], and [closure_invariant] / [rank_find]
      are the same lemmas the old checker leans on. *)

  Variable covers : A -> ExecState -> Prop.
  Hypothesis covers_state : forall a c, covers a c -> a_state a = fst c.
  Hypothesis succs_sound : forall a c, covers a c ->
    match succs a, step tm c with
    | Some l, Some c' => exists a', In a' l /\ covers a' c'
    | Some _, None => False
    | None, _ => True
    end.

  Theorem idx_check_neverqh_sound : forall t fuel a0 mkr,
    (forall ct, csteps tm t c0 = Some ct -> covers a0 (lift ct)) ->
    idx_check_neverqh t fuel a0 mkr = true ->
    NeverQuasiHaltsSt tm.
  Proof.
    intros t fuel a0 mkr Hstart H. unfold idx_check_neverqh in H.
    destruct (csteps tm t c0) as [ct|] eqn:Et; [|discriminate].
    destruct (close A a_enc succs fuel [] PositiveSet.empty [a0])
      as [pool|] eqn:Ecl; [|discriminate].
    destruct (edges_of (build_imap pool) pool) as [rows|] eqn:Erow;
      [|discriminate].
    destruct (idx_of (build_imap pool) a0) as [i0|] eqn:Ei0; [|discriminate].
    assert (Hcl : closed_b A a_enc succs pool = true)
      by (apply (edges_closed pool rows Erow)).
    assert (Hin : In a0 pool) by (apply (idx_of_In pool a0 i0 Ei0)).
    pose proof (Hstart ct eq_refl) as Hcov0.
    assert (Hct : stepn tm t InitES = Some (lift ct)).
    { rewrite <- lift_c0. apply csteps_lift; assumption. }
    intros q Hvq N.
    (* the liveness premise for q holds, so its rank check ran *)
    assert (Hro : rank_ok A a_state succs pool q
                    (rnk_of (build_imap pool) (mkr rows q)) = true).
    { rewrite forallb_forall in H.
      specialize (H q (all_St_complete q)).
      destruct Hvq as (n0 & cn & Hcn & Hqn).
      assert (Hprem : cvisits tm c0 t q
                      || existsb (fun row => st_eqb (row_state row) q) rows
                      = true).
      { destruct (le_lt_dec t n0) as [Hge | Hlt].
        - apply orb_true_intro; right.
          destruct (closure_invariant tm A a_enc succs covers a_enc_inj
                      succs_sound pool Hcl a0 (lift ct) Hin Hcov0 (n0 - t))
            as (c' & a' & Hst & HIn' & Hcov').
          assert (Hc' : stepn tm n0 InitES = Some c').
          { replace n0 with (t + (n0 - t)) by lia.
            rewrite stepn_add, Hct. assumption. }
          rewrite Hc' in Hcn. injection Hcn as <-.
          destruct (map_opt_in A erow (edge_row (build_imap pool)) pool rows
                      a' Erow HIn') as (row & Hrow & Hinrow).
          apply existsb_exists. exists row. split; [exact Hinrow|].
          unfold edge_row in Hrow.
          destruct (idx_of (build_imap pool) a'); [|discriminate].
          destruct (succs a'); [|discriminate].
          destruct (map_opt (tag (build_imap pool)) l); [|discriminate].
          injection Hrow as <-. unfold row_state. simpl.
          apply st_eqb_spec. rewrite (covers_state a' c' Hcov'). assumption.
        - apply orb_true_intro; left.
          destruct (csteps_prefix tm n0 t c0 ct) as (cn' & Hcn' & _);
            [lia | exact Et |].
          assert (Hl : stepn tm n0 InitES = Some (lift cn')).
          { rewrite <- lift_c0. apply csteps_lift; assumption. }
          rewrite Hl in Hcn. injection Hcn as <-.
          eapply cvisits_complete; [exact Hlt | exact Hcn' | exact Hqn]. }
      rewrite Hprem in H. simpl in H.
      apply (irank_ok_rank_ok pool rows q (mkr rows q) Erow H). }
    (* fetch a covered configuration at index max N t and search *)
    set (M := Nat.max N t).
    destruct (closure_invariant tm A a_enc succs covers a_enc_inj succs_sound
                pool Hcl a0 (lift ct) Hin Hcov0 (M - t))
      as (cM & aM & HstM & HInM & HcovM).
    assert (HM : stepn tm M InitES = Some cM).
    { replace M with (t + (M - t)) by (unfold M; lia).
      rewrite stepn_add, Hct. assumption. }
    destruct (rank_find tm A a_enc a_state succs covers a_enc_inj covers_state
                succs_sound pool q (rnk_of (build_imap pool) (mkr rows q))
                Hcl Hro
                (S (rnk_of (build_imap pool) (mkr rows q) aM)) aM cM M)
      as (n & Hn & Hv); try assumption; try lia.
    exists n. split; [| assumption].
    assert (N <= M) by (unfold M; lia). lia.
  Qed.

End IdxEngine.
