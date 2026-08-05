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
