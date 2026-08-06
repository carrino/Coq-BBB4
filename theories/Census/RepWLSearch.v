(** * Census/RepWLSearch: the in-Coq ranking-rules search over RepWL.

    The UNTRUSTED search half of the census RepWL tier: the exact
    analogue of Census/RankSearch.v, over the RepWL block-list
    abstraction instead of the n-gram contexts.  It mirrors
    tools/repwl_prover.py's [procedure] -- SCC decomposition of the
    q-avoiding context graph, condensation ranks, rule (a) (delete
    strictly-decreasing edges of a measure nonincreasing on an SCC)
    and rule (b) (an SCC whose every cycle strictly decreases a
    measure, certified by Bellman-Ford potentials) over the five
    RepWL measures (N/A, N/L, N/R nonblank counts; 0/l, 0/r interior
    blank counts) -- emitting the lexicographic [rwcomp] certificate
    that the EXISTING verified checker [rw_check_neverqh] consumes.

    Nothing here carries soundness: a wrong certificate merely fails
    the checker.  Certificates are keyed by [rconf_enc] ([RwRankE] /
    [RwMeasE]), so the emitted tables are positive-keyed directly.
    The RepWL delta is per-source ([rw_delta tm m a]), so every edge
    predicate below reads only the edge's source. *)

From Coq Require Import Arith Lia Bool List ZArith PArith.
From Coq Require Import FSets.FMapPositive.
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure.
From BBB4.Checkers Require Import Cycle RepWL.
Import ListNotations.

(** ** Graph plumbing (nodes keyed by [rconf_enc]) *)

Definition rkey (a : rconf) : positive := rconf_enc a.

Definition RAdj : Type := PositiveMap.tree (list rconf).

Definition radj_get (g : RAdj) (a : rconf) : list rconf :=
  match PositiveMap.find (rkey a) g with
  | Some l => l
  | None => []
  end.

Definition radj_set (g : RAdj) (a : rconf) (l : list rconf) : RAdj :=
  PositiveMap.add (rkey a) l g.

(** q-avoiding successors of the abstraction ([None] = halt or
    fail-closed: no out-edges; the verified checker re-derives) *)
Definition rqsuccs (tm : TM) (L T : nat) (q : St) (a : rconf)
  : list rconf :=
  match rw_succs tm L T a with
  | Some l => filter (fun b => negb (st_eqb (rw_state b) q)) l
  | None => []
  end.

Definition rbuild_adj (tm : TM) (L T : nat) (q : St)
    (nodes : list rconf) : RAdj :=
  fold_left (fun g a => radj_set g a (rqsuccs tm L T q a))
            nodes (PositiveMap.empty _).

Definition rfold_edges {B : Type} (nodes : list rconf) (g : RAdj)
    (f : B -> rconf -> rconf -> B) (init : B) : B :=
  fold_left (fun acc a => fold_left (fun acc' b => f acc' a b)
                                    (radj_get g a) acc)
            nodes init.

(** ** Reachability and SCCs (Kosaraju, linear in V+E; untrusted --
    a wrong partition only makes the verified check reject) *)

Definition rrev_adj (nodes : list rconf) (g : RAdj) : RAdj :=
  rfold_edges nodes g
    (fun r a b => radj_set r b (a :: radj_get r b))
    (PositiveMap.empty _).

Inductive rdfs_ev : Type := RDfsEnter (v : rconf) | RDfsExit (v : rconf).

Fixpoint rdfs_order (fuel : nat) (g : RAdj) (stack : list rdfs_ev)
    (seen : PositiveSet.t) (out : list rconf)
  : PositiveSet.t * list rconf :=
  match fuel with
  | 0 => (seen, out)
  | S f =>
      match stack with
      | [] => (seen, out)
      | RDfsExit v :: rest => rdfs_order f g rest seen (v :: out)
      | RDfsEnter v :: rest =>
          if PositiveSet.mem (rkey v) seen
          then rdfs_order f g rest seen out
          else rdfs_order f g
                 (map RDfsEnter (radj_get g v) ++ RDfsExit v :: rest)
                 (PositiveSet.add (rkey v) seen) out
      end
  end.

Definition rfinish_order (fuel : nat) (nodes : list rconf) (g : RAdj)
  : list rconf :=
  snd (fold_left
    (fun '(seen, out) v =>
       if PositiveSet.mem (rkey v) seen then (seen, out)
       else rdfs_order fuel g [RDfsEnter v] seen out)
    nodes (PositiveSet.empty, [])).

Fixpoint rscc_collect (fuel : nat) (g : RAdj) (todo : list rconf)
    (seen : PositiveSet.t) (comp : list rconf)
  : PositiveSet.t * list rconf :=
  match fuel with
  | 0 => (seen, comp)
  | S f =>
      match todo with
      | [] => (seen, comp)
      | v :: rest =>
          if PositiveSet.mem (rkey v) seen
          then rscc_collect f g rest seen comp
          else rscc_collect f g (radj_get g v ++ rest)
                            (PositiveSet.add (rkey v) seen) (v :: comp)
      end
  end.

Definition rscc_partition (fuel : nat) (nodes : list rconf) (g : RAdj)
  : list (list rconf) :=
  let order := rfinish_order fuel nodes g in
  let r := rrev_adj nodes g in
  rev (snd (fold_left
    (fun '(seen, comps) v =>
       if PositiveSet.mem (rkey v) seen then (seen, comps)
       else let '(seen', comp) := rscc_collect fuel r [v] seen [] in
            (seen', comp :: comps))
    order (PositiveSet.empty, []))).

Definition rhas_self_edge (g : RAdj) (v : rconf) : bool :=
  existsb (fun b => Pos.eqb (rkey b) (rkey v)) (radj_get g v).

Definition rscc_cyclic (g : RAdj) (c : list rconf) : bool :=
  match c with
  | [] => false
  | [v] => rhas_self_edge g v
  | _ => true
  end.

(** ** Condensation longest-path ranks *)

Definition rcid_map (comps : list (list rconf)) : PositiveMap.tree nat :=
  snd (fold_left
    (fun '(i, m) c =>
       (S i, fold_left (fun m' v => PositiveMap.add (rkey v) i m') c m))
    comps (0, PositiveMap.empty nat)).

Definition rcid_get (m : PositiveMap.tree nat) (a : rconf) : nat :=
  match PositiveMap.find (rkey a) m with
  | Some i => i | None => 0
  end.

(** condensation ranks in a map keyed by component id (the old
    list-nat + nth/rset_nth representation cost O(#comps) per edge) *)
Definition rcrk_get (m : PositiveMap.tree nat) (i : nat) : nat :=
  match PositiveMap.find (Pos.of_succ_nat i) m with
  | Some v => v | None => 0
  end.

(** one relaxation pass over all alive edges; returns (ranks, changed) *)
Definition rcrank_pass (nodes : list rconf) (g : RAdj)
    (cid : PositiveMap.tree nat) (st : PositiveMap.tree nat * bool)
  : PositiveMap.tree nat * bool :=
  rfold_edges nodes g
    (fun '(rk, ch) a b =>
       let ia := rcid_get cid a in
       let ib := rcid_get cid b in
       if Nat.eqb ia ib then (rk, ch)
       else if Nat.ltb (rcrk_get rk ia) (S (rcrk_get rk ib))
            then (PositiveMap.add (Pos.of_succ_nat ia)
                    (S (rcrk_get rk ib)) rk, true)
            else (rk, ch))
    st.

Fixpoint rcrank_iter (fuel : nat) (nodes : list rconf) (g : RAdj)
    (cid : PositiveMap.tree nat) (rk : PositiveMap.tree nat)
  : PositiveMap.tree nat :=
  match fuel with
  | 0 => rk
  | S f =>
      let '(rk', ch) := rcrank_pass nodes g cid (rk, false) in
      if ch then rcrank_iter f nodes g cid rk' else rk'
  end.

Definition rcondensation_rank (nodes : list rconf) (g : RAdj)
    (comps : list (list rconf)) : list (positive * nat) :=
  let cid := rcid_map comps in
  let rk := rcrank_iter (S (length comps)) nodes g cid
                        (PositiveMap.empty nat) in
  map (fun v => (rkey v, rcrk_get rk (rcid_get cid v))) nodes.

(** node-level longest-path rank for the final acyclic graph *)
Definition rnrank_pass (nodes : list rconf) (g : RAdj)
    (st : PositiveMap.tree nat * bool) : PositiveMap.tree nat * bool :=
  rfold_edges nodes g
    (fun '(rk, ch) a b =>
       let ra := match PositiveMap.find (rkey a) rk with
                 | Some v => v | None => 0 end in
       let rb := match PositiveMap.find (rkey b) rk with
                 | Some v => v | None => 0 end in
       if Nat.ltb ra (S rb)
       then (PositiveMap.add (rkey a) (S rb) rk, true)
       else (rk, ch))
    st.

Fixpoint rnrank_iter (fuel : nat) (nodes : list rconf) (g : RAdj)
    (rk : PositiveMap.tree nat) : PositiveMap.tree nat :=
  match fuel with
  | 0 => rk
  | S f =>
      let '(rk', ch) := rnrank_pass nodes g (rk, false) in
      if ch then rnrank_iter f nodes g rk' else rk'
  end.

Definition rnode_rank (nodes : list rconf) (g : RAdj)
  : list (positive * nat) :=
  let rk := rnrank_iter (S (length nodes)) nodes g
                        (PositiveMap.empty nat) in
  map (fun v => (rkey v, match PositiveMap.find (rkey v) rk with
                         | Some x => x | None => 0 end)) nodes.

(** ** Rules (a) and (b) on one cyclic SCC *)

(** intra-SCC edge list of [c] *)
Definition rintra_edges (g : RAdj) (cset : PositiveSet.t) (c : list rconf)
  : list (rconf * rconf) :=
  concat (map (fun a =>
    map (fun b => (a, b))
        (filter (fun b => PositiveSet.mem (rkey b) cset) (radj_get g a))) c).

Definition rcset_of (c : list rconf) : PositiveSet.t :=
  fold_left (fun s v => PositiveSet.add (rkey v) s) c PositiveSet.empty.

(** delete intra edges of [c] whose predicate holds on the edge *)
Definition rdelete_intra (g : RAdj) (cset : PositiveSet.t)
    (c : list rconf) (dead : rconf -> rconf -> bool) : RAdj :=
  fold_left (fun g' a =>
    radj_set g' a (filter (fun b => negb (PositiveSet.mem (rkey b) cset &&
                                          dead a b))
                          (radj_get g' a))) c g.

(** rule (a): [m] nonincreasing on every intra edge, decreasing on one
    (the RepWL delta reads only the source) *)
Definition rtry_rule_a (tm : TM) (g : RAdj) (cset : PositiveSet.t)
    (c : list rconf) (m : rwmeas) : option (rwcomp * RAdj) :=
  let es := rintra_edges g cset c in
  let ds := map (fun '(a, _) => rw_delta tm m a) es in
  if forallb (fun d => Z.leb d 0) ds && existsb (fun d => Z.ltb d 0) ds
  then Some (RwMeasE m 1 [] (map rkey c),
             rdelete_intra g cset c
               (fun a _ => Z.ltb (rw_delta tm m a) 0))
  else None.

(** rule (b): Bellman-Ford potentials for weights Kc*delta + 1 *)
Definition rbell_get (d : PositiveMap.tree Z) (a : rconf) : Z :=
  match PositiveMap.find (rkey a) d with
  | Some v => v | None => 0%Z
  end.

Definition rbell_pass (tm : TM) (m : rwmeas) (Kc : Z)
    (es : list (rconf * rconf)) (st : PositiveMap.tree Z * bool)
  : PositiveMap.tree Z * bool :=
  fold_left (fun '(dist, ch) '(a, b) =>
    let w := (Kc * rw_delta tm m a + 1)%Z in
    let da := rbell_get dist a in
    let db := rbell_get dist b in
    if Z.ltb (da - w)%Z db
    then (PositiveMap.add (rkey b) ((da - w)%Z) dist, true)
    else (dist, ch)) es st.

Fixpoint rbell_iter (fuel : nat) (tm : TM) (m : rwmeas) (Kc : Z)
    (es : list (rconf * rconf)) (dist : PositiveMap.tree Z)
  : option (PositiveMap.tree Z) :=
  match fuel with
  | 0 => None
  | S f =>
      let '(dist', ch) := rbell_pass tm m Kc es (dist, false) in
      if ch then rbell_iter f tm m Kc es dist' else Some dist'
  end.

Definition rtry_rule_b (tm : TM) (g : RAdj) (cset : PositiveSet.t)
    (c : list rconf) (Kc : nat) (m : rwmeas) : option (rwcomp * RAdj) :=
  let es := rintra_edges g cset c in
  match rbell_iter (S (length c)) tm m (Z.of_nat Kc) es
                   (PositiveMap.empty Z) with
  | None => None
  | Some dist =>
      let vals := map (fun v => rbell_get dist v) c in
      let mn := fold_left Z.min vals 0%Z in
      let phi := map (fun v => (rkey v, Z.to_nat (rbell_get dist v - mn)%Z))
                     c in
      Some (RwMeasE m Kc phi (map rkey c),
            rdelete_intra g cset c (fun _ _ => true))
  end.

Definition rmeasures : list rwmeas := [RwNA; RwNL; RwNR; RwZL; RwZR].

Fixpoint rfirst_some {B : Type} (f : rwmeas -> option B) (l : list rwmeas)
  : option B :=
  match l with
  | [] => None
  | m :: t => match f m with Some x => Some x | None => rfirst_some f t end
  end.

(** process one cyclic SCC: rule (a) over the measures, then rule (b) *)
Definition rprocess_scc (tm : TM) (Kc : nat)
    (st : RAdj * list rwcomp * bool) (c : list rconf)
  : RAdj * list rwcomp * bool :=
  let '(g, acc, prog) := st in
  let cset := rcset_of c in
  match rfirst_some (rtry_rule_a tm g cset c) rmeasures with
  | Some (comp, g') => (g', comp :: acc, true)
  | None =>
      match rfirst_some (rtry_rule_b tm g cset c Kc) rmeasures with
      | Some (comp, g') => (g', comp :: acc, true)
      | None => (g, acc, prog)
      end
  end.

(** ** The per-state procedure *)

Fixpoint rproc_rounds (fuel : nat) (tm : TM) (Kc rfuel : nat)
    (nodes : list rconf) (g : RAdj) (acc : list rwcomp)
  : option (list rwcomp) :=
  match fuel with
  | 0 => None
  | S f =>
      let comps := rscc_partition rfuel nodes g in
      let cyc := filter (rscc_cyclic g) comps in
      match cyc with
      | [] => Some (rev (RwRankE (rnode_rank nodes g) :: acc))
      | _ =>
          let acc' := RwRankE (rcondensation_rank nodes g comps) :: acc in
          let '(g', acc'', prog) :=
            fold_left (rprocess_scc tm Kc) cyc (g, acc', false) in
          if prog then rproc_rounds f tm Kc rfuel nodes g' acc''
          else None
      end
  end.

(** ** The interned core

    Everything above keys the graph work by [rkey = rconf_enc] -- a
    positional encoding of the whole run-length item list -- and
    recomputes it on EVERY map and set access: Kosaraju, the rank
    relaxations, and each Bellman-Ford pass pay an O(|rconf|)
    encoding per edge per pass.  Measured (docs/CENSUS_RUNTIME.md,
    ProbeRwSplit): the search is ~100 ms of a ~177 ms winning rw rung
    while the closure exploration itself is ~1 ms, and this tier
    carries ~75% of the walk.

    The core below runs the SAME algorithms with nodes interned to
    dense positive indices: [rconf_enc] is paid ONCE per node at
    interning ([iintern]) and once per emitted certificate entry; all
    interior maps and sets are keyed by the small indices.  The
    successor relation is also computed once per node ([irows]) --
    the old [rbuild_adj] recomputed [rw_succs] per premise state.
    Untrusted as before: a wrong certificate merely fails the
    verified checker. *)

Definition IAdj : Type := PositiveMap.tree (list positive).

Definition iadj_get (g : IAdj) (i : positive) : list positive :=
  match PositiveMap.find i g with Some l => l | None => [] end.

(** interning: index map (enc -> idx), node array (idx -> node) *)
Definition iintern (nodes : list rconf)
  : PositiveMap.tree positive * PositiveMap.tree rconf :=
  snd (fold_left
    (fun '(i, (im, arr)) a =>
       (Pos.succ i, (PositiveMap.add (rkey a) i im,
                     PositiveMap.add i a arr)))
    nodes (1%positive, (PositiveMap.empty _, PositiveMap.empty _))).

Definition iarr_get (arr : PositiveMap.tree rconf) (i : positive)
  : rconf :=
  match PositiveMap.find i arr with
  | Some a => a
  | None => (StA, ([], [], S0, [], []))  (* unreachable on interned idxs *)
  end.

(** successors once per node, resolved to indices (the closure is
    closed and [q]-states are filtered on both sides, so a successor
    that fails to resolve is simply dropped -- the checker is the
    authority) *)
Definition irows (tm : TM) (L T : nat) (q : St)
    (im : PositiveMap.tree positive) (nodes : list rconf) : IAdj :=
  snd (fold_left
    (fun '(i, g) a =>
       (Pos.succ i,
        PositiveMap.add i
          (fold_right (fun b acc =>
             if st_eqb (rw_state b) q then acc
             else match PositiveMap.find (rkey b) im with
                  | Some j => j :: acc
                  | None => acc
                  end)
             []
             (match rw_succs tm L T a with Some l => l | None => [] end))
          g))
    nodes (1%positive, PositiveMap.empty _)).

Definition iidxs (nodes : list rconf) : list positive :=
  rev (snd (fold_left (fun '(i, l) _ => (Pos.succ i, i :: l))
              nodes (1%positive, []))).

Definition irev_adj (idxs : list positive) (g : IAdj) : IAdj :=
  fold_left (fun r i =>
    fold_left (fun r' j => PositiveMap.add j (i :: iadj_get r' j) r')
              (iadj_get g i) r)
    idxs (PositiveMap.empty _).

Inductive idfs_ev : Type := IDfsEnter (v : positive) | IDfsExit (v : positive).

Fixpoint idfs_order (fuel : nat) (g : IAdj) (stack : list idfs_ev)
    (seen : PositiveSet.t) (out : list positive)
  : PositiveSet.t * list positive :=
  match fuel with
  | 0 => (seen, out)
  | S f =>
      match stack with
      | [] => (seen, out)
      | IDfsExit v :: rest => idfs_order f g rest seen (v :: out)
      | IDfsEnter v :: rest =>
          if PositiveSet.mem v seen
          then idfs_order f g rest seen out
          else idfs_order f g
                 (map IDfsEnter (iadj_get g v) ++ IDfsExit v :: rest)
                 (PositiveSet.add v seen) out
      end
  end.

Definition ifinish_order (fuel : nat) (idxs : list positive) (g : IAdj)
  : list positive :=
  snd (fold_left
    (fun '(seen, out) v =>
       if PositiveSet.mem v seen then (seen, out)
       else idfs_order fuel g [IDfsEnter v] seen out)
    idxs (PositiveSet.empty, [])).

Fixpoint iscc_collect (fuel : nat) (g : IAdj) (todo : list positive)
    (seen : PositiveSet.t) (comp : list positive)
  : PositiveSet.t * list positive :=
  match fuel with
  | 0 => (seen, comp)
  | S f =>
      match todo with
      | [] => (seen, comp)
      | v :: rest =>
          if PositiveSet.mem v seen
          then iscc_collect f g rest seen comp
          else iscc_collect f g (iadj_get g v ++ rest)
                            (PositiveSet.add v seen) (v :: comp)
      end
  end.

Definition iscc_partition (fuel : nat) (idxs : list positive) (g : IAdj)
  : list (list positive) :=
  let order := ifinish_order fuel idxs g in
  let r := irev_adj idxs g in
  rev (snd (fold_left
    (fun '(seen, comps) v =>
       if PositiveSet.mem v seen then (seen, comps)
       else let '(seen', comp) := iscc_collect fuel r [v] seen [] in
            (seen', comp :: comps))
    order (PositiveSet.empty, []))).

Definition iscc_cyclic (g : IAdj) (c : list positive) : bool :=
  match c with
  | [] => false
  | [v] => existsb (fun b => Pos.eqb b v) (iadj_get g v)
  | _ => true
  end.

Definition icid_map (comps : list (list positive)) : PositiveMap.tree nat :=
  snd (fold_left
    (fun '(i, m) c =>
       (S i, fold_left (fun m' v => PositiveMap.add v i m') c m))
    comps (0, PositiveMap.empty nat)).

Definition icid_get (m : PositiveMap.tree nat) (i : positive) : nat :=
  match PositiveMap.find i m with Some x => x | None => 0 end.

Definition ifold_edges {B : Type} (idxs : list positive) (g : IAdj)
    (f : B -> positive -> positive -> B) (init : B) : B :=
  fold_left (fun acc i => fold_left (fun acc' j => f acc' i j)
                                    (iadj_get g i) acc)
            idxs init.

Definition icrank_pass (idxs : list positive) (g : IAdj)
    (cid : PositiveMap.tree nat) (st : PositiveMap.tree nat * bool)
  : PositiveMap.tree nat * bool :=
  ifold_edges idxs g
    (fun '(rk, ch) a b =>
       let ia := icid_get cid a in
       let ib := icid_get cid b in
       if Nat.eqb ia ib then (rk, ch)
       else if Nat.ltb (rcrk_get rk ia) (S (rcrk_get rk ib))
            then (PositiveMap.add (Pos.of_succ_nat ia)
                    (S (rcrk_get rk ib)) rk, true)
            else (rk, ch))
    st.

Fixpoint icrank_iter (fuel : nat) (idxs : list positive) (g : IAdj)
    (cid : PositiveMap.tree nat) (rk : PositiveMap.tree nat)
  : PositiveMap.tree nat :=
  match fuel with
  | 0 => rk
  | S f =>
      let '(rk', ch) := icrank_pass idxs g cid (rk, false) in
      if ch then icrank_iter f idxs g cid rk' else rk'
  end.

(** certificate emission converts idx -> enc through the node array *)
Definition icondensation_rank (arr : PositiveMap.tree rconf)
    (idxs : list positive) (g : IAdj) (comps : list (list positive))
  : list (positive * nat) :=
  let cid := icid_map comps in
  let rk := icrank_iter (S (length comps)) idxs g cid
                        (PositiveMap.empty nat) in
  map (fun v => (rkey (iarr_get arr v), rcrk_get rk (icid_get cid v)))
      idxs.

Definition inrank_pass (idxs : list positive) (g : IAdj)
    (st : PositiveMap.tree nat * bool) : PositiveMap.tree nat * bool :=
  ifold_edges idxs g
    (fun '(rk, ch) a b =>
       let ra := match PositiveMap.find a rk with
                 | Some v => v | None => 0 end in
       let rb := match PositiveMap.find b rk with
                 | Some v => v | None => 0 end in
       if Nat.ltb ra (S rb)
       then (PositiveMap.add a (S rb) rk, true)
       else (rk, ch))
    st.

Fixpoint inrank_iter (fuel : nat) (idxs : list positive) (g : IAdj)
    (rk : PositiveMap.tree nat) : PositiveMap.tree nat :=
  match fuel with
  | 0 => rk
  | S f =>
      let '(rk', ch) := inrank_pass idxs g (rk, false) in
      if ch then inrank_iter f idxs g rk' else rk'
  end.

Definition inode_rank (arr : PositiveMap.tree rconf)
    (idxs : list positive) (g : IAdj) : list (positive * nat) :=
  let rk := inrank_iter (S (length idxs)) idxs g
                        (PositiveMap.empty nat) in
  map (fun v => (rkey (iarr_get arr v),
                 match PositiveMap.find v rk with
                 | Some x => x | None => 0 end)) idxs.

Definition iintra_edges (g : IAdj) (cset : PositiveSet.t)
    (c : list positive) : list (positive * positive) :=
  concat (map (fun a =>
    map (fun b => (a, b))
        (filter (fun b => PositiveSet.mem b cset) (iadj_get g a))) c).

Definition icset_of (c : list positive) : PositiveSet.t :=
  fold_left (fun s v => PositiveSet.add v s) c PositiveSet.empty.

Definition idelete_intra (g : IAdj) (cset : PositiveSet.t)
    (c : list positive) (dead : positive -> positive -> bool) : IAdj :=
  fold_left (fun g' a =>
    PositiveMap.add a
      (filter (fun b => negb (PositiveSet.mem b cset && dead a b))
              (iadj_get g' a)) g')
    c g.

(** per-SCC delta vector: [rw_delta] evaluated ONCE per node per
    measure attempt, instead of per edge per Bellman-Ford pass *)
Definition idvec (tm : TM) (m : rwmeas) (arr : PositiveMap.tree rconf)
    (c : list positive) : PositiveMap.tree Z :=
  fold_left (fun d i => PositiveMap.add i (rw_delta tm m (iarr_get arr i)) d)
            c (PositiveMap.empty Z).

Definition idvec_get (d : PositiveMap.tree Z) (i : positive) : Z :=
  match PositiveMap.find i d with Some v => v | None => 0%Z end.

Definition itry_rule_a (tm : TM) (arr : PositiveMap.tree rconf)
    (g : IAdj) (cset : PositiveSet.t) (c : list positive) (m : rwmeas)
  : option (rwcomp * IAdj) :=
  let dv := idvec tm m arr c in
  let es := iintra_edges g cset c in
  let ds := map (fun '(a, _) => idvec_get dv a) es in
  if forallb (fun d => Z.leb d 0) ds && existsb (fun d => Z.ltb d 0) ds
  then Some (RwMeasE m 1 [] (map (fun i => rkey (iarr_get arr i)) c),
             idelete_intra g cset c
               (fun a _ => Z.ltb (idvec_get dv a) 0))
  else None.

Definition ibell_pass (dv : PositiveMap.tree Z) (Kc : Z)
    (es : list (positive * positive)) (st : PositiveMap.tree Z * bool)
  : PositiveMap.tree Z * bool :=
  fold_left (fun '(dist, ch) '(a, b) =>
    let w := (Kc * idvec_get dv a + 1)%Z in
    let da := match PositiveMap.find a dist with
              | Some v => v | None => 0%Z end in
    let db := match PositiveMap.find b dist with
              | Some v => v | None => 0%Z end in
    if Z.ltb (da - w)%Z db
    then (PositiveMap.add b ((da - w)%Z) dist, true)
    else (dist, ch)) es st.

Fixpoint ibell_iter (fuel : nat) (dv : PositiveMap.tree Z) (Kc : Z)
    (es : list (positive * positive)) (dist : PositiveMap.tree Z)
  : option (PositiveMap.tree Z) :=
  match fuel with
  | 0 => None
  | S f =>
      let '(dist', ch) := ibell_pass dv Kc es (dist, false) in
      if ch then ibell_iter f dv Kc es dist' else Some dist'
  end.

Definition itry_rule_b (tm : TM) (arr : PositiveMap.tree rconf)
    (g : IAdj) (cset : PositiveSet.t) (c : list positive) (Kc : nat)
    (m : rwmeas) : option (rwcomp * IAdj) :=
  let dv := idvec tm m arr c in
  let es := iintra_edges g cset c in
  match ibell_iter (S (length c)) dv (Z.of_nat Kc) es
                   (PositiveMap.empty Z) with
  | None => None
  | Some dist =>
      let vals := map (fun v => match PositiveMap.find v dist with
                                | Some x => x | None => 0%Z end) c in
      let mn := fold_left Z.min vals 0%Z in
      let phi := map (fun v =>
                        (rkey (iarr_get arr v),
                         Z.to_nat ((match PositiveMap.find v dist with
                                    | Some x => x | None => 0%Z end) - mn)%Z))
                     c in
      Some (RwMeasE m Kc phi (map (fun i => rkey (iarr_get arr i)) c),
            idelete_intra g cset c (fun _ _ => true))
  end.

Definition iprocess_scc (tm : TM) (arr : PositiveMap.tree rconf) (Kc : nat)
    (st : IAdj * list rwcomp * bool) (c : list positive)
  : IAdj * list rwcomp * bool :=
  let '(g, acc, prog) := st in
  let cset := icset_of c in
  match rfirst_some (itry_rule_a tm arr g cset c) rmeasures with
  | Some (comp, g') => (g', comp :: acc, true)
  | None =>
      match rfirst_some (itry_rule_b tm arr g cset c Kc) rmeasures with
      | Some (comp, g') => (g', comp :: acc, true)
      | None => (g, acc, prog)
      end
  end.

Fixpoint iproc_rounds (fuel : nat) (tm : TM)
    (arr : PositiveMap.tree rconf) (Kc rfuel : nat)
    (idxs : list positive) (g : IAdj) (acc : list rwcomp)
  : option (list rwcomp) :=
  match fuel with
  | 0 => None
  | S f =>
      let comps := iscc_partition rfuel idxs g in
      let cyc := filter (iscc_cyclic g) comps in
      match cyc with
      | [] => Some (rev (RwRankE (inode_rank arr idxs g) :: acc))
      | _ =>
          let acc' := RwRankE (icondensation_rank arr idxs g comps) :: acc in
          let '(g', acc'', prog) :=
            fold_left (iprocess_scc tm arr Kc) cyc (g, acc', false) in
          if prog then iproc_rounds f tm arr Kc rfuel idxs g' acc''
          else None
      end
  end.

Definition rw_procedure (tm : TM) (L T : nat)
    (closure : list rconf) (q : St) : list rwcomp :=
  let nodes := filter (fun a => negb (st_eqb (rw_state a) q)) closure in
  let '(im, arr) := iintern nodes in
  let g := irows tm L T q im nodes in
  let idxs := iidxs nodes in
  let Kc := S (S (length nodes)) in
  let rfuel := S (length nodes * 8 + 8) in
  match iproc_rounds 300 tm arr Kc rfuel idxs g [] with
  | Some comps => comps
  | None => []
  end.

(** ** The census tier

    Parameter-closed: one (L, T, t) rung builds the closure, runs the
    search per premise state (prefix-visited or appearing, mirroring
    the checker's [implb] guard so absent states don't trigger a
    doomed search), and feeds the EXISTING verified checker.  The
    checker re-derives the closure and re-checks every edge, so the
    search carries no soundness.

    The checker is the INTERNED one (ClosureIdx-lex), in its
    pool-passing form: the closure this function already built for the
    search is handed straight to it, so the verified stage neither
    re-explores it nor sweeps [rw_succs] once per premise state, and
    pays one [rconf_enc] per closure node instead of one per
    certificate component per edge endpoint per state.  The pool stays
    untrusted -- [edges_of] re-derives closedness and [idx_of] the
    root.  Measured motivation: on WINNING rw attempts the verified
    checker is ~43% of the cost and the interned search left it
    untouched (docs/CENSUS_RUNTIME.md, [ProbeRwWin]). *)

(** The pre-ClosureIdx tier, kept as the reference the equality below
    is stated against and for the A/B probes.  Nothing in the proof
    depends on it. *)
Definition rw_tier_ref (tm : TM) (L T t fuel : nat) : bool :=
  match csteps tm t c0 with
  | None => false
  | Some cc =>
      let a0 := rw_seed L T cc in
      match close rconf rconf_enc (rw_succs tm L T) fuel
                  [] PositiveSet.empty [a0] with
      | None => false
      | Some Sl =>
          rw_check_neverqh tm L T t fuel
            (fun q =>
               if cvisits tm c0 t q
                  || existsb (fun a => st_eqb (rw_state a) q) Sl
               then rw_procedure tm L T Sl q
               else [])
      end
  end.

Definition rw_tier (tm : TM) (L T t fuel : nat) : bool :=
  match csteps tm t c0 with
  | None => false
  | Some cc =>
      let a0 := rw_seed L T cc in
      match close rconf rconf_enc (rw_succs tm L T) fuel
                  [] PositiveSet.empty [a0] with
      | None => false
      | Some Sl =>
          rw_check_neverqh_idx_pool tm L T t Sl
            (fun q =>
               if cvisits tm c0 t q
                  || existsb (fun a => st_eqb (rw_state a) q) Sl
               then rw_procedure tm L T Sl q
               else [])
      end
  end.

(** The wiring changes no verdict, on any machine, at any rung. *)
Theorem rw_tier_unchanged : forall tm L T t fuel,
  rw_tier tm L T t fuel = rw_tier_ref tm L T t fuel.
Proof.
  intros tm L T t fuel. unfold rw_tier, rw_tier_ref.
  destruct (csteps tm t c0) as [cc|] eqn:Ecc; [|reflexivity].
  destruct (close rconf rconf_enc (rw_succs tm L T) fuel
                  [] PositiveSet.empty [rw_seed L T cc]) as [Sl|] eqn:Ecl;
    [|reflexivity].
  exact (rw_check_neverqh_idx_pool_spec tm L T t fuel cc Sl _ Ecc Ecl).
Qed.

Theorem rw_tier_sound : forall tm L T t fuel,
  rw_tier tm L T t fuel = true -> NeverQuasiHaltsSt tm.
Proof.
  intros tm L T t fuel H.
  rewrite rw_tier_unchanged in H.
  unfold rw_tier_ref in H.
  destruct (csteps tm t c0) as [cc|]; [|discriminate].
  destruct (close rconf rconf_enc (rw_succs tm L T) fuel
                  [] PositiveSet.empty [rw_seed L T cc]) as [Sl|];
    [|discriminate].
  exact (rw_check_neverqh_sound tm L T t fuel _ H).
Qed.
