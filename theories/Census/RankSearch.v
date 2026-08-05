(** * Census/RankSearch: the in-Coq ranking-rules search (rules (a)/(b)).

    The UNTRUSTED search half of the n-gram rank pipeline
    (NEXT_SESSION.md "Kill the million lines of tables"): mirrors
    tools/bulk_prover.py's [procedure] -- SCC decomposition of the
    q-avoiding context graph, condensation ranks, rule (a) (delete
    strictly-decreasing edges of a measure nonincreasing on an SCC)
    and rule (b) (an SCC whose every cycle strictly decreases a
    measure, certified by Bellman-Ford potentials) over the three
    count-of-1s measures -- emitting the lexicographic [ngcomp]
    certificate that the EXISTING verified checker
    [ngram_check_neverqh_lex] consumes.

    Nothing here carries soundness: a wrong certificate merely fails
    the checker.  Graphs are tiny (n-gram closures at n = 3), so the
    quadratic mutual-reachability SCC computation is fine. *)

From Coq Require Import Arith Lia Bool List ZArith PArith.
From Coq Require Import FSets.FMapPositive.
From BBB4 Require Import BBB4_Statement CTape PosEnc.
From BBB4.Checkers Require Import NGram.
Import ListNotations.

(** ** Graph plumbing (nodes keyed by [cconf_enc]) *)

Definition nkey (a : cconf) : positive := cconf_enc a.

Definition Adj : Type := PositiveMap.tree (list cconf).

Definition adj_get (g : Adj) (a : cconf) : list cconf :=
  match PositiveMap.find (nkey a) g with
  | Some l => l
  | None => []
  end.

Definition adj_set (g : Adj) (a : cconf) (l : list cconf) : Adj :=
  PositiveMap.add (nkey a) l g.

(** q-avoiding successors under the closure's gram sets *)
Definition qsuccs (tm : TM) (lset rset : gset) (q : St) (a : cconf)
  : list cconf :=
  match ng_succs tm lset rset a with
  | Some l => filter (fun b => negb (st_eqb (fst b) q)) l
  | None => []
  end.

Definition build_adj (tm : TM) (lset rset : gset) (q : St)
    (nodes : list cconf) : Adj :=
  fold_left (fun g a => adj_set g a (qsuccs tm lset rset q a))
            nodes (PositiveMap.empty _).

Definition fold_edges {B : Type} (nodes : list cconf) (g : Adj)
    (f : B -> cconf -> cconf -> B) (init : B) : B :=
  fold_left (fun acc a => fold_left (fun acc' b => f acc' a b)
                                    (adj_get g a) acc)
            nodes init.

(** ** Reachability and SCCs (Kosaraju, linear in V+E)

    UNTRUSTED (as before): a wrong partition can only make the
    verified lex check reject the certificate, never accept a bad
    one.  The old per-node double-reach partition was O(V*E) per
    round and measured as the census rank tier's dominant cost. *)

Definition rev_adj (nodes : list cconf) (g : Adj) : Adj :=
  fold_edges nodes g
    (fun r a b => adj_set r b (a :: adj_get r b))
    (PositiveMap.empty _).

(** iterative DFS via an explicit enter/exit stack; [out] accumulates
    nodes in finishing order (head = latest finish) *)
Inductive dfs_ev : Type := DfsEnter (v : cconf) | DfsExit (v : cconf).

Fixpoint dfs_order (fuel : nat) (g : Adj) (stack : list dfs_ev)
    (seen : PositiveSet.t) (out : list cconf)
  : PositiveSet.t * list cconf :=
  match fuel with
  | 0 => (seen, out)
  | S f =>
      match stack with
      | [] => (seen, out)
      | DfsExit v :: rest => dfs_order f g rest seen (v :: out)
      | DfsEnter v :: rest =>
          if PositiveSet.mem (nkey v) seen
          then dfs_order f g rest seen out
          else dfs_order f g
                 (map DfsEnter (adj_get g v) ++ DfsExit v :: rest)
                 (PositiveSet.add (nkey v) seen) out
      end
  end.

Definition finish_order (fuel : nat) (nodes : list cconf) (g : Adj)
  : list cconf :=
  snd (fold_left
    (fun '(seen, out) v =>
       if PositiveSet.mem (nkey v) seen then (seen, out)
       else dfs_order fuel g [DfsEnter v] seen out)
    nodes (PositiveSet.empty, [])).

(** one transpose-DFS collection = one component *)
Fixpoint scc_collect (fuel : nat) (g : Adj) (todo : list cconf)
    (seen : PositiveSet.t) (comp : list cconf)
  : PositiveSet.t * list cconf :=
  match fuel with
  | 0 => (seen, comp)
  | S f =>
      match todo with
      | [] => (seen, comp)
      | v :: rest =>
          if PositiveSet.mem (nkey v) seen
          then scc_collect f g rest seen comp
          else scc_collect f g (adj_get g v ++ rest)
                           (PositiveSet.add (nkey v) seen) (v :: comp)
      end
  end.

Definition scc_partition (fuel : nat) (nodes : list cconf) (g : Adj)
  : list (list cconf) :=
  let order := finish_order fuel nodes g in
  let r := rev_adj nodes g in
  rev (snd (fold_left
    (fun '(seen, comps) v =>
       if PositiveSet.mem (nkey v) seen then (seen, comps)
       else let '(seen', comp) := scc_collect fuel r [v] seen [] in
            (seen', comp :: comps))
    order (PositiveSet.empty, []))).

Definition has_self_edge (g : Adj) (v : cconf) : bool :=
  existsb (fun b => Pos.eqb (nkey b) (nkey v)) (adj_get g v).

Definition scc_cyclic (g : Adj) (c : list cconf) : bool :=
  match c with
  | [] => false
  | [v] => has_self_edge g v
  | _ => true
  end.

(** ** Condensation longest-path ranks *)

Definition cid_map (comps : list (list cconf)) : PositiveMap.tree nat :=
  snd (fold_left
    (fun '(i, m) c =>
       (S i, fold_left (fun m' v => PositiveMap.add (nkey v) i m') c m))
    comps (0, PositiveMap.empty nat)).

Definition cid_get (m : PositiveMap.tree nat) (a : cconf) : nat :=
  match PositiveMap.find (nkey a) m with
  | Some i => i | None => 0
  end.

(** condensation ranks in a map keyed by component id (the old
    list-nat + nth/set_nth representation cost O(#comps) per edge) *)
Definition crk_get (m : PositiveMap.tree nat) (i : nat) : nat :=
  match PositiveMap.find (Pos.of_succ_nat i) m with
  | Some v => v | None => 0
  end.

(** [scc_partition] emits components in topological order of the
    condensation (Kosaraju pass 2), so ONE sinks-first pass computes
    the longest-path ranks -- the old fixed-point relaxation was up
    to #comps passes over every edge. *)
Definition crank_comp (g : Adj) (cid : PositiveMap.tree nat)
    (rk : PositiveMap.tree nat) (i : nat) (c : list cconf)
  : PositiveMap.tree nat :=
  let r := fold_left (fun r a =>
             fold_left (fun r b =>
                let ib := cid_get cid b in
                if Nat.eqb i ib then r
                else Nat.max r (S (crk_get rk ib)))
              (adj_get g a) r)
           c 0 in
  PositiveMap.add (Pos.of_succ_nat i) r rk.

Definition condensation_rank (nodes : list cconf) (g : Adj)
    (comps : list (list cconf)) : list (cconf * nat) :=
  let cid := cid_map comps in
  let n := length comps in
  (* comps are source-first; process reversed (sinks first) with the
     matching component ids (cid_map numbers them in list order) *)
  let rk := snd (fold_left
      (fun '(i, rk) c => (pred i, crank_comp g cid rk i c))
      (rev comps) (pred n, PositiveMap.empty nat)) in
  map (fun v => (v, crk_get rk (cid_get cid v))) nodes.

(** node-level longest-path rank for the final acyclic graph: one
    pass over the DFS finish order (descendants finish first, so
    processing earliest-finished first ranks successors before their
    predecessors) *)
Definition node_rank (nodes : list cconf) (g : Adj)
  : list (cconf * nat) :=
  let order := finish_order (S (length nodes * 8 + 8)) nodes g in
  let rk := fold_right
      (fun a rk =>
         let r := fold_left (fun r b =>
                    Nat.max r (S (match PositiveMap.find (nkey b) rk with
                                  | Some v => v | None => 0 end)))
                  (adj_get g a) 0 in
         PositiveMap.add (nkey a) r rk)
      (PositiveMap.empty nat) order in
  map (fun v => (v, match PositiveMap.find (nkey v) rk with
                    | Some x => x | None => 0 end)) nodes.

(** ** Rules (a) and (b) on one cyclic SCC *)

(** intra-SCC edge list of [c] *)
Definition intra_edges (g : Adj) (cset : PositiveSet.t) (c : list cconf)
  : list (cconf * cconf) :=
  concat (map (fun a =>
    map (fun b => (a, b))
        (filter (fun b => PositiveSet.mem (nkey b) cset) (adj_get g a))) c).

Definition cset_of (c : list cconf) : PositiveSet.t :=
  fold_left (fun s v => PositiveSet.add (nkey v) s) c PositiveSet.empty.

(** delete intra edges of [c] whose target predicate holds *)
Definition delete_intra (g : Adj) (cset : PositiveSet.t)
    (c : list cconf) (dead : cconf -> cconf -> bool) : Adj :=
  fold_left (fun g' a =>
    adj_set g' a (filter (fun b => negb (PositiveSet.mem (nkey b) cset &&
                                         dead a b))
                         (adj_get g' a))) c g.

(** rule (a): [m] nonincreasing on every intra edge, decreasing on one *)
Definition try_rule_a (tm : TM) (g : Adj) (cset : PositiveSet.t)
    (c : list cconf) (m : ngmeas) : option (ngcomp * Adj) :=
  let es := intra_edges g cset c in
  let ds := map (fun '(a, b) => ngm_delta tm m a b) es in
  if forallb (fun d => Z.leb d 0) ds && existsb (fun d => Z.ltb d 0) ds
  then Some (NgMeas m 1 [] c,
             delete_intra g cset c
               (fun a b => Z.ltb (ngm_delta tm m a b) 0))
  else None.

(** rule (b): Bellman-Ford potentials for weights Kc*delta + 1 *)
Definition bell_get (d : PositiveMap.tree Z) (a : cconf) : Z :=
  match PositiveMap.find (nkey a) d with
  | Some v => v | None => 0%Z
  end.

Definition bell_pass (tm : TM) (m : ngmeas) (Kc : Z)
    (es : list (cconf * cconf)) (st : PositiveMap.tree Z * bool)
  : PositiveMap.tree Z * bool :=
  fold_left (fun '(dist, ch) '(a, b) =>
    let w := (Kc * ngm_delta tm m a b + 1)%Z in
    let da := bell_get dist a in
    let db := bell_get dist b in
    if Z.ltb (da - w)%Z db
    then (PositiveMap.add (nkey b) ((da - w)%Z) dist, true)
    else (dist, ch)) es st.

Fixpoint bell_iter (fuel : nat) (tm : TM) (m : ngmeas) (Kc : Z)
    (es : list (cconf * cconf)) (dist : PositiveMap.tree Z)
  : option (PositiveMap.tree Z) :=
  match fuel with
  | 0 => None
  | S f =>
      let '(dist', ch) := bell_pass tm m Kc es (dist, false) in
      if ch then bell_iter f tm m Kc es dist' else Some dist'
  end.

Definition try_rule_b (tm : TM) (g : Adj) (cset : PositiveSet.t)
    (c : list cconf) (Kc : nat) (m : ngmeas) : option (ngcomp * Adj) :=
  let es := intra_edges g cset c in
  match bell_iter (S (length c)) tm m (Z.of_nat Kc) es
                  (PositiveMap.empty Z) with
  | None => None
  | Some dist =>
      let vals := map (fun v => bell_get dist v) c in
      let mn := fold_left Z.min vals 0%Z in
      let phi := map (fun v => (v, Z.to_nat (bell_get dist v - mn)%Z)) c in
      Some (NgMeas m Kc phi c,
            delete_intra g cset c (fun _ _ => true))
  end.

Definition measures : list ngmeas := [MAll; MLeft; MRight].

Fixpoint first_some {B : Type} (f : ngmeas -> option B) (l : list ngmeas)
  : option B :=
  match l with
  | [] => None
  | m :: t => match f m with Some x => Some x | None => first_some f t end
  end.

(** process one cyclic SCC: rule (a) over the measures, then rule (b) *)
Definition process_scc (tm : TM) (Kc : nat) (st : Adj * list ngcomp * bool)
    (c : list cconf) : Adj * list ngcomp * bool :=
  let '(g, acc, prog) := st in
  let cset := cset_of c in
  match first_some (try_rule_a tm g cset c) measures with
  | Some (comp, g') => (g', comp :: acc, true)
  | None =>
      match first_some (try_rule_b tm g cset c Kc) measures with
      | Some (comp, g') => (g', comp :: acc, true)
      | None => (g, acc, prog)
      end
  end.

(** ** The per-state procedure *)

Fixpoint proc_rounds (fuel : nat) (tm : TM) (Kc rfuel : nat)
    (nodes : list cconf) (g : Adj) (acc : list ngcomp)
  : option (list ngcomp) :=
  match fuel with
  | 0 => None
  | S f =>
      let comps := scc_partition rfuel nodes g in
      let cyc := filter (scc_cyclic g) comps in
      match cyc with
      | [] => Some (rev (NgRank (node_rank nodes g) :: acc))
      | _ =>
          let acc' := NgRank (condensation_rank nodes g comps) :: acc in
          let '(g', acc'', prog) :=
            fold_left (process_scc tm Kc) cyc (g, acc', false) in
          if prog then proc_rounds f tm Kc rfuel nodes g' acc''
          else None
      end
  end.

Definition rank_procedure (tm : TM) (lset rset : gset)
    (closure : list cconf) (q : St) : list ngcomp :=
  let nodes := filter (fun a => negb (st_eqb (fst a) q)) closure in
  let g := build_adj tm lset rset q nodes in
  let Kc := S (S (length nodes)) in
  let rfuel := S (length nodes * 8 + 8) in
  match proc_rounds 200 tm Kc rfuel nodes g [] with
  | Some comps => comps
  | None => []
  end.

(** ** The census tier *)

Definition rank_tier (tm : TM) (n t fuel rounds : nat) : bool :=
  match csteps tm t c0 with
  | None => false
  | Some cc =>
      let '(q0, (l, h, r)) := cc in
      let lset0 := gadds (ng_seed_side n l) gempty in
      let rset0 := gadds (ng_seed_side n r) gempty in
      let a0 := ng_start n cc in
      let '(lset, rset) := ng_grow tm a0 fuel rounds lset0 rset0 in
      let closure := ng_explore tm lset rset fuel [] PositiveSet.empty [a0] in
      ngram_check_neverqh_lex_with tm n t fuel lset rset
        (fun q => rank_procedure tm lset rset closure q)
  end.

Theorem rank_tier_sound : forall tm n t fuel rounds,
  rank_tier tm n t fuel rounds = true -> NeverQuasiHaltsSt tm.
Proof.
  intros tm n t fuel rounds H.
  unfold rank_tier in H.
  destruct (csteps tm t c0) as [[q0 [[l h] r]]|]; [|discriminate].
  match type of H with
  | (let '(_, _) := ?G in _) = true => destruct G as [lset rset]
  end.
  cbv beta iota zeta in H.
  exact (ngram_check_neverqh_lex_with_sound tm n t fuel lset rset _ H).
Qed.
