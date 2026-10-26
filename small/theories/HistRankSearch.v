(** History-refined search, adapted from RankSearch; candidates are rechecked. *)
From Coq Require Import Arith Lia Bool List ZArith PArith.
From SmallBB Require Import Statement StatementTr CTape PosEnc Closure ClosureTr BellmanFord.
From SmallBB.Checkers Require Import NGram NGramHist.
Import ListNotations.
Definition hainstr (a:hcconf) := cinstr(hproj a).
Definition hndelta tm m a b := ngm_delta tm m(hproj a)(hproj b).
Inductive hncomp := HnRank (phi:list(hcconf*nat))
 | HnMeas (m:ngmeas)(K:nat)(phi:list(hcconf*nat))(gate:list hcconf).
Definition hn_comp_denote tm c : lexcomp hcconf :=
 match c with
 | HnRank phi=>LexRank hcconf(pmap_get hcconf hctx_enc(pmap_of hcconf hctx_enc phi))
 | HnMeas m K phi gate=>LexMeas hcconf(ngm_val m)(hndelta tm m) K
   (pmap_get hcconf hctx_enc(pmap_of hcconf hctx_enc phi))
   (fun a=>pset_mem hcconf hctx_enc a(pset_of hcconf hctx_enc gate)) end.
Definition nkey (a : hcconf) : positive := hctx_enc a.

Definition Adj : Type := PositiveMap.tree (list hcconf).

Definition adj_get (g : Adj) (a : hcconf) : list hcconf :=
  match PositiveMap.find (nkey a) g with
  | Some l => l
  | None => []
  end.

Definition adj_set (g : Adj) (a : hcconf) (l : list hcconf) : Adj :=
  PositiveMap.add (nkey a) l g.

Definition fold_edges {B : Type} (nodes : list hcconf) (g : Adj)
    (f : B -> hcconf -> hcconf -> B) (init : B) : B :=
  fold_left (fun acc a => fold_left (fun acc' b => f acc' a b)
                                    (adj_get g a) acc)
            nodes init.

(** ** Reachability and SCCs (Kosaraju, linear in V+E)

    UNTRUSTED (as before): a wrong partition can only make the
    verified lex check reject the certificate, never accept a bad
    one.  The old per-node double-reach partition was O(V*E) per
    round and measured as the census rank tier's dominant cost. *)

Definition rev_adj (nodes : list hcconf) (g : Adj) : Adj :=
  fold_edges nodes g
    (fun r a b => adj_set r b (a :: adj_get r b))
    (PositiveMap.empty _).

(** iterative DFS via an explicit enter/exit stack; [out] accumulates
    nodes in finishing order (head = latest finish) *)
Inductive dfs_ev : Type := DfsEnter (v : hcconf) | DfsExit (v : hcconf).

Fixpoint dfs_order (fuel : nat) (g : Adj) (stack : list dfs_ev)
    (seen : PositiveSet.t) (out : list hcconf)
  : PositiveSet.t * list hcconf :=
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

Definition finish_order (fuel : nat) (nodes : list hcconf) (g : Adj)
  : list hcconf :=
  snd (fold_left
    (fun '(seen, out) v =>
       if PositiveSet.mem (nkey v) seen then (seen, out)
       else dfs_order fuel g [DfsEnter v] seen out)
    nodes (PositiveSet.empty, [])).

(** one transpose-DFS collection = one component *)
Fixpoint scc_collect (fuel : nat) (g : Adj) (todo : list hcconf)
    (seen : PositiveSet.t) (comp : list hcconf)
  : PositiveSet.t * list hcconf :=
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

Definition scc_partition (fuel : nat) (nodes : list hcconf) (g : Adj)
  : list (list hcconf) :=
  let order := finish_order fuel nodes g in
  let r := rev_adj nodes g in
  rev (snd (fold_left
    (fun '(seen, comps) v =>
       if PositiveSet.mem (nkey v) seen then (seen, comps)
       else let '(seen', comp) := scc_collect fuel r [v] seen [] in
            (seen', comp :: comps))
    order (PositiveSet.empty, []))).

Definition has_self_edge (g : Adj) (v : hcconf) : bool :=
  existsb (fun b => Pos.eqb (nkey b) (nkey v)) (adj_get g v).

Definition scc_cyclic (g : Adj) (c : list hcconf) : bool :=
  match c with
  | [] => false
  | [v] => has_self_edge g v
  | _ => true
  end.

(** ** Condensation longest-path ranks *)

Definition cid_map (comps : list (list hcconf)) : PositiveMap.tree nat :=
  snd (fold_left
    (fun '(i, m) c =>
       (S i, fold_left (fun m' v => PositiveMap.add (nkey v) i m') c m))
    comps (0, PositiveMap.empty nat)).

Definition cid_get (m : PositiveMap.tree nat) (a : hcconf) : nat :=
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
    (rk : PositiveMap.tree nat) (i : nat) (c : list hcconf)
  : PositiveMap.tree nat :=
  let r := fold_left (fun r a =>
             fold_left (fun r b =>
                let ib := cid_get cid b in
                if Nat.eqb i ib then r
                else Nat.max r (S (crk_get rk ib)))
              (adj_get g a) r)
           c 0 in
  PositiveMap.add (Pos.of_succ_nat i) r rk.

Definition condensation_rank (nodes : list hcconf) (g : Adj)
    (comps : list (list hcconf)) : list (hcconf * nat) :=
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
Definition node_rank (nodes : list hcconf) (g : Adj)
  : list (hcconf * nat) :=
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
Definition intra_edges (g : Adj) (cset : PositiveSet.t) (c : list hcconf)
  : list (hcconf * hcconf) :=
  concat (map (fun a =>
    map (fun b => (a, b))
        (filter (fun b => PositiveSet.mem (nkey b) cset) (adj_get g a))) c).

Definition cset_of (c : list hcconf) : PositiveSet.t :=
  fold_left (fun s v => PositiveSet.add (nkey v) s) c PositiveSet.empty.

(** delete intra edges of [c] whose target predicate holds *)
Definition delete_intra (g : Adj) (cset : PositiveSet.t)
    (c : list hcconf) (dead : hcconf -> hcconf -> bool) : Adj :=
  fold_left (fun g' a =>
    adj_set g' a (filter (fun b => negb (PositiveSet.mem (nkey b) cset &&
                                         dead a b))
                         (adj_get g' a))) c g.

(** rule (a): [m] nonincreasing on every intra edge, decreasing on one *)
Definition try_rule_a (tm : TM) (g : Adj) (cset : PositiveSet.t)
    (c : list hcconf) (m : ngmeas) : option (hncomp * Adj) :=
  let es := intra_edges g cset c in
  let ds := map (fun '(a, b) => hndelta tm m a b) es in
  if forallb (fun d => Z.leb d 0) ds && existsb (fun d => Z.ltb d 0) ds
  then Some (HnMeas m 1 [] c,
             delete_intra g cset c
               (fun a b => Z.ltb (hndelta tm m a b) 0))
  else None.

(** rule (b): Bellman-Ford potentials for weights Kc*delta + 1 *)
Definition bell_get (d : PositiveMap.tree Z) (a : hcconf) : Z :=
  match PositiveMap.find (nkey a) d with
  | Some v => v | None => 0%Z
  end.

Definition bell_pass (tm : TM) (m : ngmeas) (Kc : Z)
    (es : list (hcconf * hcconf)) (st : PositiveMap.tree Z * bool)
  : PositiveMap.tree Z * bool :=
  fold_left (fun '(dist, ch) '(a, b) =>
    let w := (Kc * hndelta tm m a b + 1)%Z in
    let da := bell_get dist a in
    let db := bell_get dist b in
    if Z.ltb (da - w)%Z db
    then (PositiveMap.add (nkey b) ((da - w)%Z) dist, true)
    else (dist, ch)) es st.

Fixpoint bell_iter (fuel : nat) (tm : TM) (m : ngmeas) (Kc : Z)
    (es : list (hcconf * hcconf)) (dist : PositiveMap.tree Z)
  : option (PositiveMap.tree Z) :=
  match fuel with
  | 0 => None
  | S f =>
      let '(dist', ch) := bell_pass tm m Kc es (dist, false) in
      if ch then bell_iter f tm m Kc es dist' else Some dist'
  end.

Definition ng_bad_self tm m Kc es :=
  bad_self hcconf nkey (fun a b => (Kc * hndelta tm m a b + 1)%Z) es.
Lemma bell_pass_self_spec : forall tm m Kc es st,
  bell_pass tm m Kc es st =
  fold_left (self_relax hcconf nkey (fun a b => (Kc * hndelta tm m a b + 1)%Z)) es st.
Proof.
  intros tm m Kc es. induction es as [|[a b] es IH]; intros [dist ch]; [reflexivity|].
  unfold bell_pass in *. cbn [fold_left].
  rewrite IH. reflexivity.
Qed.
Lemma bell_iter_bad_self : forall fuel tm m Kc es dist,
  ng_bad_self tm m Kc es = true -> bell_iter fuel tm m Kc es dist = None.
Proof.
  induction fuel as [|fuel IH]; intros tm m Kc es dist H; [reflexivity|].
  assert (E : snd (bell_pass tm m Kc es (dist,false)) = true).
  { rewrite bell_pass_self_spec. apply self_pass_bad. exact H. }
  cbn [bell_iter]. destruct (bell_pass tm m Kc es (dist,false)) as [d' ch].
  cbn in E. subst ch. apply IH. exact H.
Qed.

Definition try_rule_b_reference (tm : TM) (g : Adj) (cset : PositiveSet.t)
    (c : list hcconf) (Kc : nat) (m : ngmeas) : option (hncomp * Adj) :=
  let es := intra_edges g cset c in
  match bell_iter (S (length c)) tm m (Z.of_nat Kc) es
                  (PositiveMap.empty Z) with
  | None => None
  | Some dist =>
      let vals := map (fun v => bell_get dist v) c in
      let mn := fold_left Z.min vals 0%Z in
      let phi := map (fun v => (v, Z.to_nat (bell_get dist v - mn)%Z)) c in
      Some (HnMeas m Kc phi c,
            delete_intra g cset c (fun _ _ => true))
  end.

Definition try_rule_b (tm : TM) (g : Adj) (cset : PositiveSet.t)
    (c : list hcconf) (Kc : nat) (m : ngmeas) : option (hncomp * Adj) :=
  let es := intra_edges g cset c in
  if ng_bad_self tm m (Z.of_nat Kc) es then None else
  match bell_iter (S (length c)) tm m (Z.of_nat Kc) es
                  (PositiveMap.empty Z) with
  | None => None
  | Some dist =>
      let vals := map (fun v => bell_get dist v) c in
      let mn := fold_left Z.min vals 0%Z in
      let phi := map (fun v => (v, Z.to_nat (bell_get dist v - mn)%Z)) c in
      Some (HnMeas m Kc phi c,
            delete_intra g cset c (fun _ _ => true))
  end.

Lemma try_rule_b_spec : forall tm g cset c Kc m,
  try_rule_b tm g cset c Kc m = try_rule_b_reference tm g cset c Kc m.
Proof.
  intros. unfold try_rule_b, try_rule_b_reference.
  destruct (ng_bad_self tm m (Z.of_nat Kc) (intra_edges g cset c)) eqn:E; [|reflexivity].
  rewrite bell_iter_bad_self by exact E. reflexivity.
Qed.

Definition measures : list ngmeas := [MAll C1; MLeft C1; MRight C1; MAll C2; MLeft C2; MRight C2; MAll CN; MLeft CN; MRight CN].

Fixpoint first_some {B : Type} (f : ngmeas -> option B) (l : list ngmeas)
  : option B :=
  match l with
  | [] => None
  | m :: t => match f m with Some x => Some x | None => first_some f t end
  end.

(** process one cyclic SCC: rule (a) over the measures, then rule (b) *)
Definition process_scc (tm : TM) (Kc : nat) (st : Adj * list hncomp * bool)
    (c : list hcconf) : Adj * list hncomp * bool :=
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
    (nodes : list hcconf) (g : Adj) (acc : list hncomp)
  : option (list hncomp) :=
  match fuel with
  | 0 => None
  | S f =>
      let comps := scc_partition rfuel nodes g in
      let cyc := filter (scc_cyclic g) comps in
      match cyc with
      | [] => Some (rev (HnRank (node_rank nodes g) :: acc))
      | _ =>
          let acc' := HnRank (condensation_rank nodes g comps) :: acc in
          let '(g', acc'', prog) :=
            fold_left (process_scc tm Kc) cyc (g, acc', false) in
          if prog then proc_rounds f tm Kc rfuel nodes g' acc''
          else None
      end
  end.

Definition hn_rank_procedure tm k n ls rs Sl (target:hcconf->bool) :=
 let nodes:=filter(fun a=>negb(target a))Sl in
 let g:=fold_left(fun g a=>adj_set g a(match hng_succs tm k n ls rs a with
 |Some l=>filter(fun b=>negb(target b))l |None=>[]end))nodes(PositiveMap.empty _)in
 match proc_rounds 200 tm (S(S(length nodes)))(S(length nodes*8+8))nodes g []with
 |Some cs=>cs |None=>[]end.
Definition hgadd w s := if hgmem w s then s else w::s.
Definition hseed_side n l := map(fun d=>hwin(hlift_side l)d n)(seq 1(S(length l))).
Fixpoint hn_explore tm k n ls rs fuel (Sl:list hcconf) seen todo :=
 match fuel,todo with
 |S f,a::todo=>if PositiveSet.mem(hctx_enc a)seen then hn_explore tm k n ls rs f Sl seen todo else
   hn_explore tm k n ls rs f(a::Sl)(PositiveSet.add(hctx_enc a)seen)
     (match hng_succs tm k n ls rs a with Some l=>l++todo |None=>todo end)
 |_,_=>Sl end.
Definition hn_harvest (tm:TM) (a:hcconf) sets := let '(q,(l,h,r)):=a in let '(ls,rs):=sets in
 match tm q(hbit h)with
 |Some tr=>match t_dir tr with DR=>(hgadd l ls,rs)|DL=>(ls,hgadd r rs)end
 |None=>sets end.
Fixpoint hn_grow tm k n a0 fuel rounds ls rs :=
 match rounds with
 |0=>(ls,rs)
 |S rounds=>let nodes:=hn_explore tm k n ls rs fuel [] PositiveSet.empty[a0]in
   let '(ls',rs'):=fold_left(fun sets a=>hn_harvest tm a sets)nodes(ls,rs)in
   if (length ls'=?length ls)&&(length rs'=?length rs)then(ls,rs)
   else hn_grow tm k n a0 fuel rounds ls' rs' end.
