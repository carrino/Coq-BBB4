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

(** ** Reachability and SCCs (quadratic, sizes are small) *)

Fixpoint rreach_iter (fuel : nat) (g : RAdj) (todo : list rconf)
    (seen : PositiveSet.t) : PositiveSet.t :=
  match fuel with
  | 0 => seen
  | S f =>
      match todo with
      | [] => seen
      | a :: rest =>
          if PositiveSet.mem (rkey a) seen
          then rreach_iter f g rest seen
          else rreach_iter f g (radj_get g a ++ rest)
                           (PositiveSet.add (rkey a) seen)
      end
  end.

Definition rreach (fuel : nat) (g : RAdj) (a : rconf) : PositiveSet.t :=
  rreach_iter fuel g [a] PositiveSet.empty.

Definition rrev_adj (nodes : list rconf) (g : RAdj) : RAdj :=
  rfold_edges nodes g
    (fun r a b => radj_set r b (a :: radj_get r b))
    (PositiveMap.empty _).

(** SCC of [v] = forward-reachable /\ backward-reachable *)
Definition rscc_partition (fuel : nat) (nodes : list rconf) (g : RAdj)
  : list (list rconf) :=
  let r := rrev_adj nodes g in
  snd (fold_left
    (fun '(done, comps) v =>
       if PositiveSet.mem (rkey v) done then (done, comps)
       else
         let fwd := rreach fuel g v in
         let bwd := rreach fuel r v in
         let comp := filter (fun u => PositiveSet.mem (rkey u) fwd &&
                                      PositiveSet.mem (rkey u) bwd) nodes in
         (fold_left (fun d u => PositiveSet.add (rkey u) d) comp done,
          comp :: comps))
    nodes (PositiveSet.empty, [])).

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

Fixpoint rset_nth (l : list nat) (i v : nat) : list nat :=
  match l, i with
  | [], _ => []
  | _ :: t, 0 => v :: t
  | h :: t, S j => h :: rset_nth t j v
  end.

(** one relaxation pass over all alive edges; returns (ranks, changed) *)
Definition rcrank_pass (nodes : list rconf) (g : RAdj)
    (cid : PositiveMap.tree nat) (st : list nat * bool)
  : list nat * bool :=
  rfold_edges nodes g
    (fun '(rk, ch) a b =>
       let ia := rcid_get cid a in
       let ib := rcid_get cid b in
       if Nat.eqb ia ib then (rk, ch)
       else if Nat.ltb (nth ia rk 0) (S (nth ib rk 0))
            then (rset_nth rk ia (S (nth ib rk 0)), true)
            else (rk, ch))
    st.

Fixpoint rcrank_iter (fuel : nat) (nodes : list rconf) (g : RAdj)
    (cid : PositiveMap.tree nat) (rk : list nat) : list nat :=
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
                        (repeat 0 (length comps)) in
  map (fun v => (rkey v, nth (rcid_get cid v) rk 0)) nodes.

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

Definition rw_procedure (tm : TM) (L T : nat)
    (closure : list rconf) (q : St) : list rwcomp :=
  let nodes := filter (fun a => negb (st_eqb (rw_state a) q)) closure in
  let g := rbuild_adj tm L T q nodes in
  let Kc := S (S (length nodes)) in
  let rfuel := S (length nodes * 4 + 4) in
  match rproc_rounds 300 tm Kc rfuel nodes g [] with
  | Some comps => comps
  | None => []
  end.

(** ** The census tier

    Parameter-closed: one (L, T, t) rung builds the closure, runs the
    search per premise state (prefix-visited or appearing, mirroring
    the checker's [implb] guard so absent states don't trigger a
    doomed search), and feeds the EXISTING verified checker.  The
    checker re-derives the closure and re-checks every edge, so the
    search carries no soundness. *)

Definition rw_tier (tm : TM) (L T t fuel : nat) : bool :=
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

Theorem rw_tier_sound : forall tm L T t fuel,
  rw_tier tm L T t fuel = true -> NeverQuasiHaltsSt tm.
Proof.
  intros tm L T t fuel H.
  unfold rw_tier in H.
  destruct (csteps tm t c0) as [cc|]; [|discriminate].
  destruct (close rconf rconf_enc (rw_succs tm L T) fuel
                  [] PositiveSet.empty [rw_seed L T cc]) as [Sl|];
    [|discriminate].
  exact (rw_check_neverqh_sound tm L T t fuel _ H).
Qed.
