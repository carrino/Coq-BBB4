From Coq Require Import Arith Lia List Bool ZArith PArith.
From SmallBB Require Import Statement StatementTr CTape PosEnc Closure ClosureTr RankSearch BellmanFord.
From SmallBB.Checkers Require Import NGram FiniteNGram.
Import ListNotations.
Inductive fncomp := FncRank (phi:list(cconf*nat))
 | FncMeas (m:fnmeas)(K:nat)(phi:list(cconf*nat))(gate:list cconf).
Definition fn_comp_denote tm c : lexcomp cconf :=
 match c with
 | FncRank phi=>LexRank cconf(pmap_get cconf cconf_enc(pmap_of cconf cconf_enc phi))
 | FncMeas m K phi gate=>LexMeas cconf(fnm_val m)(fnm_delta tm m) K
   (pmap_get cconf cconf_enc(pmap_of cconf cconf_enc phi))
   (fun a=>pset_mem cconf cconf_enc a(pset_of cconf cconf_enc gate)) end.
Definition fn_try_rule_a (tm : TM) (g : Adj) (cset : PositiveSet.t)
    (c : list cconf) (m : fnmeas) : option (fncomp * Adj) :=
  let es := intra_edges g cset c in
  let ds := map (fun '(a, b) => fnm_delta tm m a b) es in
  if forallb (fun d => Z.leb d 0) ds && existsb (fun d => Z.ltb d 0) ds
  then Some (FncMeas m 1 [] c,
             delete_intra g cset c
               (fun a b => Z.ltb (fnm_delta tm m a b) 0))
  else None.

(** rule (b): Bellman-Ford potentials for weights Kc*delta + 1 *)
Definition fn_bell_get (d : PositiveMap.tree Z) (a : cconf) : Z :=
  match PositiveMap.find (nkey a) d with
  | Some v => v | None => 0%Z
  end.

Definition fn_bell_pass (tm : TM) (m : fnmeas) (Kc : Z)
    (es : list (cconf * cconf)) (st : PositiveMap.tree Z * bool)
  : PositiveMap.tree Z * bool :=
  fold_left (fun '(dist, ch) '(a, b) =>
    let w := (Kc * fnm_delta tm m a b + 1)%Z in
    let da := fn_bell_get dist a in
    let db := fn_bell_get dist b in
    if Z.ltb (da - w)%Z db
    then (PositiveMap.add (nkey b) ((da - w)%Z) dist, true)
    else (dist, ch)) es st.

Fixpoint fn_bell_iter (fuel : nat) (tm : TM) (m : fnmeas) (Kc : Z)
    (es : list (cconf * cconf)) (dist : PositiveMap.tree Z)
  : option (PositiveMap.tree Z) :=
  match fuel with
  | 0 => None
  | S f =>
      let '(dist', ch) := fn_bell_pass tm m Kc es (dist, false) in
      if ch then fn_bell_iter f tm m Kc es dist' else Some dist'
  end.

Definition fn_ng_bad_self tm m Kc es :=
  bad_self cconf nkey (fun a b => (Kc * fnm_delta tm m a b + 1)%Z) es.
Lemma fn_bell_pass_self_spec : forall tm m Kc es st,
  fn_bell_pass tm m Kc es st =
  fold_left (self_relax cconf nkey (fun a b => (Kc * fnm_delta tm m a b + 1)%Z)) es st.
Proof.
  intros tm m Kc es. induction es as [|[a b] es IH]; intros [dist ch]; [reflexivity|].
  unfold fn_bell_pass in *. cbn [fold_left].
  rewrite IH. reflexivity.
Qed.
Lemma fn_bell_iter_bad_self : forall fuel tm m Kc es dist,
  fn_ng_bad_self tm m Kc es = true -> fn_bell_iter fuel tm m Kc es dist = None.
Proof.
  induction fuel as [|fuel IH]; intros tm m Kc es dist H; [reflexivity|].
  assert (E : snd (fn_bell_pass tm m Kc es (dist,false)) = true).
  { rewrite fn_bell_pass_self_spec. apply self_pass_bad. exact H. }
  cbn [fn_bell_iter]. destruct (fn_bell_pass tm m Kc es (dist,false)) as [d' ch].
  cbn in E. subst ch. apply IH. exact H.
Qed.

Definition fn_try_rule_b_reference (tm : TM) (g : Adj) (cset : PositiveSet.t)
    (c : list cconf) (Kc : nat) (m : fnmeas) : option (fncomp * Adj) :=
  let es := intra_edges g cset c in
  match fn_bell_iter (S (length c)) tm m (Z.of_nat Kc) es
                  (PositiveMap.empty Z) with
  | None => None
  | Some dist =>
      let vals := map (fun v => fn_bell_get dist v) c in
      let mn := fold_left Z.min vals 0%Z in
      let phi := map (fun v => (v, Z.to_nat (fn_bell_get dist v - mn)%Z)) c in
      Some (FncMeas m Kc phi c,
            delete_intra g cset c (fun _ _ => true))
  end.

Definition fn_try_rule_b (tm : TM) (g : Adj) (cset : PositiveSet.t)
    (c : list cconf) (Kc : nat) (m : fnmeas) : option (fncomp * Adj) :=
  let es := intra_edges g cset c in
  if fn_ng_bad_self tm m (Z.of_nat Kc) es then None else
  match fn_bell_iter (S (length c)) tm m (Z.of_nat Kc) es
                  (PositiveMap.empty Z) with
  | None => None
  | Some dist =>
      let vals := map (fun v => fn_bell_get dist v) c in
      let mn := fold_left Z.min vals 0%Z in
      let phi := map (fun v => (v, Z.to_nat (fn_bell_get dist v - mn)%Z)) c in
      Some (FncMeas m Kc phi c,
            delete_intra g cset c (fun _ _ => true))
  end.

Lemma fn_try_rule_b_spec : forall tm g cset c Kc m,
  fn_try_rule_b tm g cset c Kc m = fn_try_rule_b_reference tm g cset c Kc m.
Proof.
  intros. unfold fn_try_rule_b, fn_try_rule_b_reference.
  destruct (fn_ng_bad_self tm m (Z.of_nat Kc) (intra_edges g cset c)) eqn:E; [|reflexivity].
  rewrite fn_bell_iter_bad_self by exact E. reflexivity.
Qed.

Definition fn_measures : list fnmeas := [FnCount (MAll C1); FnCount (MLeft C1); FnCount (MRight C1); FnCount (MAll C2); FnCount (MLeft C2); FnCount (MRight C2); FnCount (MAll CN); FnCount (MLeft CN); FnCount (MRight CN); FnSpanL; FnSpanR].

Fixpoint fn_first_some {B : Type} (f : fnmeas -> option B) (l : list fnmeas)
  : option B :=
  match l with
  | [] => None
  | m :: t => match f m with Some x => Some x | None => fn_first_some f t end
  end.

(** process one cyclic SCC: rule (a) over the fn_measures, then rule (b) *)
Definition fn_process_scc (tm : TM) (Kc : nat) (st : Adj * list fncomp * bool)
    (c : list cconf) : Adj * list fncomp * bool :=
  let '(g, acc, prog) := st in
  let cset := cset_of c in
  match fn_first_some (fn_try_rule_a tm g cset c) fn_measures with
  | Some (comp, g') => (g', comp :: acc, true)
  | None =>
      match fn_first_some (fn_try_rule_b tm g cset c Kc) fn_measures with
      | Some (comp, g') => (g', comp :: acc, true)
      | None => (g, acc, prog)
      end
  end.

(** ** The per-state procedure *)

Fixpoint fn_proc_rounds (fuel : nat) (tm : TM) (Kc rfuel : nat)
    (nodes : list cconf) (g : Adj) (acc : list fncomp)
  : option (list fncomp) :=
  match fuel with
  | 0 => None
  | S f =>
      let comps := scc_partition rfuel nodes g in
      let cyc := filter (scc_cyclic g) comps in
      match cyc with
      | [] => Some (rev (FncRank (node_rank nodes g) :: acc))
      | _ =>
          let acc' := FncRank (condensation_rank nodes g comps) :: acc in
          let '(g', acc'', prog) :=
            fold_left (fn_process_scc tm Kc) cyc (g, acc', false) in
          if prog then fn_proc_rounds f tm Kc rfuel nodes g' acc''
          else None
      end
  end.


Definition fn_rank_procedure tm n ls rs (Sl:list cconf) (is_target:cconf->bool) :=
 let nodes:=filter(fun a=>negb(is_target a))Sl in
 let g:=fold_left(fun g a=>adj_set g a
   (match fn_succs tm n ls rs a with Some l=>filter(fun b=>negb(is_target b))l|None=>[]end))
   nodes(PositiveMap.empty _)in
 match fn_proc_rounds 200 tm (S(S(length nodes)))(S(length nodes*8+8))nodes g []with
 |Some cs=>cs|None=>[]end.
