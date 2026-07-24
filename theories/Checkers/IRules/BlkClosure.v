(** * IRules.BlkClosure: untrusted block-hop closure for the v5c engine.

    The Phase-2 block engine's clean crossing ([EngineK.bhop_result])
    resolves a block hop only when the crossed output word's primitive
    root is a declared block in the table [blks] (via [blk_find]).  For
    a family of BBB-verified never-QH machines (the "v5 gap", third
    corner) the crossed output is a ROTATION of a declared block that is
    not itself in the table -- e.g. crossing [b10 = [S1;S1;S1;S1;S0]] in
    state [StC] yields [[S0;S1;S1;S0;S1]], a rotation of [b9], which
    [blk_find] misses -- so [bhop_result] returns [None] and the replay
    stalls, where the C verifier (whose emitted table already contains
    the rotation) crosses cleanly.

    [blk_closure] is UNTRUSTED preprocessing: it augments [blks] with
    the primitive-root words that block hops can produce, using fresh
    ids.  Soundness NEVER depends on it: [bhop_result] re-verifies every
    hop against the trusted-only-for-soundness table [mk_tbl blks]
    ([bhop_result_spec] proves [nreps (tbl nsym) factor = hout]), and
    the whole checker chain is parametric in [blks] with its soundness
    resting only on [raw_ok (mk_tbl blks)] -- which [mk_tbl_raw] gives
    for ANY block list.  So closing the table can only make the engine
    accept MORE crossings, never an unsound one.  There is nothing to
    prove here beyond termination (a [fuel] bound). *)

From Coq Require Import Arith ZArith Bool List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers.IRules Require Import Expr RLE Engine EngineK RulesBlk
     MetaBlk.
Import ListNotations.
Open Scope Z_scope.

Fixpoint blk_find_opt (blks : list (nat * list Sym)) (w : list Sym)
  : option nat :=
  match blks with
  | [] => None
  | (i, cs) :: t => if lsym_eqb cs w then Some i else blk_find_opt t w
  end.

Definition max_id (blks : list (nat * list Sym)) : nat :=
  fold_left (fun m p => Nat.max m (fst p)) blks O.

(** The primitive-root output word a clean block hop from [q]/[mv] over
    block [s] produces (only when it is a genuine multi-cell block). *)
Definition hop_root (tm : TM) (tbl : BTbl) (q : St) (mv : Dir) (s : BSym)
  : option (list Sym) :=
  match tbl s with
  | [] => None
  | c :: cs =>
      match hop_sim tm q mv 1024 q [] c cs with
      | Some (hout, _) =>
          let r := firstn (prim_root_len hout) hout in
          if (2 <=? length r)%nat then Some r else None
      | None => None
      end
  end.

Definition dirs : list Dir := [DL; DR].

Definition closure_pass (tm : TM) (blks : list (nat * list Sym))
    (ids : list nat) : list (nat * list Sym) :=
  let tbl := mk_tbl blks in
  let cands :=
    flat_map (fun s =>
      flat_map (fun q =>
        flat_map (fun mv =>
          match hop_root tm tbl q mv s with
          | Some r => [r] | None => [] end) dirs) all_St) ids in
  let add := fold_left (fun acc r =>
      match blk_find_opt (blks ++ acc) r with
      | Some _ => acc
      | None => acc ++ [(S (max_id (blks ++ acc)), r)]
      end) cands [] in
  blks ++ add.

Definition blk_ids (blks : list (nat * list Sym)) : list nat :=
  map (@fst nat (list Sym)) blks.

Fixpoint blk_closure (tm : TM) (blks : list (nat * list Sym)) (fuel : nat)
  : list (nat * list Sym) :=
  match fuel with
  | O => blks
  | S f =>
      let blks' := closure_pass tm blks (blk_ids blks) in
      if Nat.eqb (length blks') (length blks) then blks'
      else blk_closure tm blks' f
  end.
