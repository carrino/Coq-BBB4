(** * IRules.Reblock: denotation-preserving cell re-blocking for the
    v5-gap engine extension (gap 2).

    A family of BBB-verified never-QH certificates (the "v5 rule-replay
    gap", second corner) needs the meta-cycle replay to re-encode a
    concrete near-head run of single-cell runs back into multi-cell
    block runs -- e.g. [b0.b1^4.b0^4.b1^4...] coalescing into [b2^2] --
    so that a certificate rule matches (the landed [beng_stepS] otherwise
    stalls at a variable-block boundary).  This mirrors the C verifier's
    [iv_reblock_side] / [iv_enc_side] canonicalization.

    The greedy factorization ([reblock_side]) is UNTRUSTED search output
    -- soundness never depends on it being correct.  [breblock_side]
    accepts the candidate ONLY when [RulesBlk.bstreams_eq] re-verifies it
    denotes the same cells (the affected prefix is all constant-count, so
    [bstreams_eq] decides it), exactly the "untrusted candidate, verified
    by bstreams" pattern of [bcanon].  [breblock_cfg_bsemX] is the one
    new lemma; its axiom footprint is [functional_extensionality_dep]
    only (it is discharged from [bstreams_eq_sound]). *)

From Coq Require Import ZArith List Bool Arith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers.IRules Require Import Expr RLE Engine EngineK RulesBlk
     EngineKS.
Import ListNotations.
Open Scope Z_scope.

(** ** The untrusted greedy factorization (mirror of iv_enc_side) *)

Fixpoint lsymeqb (a b : list Sym) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => sym_eqb x y && lsymeqb a' b'
  | _, _ => false
  end.

Definition has_period (w : list Sym) (p : nat) : bool :=
  forallb (fun i => sym_eqb (nth i w S0) (nth (Nat.modulo i p) w S0))
          (seq 0 (length w)).

Definition primitive (w : list Sym) : bool :=
  negb (existsb (fun p => (Nat.eqb (Nat.modulo (length w) p) 0) && has_period w p)
                (seq 1 (length w - 1))).

Fixpoint count_reps (w buf : list Sym) (fuel : nat) : nat :=
  match fuel with
  | O => O
  | S f =>
      if (Nat.leb (length w) (length buf)) && lsymeqb w (firstn (length w) buf)
      then S (count_reps w (skipn (length w) buf) f) else O
  end.

Definition find_blk (blks : list (nat * list Sym)) (w : list Sym) : option nat :=
  match filter (fun p => lsymeqb (snd p) w) blks with
  | (id, _) :: _ => Some id
  | [] => None
  end.

Fixpoint lead_sym_run (c : Sym) (buf : list Sym) : nat :=
  match buf with
  | [] => O
  | x :: t => if sym_eqb x c then S (lead_sym_run c t) else O
  end.

Definition cell_to_blk (c : Sym) : nat := match c with S0 => 0 | S1 => 1 end.

Definition try_block (blks : list (nat * list Sym)) (buf : list Sym) (L : nat)
  : option (nat * nat * nat) :=
  let w := firstn L buf in
  if (Nat.leb (2 * L) (length buf)) && primitive w then
    let r := count_reps w buf (S (length buf)) in
    if (Nat.leb 2 r) && (Nat.leb 16 (r * L)) then
      match find_blk blks w with Some id => Some (id, r, L) | None => None end
    else None
  else None.

Fixpoint first_block (blks : list (nat * list Sym)) (buf : list Sym)
    (Ls : list nat) : option (nat * nat * nat) :=
  match Ls with
  | [] => None
  | L :: t =>
      match try_block blks buf L with
      | Some x => Some x
      | None => first_block blks buf t
      end
  end.

Fixpoint enc_side (blks : list (nat * list Sym)) (buf : list Sym) (fuel : nat)
  : option (list BRun) :=
  match fuel with
  | O => None
  | S f =>
      match buf with
      | [] => Some []
      | c0 :: _ =>
          match first_block blks buf [2;3;4;5;6;7;8]%nat with
          | Some (id, r, L) =>
              match enc_side blks (skipn (r * L) buf) f with
              | Some rest => Some ((id, econst (Z.of_nat r)) :: rest)
              | None => None
              end
          | None =>
              let r := lead_sym_run c0 buf in
              match enc_side blks (skipn r buf) f with
              | Some rest => Some ((cell_to_blk c0, econst (Z.of_nat r)) :: rest)
              | None => None
              end
          end
      end
  end.

Definition const_cell (tbl : BTbl) (r : BRun) : option (Sym * nat) :=
  if cf_zeros (e_cf (snd r)) && Nat.eqb (length (tbl (fst r))) 1
  then Some (hd S0 (tbl (fst r)), Z.to_nat (e_c0 (snd r)))
  else None.

Fixpoint lead_prefix (tbl : BTbl) (rs : list BRun) (fuel : nat)
  : (list Sym * list BRun) :=
  match fuel, rs with
  | S f, r :: t =>
      match const_cell tbl r with
      | Some (c, n) => let p := lead_prefix tbl t f in (repeat c n ++ fst p, snd p)
      | None => ([], r :: t)
      end
  | _, _ => ([], rs)
  end.

Definition reblock_side (tbl : BTbl) (blks : list (nat * list Sym))
    (rs : list BRun) : list BRun :=
  let p := lead_prefix tbl rs (length rs) in
  match enc_side blks (fst p) (S (length (fst p))) with
  | Some enc => enc ++ snd p
  | None => rs
  end.

(** ** The verified re-block (soundness surface) *)

Definition breblock_side (lo : list Z) (tbl : BTbl)
    (blks : list (nat * list Sym)) (rs : list BRun) : list BRun :=
  let cand := reblock_side tbl blks rs in
  if bstreams_eq tbl lo rs cand then cand else rs.

Lemma breblock_side_den : forall lo tbl blks rs nu,
  raw_ok tbl -> bge lo nu ->
  bdside tbl nu (breblock_side lo tbl blks rs) = bdside tbl nu rs.
Proof.
  intros lo tbl blks rs nu Hraw Hb. unfold breblock_side.
  destruct (bstreams_eq tbl lo rs (reblock_side tbl blks rs)) eqn:Hv.
  - symmetry. exact (bstreams_eq_sound tbl lo rs _ nu Hraw Hb Hv).
  - reflexivity.
Qed.

Definition breblock_cfg (lo : list Z) (tbl : BTbl)
    (blks : list (nat * list Sym)) (c : BCfg) : BCfg :=
  mkBCfg (b_st c) (b_hs c)
         (breblock_side lo tbl blks (b_L c))
         (breblock_side lo tbl blks (b_R c)).

Lemma breblock_cfg_bsemX : forall lo tbl blks c nu XL XR,
  raw_ok tbl -> bge lo nu ->
  bsemX tbl nu (breblock_cfg lo tbl blks c) XL XR = bsemX tbl nu c XL XR.
Proof.
  intros lo tbl blks c nu XL XR Hraw Hb. unfold breblock_cfg, bsemX.
  cbn [b_st b_hs b_L b_R].
  rewrite !(breblock_side_den lo tbl blks _ nu Hraw Hb). reflexivity.
Qed.
