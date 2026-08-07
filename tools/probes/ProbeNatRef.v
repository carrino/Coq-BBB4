(** HISTORICAL: this file validated the unary-nat -> binary-N scan
    conversion (commit fe1e283) by diffing candidate lists against a
    reference copy of the ORIGINAL nat implementation.  The candidate
    rule has since changed deliberately (exact records + cycle twins,
    replacing the approximate lp_rec_cands), so re-running it now
    reports divergence BY DESIGN.  Keep for the record; do not use as
    a gate. *)
(* The ORIGINAL unary-nat scan, self-contained, as a reference for the
   binary-N rewrite.  Diffs lp_candidates over real machines. *)
From Coq Require Import Arith Bool List NArith ZArith.
From BBB4 Require Import BBB4_Statement CTape ProbeWalkCommon ProbeTierBig.
From BBB4.Census Require Import TNF_QH Decide.
Import ListNotations.

Record ent := mkEnt { eq_ : St; es : Sym; ep : Z;
                      err : bool; el : bool; ek : nat }.

Fixpoint run (tm : TM) (gas k : nat) (c : cconf) (pos : Z)
    (hist : list ent) : list ent :=
  match gas with
  | 0 => hist
  | S g =>
      let '(q, (l, h, r)) := c in
      let e := mkEnt q h pos
                 (match r with [] => true | _ :: _ => false end)
                 (match l with [] => true | _ :: _ => false end) k in
      match tm q h with
      | None => hist
      | Some tr =>
          match cstep tm c with
          | None => hist
          | Some c' =>
              let pos' := match t_dir tr with
                          | DR => (pos + 1)%Z | DL => (pos - 1)%Z end in
              run tm g (S k) c' pos' (e :: hist)
          end
      end
  end.

Fixpoint rew (l0 l1 : list ent) (n : nat) : bool :=
  match n with
  | 0 => true
  | S m =>
      match l0, l1 with
      | a :: l0', b :: l1' =>
          st_eqb (eq_ a) (eq_ b) && sym_eqb (es a) (es b) && rew l0' l1' m
      | _, _ => false
      end
  end.

Fixpoint scan (h0 : ent) (tl0 l1 : list ent) (cap : nat)
    (acc : list lp_cand) : list lp_cand :=
  match l1 with
  | [] => rev acc
  | h1 :: l1' =>
      match cap with
      | 0 => rev acc
      | S cap' =>
          let P := ek h0 - ek h1 in
          if st_eqb (eq_ h0) (eq_ h1) && sym_eqb (es h0) (es h1)
             && (if 2 * P <=? ek h0 then rew tl0 l1' P else true)
          then
            match
              match Z.compare (ep h0) (ep h1) with
              | Eq => Some (fun n1 => LpCycle n1 P)
              | Gt => if err h1 then Some (fun n1 => LpTC DR n1 P) else None
              | Lt => if el h1 then Some (fun n1 => LpTC DL n1 P) else None
              end
            with
            | Some mk =>
                let n1 := ek h1 in
                let b := n1 mod P in
                let cs := if b + P <? n1 then [mk b; mk (b + P); mk n1]
                          else if b <? n1 then [mk b; mk n1] else [mk n1] in
                scan h0 tl0 l1' cap' (rev_append cs acc)
            | None => scan h0 tl0 l1' (S cap') acc
            end
          else scan h0 tl0 l1' (S cap') acc
      end
  end.

Fixpoint firstsame (q : St) (l : list ent) (side : bool) : option nat :=
  match l with
  | [] => None
  | e :: t =>
      if (if side then err e else el e)
      then if st_eqb (eq_ e) q then Some (ek e) else firstsame q t side
      else firstsame q t side
  end.

Fixpoint recs (l : list ent) (side : bool) (n : nat) : list ent :=
  match n with
  | 0 => []
  | S m => match l with
           | [] => []
           | e :: t => if (if side then err e else el e)
                       then e :: recs t side m else recs t side n
           end
  end.

Definition reccands (hist : list ent) (side : bool) : list lp_cand :=
  let d := if side then DR else DL in
  concat (map (fun e =>
    match firstsame (eq_ e) (filter (fun e' => ek e' <? ek e) hist) side with
    | Some a => [LpTC d a (ek e - a)]
    | None => []
    end) (recs hist side 2)).

Definition cands_nat (tm : TM) (gas : nat) : list lp_cand :=
  match run tm gas 0 c0 0%Z [] with
  | [] => []
  | h0 :: tl => scan h0 tl tl 6 [] ++ reccands (h0 :: tl) true
                ++ reccands (h0 :: tl) false
  end.

Definition ceq (a b : lp_cand) : bool :=
  match a, b with
  | LpCycle n p, LpCycle n' p' => (n =? n') && (p =? p')
  | LpTC d n p, LpTC d' n' p' =>
      (match d, d' with DR, DR | DL, DL => true | _, _ => false end)
      && (n =? n') && (p =? p')
  | _, _ => false
  end.
Fixpoint leq (a b : list lp_cand) : bool :=
  match a, b with
  | [], [] => true
  | x :: t, y :: u => ceq x y && leq t u
  | _, _ => false
  end.

(* machines whose candidate list differs, at both gas rungs *)
Definition diff (l : list TM) (gas : nat) : nat :=
  List.length (filter (fun tm =>
    negb (leq (lp_candidates tm gas) (cands_nat tm gas))) l).

Time Eval vm_compute in (diff ProbeTierBig.grp_T 130,
                         diff ProbeTierBig.grp_T 512).
Time Eval vm_compute in (diff ProbeTierBig.grp_C 130,
                         diff ProbeTierBig.grp_C 512).
Time Eval vm_compute in (diff ProbeTierBig.grp_N6 130,
                         diff ProbeTierBig.grp_N6 512).
