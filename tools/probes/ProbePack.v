(** Packed-representation A/B probe (UNTRUSTED, not in _CoqProject).

    Measures the Uint63/PArray packed n-gram closure against the
    current [cconf]/PositiveSet one on the SAME machine and the SAME
    gram sets, so the ratio is the packed arc's headline number.

    Layout of a packed context (n <= 6):
      bits 0-1   state (StA..StD)
      bit  2     head symbol
      bits 3..3+n-1     left window, nearest cell at the low bit
      bits 3+n..3+2n-1  right window, likewise
    so a context is 3 + 2n <= 15 bits and the visited set is one
    PArray of 2^15 slots -- O(1) membership, zero allocation. *)

From Coq Require Import Arith Bool List ZArith Uint63 PArray.
From BBB4 Require Import BBB4_Statement CTape PosEnc.
From BBB4.Checkers Require Import NGram.
Import ListNotations.
Open Scope uint63_scope.

Definition T (w : Sym) (d : Dir) (n : St) := Some (mkTrans w d n).
Definition mk8 (a0 a1 b0 b1 c0' c1 d0 d1 : option Trans) : TM :=
  fun q s => match q, s with
  | StA, S0 => a0 | StA, S1 => a1 | StB, S0 => b0 | StB, S1 => b1
  | StC, S0 => c0' | StC, S1 => c1 | StD, S0 => d0 | StD, S1 => d1 end.

(* 1RB0LA_1RC1LA_1RD0LB_1LD1RC : caught at rung (6,800) *)
Definition m6 : TM :=
  mk8 (T S1 DR StB) (T S0 DL StA) (T S1 DR StC) (T S1 DL StA)
      (T S1 DR StD) (T S0 DL StB) (T S1 DL StD) (T S1 DR StC).
(* holdout #1: 1RB1LA_1LC0RA_1LD0LD_0RB0LC -- full failing ladder *)
Definition hold1 : TM :=
  mk8 (T S1 DR StB) (T S1 DL StA) (T S1 DL StC) (T S0 DR StA)
      (T S1 DL StD) (T S0 DL StD) (T S0 DR StB) (T S0 DL StC).

(** ** Bit plumbing *)

Definition st_bits (q : St) : int :=
  match q with StA => 0 | StB => 1 | StC => 2 | StD => 3 end.
Definition bits_st (i : int) : St :=
  if i =? 0 then StA else if i =? 1 then StB
  else if i =? 2 then StC else StD.
Definition sym_bit (s : Sym) : int := match s with S0 => 0 | S1 => 1 end.
Definition bit_sym (i : int) : Sym := if i =? 0 then S0 else S1.

Definition nmask (n : nat) : int := (1 << (of_Z (Z.of_nat n))) - 1.

(* window (nearest-first list) <-> bits (nearest at bit 0) *)
Fixpoint wbits (l : list Sym) : int :=
  match l with
  | [] => 0
  | s :: t => (sym_bit s) lor ((wbits t) << 1)
  end.
Fixpoint wlist (n : nat) (w : int) : list Sym :=
  match n with
  | O => []
  | S k => bit_sym (w land 1) :: wlist k (w >> 1)
  end.

Definition pk (n : nat) (q : St) (h : Sym) (lw rw : int) : int :=
  (st_bits q) lor ((sym_bit h) << 2) lor (lw << 3)
              lor (rw << (3 + of_Z (Z.of_nat n))).

Definition pk_of (n : nat) (a : cconf) : int :=
  let '(q, (lw, s, rw)) := a in pk n q s (wbits lw) (wbits rw).

Definition un_pk (n : nat) (a : int) : cconf :=
  let ni := of_Z (Z.of_nat n) in
  (bits_st (a land 3),
   (wlist n ((a >> 3) land (nmask n)),
    bit_sym ((a >> 2) land 1),
    wlist n ((a >> (3 + ni)) land (nmask n)))).

Definition g_q (a : int) : int := a land 3.
Definition g_h (a : int) : int := (a >> 2) land 1.
Definition g_lw (n : nat) (a : int) : int := (a >> 3) land (nmask n).
Definition g_rw (n : nat) (a : int) : int :=
  (a >> (3 + of_Z (Z.of_nat n))) land (nmask n).

(** ** Gram sets as bitmasks

    A window of n <= 6 bits has < 64 values, one bit short of an
    int63, so a set is a (lo, hi) pair splitting at 32. *)

Definition gbits : Type := (int * int)%type.

Definition gb_mem (g : gbits) (v : int) : bool :=
  let '(lo, hi) := g in
  if v <? 32 then ((lo >> v) land 1) =? 1
  else ((hi >> (v - 32)) land 1) =? 1.

Definition gb_add (g : gbits) (v : int) : gbits :=
  let '(lo, hi) := g in
  if v <? 32 then (lo lor (1 << v), hi) else (lo, hi lor (1 << (v - 32))).

(* import a PositiveSet gram set by testing every window value *)
Fixpoint gb_import_aux (n : nat) (k : nat) (s : gset) (acc : gbits) : gbits :=
  match k with
  | O => acc
  | S k' =>
      let v := of_Z (Z.of_nat k') in
      gb_import_aux n k' s (if gmem (wlist n v) s then gb_add acc v else acc)
  end.
Definition gb_import (n : nat) (s : gset) : gbits :=
  gb_import_aux n (Nat.pow 2 n) s (0, 0).

(** ** Packed successors

    Right move, write w, next q':
      new_lw = w :: removelast lw   = (lw << 1 | w) & mask
      new_h  = chd rw               = rw & 1
      new_rw = tl rw ++ [x]         = (rw >> 1) | (x << (n-1))
    Left move mirrors it.  Compare [ng_brR]/[ng_brL] in NGram.v. *)

Definition pk_succs (tm : TM) (n : nat) (lg rg : gbits) (a : int)
  : option (list int) :=
  let ni := of_Z (Z.of_nat n) in
  let msk := nmask n in
  let top := ni - 1 in
  let q := g_q a in let h := g_h a in
  let lw := g_lw n a in let rw := g_rw n a in
  match tm (bits_st q) (bit_sym h) with
  | None => None
  | Some tr =>
      let w := sym_bit (t_write tr) in
      let q' := st_bits (t_next tr) in
      match t_dir tr with
      | DR =>
          if gb_mem lg lw then
            let nlw := ((lw << 1) lor w) land msk in
            let nh := rw land 1 in
            let base := q' lor (nh << 2) lor (nlw << 3) in
            let r0 := rw >> 1 in
            let r1 := (rw >> 1) lor (1 << top) in
            Some ((if gb_mem rg r0 then [base lor (r0 << (3 + ni))] else [])
                  ++ (if gb_mem rg r1 then [base lor (r1 << (3 + ni))] else []))
          else None
      | DL =>
          if gb_mem rg rw then
            let nrw := ((rw << 1) lor w) land msk in
            let nh := lw land 1 in
            let l0 := lw >> 1 in
            let l1 := (lw >> 1) lor (1 << top) in
            let base := q' lor (nh << 2) lor (nrw << (3 + ni)) in
            Some ((if gb_mem lg l0 then [base lor (l0 << 3)] else [])
                  ++ (if gb_mem lg l1 then [base lor (l1 << 3)] else []))
          else None
      end
  end.

(** ** Packed exploration: PArray visited set, int worklist *)

Definition vsize (n : nat) : int := 1 << (of_Z (Z.of_nat (3 + 2 * n))).

Fixpoint pk_explore (tm : TM) (n : nat) (lg rg : gbits) (fuel : nat)
    (cnt : nat) (vis : array int) (todo : list int) : nat * array int :=
  match fuel with
  | O => (cnt, vis)
  | S f =>
      match todo with
      | [] => (cnt, vis)
      | a :: todo' =>
          if vis.[a] =? 1 then pk_explore tm n lg rg f cnt vis todo'
          else
            let vis' := vis.[a <- 1] in
            match pk_succs tm n lg rg a with
            | None => pk_explore tm n lg rg f (S cnt) vis' todo'
            | Some l => pk_explore tm n lg rg f (S cnt) vis' (l ++ todo')
            end
      end
  end.

Definition pk_closure (tm : TM) (n : nat) (fuel : nat) (lg rg : gbits) (a0 : int)
  : nat :=
  fst (pk_explore tm n lg rg fuel 0 (PArray.make (vsize n) 0) [a0]).

(** ** The instances: same machine, same gram sets, both engines *)

Definition n6 : nat := 6.
Definition cc6 : cconf := match csteps m6 800 c0 with Some c => c | None => c0 end.
Definition seed6l : gset :=
  match cc6 with (q,(l,h,r)) => gadds (ng_seed_side n6 l) gempty end.
Definition seed6r : gset :=
  match cc6 with (q,(l,h,r)) => gadds (ng_seed_side n6 r) gempty end.
Definition grown6 : gset * gset :=
  Eval vm_compute in ng_grow m6 (ng_start n6 cc6) 200000 512 seed6l seed6r.
Definition a06 : cconf := Eval vm_compute in ng_start n6 cc6.

Definition lg6 : gbits := Eval vm_compute in gb_import n6 (fst grown6).
Definition rg6 : gbits := Eval vm_compute in gb_import n6 (snd grown6).
Definition p06 : int := Eval vm_compute in pk_of n6 a06.

(* fuel as a PRE-EVALUATED constant: an inline [200000] literal is
   [Init.Nat.of_num_uint ...], which vm_compute re-expands into a
   200,000-deep unary nat at every use.  Inside a loop that buries the
   closure cost entirely.  Naming it makes the VM build it ONCE and
   memoise it on the constant -- which is also how the real walk
   behaves, since Run.v's [decider] is itself a global constant.  Both
   engines share this one constant. *)
Definition F200k : nat := 200000.

(* agreement check: same closure size both ways *)
Eval vm_compute in
  (List.length (ng_explore m6 (fst grown6) (snd grown6) F200k []
             PositiveSet.empty [a06]),
   pk_closure m6 n6 F200k lg6 rg6 p06).

(* per-successor agreement over the whole reachable closure *)
Definition succ_agree : bool :=
  forallb (fun a =>
    match ng_succs m6 (fst grown6) (snd grown6) a, pk_succs m6 n6 lg6 rg6 (pk_of n6 a) with
    | None, None => true
    | Some l, Some pl =>
        (List.length l =? List.length pl)%nat &&
        forallb (fun p => existsb (fun b => ceqb b (un_pk n6 p)) l) pl
    | _, _ => false
    end)
    (ng_explore m6 (fst grown6) (snd grown6) F200k [] PositiveSet.empty [a06]).
Eval vm_compute in succ_agree.

(** ** Timing: the walk repeats this per machine, so loop it.

    The fuel must be a PRE-EVALUATED constant: an inline [200000]
    literal is [Init.Nat.of_num_uint ...], which vm_compute re-expands
    into a 200,000-deep unary nat on every loop iteration and buries
    the closure cost entirely (measured: it accounts for ~99% of a
    naive loop).  Both sides share the same hoisted constant. *)


(** Variant: linear int list as the visited set.

    n-gram closures in this census are TENS of nodes, so a 2^15-slot
    PArray is pure waste -- one [PArray.make] per machine allocates
    1000x the closure.  With packed keys a membership test is a
    single-word compare, so a plain list beats every indexed
    structure at this size. *)

Fixpoint pkl_explore (tm : TM) (n : nat) (lg rg : gbits) (fuel : nat)
    (seen : list int) (todo : list int) : list int :=
  match fuel with
  | O => seen
  | S f =>
      match todo with
      | [] => seen
      | a :: todo' =>
          if existsb (fun x => x =? a) seen
          then pkl_explore tm n lg rg f seen todo'
          else match pk_succs tm n lg rg a with
               | None => pkl_explore tm n lg rg f (a :: seen) todo'
               | Some l => pkl_explore tm n lg rg f (a :: seen) (l ++ todo')
               end
      end
  end.

Definition pkl_closure (tm : TM) (n : nat) (fuel : nat) (lg rg : gbits) (a0 : int)
  : nat := List.length (pkl_explore tm n lg rg fuel [] [a0]).

Eval vm_compute in pkl_closure m6 n6 F200k lg6 rg6 p06.

(** CONTROL: the current [cconf] representation, but with the trie
    swapped for a linear list + [ceqb].  Separates "the win came from
    int packing" from "the win came from dropping the trie" -- this
    variant needs NO primitives, so it costs nothing in axiom
    footprint. *)

Fixpoint ngl_explore (tm : TM) (lset rset : gset) (fuel : nat)
    (seen : list cconf) (todo : list cconf) : list cconf :=
  match fuel with
  | O => seen
  | S f =>
      match todo with
      | [] => seen
      | a :: todo' =>
          if existsb (ceqb a) seen
          then ngl_explore tm lset rset f seen todo'
          else match ng_succs tm lset rset a with
               | None => ngl_explore tm lset rset f (a :: seen) todo'
               | Some l => ngl_explore tm lset rset f (a :: seen) (l ++ todo')
               end
      end
  end.

Eval vm_compute in
  List.length (ngl_explore m6 (fst grown6) (snd grown6) F200k [] [a06]).

Fixpoint rep_ctl (k : nat) (acc : bool) : bool :=
  match k with
  | O => acc
  | S j => rep_ctl j (acc && Nat.eqb (List.length
             (ngl_explore m6 (fst grown6) (snd grown6) F200k [] [a06])) 29)
  end.

(* tail-recursive, bool accumulator: the loop measures the closure
   computation, not nat arithmetic *)
Fixpoint rep_old (k : nat) (acc : bool) : bool :=
  match k with
  | O => acc
  | S j => rep_old j (acc && Nat.eqb (List.length
             (ng_explore m6 (fst grown6) (snd grown6)
                F200k [] PositiveSet.empty [a06])) 29)
  end.

Fixpoint rep_new (k : nat) (acc : bool) : bool :=
  match k with
  | O => acc
  | S j => rep_new j (acc && Nat.eqb (pk_closure m6 n6 F200k lg6 rg6 p06) 29)
  end.

Fixpoint rep_newl (k : nat) (acc : bool) : bool :=
  match k with
  | O => acc
  | S j => rep_newl j (acc && Nat.eqb (pkl_closure m6 n6 F200k lg6 rg6 p06) 29)
  end.

Time Eval vm_compute in rep_old 2000 true.
Time Eval vm_compute in rep_new 2000 true.
Time Eval vm_compute in rep_newl 2000 true.
Time Eval vm_compute in rep_ctl 2000 true.
