(** Is the packed win about MACHINE WORDS, or about SHORT KEYS?
    (UNTRUSTED probe, not in _CoqProject.)

    ProbePackRank.v measures 7.4x for the closure+closedness+rank stage
    on int63 nodes.  Two separable things produce that:

      (i)  a node comparison is one machine-word compare instead of
           [cconf_enc] + a Patricia walk over a ~20-bit key;
      (ii) the closure carries its own edges, so the rank checks never
           look a successor up at all.

    (ii) needs no primitives.  And (i) has an axiom-free approximation:
    INTERN the closure's nodes to indices 1..n and key everything by
    the index -- a 5-bit positive for a 29-node closure instead of a
    full context encoding.  This probe measures that middle path, so
    the primitive-int decision is made against the right baseline. *)

From Coq Require Import Arith Bool List PArith.
From Coq Require Import FSets.FMapPositive.
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure.
From BBB4.Checkers Require Import NGram ExactClosure.
Import ListNotations.

Definition T (w : Sym) (d : Dir) (n : St) := Some (mkTrans w d n).
Definition mk8 (a0 a1 b0 b1 c0' c1 d0 d1 : option Trans) : TM :=
  fun q s => match q, s with
  | StA, S0 => a0 | StA, S1 => a1 | StB, S0 => b0 | StB, S1 => b1
  | StC, S0 => c0' | StC, S1 => c1 | StD, S0 => d0 | StD, S1 => d1 end.

Definition m6 : TM :=
  mk8 (T S1 DR StB) (T S0 DL StA) (T S1 DR StC) (T S1 DL StA)
      (T S1 DR StD) (T S0 DL StB) (T S1 DL StD) (T S1 DR StC).

Definition F200k : nat := 200000.
Definition R512 : nat := 512.
Definition n6 : nat := 6.
Definition t6 : nat := 800.

Definition cc6 : cconf := Eval vm_compute in
  match csteps m6 t6 c0 with Some c => c | None => c0 end.
Definition a06 : cconf := Eval vm_compute in ng_start n6 cc6.
Definition grown6 : gset * gset := Eval vm_compute in
  ng_grow m6 a06 F200k R512
    (match cc6 with (q,(l,h,r)) => gadds (ng_seed_side n6 l) gempty end)
    (match cc6 with (q,(l,h,r)) => gadds (ng_seed_side n6 r) gempty end).
Definition succs6 := ng_succs m6 (fst grown6) (snd grown6).

(** ** Interning exploration

    One worklist pass that assigns each newly seen context the next
    index and records (index, state, successor indices).  The index
    map is a PositiveMap keyed by [cconf_enc] -- paid ONCE per node,
    not once per membership test as today. *)

Record inode := { i_st : St; i_succ : list positive }.

Definition ist : Type := (positive * PositiveMap.tree positive
                          * list (positive * inode))%type.

(* resolve a context to its index, allocating one if new *)
Definition intern (s : ist) (a : cconf) : positive * ist :=
  let '(next, m, out) := s in
  match PositiveMap.find (cconf_enc a) m with
  | Some i => (i, s)
  | None => (next, (Pos.succ next, PositiveMap.add (cconf_enc a) next m, out))
  end.

Fixpoint iexplore (fuel : nat) (s : ist) (todo : list cconf)
  : option ist :=
  match fuel with
  | O => None
  | S f =>
      match todo with
      | [] => Some s
      | a :: todo' =>
          let '(i, s1) := intern s a in
          let '(_, _, out1) := s1 in
          if existsb (fun p => Pos.eqb (fst p) i) out1
          then iexplore f s1 todo'
          else match succs6 a with
               | None => None
               | Some l =>
                   (* intern every successor, then record the node *)
                   let '(idxs, s2) :=
                     fold_left (fun '(acc, st) b =>
                                  let '(j, st') := intern st b in
                                  (acc ++ [j], st'))
                               l ([], s1) in
                   let '(nx, m2, out2) := s2 in
                   iexplore f (nx, m2,
                              (i, {| i_st := ec_state a; i_succ := idxs |})
                              :: out2)
                            (l ++ todo')
               end
      end
  end.

Definition inodes (a0 : cconf) : list (positive * inode) :=
  match iexplore F200k (1%positive, PositiveMap.empty _, []) [a0] with
  | Some (_, _, out) => out
  | None => []
  end.

(** ** Rank stage on interned indices *)

Definition irank_get (r : PositiveMap.tree nat) (i : positive) : nat :=
  match PositiveMap.find i r with Some v => v | None => 0 end.
Definition irank_has (r : PositiveMap.tree nat) (i : positive) : bool :=
  match PositiveMap.find i r with Some _ => true | None => false end.

(* state of a successor index, via the same node table *)
Definition ist_of (nl : list (positive * inode)) (i : positive) : St :=
  match find (fun p => Pos.eqb (fst p) i) nl with
  | Some (_, nd) => i_st nd
  | None => StA
  end.

Definition inonq (nl : list (positive * inode)) (q : St) (nd : inode)
  : list positive :=
  filter (fun j => negb (st_eqb (ist_of nl j) q)) (i_succ nd).

Definition ipeel_pass (nl : list (positive * inode)) (q : St)
    (st : PositiveMap.tree nat * list (positive * inode) * bool)
    (rem : list (positive * inode))
  : PositiveMap.tree nat * list (positive * inode) * bool :=
  fold_left (fun '(r, stuck, prog) p =>
    let sl := inonq nl q (snd p) in
    if forallb (irank_has r) sl
    then (PositiveMap.add (fst p)
            (match sl with
             | [] => 0
             | _ => S (fold_left Nat.max (map (irank_get r) sl) 0)
             end) r, stuck, true)
    else (r, p :: stuck, prog)) rem st.

Fixpoint ipeel_iter (k : nat) (nl : list (positive * inode)) (q : St)
    (r : PositiveMap.tree nat) (rem : list (positive * inode))
  : PositiveMap.tree nat :=
  match k, rem with
  | 0, _ | _, [] => r
  | S k', _ =>
      let '(r', stuck, prog) := ipeel_pass nl q (r, [], false) rem in
      if prog then ipeel_iter k' nl q r' stuck else r'
  end.

Definition iranks (nl : list (positive * inode)) (q : St)
  : PositiveMap.tree nat :=
  ipeel_iter (S (List.length nl)) nl q (PositiveMap.empty nat)
    (filter (fun p => negb (st_eqb (i_st (snd p)) q)) nl).

Definition irank_ok (nl : list (positive * inode)) (q : St)
    (r : PositiveMap.tree nat) : bool :=
  forallb (fun p =>
    if st_eqb (i_st (snd p)) q then true
    else forallb (fun j =>
           implb (negb (st_eqb (ist_of nl j) q))
                 (Nat.ltb (irank_get r j) (irank_get r (fst p))))
         (i_succ (snd p))) nl.

Definition ilive (nl : list (positive * inode)) : bool :=
  forallb (fun q => irank_ok nl q (iranks nl q)) all_St.

Definition istage_of (a0 : cconf) : bool :=
  let nl := inodes a0 in
  match nl with [] => false | _ => ilive nl end.

(** ** A/B against the current implementation *)

Definition Sl6 : list cconf := Eval vm_compute in
  ng_explore m6 (fst grown6) (snd grown6) F200k [] PositiveSet.empty [a06].

Definition stage_now_of (a0 : cconf) : bool :=
  let Sl := ng_explore m6 (fst grown6) (snd grown6) F200k []
              PositiveSet.empty [a0] in
  closed_b cconf cconf_enc succs6 Sl &&
  forallb (fun q => rank_ok cconf ec_state succs6 Sl q
             (compute_ranks cconf cconf_enc ec_state succs6 Sl q)) all_St.

Eval vm_compute in (List.length (inodes a06), stage_now_of a06, istage_of a06).

Fixpoint rep_now (k : nat) (a0 : cconf) (acc : bool) : bool :=
  match k with O => acc | S j => rep_now j a0 (acc && stage_now_of a0) end.
Fixpoint rep_int (k : nat) (a0 : cconf) (acc : bool) : bool :=
  match k with O => acc | S j => rep_int j a0 (acc && istage_of a0) end.

Time Eval vm_compute in rep_now 200 a06 true.
Time Eval vm_compute in rep_int 200 a06 true.
