(** Binary certificate payloads and their verified checker.
    The runtime checker uses N directly; legacy_epres is a proof denotation.
    Universal equality relates this checker to the existing checker on that
    denotation. Graphs, gates, missing-key defaults and index order agree. *)
From Coq Require Import Arith Bool List ZArith PArith FSets.FMapPositive MSets.MSetPositive.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr.
From BBB4.Checkers Require Import ClosureIdxTr.
Import ListNotations.

(** The new binary certificate ABI. K remains nat; its conversion is shared
    once per component. Both rank and measure-potential maps hold N. *)
Inductive binary_epres (A : Type) : Type :=
| BinaryERank (phi : PositiveMap.tree N)
| BinaryEMeas (mval : cconf -> nat) (md : A -> Z) (K : nat)
              (phi : PositiveMap.tree N) (gate : PositiveSet.t).

Definition legacy_epres {A : Type} (p : binary_epres A)
    : ClosureIdxTr.epres A :=
  match p with
  | BinaryERank _ phi => ClosureIdxTr.ERank A (PositiveMap.map N.to_nat phi)
  | BinaryEMeas _ mval md K phi gate =>
      ClosureIdxTr.EMeas A mval md K (PositiveMap.map N.to_nat phi) gate
  end.

Definition binary_lookup (phi : PositiveMap.tree N) (e : positive) : N :=
  match PositiveMap.find e phi with Some n => n | None => 0%N end.

Lemma binary_lookup_legacy : forall phi e,
  ClosureIdxTr.enat (PositiveMap.map N.to_nat phi) e =
  N.to_nat (binary_lookup phi e).
Proof.
  intros phi e. unfold ClosureIdxTr.enat, PositiveMap.map, binary_lookup.
  rewrite PositiveMap.gmapi. destruct (PositiveMap.find e phi); reflexivity.
Qed.

Lemma binary_rank_ltb : forall x y,
  (Z.of_nat y <? Z.of_nat x)%Z = (y <? x)%nat.
Proof.
  intros x y. destruct (y <? x)%nat eqn:E.
  - apply Nat.ltb_lt in E. apply Z.ltb_lt. now apply Nat2Z.inj_lt.
  - apply Nat.ltb_ge in E. apply Z.ltb_ge. now apply Nat2Z.inj_le.
Qed.

Lemma binary_rank_leb : forall x y,
  (Z.of_nat y <=? Z.of_nat x)%Z = (y <=? x)%nat.
Proof.
  intros x y. destruct (y <=? x)%nat eqn:E.
  - apply Nat.leb_le in E. apply Z.leb_le. now apply Nat2Z.inj_le.
  - apply Nat.leb_gt in E. apply Z.leb_gt. now apply Nat2Z.inj_lt.
Qed.

Inductive binary_cval : Type :=
| BVRank (r : Z)
| BVMeas (gate : bool) (potential weighted_delta : Z).

(** This conversion is used only in proofs, never by the new checker.
    Applying it to the old vmap would repeat the scale conversion per node. *)
Definition binary_value (v : ClosureIdxTr.cval) : binary_cval :=
  match v with
  | ClosureIdxTr.VRank r => BVRank (Z.of_nat r)
  | ClosureIdxTr.VMeas K g p d =>
      BVMeas g (Z.of_nat p) (Z.of_nat K * d)%Z
  end.

Definition binary_strict (x y : binary_cval) : bool :=
  match x, y with
  | BVRank rx, BVRank ry => (ry <? rx)%Z
  | BVMeas gx px wx, BVMeas gy py _ =>
      if gx then if gy then (wx + py - px <=? -1)%Z else false
      else false
  | _, _ => false
  end.

Definition binary_noninc (x y : binary_cval) : bool :=
  match x, y with
  | BVRank rx, BVRank ry => (ry <=? rx)%Z
  | BVMeas gx px wx, BVMeas gy py _ =>
      if gy then if gx then (wx + py - px <=? 0)%Z else false
      else true
  | _, _ => false
  end.

Fixpoint binary_lex_edge_ok (xs ys : list binary_cval) : bool :=
  match xs, ys with
  | x :: xt, y :: yt =>
      if binary_strict x y then true
      else if binary_noninc x y then binary_lex_edge_ok xt yt else false
  | _, _ => false
  end.

Lemma binary_strict_spec : forall x y,
  binary_strict (binary_value x) (binary_value y) = ClosureIdxTr.vstrict x y.
Proof.
  intros [rx | K gx px dx] [ry | K' gy py dy];
    cbn [binary_strict binary_value ClosureIdxTr.vstrict];
    try reflexivity. apply binary_rank_ltb.
Qed.

Lemma binary_noninc_spec : forall x y,
  binary_noninc (binary_value x) (binary_value y) = ClosureIdxTr.vnoninc x y.
Proof.
  intros [rx | K gx px dx] [ry | K' gy py dy];
    cbn [binary_noninc binary_value ClosureIdxTr.vnoninc];
    try reflexivity. apply binary_rank_leb.
Qed.

Lemma binary_lex_edge_ok_spec : forall xs ys,
  binary_lex_edge_ok (map binary_value xs) (map binary_value ys) =
  ClosureIdxTr.vlex_edge_ok xs ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys]; [reflexivity|reflexivity|reflexivity|].
  cbn [map binary_lex_edge_ok ClosureIdxTr.vlex_edge_ok].
  rewrite binary_strict_spec, binary_noninc_spec, IH. reflexivity.
Qed.

Section Preparation.
  Variable A : Type.
  Variable enc : A -> positive.

  Inductive prepared_epres : Type :=
  | PERank (phi : PositiveMap.tree N)
  | PEMeas (md : A -> Z) (scale : Z)
           (phi : PositiveMap.tree N) (gate : PositiveSet.t).

  Definition prepare_epres (p : binary_epres A) : prepared_epres :=
    match p with
    | BinaryERank _ phi => PERank phi
    | BinaryEMeas _ _ md K phi gate =>
        PEMeas md (Z.of_nat K) phi gate
    end.

  Definition prepared_value (e : positive) (a : A) (p : prepared_epres)
      : binary_cval :=
    match p with
    | PERank phi => BVRank (Z.of_N (binary_lookup phi e))
    | PEMeas md K phi gate =>
        BVMeas (PositiveSet.mem e gate)
          (Z.of_N (binary_lookup phi e)) (K * md a)%Z
    end.

  Definition prepared_values (ps : list prepared_epres) (a : A)
      : list binary_cval :=
    let e := enc a in map (prepared_value e a) ps.

  Lemma prepared_value_spec : forall e a p,
    prepared_value e a (prepare_epres p) =
    binary_value (ClosureIdxTr.cval_of A e a (legacy_epres p)).
  Proof.
    intros e a [phi | mval md K phi gate];
      cbn [prepare_epres prepared_value legacy_epres ClosureIdxTr.cval_of binary_value];
      rewrite binary_lookup_legacy, N_nat_Z; reflexivity.
  Qed.

  Lemma prepared_values_spec : forall ps a,
    prepared_values (map prepare_epres ps) a =
    map binary_value (ClosureIdxTr.vals_of A enc (map legacy_epres ps) a).
  Proof.
    intros ps a. unfold prepared_values, ClosureIdxTr.vals_of.
    rewrite !map_map. apply map_ext. intro p. apply prepared_value_spec.
  Qed.

  Definition binary_vmap : Type := PositiveMap.tree (list binary_cval).

  Definition binary_vmap_of (ps : list (binary_epres A))
      (ip : list (positive * A)) : binary_vmap :=
    let prepared := map prepare_epres ps in
    fold_left
      (fun m p => PositiveMap.add (fst p) (prepared_values prepared (snd p)) m)
      ip (PositiveMap.empty _).

  Definition binary_get (m : binary_vmap) (i : positive) : list binary_cval :=
    match PositiveMap.find i m with Some vs => vs | None => [] end.

  Definition values_related (bm : binary_vmap) (vm : ClosureIdxTr.vmap) : Prop :=
    forall k, PositiveMap.find k bm =
      option_map (map binary_value) (PositiveMap.find k vm).

  Lemma binary_fold_related : forall ps ip bm vm,
    values_related bm vm ->
    values_related
      (fold_left
        (fun m p => PositiveMap.add (fst p)
          (prepared_values (map prepare_epres ps) (snd p)) m) ip bm)
      (fold_left
        (fun m p => PositiveMap.add (fst p)
          (ClosureIdxTr.vals_of A enc (map legacy_epres ps) (snd p)) m) ip vm).
  Proof.
    intros ps ip. induction ip as [|[i a] ip IH]; intros bm vm H;
      [exact H|].
    cbn [fold_left fst snd]. apply IH. intro k.
    destruct (Pos.eq_dec k i) as [-> | Hne].
    - rewrite !PositiveMap.gss. cbn [option_map].
      rewrite prepared_values_spec. reflexivity.
    - rewrite !PositiveMap.gso by congruence. apply H.
  Qed.

  Lemma binary_get_spec : forall ps ip i,
    binary_get (binary_vmap_of ps ip) i =
    map binary_value (ClosureIdxTr.vget (ClosureIdxTr.vmap_of A enc (map legacy_epres ps) ip) i).
  Proof.
    intros ps ip i.
    assert (H0 : values_related (PositiveMap.empty _) (PositiveMap.empty _)).
    { intro k. rewrite !PositiveMap.gempty. reflexivity. }
    pose proof (binary_fold_related ps ip _ _ H0 i) as E.
    unfold binary_get, binary_vmap_of, ClosureIdxTr.vget, ClosureIdxTr.vmap_of.
    rewrite E.
    destruct (PositiveMap.find i
      (fold_left
        (fun m p => PositiveMap.add (fst p)
          (ClosureIdxTr.vals_of A enc (map legacy_epres ps) (snd p)) m)
        ip (PositiveMap.empty _))); reflexivity.
  Qed.

  Definition binary_row_ok (q : Instr) (vm : binary_vmap)
      (row : ClosureIdxTr.erow) : bool :=
    let '(i, s, js) := row in
    if instr_eqb s q then true
    else
      let xs := binary_get vm i in
      allb_tr (fun p => if instr_eqb (snd p) q then true
        else binary_lex_edge_ok xs (binary_get vm (fst p))) js.

  Definition binary_lex_ok (rows : list ClosureIdxTr.erow) (q : Instr)
      (vm : binary_vmap) : bool := allb_tr (binary_row_ok q vm) rows.

  Lemma binary_row_ok_spec : forall ps ip q row,
    binary_row_ok q (binary_vmap_of ps ip) row =
    ClosureIdxTr.vrow_ok q (ClosureIdxTr.vmap_of A enc (map legacy_epres ps) ip) row.
  Proof.
    intros ps ip q [[i s] js].
    unfold binary_row_ok, ClosureIdxTr.vrow_ok.
    destruct (instr_eqb s q); [reflexivity|].
    rewrite binary_get_spec. apply ClosureIdxTr.forallb_ext.
    intros [j s']. cbn [fst snd].
    destruct (instr_eqb s' q); [reflexivity|].
    rewrite binary_get_spec, binary_lex_edge_ok_spec. reflexivity.
  Qed.

  Lemma binary_lex_ok_spec : forall ps ip q rows,
    binary_lex_ok rows q (binary_vmap_of ps ip) =
    ClosureIdxTr.vlex_ok rows q (ClosureIdxTr.vmap_of A enc (map legacy_epres ps) ip).
  Proof.
    intros ps ip q rows. unfold binary_lex_ok, ClosureIdxTr.vlex_ok.
    apply ClosureIdxTr.forallb_ext. intro row. apply binary_row_ok_spec.
  Qed.

  Variable tm : TM.
  Variable instruction : A -> Instr.
  Variable successors : A -> option (list A).

  Definition lex_check_binary_pool (t : nat) (a0 : A) (pool : list A)
      (cert : Instr -> list (binary_epres A)) : bool :=
    match csteps tm t c0 with
    | Some _ =>
        match ClosureIdxTr.edges_of A enc instruction successors
          (ClosureIdxTr.build_imap A enc pool) pool with
        | None => false
        | Some rows =>
            match ClosureIdxTr.idx_of A enc
              (ClosureIdxTr.build_imap A enc pool) a0 with
            | None => false
            | Some _ =>
                let ip := ClosureIdxTr.ipool A pool in
                allb_tr (fun q =>
                  if (if cfires tm c0 t q then true
                      else existsb
                        (fun row => instr_eqb (ClosureIdxTr.row_instr row) q) rows)
                  then binary_lex_ok rows q (binary_vmap_of (cert q) ip)
                  else true) all_Instr
            end
        end
    | None => false
    end.

  (** Proposed exact equality for EVERY binary certificate: no injectivity,
      closure, key-validity, numeric-range, fuel or generated-map premise. *)
  Theorem lex_check_binary_pool_spec : forall t a0 pool cert,
    lex_check_binary_pool t a0 pool cert =
    ClosureIdxTr.lex_check_idx_pool tm A enc instruction successors t a0 pool (fun q => map legacy_epres (cert q)).
  Proof.
    intros t a0 pool cert.
    unfold lex_check_binary_pool, ClosureIdxTr.lex_check_idx_pool.
    destruct (csteps tm t c0); [|reflexivity].
    destruct (ClosureIdxTr.edges_of A enc instruction successors
      (ClosureIdxTr.build_imap A enc pool) pool) as [rows|]; [|reflexivity].
    destruct (ClosureIdxTr.idx_of A enc
      (ClosureIdxTr.build_imap A enc pool) a0); [|reflexivity].
    apply ClosureIdxTr.forallb_ext. intro q.
    destruct (if cfires tm c0 t q then true
      else existsb (fun row => instr_eqb (ClosureIdxTr.row_instr row) q) rows);
      [apply binary_lex_ok_spec | reflexivity].
  Qed.
End Preparation.

(** Assumption audit for binary-checker equivalence. *)
Print Assumptions binary_lookup_legacy.
Print Assumptions binary_rank_ltb.
Print Assumptions binary_rank_leb.
Print Assumptions binary_strict_spec.
Print Assumptions binary_noninc_spec.
Print Assumptions prepared_value_spec.
Print Assumptions binary_fold_related.
Print Assumptions binary_get_spec.
Print Assumptions lex_check_binary_pool_spec.
