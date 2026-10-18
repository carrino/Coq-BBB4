(** Gate-aware evaluation of binary certificates.
    The certificate ABI is unchanged. False measure gates use a canonical
    value without looking up phi, evaluating md, or multiplying.
    K is converted once per component. *)
From Coq Require Import Arith Bool List ZArith PArith FSets.FMapPositive MSets.MSetPositive.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr.
From BBB4.Checkers Require Import ClosureIdxTr ClosureBinaryCertTr.
Import ListNotations.

Definition normalize_binary_value (v : binary_cval) : binary_cval :=
  match v with
  | BVRank n => BVRank n
  | BVMeas true p d => BVMeas true p d
  | BVMeas false _ _ => BVMeas false 0%Z 0%Z
  end.

Lemma normalize_binary_strict : forall x y,
  binary_strict (normalize_binary_value x) (normalize_binary_value y) =
  binary_strict x y.
Proof.
  intros [rx|gx px dx] [ry|gy py dy];
    try destruct gx; try destruct gy; reflexivity.
Qed.

Lemma normalize_binary_noninc : forall x y,
  binary_noninc (normalize_binary_value x) (normalize_binary_value y) =
  binary_noninc x y.
Proof.
  intros [rx|gx px dx] [ry|gy py dy];
    try destruct gx; try destruct gy; reflexivity.
Qed.

Lemma normalize_binary_lex_edge_ok : forall xs ys,
  binary_lex_edge_ok (map normalize_binary_value xs)
    (map normalize_binary_value ys) = binary_lex_edge_ok xs ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys];
    [reflexivity|reflexivity|reflexivity|].
  cbn [map binary_lex_edge_ok].
  rewrite normalize_binary_strict, normalize_binary_noninc, IH. reflexivity.
Qed.

Section GatedPreparation.
  Variable A : Type.
  Variable enc : A -> positive.

  Definition gated_prepared_value (e : positive) (a : A)
      (p : prepared_epres A) : binary_cval :=
    match p with
    | PERank _ phi => BVRank (Z.of_N (binary_lookup phi e))
    | PEMeas _ md K phi gate =>
        if PositiveSet.mem e gate
        then BVMeas true (Z.of_N (binary_lookup phi e)) (K * md a)%Z
        else BVMeas false 0%Z 0%Z
    end.

  Definition gated_prepared_values (ps : list (prepared_epres A)) (a : A)
      : list binary_cval :=
    let e := enc a in map (gated_prepared_value e a) ps.

  Lemma gated_prepared_value_spec : forall e a p,
    gated_prepared_value e a p =
    normalize_binary_value (prepared_value A e a p).
  Proof.
    intros e a [phi|md K phi gate];
      cbn [gated_prepared_value prepared_value normalize_binary_value];
      [reflexivity|].
    destruct (PositiveSet.mem e gate); reflexivity.
  Qed.

  Lemma gated_prepared_values_spec : forall ps a,
    gated_prepared_values ps a =
    map normalize_binary_value (prepared_values A enc ps a).
  Proof.
    intros ps a. unfold gated_prepared_values, prepared_values.
    rewrite map_map. apply map_ext. intro p. apply gated_prepared_value_spec.
  Qed.

  Definition gated_vmap_of (ps : list (binary_epres A))
      (ip : list (positive * A)) : binary_vmap :=
    let prepared := map (prepare_epres A) ps in
    fold_left
      (fun m p => PositiveMap.add (fst p)
        (gated_prepared_values prepared (snd p)) m)
      ip (PositiveMap.empty _).

  Definition gated_values_related (gm bm : binary_vmap) : Prop :=
    forall k, PositiveMap.find k gm =
      option_map (map normalize_binary_value) (PositiveMap.find k bm).

  Lemma gated_fold_related : forall ps ip gm bm,
    gated_values_related gm bm ->
    gated_values_related
      (fold_left
        (fun m p => PositiveMap.add (fst p)
          (gated_prepared_values ps (snd p)) m) ip gm)
      (fold_left
        (fun m p => PositiveMap.add (fst p)
          (prepared_values A enc ps (snd p)) m) ip bm).
  Proof.
    intros ps ip. induction ip as [|[i a] ip IH]; intros gm bm H;
      [exact H|].
    cbn [fold_left fst snd]. apply IH. intro k.
    destruct (Pos.eq_dec k i) as [->|Hne].
    - rewrite !PositiveMap.gss. cbn [option_map].
      rewrite gated_prepared_values_spec. reflexivity.
    - rewrite !PositiveMap.gso by congruence. apply H.
  Qed.

  Lemma gated_get_spec : forall ps ip i,
    binary_get (gated_vmap_of ps ip) i =
    map normalize_binary_value (binary_get (binary_vmap_of A enc ps ip) i).
  Proof.
    intros ps ip i.
    assert (H0 : gated_values_related (PositiveMap.empty _) (PositiveMap.empty _)).
    { intro k. rewrite !PositiveMap.gempty. reflexivity. }
    pose proof (gated_fold_related (map (prepare_epres A) ps) ip _ _ H0 i) as E.
    unfold binary_get, gated_vmap_of, binary_vmap_of. rewrite E.
    destruct (PositiveMap.find i
      (fold_left
        (fun m p => PositiveMap.add (fst p)
          (prepared_values A enc (map (prepare_epres A) ps) (snd p)) m)
        ip (PositiveMap.empty _))); reflexivity.
  Qed.

  Lemma gated_row_ok_spec : forall ps ip q row,
    binary_row_ok q (gated_vmap_of ps ip) row =
    binary_row_ok q (binary_vmap_of A enc ps ip) row.
  Proof.
    intros ps ip q [[i s] js]. unfold binary_row_ok.
    destruct (instr_eqb s q); [reflexivity|].
    rewrite gated_get_spec. apply ClosureIdxTr.forallb_ext.
    intros [j s']. cbn [fst snd].
    destruct (instr_eqb s' q); [reflexivity|].
    rewrite gated_get_spec, normalize_binary_lex_edge_ok. reflexivity.
  Qed.

  Lemma gated_lex_ok_spec : forall ps ip q rows,
    binary_lex_ok rows q (gated_vmap_of ps ip) =
    binary_lex_ok rows q (binary_vmap_of A enc ps ip).
  Proof.
    intros ps ip q rows. unfold binary_lex_ok.
    apply ClosureIdxTr.forallb_ext. intro row. apply gated_row_ok_spec.
  Qed.

  Variable tm : TM.
  Variable instruction : A -> Instr.
  Variable successors : A -> option (list A).

  Definition lex_check_binary_gated_pool (t : nat) (a0 : A) (pool : list A)
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
                  then binary_lex_ok rows q (gated_vmap_of (cert q) ip)
                  else true) all_Instr
            end
        end
    | None => false
    end.

  Theorem lex_check_binary_gated_pool_spec : forall t a0 pool cert,
    lex_check_binary_gated_pool t a0 pool cert =
    lex_check_binary_pool A enc tm instruction successors t a0 pool cert.
  Proof.
    intros t a0 pool cert.
    unfold lex_check_binary_gated_pool, lex_check_binary_pool.
    destruct (csteps tm t c0); [|reflexivity].
    destruct (ClosureIdxTr.edges_of A enc instruction successors
      (ClosureIdxTr.build_imap A enc pool) pool) as [rows|]; [|reflexivity].
    destruct (ClosureIdxTr.idx_of A enc
      (ClosureIdxTr.build_imap A enc pool) a0); [|reflexivity].
    apply ClosureIdxTr.forallb_ext. intro q.
    destruct (if cfires tm c0 t q then true
      else existsb (fun row => instr_eqb (ClosureIdxTr.row_instr row) q) rows);
      [apply gated_lex_ok_spec|reflexivity].
  Qed.

  Corollary lex_check_binary_gated_pool_legacy_spec : forall t a0 pool cert,
    lex_check_binary_gated_pool t a0 pool cert =
    ClosureIdxTr.lex_check_idx_pool tm A enc instruction successors t a0 pool
      (fun q => map legacy_epres (cert q)).
  Proof.
    intros t a0 pool cert. rewrite lex_check_binary_gated_pool_spec.
    apply lex_check_binary_pool_spec.
  Qed.
End GatedPreparation.

(** Assumption audit for gate normalization and checker equivalence. *)
Print Assumptions normalize_binary_strict.
Print Assumptions normalize_binary_noninc.
Print Assumptions normalize_binary_lex_edge_ok.
Print Assumptions gated_prepared_value_spec.
Print Assumptions gated_fold_related.
Print Assumptions gated_get_spec.
Print Assumptions lex_check_binary_gated_pool_spec.
Print Assumptions lex_check_binary_gated_pool_legacy_spec.
