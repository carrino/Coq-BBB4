(** Verified RW tier for binary certificates.
    Runtime evaluation does not call the unary legacy denotation.
    Soundness relates arbitrary binary certificates to the existing
    verified checker. *)
From Coq Require Import Arith Bool List NArith ZArith PArith.
From Coq Require Import FSets.FMapPositive MSets.MSetPositive.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape Closure ClosureTr.
From BBB4.Checkers Require Import RepWL ClosureIdxTr ClosureBinaryCertTr ClosureBinaryGatedTr.
From BBB4.Census Require Import RepWLSearch.
From BBB4.CensusTr Require Import RepWLTr RepWLBinaryProducerTr.
Import ListNotations.
Open Scope nat_scope.

Definition rpmN_of (tbl : list (positive * N)) : PositiveMap.tree N :=
  fold_left (fun mp e => PositiveMap.add (fst e) (snd e) mp) tbl
    (PositiveMap.empty N).

(* This structural map is proof-only; the runtime maps retain binary N. *)
Fixpoint phi_tree_legacy (t : PositiveMap.tree N) : PositiveMap.tree nat :=
  match t with
  | PositiveMap.Leaf _ => PositiveMap.Leaf nat
  | PositiveMap.Node l o r => PositiveMap.Node (phi_tree_legacy l)
      (option_map N.to_nat o) (phi_tree_legacy r)
  end.
Lemma phi_tree_xmapi : forall t prefix,
  PositiveMap.xmapi (fun _ => N.to_nat) t prefix = phi_tree_legacy t.
Proof.
  induction t as [|l IHl o r IHr]; intro prefix; cbn;
    [reflexivity|]. rewrite IHl, IHr. reflexivity.
Qed.
Lemma phi_tree_map : forall t,
  PositiveMap.map N.to_nat t = phi_tree_legacy t.
Proof. intro t. unfold PositiveMap.map, PositiveMap.mapi. apply phi_tree_xmapi. Qed.
Lemma phi_tree_add : forall p value t,
  phi_tree_legacy (PositiveMap.add p value t) =
  PositiveMap.add p (N.to_nat value) (phi_tree_legacy t).
Proof.
  induction p; intros value [|l o r]; cbn; try rewrite IHp; reflexivity.
Qed.
Lemma rpmN_fold_legacy : forall tbl initial,
  phi_tree_legacy
    (fold_left (fun mp e => PositiveMap.add (fst e) (snd e) mp) tbl initial) =
  fold_left (fun mp e => PositiveMap.add (fst e) (snd e) mp)
    (rw_phiN_legacy tbl) (phi_tree_legacy initial).
Proof.
  induction tbl as [|[p value] tbl IH]; intro initial;
    cbn [fold_left rw_phiN_legacy map]; [reflexivity|].
  rewrite IH, phi_tree_add. reflexivity.
Qed.
Lemma rpmN_of_legacy : forall tbl,
  PositiveMap.map N.to_nat (rpmN_of tbl) = rpm_of (rw_phiN_legacy tbl).
Proof.
  intro tbl. rewrite phi_tree_map. unfold rpmN_of, rpm_of.
  rewrite rpmN_fold_legacy. reflexivity.
Qed.

Definition rw_binary_epres_tr (tm : TM) (c : rwcompN) : binary_epres rconf :=
  match c with
  | RwRankN phi => BinaryERank rconf (rpmN_of phi)
  | RwMeasN m K phi gate =>
      BinaryEMeas rconf (rw_mval m) (fun a => rw_delta tm m a) K
        (rpmN_of phi) (rps_of gate)
  end.
Lemma rw_binary_epres_legacy : forall tm c,
  legacy_epres (rw_binary_epres_tr tm c) = rw_epres_tr tm (rwcompN_legacy c).
Proof.
  intros tm [phi|m K phi gate];
    cbn [legacy_epres rw_binary_epres_tr rw_epres_tr rwcompN_legacy];
    rewrite rpmN_of_legacy; reflexivity.
Qed.
Lemma rw_binary_epres_list_legacy : forall tm cert,
  map legacy_epres (map (rw_binary_epres_tr tm) cert) =
  map (rw_epres_tr tm) (map rwcompN_legacy cert).
Proof.
  intros tm cert. rewrite !map_map. apply map_ext.
  intro c. apply rw_binary_epres_legacy.
Qed.

(* Pointwise certificate congruence avoids functional extensionality. *)
Lemma rw_idx_pool_cert_ext : forall tm L T t M a0 Sl cert1 cert2,
  (forall tg, cert1 tg = cert2 tg) ->
  lex_check_idx_pool tm rconf rconf_enc rw_instr (rw_succs_cut M tm L T)
    t a0 Sl cert1 =
  lex_check_idx_pool tm rconf rconf_enc rw_instr (rw_succs_cut M tm L T)
    t a0 Sl cert2.
Proof.
  intros tm L T t M a0 Sl cert1 cert2 H.
  unfold lex_check_idx_pool.
  destruct (csteps tm t c0); [|reflexivity].
  destruct (edges_of rconf rconf_enc rw_instr (rw_succs_cut M tm L T)
    (build_imap rconf rconf_enc Sl) Sl) as [rows|]; [|reflexivity].
  destruct (idx_of rconf rconf_enc (build_imap rconf rconf_enc Sl) a0);
    [|reflexivity].
  apply ClosureIdxTr.forallb_ext. intro tg. rewrite H. reflexivity.
Qed.

Definition rw_check_binary_neverqhtr_closed (tm : TM) (L T t M : nat)
    (Sl : list rconf) (cert : Instr -> list rwcompN) : bool :=
  (1 <=? L) && (2 <=? T) &&
  match csteps tm t c0 with
  | Some cc =>
      lex_check_binary_gated_pool rconf rconf_enc tm rw_instr (rw_succs_cut M tm L T)
        t (rw_seed L T cc) Sl
        (fun tg => map (rw_binary_epres_tr tm) (cert tg))
  | None => false
  end.
Lemma rw_check_binary_neverqhtr_closed_spec : forall tm L T t M Sl cert,
  rw_check_binary_neverqhtr_closed tm L T t M Sl cert =
  rw_check_neverqhtr_closed tm L T t M Sl
    (fun tg => map rwcompN_legacy (cert tg)).
Proof.
  intros tm L T t M Sl cert.
  unfold rw_check_binary_neverqhtr_closed, rw_check_neverqhtr_closed.
  destruct ((1 <=? L) && (2 <=? T)); [|reflexivity].
  cbn [andb]. destruct (csteps tm t c0) as [cc|]; [|reflexivity].
  rewrite lex_check_binary_gated_pool_legacy_spec.
  apply rw_idx_pool_cert_ext. intro tg. apply rw_binary_epres_list_legacy.
Qed.

Definition rw_binary_procedure_tr (tm : TM) (L T : nat)
    (closure : list rconf) (tg : Instr) : list rwcompN :=
  let nodes := filter (fun a => negb (instr_eqb (rw_instr a) tg)) closure in
  let '(im, arr) := iintern nodes in
  let g := irows_tr tm L T tg im nodes in
  let idxs := iidxs nodes in
  let Kc := S (S (length nodes)) in
  let rfuel := S (length nodes * 8 + 8) in
  match iproc_rounds_binary_tr 300 tm arr Kc rfuel idxs g [] with
  | Some comps => comps
  | None => []
  end.


Definition rw_binary_tier_tr (tm : TM) (L T t fuel M : nat) : bool :=
  match csteps tm t c0 with
  | None => false
  | Some cc =>
      match close rconf rconf_enc (rw_succs_cut M tm L T) fuel
        [] PositiveSet.empty [rw_seed L T cc] with
      | None => false
      | Some Sl =>
          rw_check_binary_neverqhtr_closed tm L T t M Sl
            (fun tg =>
              if cfires tm c0 t tg ||
                 existsb (fun a => instr_eqb (rw_instr a) tg) Sl
              then rw_binary_procedure_tr tm L T Sl tg else [])
      end
  end.
Theorem rw_binary_tier_tr_sound : forall tm L T t fuel M,
  rw_binary_tier_tr tm L T t fuel M = true -> NeverQuasiHaltsTr tm.
Proof.
  intros tm L T t fuel M H. unfold rw_binary_tier_tr in H.
  destruct (csteps tm t c0) as [cc|] eqn:Ecc; [|discriminate].
  destruct (close rconf rconf_enc (rw_succs_cut M tm L T) fuel
    [] PositiveSet.empty [rw_seed L T cc]) as [Sl|] eqn:Ecl;
    [|discriminate].
  rewrite rw_check_binary_neverqhtr_closed_spec in H.
  rewrite (rw_check_neverqhtr_closed_spec tm L T t fuel M cc Sl _ Ecc Ecl) in H.
  eapply rw_check_neverqhtr_sound. exact H.
Qed.

(* Assumption audit for certificate translation and tier soundness. *)
Print Assumptions rpmN_of_legacy.
Print Assumptions rw_binary_epres_legacy.
Print Assumptions rw_check_binary_neverqhtr_closed_spec.
Print Assumptions rw_binary_tier_tr_sound.
