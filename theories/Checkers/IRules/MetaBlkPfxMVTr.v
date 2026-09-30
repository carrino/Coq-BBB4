(** * IRules.MetaBlkPfxMVTr: the Phase-2 block certificate checker with
    the v4 MATRIX meta map, at TRANSITION level.

    [MetaBlkPfxTr.irulesblkpfx_check_neverqhtr] fixes one meta variable
    [k] and a scalar cycle [C(k) ->* C(a k + b)].  BBB's [bin/irules]
    also emits certificates with [nvar] = 2 or 3 meta variables and an
    affine map [x -> M x + c] ([nvar], [mmrow], [xmin], [x0],
    [tplrunmv]: every template run's count is one meta variable plus a
    constant, or a constant).  The doubling bouncers of class SP whose
    tape carries two independently growing blocks need it (SCOPING_INSTR.md
    7.4.SPW).  [MetaBlkPfx]'s header notes that none of its Phase-2
    certificates used the matrix map, so it was never ported.

    Everything below the meta layer is reused verbatim: the rules are
    [RulesBlkPfx] prefix block rules validated by [check_rulesBlkP], and
    the meta cycle is replayed by [breplayKP], which is generic in the
    bounds vector [lo] and the valuation [nu].  Only the scalar pieces
    change:

    - a valuation [nu : nat -> Z] replaces [fun _ => K], and the anchor
      valuation is [x0] read by [nth];
    - the bounds vector is [xmin] instead of [[kmin]];
    - the next valuation is [mstep M cc nu i = M_i . nu + cc_i], and the
      want template is the start template with each run's variable
      replaced by its row ([mvwant_shift]);
    - the inward check [xmin <= M xmin + cc] with [M >= 0] makes the
      bounds an invariant of [mstep] ([mstep_bge]).

    The anchor gate is [MetaBlkPfxTr]'s, with [nu] in place of [K]; the
    recurrence argument is [MetaTileTr.meta_tile_neverqhtr].  There are
    two checkers, one per replay engine: the plain [MetaBlkPfx] one and
    the v5c one of [MetaBlkPfxV5c] (see [MetaBlkPfxV5cTr]).

    [Print Assumptions irulesblkmv_check_neverqhtr_sound] and
    [irulesblkmv_check_neverqhtr_v5c_sound] must be
    [functional_extensionality_dep] only. *)

From Coq Require Import Arith ZArith Lia Bool List Setoid.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
From BBB4.Checkers.IRules Require Import AnchorVisits AnchorVisitsTr MetaTr.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta RulesK
     EngineK RulesBlk MetaBlk EngineKS RulesBlkPfx MetaBlkPfx StreamEq
     MetaBlkPfxV5 Reblock MetaBlkPfxV5b BlkClosure StreamEq2 MetaBlkPfxV5c
     MetaTileTr.
Import ListNotations.
Open Scope Z_scope.

(** ** Templates over several meta variables *)

(** A template run: block symbol, the meta variable its count follows
    ([None]: a constant run), and the constant added to it. *)
Definition BTRunMV : Set := (BSym * option nat * Z)%type.

Fixpoint unit_cf (i : nat) : list Z :=
  match i with
  | O => [1]
  | S j => 0 :: unit_cf j
  end.

Definition mv_start (r : BTRunMV) : BRun :=
  let '(s, mv, be) := r in
  match mv with
  | None => (s, mkExpr be [])
  | Some i => (s, mkExpr be (unit_cf i))
  end.

Definition mv_want (M : list (list Z)) (cc : list Z) (r : BTRunMV) : BRun :=
  let '(s, mv, be) := r in
  match mv with
  | None => (s, mkExpr be [])
  | Some i => (s, mkExpr (nth i cc 0 + be) (nth i M []))
  end.

(** The meta map on valuations. *)
Definition mstep (M : list (list Z)) (cc : list Z) (nu : nat -> Z) : nat -> Z :=
  fun i => dot (nth i M []) nu 0 + nth i cc 0.

Definition xnu (x : list Z) : nat -> Z := fun i => nth i x 0.

Lemma dot_unit : forall i nu j, dot (unit_cf i) nu j = nu (j + i)%nat.
Proof.
  induction i as [|i IH]; intros nu j; cbn [unit_cf dot].
  - rewrite Nat.add_0_r. ring.
  - rewrite IH. replace (S j + i)%nat with (j + S i)%nat by lia. ring.
Qed.

Lemma mv_shift_run : forall M cc nu r,
  cnt nu (snd (mv_want M cc r)) = cnt (mstep M cc nu) (snd (mv_start r)) /\
  fst (mv_want M cc r) = fst (mv_start r).
Proof.
  intros M cc nu [[s [i|]] be]; simpl; split; try reflexivity.
  unfold cnt, eval; cbn [e_c0 e_cf].
  rewrite dot_unit. unfold mstep. simpl. f_equal. ring.
Qed.

Lemma mvwant_shift : forall tbl M cc nu rs,
  bdside tbl nu (map (mv_want M cc) rs) =
  bdside tbl (mstep M cc nu) (map mv_start rs).
Proof.
  induction rs as [|r t IH]; [reflexivity|].
  simpl map. destruct (mv_want M cc r) as [s1 e1] eqn:Hw.
  destruct (mv_start r) as [s2 e2] eqn:Hs.
  destruct (mv_shift_run M cc nu r) as [Hc Hf].
  rewrite Hw, Hs in Hc, Hf. simpl in Hc, Hf. subst s2.
  rewrite !bdside_cons, IH, Hc. reflexivity.
Qed.

(** ** The bounds are an invariant of the meta map *)

(** [xmin_i <= M_i . xmin + cc_i] for every index that any of the three
    lists reaches (beyond them every term is 0). *)
Definition mv_inward (M : list (list Z)) (cc xmin : list Z) : bool :=
  forallb (fun i => nth i xmin 0 <=? mstep M cc (xnu xmin) i)
          (seq 0 (length xmin + length M + length cc)).

Lemma mstep_bge : forall M cc xmin nu,
  forallb cf_nonneg M = true ->
  mv_inward M cc xmin = true ->
  bge xmin nu -> bge xmin (mstep M cc nu).
Proof.
  intros M cc xmin nu HM Hin Hb i.
  assert (Hrow : cf_nonneg (nth i M []) = true).
  { destruct (Nat.lt_ge_cases i (length M)) as [Hl|Hl].
    - rewrite forallb_forall in HM. apply HM, nth_In, Hl.
    - rewrite nth_overflow by exact Hl. reflexivity. }
  assert (Hle : mstep M cc (xnu xmin) i <= mstep M cc nu i).
  { unfold mstep. pose proof (dot_le (nth i M []) (xnu xmin) nu 0 Hrow Hb).
    lia. }
  destruct (Nat.lt_ge_cases i (length xmin + length M + length cc)) as [Hl|Hl].
  - unfold mv_inward in Hin. rewrite forallb_forall in Hin.
    specialize (Hin i (proj2 (in_seq _ _ _) (conj (Nat.le_0_l i) Hl))).
    apply Z.leb_le in Hin. lia.
  - unfold mstep, xnu in *.
    rewrite (nth_overflow xmin) by lia.
    rewrite (nth_overflow M) in Hle |- * by lia.
    rewrite (nth_overflow cc) in Hle |- * by lia.
    simpl in *. lia.
Qed.

(** [xmin <= x0] componentwise. *)
Definition mv_le (xmin x0 : list Z) : bool :=
  forallb (fun i => nth i xmin 0 <=? nth i x0 0)
          (seq 0 (length xmin + length x0)).

Lemma mv_le_bge : forall xmin x0,
  mv_le xmin x0 = true -> bge xmin (xnu x0).
Proof.
  intros xmin x0 H i. unfold xnu.
  destruct (Nat.lt_ge_cases i (length xmin + length x0)) as [Hl|Hl].
  - unfold mv_le in H. rewrite forallb_forall in H.
    specialize (H i (proj2 (in_seq _ _ _) (conj (Nat.le_0_l i) Hl))).
    apply Z.leb_le in H. exact H.
  - rewrite !nth_overflow by lia. lia.
Qed.

(** ** The certificate record *)

Record BIRCertMV : Set := mkBIRCertMV {
  cmv_anchor : nat;
  cmv_x0 : list Z;
  cmv_xmin : list Z;
  cmv_M : list (list Z);
  cmv_cc : list Z;
  cmv_st : St;
  cmv_hs : Sym;
  cmv_blks : list (nat * list Sym);
  cmv_TL : list BTRunMV;
  cmv_TR : list BTRunMV;
  cmv_rules : list BRuleP
}.

Definition bmv_start (cert : BIRCertMV) : BCfg :=
  mkBCfg (cmv_st cert) (cmv_hs cert)
         (map mv_start (cmv_TL cert)) (map mv_start (cmv_TR cert)).

Definition bmv_want (cert : BIRCertMV) : BCfg :=
  mkBCfg (cmv_st cert) (cmv_hs cert)
         (map (mv_want (cmv_M cert) (cmv_cc cert)) (cmv_TL cert))
         (map (mv_want (cmv_M cert) (cmv_cc cert)) (cmv_TR cert)).

Definition mstepc (cert : BIRCertMV) : (nat -> Z) -> nat -> Z :=
  mstep (cmv_M cert) (cmv_cc cert).

Lemma bmv_want_shift : forall tbl cert nu,
  bsem tbl nu (bmv_want cert) = bsem tbl (mstepc cert nu) (bmv_start cert).
Proof.
  intros. unfold bsem, bdcfg, bmv_want, bmv_start, mstepc.
  cbn [b_st b_hs b_L b_R].
  rewrite !mvwant_shift. reflexivity.
Qed.

(** ** The checkers

    Two engines: the plain [MetaBlkPfx] replay, and the v5c one
    ([MetaBlkPfxV5c]: closed block table, re-blocking replay, multi-run
    cell-stream end-match), whose pieces are all generic in the bounds
    vector and the valuation.  The meta layer is the same for both;
    [mv_meta_sound] proves it once, from the engine's cycle. *)

Definition mv_gate (tm : TM) (tbl : BTbl) (cert : BIRCertMV) (F : list Tr)
    : bool :=
  match csteps_tvis tm (cmv_anchor cert) c0 tvm_empty with
  | Some (q, (l, h, r), tvis) =>
      st_eqb q (cmv_st cert) && sym_eqb h (cmv_hs cert) &&
      lpad_eqb l (bdside tbl (xnu (cmv_x0 cert))
                    (map mv_start (cmv_TL cert))) &&
      lpad_eqb r (bdside tbl (xnu (cmv_x0 cert))
                    (map mv_start (cmv_TR cert))) &&
      forallb (fun t => implb (tvm_get tvis t) (tr_in t F)) all_Instr
  | None => false
  end.

Definition mv_scalars (cert : BIRCertMV) : bool :=
  mv_le (cmv_xmin cert) (cmv_x0 cert) &&
  forallb cf_nonneg (cmv_M cert) &&
  mv_inward (cmv_M cert) (cmv_cc cert) (cmv_xmin cert).

Lemma mv_meta_sound : forall tm tbl cert F,
  mv_scalars cert = true ->
  mv_gate tm tbl cert F = true ->
  (forall nu, bge (cmv_xmin cert) nu ->
     exists n, (1 <= n)%nat /\
       Reach tm F n (bsem tbl nu (bmv_start cert))
                    (bsem tbl (mstepc cert nu) (bmv_start cert))) ->
  NeverQuasiHaltsTr tm.
Proof.
  intros tm tbl cert F Hs Hg Hcycle.
  unfold mv_scalars in Hs.
  apply andb_prop in Hs as [Hs Hinward].
  apply andb_prop in Hs as [Hx0 HM].
  unfold mv_gate in Hg.
  destruct (csteps_tvis tm (cmv_anchor cert) c0 tvm_empty)
    as [[[q1 [[l1 h1] r1]] tvis]|] eqn:Hanchv; [|discriminate].
  pose proof (csteps_tvis_csteps _ _ _ _ _ _ Hanchv) as Hanch.
  apply andb_prop in Hg as [Hg Hpre].
  apply andb_prop in Hg as [Hg HpadR].
  apply andb_prop in Hg as [Hg HpadL].
  apply andb_prop in Hg as [Hq1 Hh1].
  apply st_eqb_spec in Hq1. apply sym_eqb_spec in Hh1.
  apply (meta_tile_neverqhtr tm (nat -> Z) (bge (cmv_xmin cert))
           (fun nu => bsem tbl nu (bmv_start cert)) (mstepc cert) F
           (cmv_anchor cert) (xnu (cmv_x0 cert)) (q1, (l1, h1, r1)) tvis);
    [| exact (mv_le_bge _ _ Hx0) | | exact Hcycle | exact Hanchv | exact Hpre].
  - rewrite <- lift_c0.
    rewrite (csteps_lift _ _ _ _ Hanch).
    f_equal.
    unfold bsem, bdcfg, bmv_start. cbn [b_st b_hs b_L b_R].
    rewrite !lift_cc, Hq1, Hh1.
    rewrite (lpad_eqb_lift _ _ HpadL), (lpad_eqb_lift _ _ HpadR).
    reflexivity.
  - intros nu Hb. exact (mstep_bge _ _ _ nu HM Hinward Hb).
Qed.

(** *** The plain engine *)

Definition irulesblkmv_check_neverqhtr (tm : TM) (cert : BIRCertMV)
    (cfuel fuel : nat) : bool :=
  let blks := cmv_blks cert in
  let tbl := mk_tbl blks in
  let lo := cmv_xmin cert in
  mv_scalars cert &&
  match check_rulesBlkP tm tbl blks cfuel fuel (cmv_rules cert) with
  | None => false
  | Some rules =>
      match breplayKP tm tbl blks lo cfuel rules
              (fun c => bend_eqb tbl lo c (bmv_want cert))
              (false, false) fuel false (bmv_start cert) with
      | None => false
      | Some (_, F) => mv_gate tm tbl cert F
      end
  end.

Theorem irulesblkmv_check_neverqhtr_sound : forall tm cert cfuel fuel,
  irulesblkmv_check_neverqhtr tm cert cfuel fuel = true ->
  NeverQuasiHaltsTr tm.
Proof.
  intros tm cert cfuel fuel H.
  unfold irulesblkmv_check_neverqhtr in H. cbv zeta in H.
  set (blks := cmv_blks cert) in *.
  set (tbl := mk_tbl blks) in *.
  set (lo := cmv_xmin cert) in *.
  pose proof (mk_tbl_raw blks) as Hraw.
  apply andb_prop in H as [Hs H].
  destruct (check_rulesBlkP tm tbl blks cfuel fuel (cmv_rules cert))
    as [rules|] eqn:Hcr; [|discriminate].
  destruct (breplayKP tm tbl blks lo cfuel rules
              (fun c => bend_eqb tbl lo c (bmv_want cert))
              (false, false) fuel false (bmv_start cert)) as [[cend F]|]
    eqn:Hrep; [|discriminate].
  apply (mv_meta_sound tm tbl cert F Hs H).
  intros nu Hb.
  destruct (breplayKP_sound tm tbl blks lo cfuel rules _
              (false, false) fuel false
              (bmv_start cert) cend F Hraw Hrep nu [] [] Hb
              (fun _ => eq_refl) (fun _ => eq_refl))
    as (Hend & n & HR & Hpos).
  { intros r Fr c1 c2 Hin Happ.
    exact (ruleBlkPfx_apply_sound tm tbl lo r Fr c1 c2
             (false, false) Hraw Happ
             (check_rulesBlkP_sound tm tbl blks cfuel fuel _ _ Hraw Hcr
                r Fr Hin)
             nu Hb [] [] (fun _ => eq_refl) (fun _ => eq_refl)). }
  exists n. split; [apply Hpos; reflexivity|].
  rewrite !bsemX_nil in HR.
  setoid_rewrite (bend_eqb_bsem tbl lo cend (bmv_want cert)
                    nu Hraw Hb Hend) in HR.
  setoid_rewrite (bmv_want_shift tbl cert nu) in HR.
  exact HR.
Qed.

(** *** The v5c engine *)

Definition irulesblkmv_check_neverqhtr_v5c (tm : TM) (cert : BIRCertMV)
    (cfuel fuel : nat) : bool :=
  let blks := blk_closure tm (cmv_blks cert) v5c_closure_fuel in
  let tbl := mk_tbl blks in
  let lo := cmv_xmin cert in
  mv_scalars cert &&
  match check_rulesRB tm tbl blks cfuel fuel (cmv_rules cert) with
  | None => false
  | Some rules =>
      match breplayRB tm tbl blks lo cfuel rules
              (fun c => bend_eqb3 tbl lo c (bmv_want cert))
              (false, false) fuel false (bmv_start cert) with
      | None => false
      | Some (_, F) => mv_gate tm tbl cert F
      end
  end.

Theorem irulesblkmv_check_neverqhtr_v5c_sound : forall tm cert cfuel fuel,
  irulesblkmv_check_neverqhtr_v5c tm cert cfuel fuel = true ->
  NeverQuasiHaltsTr tm.
Proof.
  intros tm cert cfuel fuel H.
  unfold irulesblkmv_check_neverqhtr_v5c in H. cbv zeta in H.
  set (blks := blk_closure tm (cmv_blks cert) v5c_closure_fuel) in *.
  set (tbl := mk_tbl blks) in *.
  set (lo := cmv_xmin cert) in *.
  pose proof (mk_tbl_raw blks) as Hraw.
  apply andb_prop in H as [Hs H].
  destruct (check_rulesRB tm tbl blks cfuel fuel (cmv_rules cert))
    as [rules|] eqn:Hcr; [|discriminate].
  destruct (breplayRB tm tbl blks lo cfuel rules
              (fun c => bend_eqb3 tbl lo c (bmv_want cert))
              (false, false) fuel false (bmv_start cert)) as [[cend F]|]
    eqn:Hrep; [|discriminate].
  apply (mv_meta_sound tm tbl cert F Hs H).
  intros nu Hb.
  destruct (breplayRB_sound tm tbl blks lo cfuel rules _
              (false, false) fuel false
              (bmv_start cert) cend F Hraw Hrep nu [] [] Hb
              (fun _ => eq_refl) (fun _ => eq_refl))
    as (Hend & n & HR & Hpos).
  { intros r Fr c1 c2 Hin Happ.
    exact (ruleBlkPfx_apply_sound tm tbl lo r Fr c1 c2
             (false, false) Hraw Happ
             (check_rulesRB_sound tm tbl blks cfuel fuel _ _ Hraw Hcr
                r Fr Hin)
             nu Hb [] [] (fun _ => eq_refl) (fun _ => eq_refl)). }
  exists n. split; [apply Hpos; reflexivity|].
  rewrite !bsemX_nil in HR.
  setoid_rewrite (bend_eqb3_bsem tbl lo cend (bmv_want cert)
                    nu Hraw Hb Hend) in HR.
  setoid_rewrite (bmv_want_shift tbl cert nu) in HR.
  exact HR.
Qed.
