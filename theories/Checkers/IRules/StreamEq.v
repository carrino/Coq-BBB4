(** * IRules.StreamEq: symbolic cell-stream equality for the v5 end-match.

    The Phase-2 meta-cycle replay ([MetaBlkPfx.breplayKP]) closes when the
    replayed configuration equals the shifted template [bwantp_cfg].  The
    landed [RulesBlk.bend_eqb] recognises this only up to
    constant-count block re-encoding ([bstreams_eq] / [bcanon_rle]).  A
    family of BBB-verified certificates (the "v5 rule-replay gap": 45
    list-C never-QH machines the C prover's [bin/verify] accepts) close
    on a configuration that is CELL-equal to the template but whose run
    decomposition splits a variable-count block run against surrounding
    constant runs -- e.g. [b2^(4+3k) . b0 . b1] denotes the same tape as
    [b2^(5+3k)] but has three runs versus one.  [bstreams_eq] cannot
    expand the variable-count block, so it refuses; the C verifier's
    [iv_streams_eq] walks the cells symbolically and accepts.

    This module supplies a sound recognizer for that corner.  The
    meta-cycle replay works over a SINGLE variable [k] ([lo = [kmin]]),
    so every run count is affine [c0 + c1*k] and each side of the
    denoted tape has the shape [U ++ W^(k-k0) ++ V] with [U],[V]
    constant cell words and [W] the per-step growth of the one
    variable run.  Two such one-pump words are equal for ALL [k >= k0]
    iff they are equal at [k = k0] and [k = k0+1] (a conjugacy
    induction, [one_pump_all]); no combinatorics-on-words decision
    procedure is needed.

    [cseq] is UNTRUSTED search-shaped (it extracts [U,W,V] and does two
    concrete cell-string comparisons); [cseq_sound] is the only new
    trust surface, and it reduces the accepted case to the two landed
    facts.  [Print Assumptions cseq_sound] /
    [bend_eqb2_bsem] is [functional_extensionality_dep] only. *)

From Coq Require Import Arith ZArith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers.IRules Require Import Expr RLE Engine EngineK RulesBlk.
Import ListNotations.
Open Scope Z_scope.

(** ** One-pump word conjugacy (the mathematical core) *)

Lemma nreps_nil : forall n, nreps (@nil Sym) n = [].
Proof. induction n as [|n IH]; [reflexivity | rewrite nreps_S, IH; reflexivity]. Qed.

Lemma conj_pow : forall (X D Y : list Sym),
  X ++ D = D ++ Y ->
  forall t, nreps X t ++ D = D ++ nreps Y t.
Proof.
  intros X D Y H. induction t as [|t IH]; simpl.
  - rewrite app_nil_r. reflexivity.
  - rewrite nreps_S. rewrite <- app_assoc, IH.
    rewrite app_assoc, H, <- app_assoc. reflexivity.
Qed.

Lemma app_split : forall (U V U' V' : list Sym),
  U ++ V = U' ++ V' -> (length U <= length U')%nat ->
  exists D, U' = U ++ D /\ V = D ++ V'.
Proof.
  induction U as [|x U IH]; intros V U' V' Heq Hlen; simpl in *.
  - exists U'. split; [reflexivity | exact Heq].
  - destruct U' as [|y U']; simpl in *; [lia|].
    injection Heq as Hxy Heq'. subst y.
    apply le_S_n in Hlen.
    destruct (IH V U' V' Heq' Hlen) as [D [HU' HV]].
    exists D. split; [rewrite HU'; reflexivity | exact HV].
Qed.

Lemma one_pump_all : forall (U X V U' Y V' : list Sym),
  (length X = length Y)%nat ->
  U ++ V = U' ++ V' ->
  U ++ X ++ V = U' ++ Y ++ V' ->
  forall t, U ++ nreps X t ++ V = U' ++ nreps Y t ++ V'.
Proof.
  intros U X V U' Y V' HXY H0 H1 t.
  destruct (Nat.le_ge_cases (length U) (length U')) as [Hle|Hge].
  - destruct (app_split U V U' V' H0 Hle) as [D [HU' HV]].
    subst U' V.
    assert (HXD : X ++ D = D ++ Y).
    { apply (app_inv_head U).
      rewrite (app_assoc U X D).
      apply (app_inv_tail V').
      rewrite <- !app_assoc. rewrite <- !app_assoc in H1. exact H1. }
    replace (nreps X t ++ (D ++ V')) with ((nreps X t ++ D) ++ V')
      by (rewrite app_assoc; reflexivity).
    rewrite (conj_pow X D Y HXD t).
    rewrite <- !app_assoc. reflexivity.
  - destruct (app_split U' V' U V ltac:(symmetry; exact H0) Hge) as [D [HU HV]].
    subst U V'.
    assert (HYD : Y ++ D = D ++ X).
    { apply (app_inv_head U').
      rewrite (app_assoc U' Y D).
      apply (app_inv_tail V).
      rewrite <- !app_assoc. rewrite <- !app_assoc in H1. symmetry. exact H1. }
    replace (nreps Y t ++ (D ++ V)) with ((nreps Y t ++ D) ++ V)
      by (rewrite app_assoc; reflexivity).
    rewrite (conj_pow Y D X HYD t).
    rewrite <- !app_assoc. reflexivity.
Qed.

(** ** Single-variable expression facts *)

(** A run count is "single variable" when all coefficients beyond
    index 0 vanish; then it depends only on [nu 0]. *)
Definition sv_cf (cf : list Z) : bool := cf_zeros (skipn 1 cf).

Lemma dot_sv : forall cf nu,
  sv_cf cf = true -> dot cf nu 0 = nth 0 cf 0 * nu 0%nat.
Proof.
  intros cf nu H. destruct cf as [|c t]; simpl in *.
  - lia.
  - unfold sv_cf in H. simpl in H.
    rewrite (cf_zeros_dot t nu 1 H). lia.
Qed.

Lemma eval_sv : forall e nu,
  sv_cf (e_cf e) = true -> eval nu e = e_c0 e + nth 0 (e_cf e) 0 * nu 0%nat.
Proof.
  intros e nu H. unfold eval. rewrite (dot_sv _ nu H). reflexivity.
Qed.

(** ** Concrete (constant) runs are valuation-independent *)

Definition sv_const_run (r : BRun) : bool :=
  sv_cf (e_cf (snd r)) && Z.eqb (nth 0 (e_cf (snd r)) 0) 0.

Lemma cnt_const : forall e f g,
  sv_const_run (0%nat, e) = true -> cnt f e = cnt g e.
Proof.
  intros e f g H. unfold sv_const_run, cnt in *. simpl in H.
  apply andb_prop in H as [Hsv Hc0].
  apply Z.eqb_eq in Hc0.
  rewrite (eval_sv e f Hsv), (eval_sv e g Hsv), Hc0. reflexivity.
Qed.

Lemma bdside_const_eq : forall tbl rs f g,
  forallb sv_const_run rs = true ->
  bdside tbl f rs = bdside tbl g rs.
Proof.
  induction rs as [|[s e] t IH]; intros f g H; [reflexivity|].
  simpl in H. apply andb_prop in H as [Hr Ht].
  rewrite !bdside_cons, (IH f g Ht).
  rewrite (cnt_const e f g Hr). reflexivity.
Qed.

(** ** The one-pump extractor (UNTRUSTED) *)

(** [exp1 tbl k0 rs = Some (U, A, V)] means [rs] has at most one
    variable run and the tape it denotes at valuation [k = k0 + t] is
    [U ++ A^t ++ V], with [U],[V] concrete words and [A] the block word
    added per unit of [k]. *)
Fixpoint exp1 (tbl : BTbl) (k0 : Z) (rs : list BRun)
  : option (list Sym * list Sym * list Sym) :=
  match rs with
  | [] => Some ([], [], [])
  | (s, e) :: rest =>
      if sv_cf (e_cf e) then
        let c1 := nth 0 (e_cf e) 0 in
        let v0 := cnt (fun _ => k0) e in
        if Z.eqb c1 0 then
          match exp1 tbl k0 rest with
          | Some (U, A, V) => Some (nreps (tbl s) v0 ++ U, A, V)
          | None => None
          end
        else if (0 <=? c1) && (0 <=? eval (fun _ => k0) e) then
          if forallb sv_const_run rest
          then Some (nreps (tbl s) v0,
                     nreps (tbl s) (Z.to_nat c1),
                     bdside tbl (fun _ => k0) rest)
          else None
        else None
      else None
  end.

Lemma exp1_bdside : forall tbl k0 rs U A V nu,
  exp1 tbl k0 rs = Some (U, A, V) ->
  k0 <= nu 0%nat ->
  bdside tbl nu rs = U ++ nreps A (Z.to_nat (nu 0%nat - k0)) ++ V.
Proof.
  intros tbl k0 rs. induction rs as [|[s e] rest IH];
    intros U A V nu Hexp Hle; simpl in Hexp.
  - injection Hexp as <- <- <-. rewrite nreps_nil. reflexivity.
  - destruct (sv_cf (e_cf e)) eqn:Hsv; [|discriminate].
    set (c1 := nth 0 (e_cf e) 0) in *.
    set (t := Z.to_nat (nu 0%nat - k0)).
    assert (Hnu0 : nu 0%nat = k0 + Z.of_nat t)
      by (unfold t; rewrite Z2Nat.id by lia; lia).
    rewrite bdside_cons.
    destruct (Z.eqb c1 0) eqn:Hc1.
    + (* constant run *)
      apply Z.eqb_eq in Hc1.
      destruct (exp1 tbl k0 rest) as [[[U0 A0] V0]|] eqn:Hrec; [|discriminate].
      injection Hexp as <- <- <-.
      assert (Hcnt : cnt nu e = cnt (fun _ => k0) e).
      { unfold cnt. rewrite (eval_sv e nu Hsv), (eval_sv e (fun _ => k0) Hsv).
        fold c1. rewrite Hc1. lia. }
      rewrite Hcnt.
      rewrite (IH U0 A0 V0 nu eq_refl Hle).
      rewrite <- app_assoc. reflexivity.
    + (* the single variable run *)
      destruct ((0 <=? c1) && (0 <=? eval (fun _ => k0) e)) eqn:Hg; [|discriminate].
      apply andb_prop in Hg as [Hc1pos Hv0pos].
      apply Z.leb_le in Hc1pos, Hv0pos.
      destruct (forallb sv_const_run rest) eqn:Hrest; [|discriminate].
      injection Hexp as <- <- <-.
      (* value of the variable run count at nu *)
      assert (Heval : eval nu e = eval (fun _ => k0) e + c1 * Z.of_nat t).
      { rewrite (eval_sv e nu Hsv), (eval_sv e (fun _ => k0) Hsv).
        fold c1. rewrite Hnu0. lia. }
      assert (Hcnt : cnt nu e = (cnt (fun _ => k0) e + Z.to_nat c1 * t)%nat).
      { unfold cnt. rewrite Heval.
        rewrite Z2Nat.inj_add by (try lia; apply Z.mul_nonneg_nonneg; lia).
        rewrite Z2Nat.inj_mul by lia. rewrite Nat2Z.id. reflexivity. }
      rewrite Hcnt.
      rewrite nreps_add, nreps_mul.
      rewrite (bdside_const_eq tbl rest nu (fun _ => k0) Hrest).
      rewrite <- app_assoc. reflexivity.
Qed.

(** [exp1] guarantees every run is single-variable, so the whole side
    only sees [nu 0]. *)
Lemma exp1_sv : forall tbl k0 rs U A V nu,
  exp1 tbl k0 rs = Some (U, A, V) ->
  bdside tbl nu rs = bdside tbl (fun _ => nu 0%nat) rs.
Proof.
  intros tbl k0 rs. induction rs as [|[s e] rest IH];
    intros U A V nu Hexp; [reflexivity|].
  simpl in Hexp.
  destruct (sv_cf (e_cf e)) eqn:Hsv; [|discriminate].
  rewrite !bdside_cons.
  assert (Hcnt : cnt nu e = cnt (fun _ => nu 0%nat) e).
  { unfold cnt. rewrite (eval_sv e nu Hsv), (eval_sv e (fun _ => nu 0%nat) Hsv).
    reflexivity. }
  rewrite Hcnt. f_equal.
  destruct (Z.eqb (nth 0 (e_cf e) 0) 0) eqn:Hc1.
  - destruct (exp1 tbl k0 rest) as [[[U0 A0] V0]|] eqn:Hrec; [|discriminate].
    exact (IH U0 A0 V0 nu eq_refl).
  - destruct ((0 <=? nth 0 (e_cf e) 0) && (0 <=? eval (fun _ => k0) e));
      [|discriminate].
    destruct (forallb sv_const_run rest) eqn:Hrest; [|discriminate].
    apply (bdside_const_eq tbl rest nu (fun _ => nu 0%nat) Hrest).
Qed.

(** ** The recognizer *)

Fixpoint lsym_eqb (a b : list Sym) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => sym_eqb x y && lsym_eqb a' b'
  | _, _ => false
  end.

Lemma lsym_eqb_eq : forall a b, lsym_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros b H; destruct b as [|y b];
    simpl in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [Hxy Ht].
  apply sym_eqb_spec in Hxy. rewrite Hxy, (IH b Ht). reflexivity.
Qed.

(** Symbolic cell-stream equality of two run lists, for every valuation
    with [nu 0 >= nth 0 lo 0].  Sound but incomplete; complements
    [bstreams_eq] on the one-pump v5 corner. *)
Definition cseq (tbl : BTbl) (lo : list Z) (xa xb : list BRun) : bool :=
  let k0 := nth 0 lo 0 in
  match exp1 tbl k0 xa, exp1 tbl k0 xb with
  | Some (Ua, Aa, Va), Some (Ub, Ab, Vb) =>
      lsym_eqb (Ua ++ Va) (Ub ++ Vb)
      && lsym_eqb (Ua ++ Aa ++ Va) (Ub ++ Ab ++ Vb)
      && Nat.eqb (length Aa) (length Ab)
  | _, _ => false
  end.

Theorem cseq_sound : forall tbl lo xa xb nu,
  bge lo nu ->
  cseq tbl lo xa xb = true ->
  bdside tbl nu xa = bdside tbl nu xb.
Proof.
  intros tbl lo xa xb nu Hb H. unfold cseq in H.
  set (k0 := nth 0 lo 0) in *.
  destruct (exp1 tbl k0 xa) as [[[Ua Aa] Va]|] eqn:Ha; [|discriminate].
  destruct (exp1 tbl k0 xb) as [[[Ub Ab] Vb]|] eqn:Hbx; [|discriminate].
  apply andb_prop in H as [H Hlen].
  apply andb_prop in H as [H0 H1].
  apply Nat.eqb_eq in Hlen.
  apply lsym_eqb_eq in H0, H1.
  (* nu 0 >= k0 *)
  assert (Hk0 : k0 <= nu 0%nat).
  { unfold k0. specialize (Hb 0%nat). exact Hb. }
  set (t := Z.to_nat (nu 0%nat - k0)).
  (* reduce each side to the one-pump normal form at k = nu 0 *)
  rewrite (exp1_sv tbl k0 xa Ua Aa Va nu Ha).
  rewrite (exp1_sv tbl k0 xb Ub Ab Vb nu Hbx).
  assert (Hk0' : k0 <= (fun _ : nat => nu 0%nat) 0%nat) by exact Hk0.
  rewrite (exp1_bdside tbl k0 xa Ua Aa Va (fun _ => nu 0%nat) Ha Hk0').
  rewrite (exp1_bdside tbl k0 xb Ub Ab Vb (fun _ => nu 0%nat) Hbx Hk0').
  simpl. fold t.
  exact (one_pump_all Ua Aa Va Ub Ab Vb Hlen H0 H1 t).
Qed.

(** ** The v5 end-match and its denotation soundness *)

Definition bend_eqb2 (tbl : BTbl) (lo : list Z) (c want : BCfg) : bool :=
  bend_eqb tbl lo c want
  || (st_eqb (b_st c) (b_st want) && sym_eqb (b_hs c) (b_hs want)
      && cseq tbl lo (b_L c) (b_L want)
      && cseq tbl lo (b_R c) (b_R want)).

Theorem bend_eqb2_bsem : forall tbl lo c want nu,
  raw_ok tbl -> bge lo nu ->
  bend_eqb2 tbl lo c want = true -> bsem tbl nu c = bsem tbl nu want.
Proof.
  intros tbl lo c want nu Hraw Hb H. unfold bend_eqb2 in H.
  apply orb_prop in H as [H | H].
  - exact (bend_eqb_bsem tbl lo c want nu Hraw Hb H).
  - apply andb_prop in H as [H HR].
    apply andb_prop in H as [H HL].
    apply andb_prop in H as [Hst Hhs].
    apply st_eqb_spec in Hst. apply sym_eqb_spec in Hhs.
    unfold bsem, bdcfg. rewrite Hst, Hhs.
    rewrite (cseq_sound tbl lo _ _ nu Hb HL).
    rewrite (cseq_sound tbl lo _ _ nu Hb HR). reflexivity.
Qed.
