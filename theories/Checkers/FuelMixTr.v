(** * FuelMixTr: nonnegative sums of exact pattern measures.

    A sum of pattern counts is a natural-valued measure. Its delta is
    the same sum of the individual exact deltas. Certificates combine
    these sums with finite node potentials, ranks and the existing
    fuel runner rule. Search coefficients are untrusted: the checker
    verifies every edge using integer arithmetic. *)

From Coq Require Import Arith Lia Bool List ZArith Ring.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape PosEnc
  Records Closure.
From BBB4.Checkers Require Import ExactClosure NGram NGramTr Fuel FuelClass
  FuelWide FuelSCCTr FuelWideTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Definition fmxterm : Type := (nat * list Sym * ngreg)%type.

Fixpoint fmx_val (terms : list fmxterm) (cc : cconf) : nat :=
  match terms with
  | [] => 0
  | (w, p, rg) :: rest => w * pm_val p rg cc + fmx_val rest cc
  end.

Fixpoint fmx_delta (tm : TM) (terms : list fmxterm) (a a' : cconf) : Z :=
  match terms with
  | [] => 0%Z
  | (w, p, rg) :: rest =>
      (Z.of_nat w * pm_delta tm p rg a a' + fmx_delta tm rest a a')%Z
  end.

Definition fmx_ok (n : nat) (terms : list fmxterm) : bool :=
  forallb (fun term => let '(_, p, rg) := term in pm_ok n p rg) terms.

Lemma fmx_exact : forall tm n lset rset terms a cc a' cc',
  fmx_ok n terms = true ->
  ng_covers n lset rset a (lift cc) ->
  cstep tm cc = Some cc' ->
  Z.of_nat (fmx_val terms cc') =
    (Z.of_nat (fmx_val terms cc) + fmx_delta tm terms a a')%Z.
Proof.
  intros tm n lset rset terms.
  induction terms as [|[[w p] rg] rest IH]; intros a cc a' cc' Hok Hcov Hstep.
  - reflexivity.
  - cbn [fmx_ok forallb] in Hok.
    apply andb_prop in Hok as [Hp Hr].
    assert (Hex : Z.of_nat (pm_val p rg cc') =
        (Z.of_nat (pm_val p rg cc) + pm_delta tm p rg a a')%Z).
    { apply (pm_exact tm n lset rset p rg a cc a' cc'); try assumption.
      - unfold pm_ok in Hp. apply andb_prop in Hp as [He _].
        apply existsb_exists in He as (x & Hx & Hx1).
        apply sym_eqb_spec in Hx1. subst x. assumption.
      - unfold pm_ok in Hp. apply andb_prop in Hp as [_ Hb].
        destruct rg; apply Nat.leb_le; assumption. }
    specialize (IH a cc a' cc' Hr Hcov Hstep).
    cbn [fmx_val fmx_delta].
    repeat rewrite Nat2Z.inj_add. repeat rewrite Nat2Z.inj_mul.
    rewrite Hex, IH. ring.
Qed.

Inductive fmxcomp : Type :=
| FMRankE (phi : list (positive * nat))
| FMPattSumE (terms : list fmxterm) (K : nat)
             (phi : list (positive * nat)) (gate : list positive).

Definition fmx_comp_denote (tm : TM) (n : nat) (c : fmxcomp)
    : lexcomp fcconf :=
  match c with
  | FMRankE phi => LexRank fcconf (fpmape_get (pmape_of phi))
  | FMPattSumE terms K phi gate =>
      if fmx_ok n terms then
        let pm := pmape_of phi in
        let gs := psete_of gate in
        LexMeas fcconf (fmx_val terms)
          (fun a a' => fmx_delta tm terms (fst a) (fst a')) K
          (fpmape_get pm) (fun a => PositiveSet.mem (fcconf_enc a) gs)
      else LexRank fcconf (fun _ => 0)
  end.

Definition fmx_cert_denote (tm : TM) (n : nat)
    (ct : list fmxcomp * list positive)
    : list (lexcomp fcconf) * (fcconf -> bool) :=
  (map (fmx_comp_denote tm n) (fst ct),
   let gs := psete_of (snd ct) in
   fun a => PositiveSet.mem (fcconf_enc a) gs).

Lemma fmx_comp_exact : forall tm n lset rset c,
  comp_exact tm fcconf (fw_succs tm lset rset) (fw_covers n lset rset)
    (fmx_comp_denote tm n c).
Proof.
  intros tm n lset rset [phi | terms K phi gate]; simpl; [exact I|].
  destruct (fmx_ok n terms) eqn:Hok; [|exact I].
  intros a cc a' cc' sl Hca Hca' Hstep Es HInl.
  exact (fmx_exact tm n lset rset terms (fst a) cc (fst a') cc'
           Hok (proj1 Hca) Hstep).
Qed.

Definition ngram_check_neverqh_fuelmixtr (tm : TM) (n t fuel rounds : nat)
    (cert : Instr -> list fmxcomp * list positive) : bool :=
  (1 <=? n) &&
  match csteps tm t c0 with
  | Some cc =>
      let '(q, (l, h, r)) := cc in
      let lset0 := gadds (ng_seed_side n l) gempty in
      let rset0 := gadds (ng_seed_side n r) gempty in
      let a0 := ng_start n cc in
      let '(lset, rset) := ng_grow tm a0 fuel rounds lset0 rset0 in
      ng_seed_ok n lset rset cc &&
      closure_check_neverqh_fuelscctr tm fcconf fcconf_enc fw_instr
        (fw_succs tm lset rset)
        (fwnode_moves_right tm) fwnode_rfuel_ge1
        t fuel (fw_start n cc)
        (fun q => fmx_cert_denote tm n (cert q))
  | None => false
  end.

Theorem ngram_check_neverqh_fuelmixtr_sound : forall tm n t fuel rounds cert,
  ngram_check_neverqh_fuelmixtr tm n t fuel rounds cert = true ->
  NeverQuasiHaltsTr tm.
Proof.
  intros tm n t fuel rounds cert H.
  unfold ngram_check_neverqh_fuelmixtr in H.
  apply andb_prop in H as [Hn H]. apply Nat.leb_le in Hn.
  destruct (csteps tm t c0) as [[q [[l h] r]]|] eqn:Et; [|discriminate].
  match type of H with
  | (let '(_, _) := ?G in _) = true => destruct G as [lset rset] eqn:Eg
  end.
  cbv beta iota zeta in H.
  apply andb_prop in H as [Hseed Hcheck].
  apply (closure_check_neverqh_fuelscctr_sound tm fcconf fcconf_enc fw_instr
           (fw_succs tm lset rset)
           (fwnode_moves_right tm) fwnode_rfuel_ge1
           (fw_covers n lset rset)) in Hcheck;
    [assumption | | | | | | |].
  - exact fcconf_enc_inj.
  - intros a c Hc. eapply fw_covers_instr; eauto.
  - intros a c Hc. apply fw_succs_sound; assumption.
  - intros a c Hmr Hc. eapply fwnode_moves_right_sound; eauto.
  - intros a c Hrf Hc. eapply fwnode_rfuel_ge1_sound; eauto.
  - intros ct' Hct'. rewrite Et in Hct'. injection Hct' as <-.
    apply fw_start_covers. exact Hseed.
  - intros q0. apply Forall_forall. intros comp Hin.
    cbn [fmx_cert_denote fst] in Hin.
    apply in_map_iff in Hin. destruct Hin as (c & <- & _).
    apply fmx_comp_exact.
Qed.
