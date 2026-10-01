(** * FuelWideTr: instruction-target instance of FuelWide.

    Refined contexts, their fuel classes, successor soundness and
    certificate measures are exactly FuelWide's.  Only the target
    projection and per-instruction certificate table change. *)

From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape PosEnc
  Records Closure.
From BBB4.Checkers Require Import ExactClosure NGram NGramTr Fuel FuelClass
  FuelWide FuelSCCTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Definition fw_instr (a : fcconf) : Instr := cinstr (fst a).

Lemma fw_covers_instr : forall n lset rset a c,
  fw_covers n lset rset a c -> fw_instr a = instr_of c.
Proof.
  intros n lset rset a c (Hng & _ & _).
  exact (ng_covers_instr n lset rset (fst a) c Hng).
Qed.

(** ** The checker *)

Definition ngram_check_neverqh_fuelwtr (tm : TM) (n t fuel rounds : nat)
    (cert : Instr -> list ngcomp * list positive) : bool :=
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
        (fun q => fw_cert_denote tm n (cert q))
  | None => false
  end.

Theorem ngram_check_neverqh_fuelwtr_sound : forall tm n t fuel rounds cert,
  ngram_check_neverqh_fuelwtr tm n t fuel rounds cert = true ->
  NeverQuasiHaltsTr tm.
Proof.
  intros tm n t fuel rounds cert H.
  unfold ngram_check_neverqh_fuelwtr in H.
  apply andb_prop in H as [Hn H].
  apply Nat.leb_le in Hn.
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
    cbn [fw_cert_denote fst] in Hin.
    apply in_map_iff in Hin. destruct Hin as (c & <- & _).
    destruct c as [phi | m K phi gate | phi | pp rg K phi gate]; simpl.
    + exact I.
    + intros a cc a' cc' sl Hca Hca' Hstep Es HInl.
      apply (ngm_exact tm n lset rset m (fst a) cc (fst a') cc' Hn
               (proj1 Hca) Hstep).
    + exact I.
    + destruct (pm_ok n pp rg) eqn:Epm; [|exact I].
      apply andb_prop in Epm as [He Hb].
      intros a cc a' cc' sl Hca Hca' Hstep Es HInl.
      apply (pm_exact tm n lset rset pp rg (fst a) cc (fst a') cc');
        try assumption.
      * apply existsb_exists in He as (x & Hx & Hx1).
        apply sym_eqb_spec in Hx1. subst x. assumption.
      * destruct rg; apply Nat.leb_le; assumption.
      * exact (proj1 Hca).
Qed.
