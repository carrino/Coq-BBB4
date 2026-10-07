(** * Instruction liveness from a supplied, checked closure.

    The pool and lexicographic certificates are untrusted data. Membership
    of the initial abstraction, every successor edge, and the decreasing
    certificates are checked here. No closure or rank search is needed.
    The liveness argument reuses [ClosureTr]'s invariant and lexicographic
    well-foundedness lemmas. *)
From Coq Require Import Arith Lia Bool List ZArith PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape Closure ClosureTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Section Pool.
  Variable tm : TM.
  Variable A : Type.
  Variable enc : A -> positive.
  Variable instruction : A -> Instr.
  Variable successors : A -> option (list A).

  Definition closure_pool_check_tr (t : nat) (a0 : A) (pool : list A)
      (cert : Instr -> list (lexcomp A)) : bool :=
    mem_tr A enc a0 pool && closed_tr_b A enc successors pool &&
    forallb (fun tg =>
      if cfires tm c0 t tg ||
         existsb (fun a => instr_eqb (instruction a) tg) pool
      then lex_ok_tr A instruction successors pool tg (cert tg)
      else true) all_Instr.

  Variable covers : A -> ExecState -> Prop.
  Hypothesis enc_injective : forall a b, enc a = enc b -> a = b.
  Hypothesis covers_instruction : forall a c,
    covers a c -> instruction a = instr_of c.
  Hypothesis successors_sound : forall a c, covers a c ->
    match successors a, step tm c with
    | Some l, Some c' => exists a', In a' l /\ covers a' c'
    | Some _, None => False
    | None, _ => True
    end.

  Theorem closure_pool_check_tr_sound : forall t ct a0 pool cert,
    csteps tm t c0 = Some ct ->
    covers a0 (lift ct) ->
    (forall tg, Forall (comp_exact tm A successors covers) (cert tg)) ->
    closure_pool_check_tr t a0 pool cert = true ->
    NeverQuasiHaltsTr tm.
  Proof.
    intros t ct a0 pool cert Et Hcov0 Hcert H.
    unfold closure_pool_check_tr in H.
    apply andb_prop in H as [Hpool Hq].
    apply andb_prop in Hpool as [Hin Hcl].
    apply (mem_In_tr A enc enc_injective) in Hin.
    assert (Hct : stepn tm t InitES = Some (lift ct)).
    { rewrite <- lift_c0. apply csteps_lift; assumption. }
    intros tg Hvq N.
    assert (Hro : lex_ok_tr A instruction successors pool tg (cert tg) = true).
    { rewrite forallb_forall in Hq.
      specialize (Hq tg (all_Instr_complete tg)).
      destruct Hvq as (n0 & cn & Hcn & Hqn).
      assert (Hprem : cfires tm c0 t tg ||
                      existsb (fun a => instr_eqb (instruction a) tg) pool
                      = true).
      { destruct (le_lt_dec t n0) as [Hge | Hlt].
        - apply orb_true_intro; right.
          destruct (closure_invariant_tr tm A enc successors covers
                      enc_injective successors_sound pool Hcl a0 (lift ct)
                      Hin Hcov0 (n0 - t)) as (c' & a' & Hst & HIn' & Hcov').
          assert (Hc' : stepn tm n0 InitES = Some c').
          { replace n0 with (t + (n0 - t)) by lia.
            rewrite stepn_add, Hct. assumption. }
          rewrite Hc' in Hcn. injection Hcn as <-.
          apply existsb_exists. exists a'.
          split; [assumption|].
          apply instr_eqb_spec. rewrite (covers_instruction a' c' Hcov').
          assumption.
        - apply orb_true_intro; left.
          destruct (csteps_prefix tm n0 t c0 ct) as (cn' & Hcn' & _);
            [lia | exact Et |].
          assert (Hl : stepn tm n0 InitES = Some (lift cn')).
          { rewrite <- lift_c0. apply csteps_lift; assumption. }
          rewrite Hl in Hcn. injection Hcn as <-.
          eapply cfires_complete; [exact Hlt | exact Hcn' |].
          rewrite <- cinstr_lift. exact Hqn. }
      rewrite Hprem in Hq. exact Hq. }
    set (M := Nat.max N t).
    destruct (closure_invariant_tr tm A enc successors covers
                enc_injective successors_sound pool Hcl a0 (lift ct)
                Hin Hcov0 (M - t)) as (cM & aM & HstM & HInM & HcovM).
    assert (HM : stepn tm M InitES = Some cM).
    { replace M with (t + (M - t)) by (unfold M; lia).
      rewrite stepn_add, Hct. assumption. }
    destruct (stepn_csteps tm M cM HM) as (ccM & HccM & HliftM).
    rewrite <- HliftM in HcovM, HM.
    destruct (lex_find_tr tm A enc instruction successors covers
                enc_injective covers_instruction successors_sound
                pool tg (cert tg) Hcl Hro (Hcert tg)
                (lex_tuple A (cert tg) aM ccM)
                (lexlt_wf_len (length (lex_tuple A (cert tg) aM ccM)) _
                   eq_refl)
                aM ccM M eq_refl HInM HcovM HM)
      as (n & Hn & Hv).
    exists n. split; [| assumption].
    assert (N <= M) by (unfold M; lia). lia.
  Qed.
End Pool.
