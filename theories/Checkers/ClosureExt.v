(** * ClosureExt: a closure liveness check with ONE state discharged outside.

    [Closure.closure_check_neverqh_lex] obliges EVERY state that the closure
    or the simulated prefix visits to carry a rank/lex liveness certificate.
    On the (4,2) counter residue that gate fails, and it fails for a reason
    that is now measured rather than guessed (docs/WHY_NO_HAMMER.md): a
    finite abstraction cannot see a carry whose wait is unbounded, so the
    q-avoiding subgraph keeps a spurious "stay in the low bits" cycle.

    But it fails for exactly ONE state per machine.  This file lets that one
    state be discharged by a THEOREM instead -- typically
    [ReachSt.reach_st_recurs], which proves the same liveness on the machine
    itself rather than on an abstraction.  Everything else is the engine
    verbatim: the closure still supplies non-halting and the liveness of the
    other three states, and the proof below is
    [closure_check_neverqh_lex_sound]'s with one extra case split.

    Nothing here weakens the checker.  The skipped state's obligation is not
    dropped, it is MOVED: [closure_check_neverqh_lex_ext_sound] takes the
    liveness of [qext] as a premise and the caller has to prove it.

    Axiom footprint: none of its own. *)

From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement CTape PosEnc Records Closure.
From BBB4.Checkers Require Import Cycle.
Import ListNotations.

Section ClosureExtEngine.

  Variable tm : TM.
  Variable A : Type.
  Variable a_enc : A -> positive.
  Variable a_state : A -> St.
  Variable succs : A -> option (list A).
  Variable covers : A -> ExecState -> Prop.
  Hypothesis a_enc_inj : forall x y, a_enc x = a_enc y -> x = y.
  Hypothesis covers_state : forall a c, covers a c -> a_state a = fst c.
  Hypothesis succs_sound : forall a c, covers a c ->
    match succs a with
    | Some l => match step tm c with
                | Some c' => exists a', In a' l /\ covers a' c'
                | None => False
                end
    | None => True
    end.

  (** The engine's check with the gate for [qext] lifted. *)
  Definition closure_check_neverqh_lex_ext (t fuel : nat) (a0 : A)
      (cert : St -> list (lexcomp A)) (qext : St) : bool :=
    match csteps tm t c0 with
    | Some ct =>
        match close A a_enc succs fuel [] PositiveSet.empty [a0] with
        | Some Sl =>
            closed_b A a_enc succs Sl && mem A a_enc a0 Sl &&
            forallb (fun q =>
              st_eqb q qext ||
              implb (cvisits tm c0 t q
                     || existsb (fun a => st_eqb (a_state a) q) Sl)
                    (lex_ok A a_state succs Sl q (cert q))) all_St
        | None => false
        end
    | None => false
    end.

  Theorem closure_check_neverqh_lex_ext_sound : forall t fuel a0 cert qext,
    (forall ct, csteps tm t c0 = Some ct -> covers a0 (lift ct)) ->
    (forall q, Forall (comp_exact tm A succs covers) (cert q)) ->
    (forall N, exists n, N <= n /\ VisitsAt tm qext n) ->
    closure_check_neverqh_lex_ext t fuel a0 cert qext = true ->
    NeverQuasiHaltsSt tm.
  Proof.
    intros t fuel a0 cert qext Hstart Hcert Hext H.
    unfold closure_check_neverqh_lex_ext in H.
    destruct (csteps tm t c0) as [ct|] eqn:Et; [|discriminate].
    destruct (close A a_enc succs fuel [] PositiveSet.empty [a0]) as [Sl|];
      [|discriminate].
    apply andb_prop in H as [H Hq].
    apply andb_prop in H as [Hcl Hin].
    apply (mem_In A a_enc a_enc_inj) in Hin.
    pose proof (Hstart ct eq_refl) as Hcov0.
    assert (Hct : stepn tm t InitES = Some (lift ct)).
    { rewrite <- lift_c0. apply csteps_lift; assumption. }
    intros q Hvq N.
    destruct (st_eqb q qext) eqn:Eqe.
    { (* the state whose liveness was moved outside the engine *)
      apply st_eqb_spec in Eqe. subst q. apply Hext. }
    assert (Hro : lex_ok A a_state succs Sl q (cert q) = true).
    { rewrite forallb_forall in Hq.
      specialize (Hq q (all_St_complete q)). rewrite Eqe in Hq. simpl in Hq.
      destruct Hvq as (n0 & cn & Hcn & Hqn).
      assert (Hprem : cvisits tm c0 t q
                      || existsb (fun a => st_eqb (a_state a) q) Sl = true).
      { destruct (le_lt_dec t n0) as [Hge | Hlt].
        - apply orb_true_intro; right.
          destruct (closure_invariant tm A a_enc succs covers a_enc_inj
                      succs_sound Sl Hcl a0 (lift ct) Hin Hcov0 (n0 - t))
            as (c' & a' & Hst & HIn' & Hcov').
          assert (Hc' : stepn tm n0 InitES = Some c').
          { replace n0 with (t + (n0 - t)) by lia.
            rewrite stepn_add, Hct. assumption. }
          rewrite Hc' in Hcn. injection Hcn as <-.
          apply existsb_exists. exists a'.
          split; [assumption|].
          apply st_eqb_spec. rewrite (covers_state a' c' Hcov'). assumption.
        - apply orb_true_intro; left.
          destruct (csteps_prefix tm n0 t c0 ct) as (cn' & Hcn' & _);
            [lia | exact Et |].
          assert (Hl : stepn tm n0 InitES = Some (lift cn')).
          { rewrite <- lift_c0. apply csteps_lift; assumption. }
          rewrite Hl in Hcn. injection Hcn as <-.
          eapply cvisits_complete; [exact Hlt | exact Hcn' | exact Hqn]. }
      rewrite Hprem in Hq.
      destruct (lex_ok A a_state succs Sl q (cert q)); [reflexivity|discriminate]. }
    set (M := Nat.max N t).
    destruct (closure_invariant tm A a_enc succs covers a_enc_inj succs_sound
                Sl Hcl a0 (lift ct) Hin Hcov0 (M - t))
      as (cM & aM & HstM & HInM & HcovM).
    assert (HM : stepn tm M InitES = Some cM).
    { replace M with (t + (M - t)) by (unfold M; lia).
      rewrite stepn_add, Hct. assumption. }
    destruct (stepn_csteps tm M cM HM) as (ccM & HccM & HliftM).
    rewrite <- HliftM in HcovM, HM.
    destruct (lex_find tm A a_enc a_state succs covers a_enc_inj covers_state
                succs_sound Sl q (cert q) Hcl Hro (Hcert q)
                (lex_tuple A (cert q) aM ccM)
                (lexlt_wf_len (length (lex_tuple A (cert q) aM ccM)) _ eq_refl)
                aM ccM M eq_refl HInM HcovM HM)
      as (n' & Hn' & Hv).
    exists n'. split; [| assumption].
    assert (N <= M) by (unfold M; lia). lia.
  Qed.

End ClosureExtEngine.
