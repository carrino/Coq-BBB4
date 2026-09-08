(** * CensusTr/RepWLTr: the RepWL block-list tier at TRANSITION level.

    The state census's biggest unique deep-tier decider
    (docs/CENSUS_RUNTIME.md residue ablation: 7/40 residue machines
    are RepWL-only), ported to instruction targets.  The abstraction
    is untouched: an [rconf] pins the head symbol like an n-gram
    context does, so the instruction projection is [rw_instr] and the
    covers bridge is one congruence.  Everything else — the
    run-length step ([rw_succs] + soundness), the seed, the five
    measures and their exactness, the certificate syntax/denotation,
    the interned SCC/Bellman-Ford search, and the M4 node-size cut —
    is REUSED from Checkers/RepWL.v and Census/RepWLSearch.v.

    Two deltas from the state assembly:

    - the verified closure runs directly on the CUT successor
      function ([rw_succs_cut]): a too-big node fails closed (a
      [None] successor is always allowed by the engine's contract),
      so soundness is direct rather than routed through the
      cut-pool-equals-uncut-pool transfer;
    - no ClosureIdx interning yet (the state measured it at ~1.14x on
      this ladder; it can land later without touching soundness).

    [rw_tier_tr] is parameter-closed: certificates come from the
    in-Coq search, never from per-machine tables. *)

From Coq Require Import Arith Lia Bool List ZArith PArith.
From Coq Require Import FSets.FMapPositive MSets.MSetPositive.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape PosEnc
  Closure ClosureTr.
From BBB4.Checkers Require Import RepWL WrapTr.
From BBB4.Census Require Import RepWLSearch.
Import ListNotations.
Open Scope nat_scope.

Set Default Goal Selector "!".

(** ** The instruction projection *)

Definition rw_instr (a : rconf) : Instr :=
  let '(q, (li, lb, h, rb, ri)) := a in (q, h).

Lemma rw_covers_instr : forall a c,
  rw_covers a c -> rw_instr a = instr_of c.
Proof.
  intros [q [[[[li lb] h] rb] ri]] c (Hq & Hh & _).
  unfold rw_instr, instr_of. rewrite Hq, Hh. reflexivity.
Qed.

Lemma rw_covers'_instr : forall a c,
  rw_covers' a c -> rw_instr a = instr_of c.
Proof.
  intros a c [Hc _]. exact (rw_covers_instr a c Hc).
Qed.

(** the cut successor function fails closed on a too-big node, which
    the engine's contract always allows *)
Lemma rw_succs_cut_sound' : forall M tm L T a c,
  1 <= L -> 2 <= T ->
  rw_covers' a c ->
  match rw_succs_cut M tm L T a, step tm c with
  | Some l, Some c' => exists a', In a' l /\ rw_covers' a' c'
  | Some _, None => False
  | None, _ => True
  end.
Proof.
  intros M tm L T a c HL HT Hcov.
  unfold rw_succs_cut.
  destruct (M <? rw_asz a).
  - destruct (step tm c); exact I.
  - apply rw_succs_sound'; assumption.
Qed.

(** ** The verified checker *)

Definition rw_check_neverqhtr (tm : TM) (L T t fuel M : nat)
    (cert : Instr -> list rwcomp) : bool :=
  (1 <=? L) && (2 <=? T) &&
  match csteps tm t c0 with
  | Some cc =>
      closure_check_neverqhtr_lex tm rconf rconf_enc rw_instr
        (rw_succs_cut M tm L T) t fuel (rw_seed L T cc)
        (fun tg => map (rw_comp_denote tm) (cert tg))
  | None => false
  end.

Theorem rw_check_neverqhtr_sound : forall tm L T t fuel M cert,
  rw_check_neverqhtr tm L T t fuel M cert = true ->
  NeverQuasiHaltsTr tm.
Proof.
  intros tm L T t fuel M cert H.
  unfold rw_check_neverqhtr in H.
  apply andb_prop in H as [Hg H].
  apply andb_prop in Hg as [HL HT].
  apply Nat.leb_le in HL. apply Nat.leb_le in HT.
  destruct (csteps tm t c0) as [cc|] eqn:Et; [| discriminate].
  apply (closure_check_neverqhtr_lex_sound tm rconf rconf_enc rw_instr
           (rw_succs_cut M tm L T) rw_covers') in H;
    [assumption | | | | |].
  - exact rconf_enc_inj.
  - intros a c Hc. exact (rw_covers'_instr a c Hc).
  - intros a c Hc. apply rw_succs_cut_sound'; assumption.
  - intros ct' Hct'. rewrite Et in Hct'. injection Hct' as <-.
    split; [apply rw_seed_covers; assumption |
            apply rw_seed_wf; assumption].
  - intros tg. apply Forall_forall. intros comp Hin.
    apply in_map_iff in Hin. destruct Hin as (c & <- & _).
    destruct c as [phi | m K phi gate]; simpl.
    + exact I.
    + intros a cc0 a' cc0' sl Hca Hca' Hstep Es HInl.
      exact (rw_meas_exact tm m a cc0 cc0' Hca Hstep).
Qed.

(** ** The untrusted certificate search (RepWLSearch's, avoid-filter
    moved from states to instructions; the interned SCC / condensation
    / Bellman-Ford machinery is reused as-is) *)

Definition irows_tr (tm : TM) (L T : nat) (tg : Instr)
    (im : PositiveMap.tree positive) (nodes : list rconf) : IAdj :=
  snd (fold_left
    (fun '(i, g) a =>
       (Pos.succ i,
        PositiveMap.add i
          (fold_right (fun b acc =>
             if instr_eqb (rw_instr b) tg then acc
             else match PositiveMap.find (rkey b) im with
                  | Some j => j :: acc
                  | None => acc
                  end)
             []
             (match rw_succs tm L T a with Some l => l | None => [] end))
          g))
    nodes (1%positive, PositiveMap.empty _)).

Definition rw_procedure_tr (tm : TM) (L T : nat)
    (closure : list rconf) (tg : Instr) : list rwcomp :=
  let nodes := filter (fun a => negb (instr_eqb (rw_instr a) tg)) closure in
  let '(im, arr) := iintern nodes in
  let g := irows_tr tm L T tg im nodes in
  let idxs := iidxs nodes in
  let Kc := S (S (length nodes)) in
  let rfuel := S (length nodes * 8 + 8) in
  match iproc_rounds 300 tm arr Kc rfuel idxs g [] with
  | Some comps => comps
  | None => []
  end.

(** ** The parameter-closed tier *)

Definition rw_tier_tr (tm : TM) (L T t fuel M : nat) : bool :=
  match csteps tm t c0 with
  | None => false
  | Some cc =>
      let a0 := rw_seed L T cc in
      match close rconf rconf_enc (rw_succs_cut M tm L T) fuel
                  [] PositiveSet.empty [a0] with
      | None => false
      | Some Sl =>
          rw_check_neverqhtr tm L T t fuel M
            (fun tg =>
               if cfires tm c0 t tg
                  || existsb (fun a => instr_eqb (rw_instr a) tg) Sl
               then rw_procedure_tr tm L T Sl tg
               else [])
      end
  end.

Theorem rw_tier_tr_sound : forall tm L T t fuel M,
  rw_tier_tr tm L T t fuel M = true -> NeverQuasiHaltsTr tm.
Proof.
  intros tm L T t fuel M H.
  unfold rw_tier_tr in H.
  destruct (csteps tm t c0) as [cc|]; [|discriminate].
  destruct (close rconf rconf_enc (rw_succs_cut M tm L T) fuel
                  [] PositiveSet.empty [rw_seed L T cc]) as [Sl|];
    [|discriminate].
  exact (rw_check_neverqhtr_sound tm L T t fuel M _ H).
Qed.

(** ** Tier W-wrap: transition-quasihalting via the wrapped RepWL closure

    The generic wrap argument (Checkers/WrapTr [WrapGeneric])
    instantiated at the RepWL domain: close [rw_succs_cut] over the
    MULTI-PIN WRAPPED machine and discharge every appearing
    instruction's recurrence through the rank/lex gates.  This is the
    tier the 7.1m diagnosis asked for -- an instruction pin is a
    tape-value exclusion, and the run-length blocks carry the
    precision the n-gram window refill lacks. *)

Definition rw_check_qhbtr (tm : TM) (tgs : list (Instr * nat))
    (L T t fuel M : nat) (cert : Instr -> list rwcomp) : bool :=
  (1 <=? L) && (2 <=? T) &&
  match csteps tm t c0 with
  | Some ct =>
      let tmw := tm_wrap_trs tm (map fst tgs) in
      wrap_check_qhboundtr_g tm tgs t rconf rconf_enc rw_instr
        (rw_succs_cut M tmw L T) fuel (rw_seed L T ct)
        (fun tg => map (rw_comp_denote tmw) (cert tg))
  | None => false
  end.

Theorem rw_check_qhbtr_sound : forall tm tgs L T t fuel M cert,
  rw_check_qhbtr tm tgs L T t fuel M cert = true ->
  NonHalt tm
  /\ (forall tg' s', QuietAfterTr tm tg' s' -> S s' <= S t)
  /\ QuasiHaltsTr tm.
Proof.
  intros tm tgs L T t fuel M cert H.
  unfold rw_check_qhbtr in H.
  apply andb_prop in H as [Hg H].
  apply andb_prop in Hg as [HL HT].
  apply Nat.leb_le in HL. apply Nat.leb_le in HT.
  destruct (csteps tm t c0) as [ct|] eqn:Et; [|discriminate].
  apply (wrap_check_qhboundtr_g_sound tm tgs t rconf rconf_enc rw_instr
           (rw_succs_cut M (tm_wrap_trs tm (map fst tgs)) L T) rw_covers')
    in H; [assumption | | | | |].
  - exact rconf_enc_inj.
  - intros a c Hc. exact (rw_covers'_instr a c Hc).
  - intros a c Hc. apply rw_succs_cut_sound'; assumption.
  - intros ct' Hct'. rewrite Et in Hct'. injection Hct' as <-.
    split; [apply rw_seed_covers; assumption |
            apply rw_seed_wf; assumption].
  - intros tg. apply Forall_forall. intros comp Hin.
    apply in_map_iff in Hin. destruct Hin as (c & <- & _).
    destruct c as [phi | m0 K phi gate]; simpl.
    + exact I.
    + intros a cc0 a' cc0' sl Hca Hca' Hstep Es HInl.
      exact (rw_meas_exact (tm_wrap_trs tm (map fst tgs))
               m0 a cc0 cc0' Hca Hstep).
Qed.

(** the parameter-closed tier: pin from the caller's last-fire scan,
    wrap, close once for the SEARCH, and hand the checker the
    certificates (it re-closes -- same double-close [rw_tier_tr]
    accepts) *)
Definition rw_tier_qhbtr (tm : TM) (lf : list (Instr * nat))
    (L T t fuel M : nat) : bool :=
  match filter (fun p => snd p <? t) lf with
  | [] => false
  | pins =>
      match csteps tm t c0 with
      | None => false
      | Some ct =>
          let tmw := tm_wrap_trs tm (map fst pins) in
          let a0 := rw_seed L T ct in
          match close rconf rconf_enc (rw_succs_cut M tmw L T) fuel
                      [] PositiveSet.empty [a0] with
          | None => false
          | Some Sl =>
              rw_check_qhbtr tm pins L T t fuel M
                (fun tg => rw_procedure_tr tmw L T Sl tg)
          end
      end
  end.

Theorem rw_tier_qhbtr_sound : forall tm lf L T t fuel M,
  rw_tier_qhbtr tm lf L T t fuel M = true ->
  NonHalt tm
  /\ (forall tg' s', QuietAfterTr tm tg' s' -> S s' <= S t)
  /\ QuasiHaltsTr tm.
Proof.
  intros tm lf L T t fuel M H.
  unfold rw_tier_qhbtr in H.
  destruct (filter (fun p => snd p <? t) lf) as [|p0 rest] eqn:Ef;
    [discriminate|].
  destruct (csteps tm t c0) as [ct|]; [|discriminate].
  destruct (close rconf rconf_enc _ fuel [] PositiveSet.empty _)
    as [Sl|]; [|discriminate].
  exact (rw_check_qhbtr_sound tm (p0 :: rest) L T t fuel M _ H).
Qed.
