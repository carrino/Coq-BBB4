(** * IRules.MetaTileTr: the transition-level recurrence argument of the
    irules meta checkers, once, for any meta parameter.

    [MetaBlkPfxTr.irulesblkpfx_check_neverqhtr_sound] ends with the same
    argument every meta checker makes: an anchor the machine reaches, a
    cycle from every admissible parameter value to the next one that
    fires only instructions of [F] and fires every one of them, and a
    prefix gate saying every instruction fired before the anchor is in
    [F].  Then every fired instruction recurs.  Here that argument is
    stated over an arbitrary parameter type [V] (a scalar [K] for the
    [a K + b] checkers, a valuation for the matrix map of
    [MetaBlkPfxMVTr]), so the new checkers of SCOPING_INSTR.md 7.4.SPW
    ([MetaBlkPfxV5cTr], [MetaBlkPfxMVTr]) only prove their cycle.

    [Print Assumptions meta_tile_neverqhtr] must be
    [functional_extensionality_dep] at most. *)

From Coq Require Import Arith ZArith Lia Bool List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
From BBB4.Checkers.IRules Require Import AnchorVisits AnchorVisitsTr MetaTr.
From BBB4.Checkers.IRules Require Import Engine.
Import ListNotations.

Theorem meta_tile_neverqhtr : forall tm (V : Type) (P : V -> Prop)
    (sem : V -> ExecState) (f : V -> V) (F : list Tr) (anchor : nat)
    (v0 : V) (c : cconf) (tvis : tmask),
  stepn tm anchor InitES = Some (sem v0) -> P v0 ->
  (forall v, P v -> P (f v)) ->
  (forall v, P v -> exists n, (1 <= n)%nat /\ Reach tm F n (sem v) (sem (f v))) ->
  csteps_tvis tm anchor c0 tvm_empty = Some (c, tvis) ->
  forallb (fun t => implb (tvm_get tvis t) (tr_in t F)) all_Instr = true ->
  NeverQuasiHaltsTr tm.
Proof.
  intros tm V P sem f F anchor v0 c tvis Hanchor Hv0 Hinw Hcycle Hanchv Hpre.
  assert (Htiles : forall i, exists N v,
    (anchor + i <= N)%nat /\ P v /\
    stepn tm N InitES = Some (sem v) /\
    forall m, (anchor <= m)%nat -> (m < N)%nat ->
      exists cm, stepn tm m InitES = Some cm /\ In (trans_of cm) F).
  { induction i as [|i IH].
    - exists anchor, v0.
      split; [lia|]. split; [exact Hv0|]. split; [exact Hanchor|].
      intros m Hm1 Hm2. lia.
    - destruct IH as (N & v & HN & Hv & Hstep & Hcov).
      destruct (Hcycle v Hv) as (n & Hn1 & HS & HC & _).
      exists (N + n)%nat, (f v).
      split; [lia|]. split; [apply Hinw; exact Hv|]. split.
      + rewrite stepn_add, Hstep. exact HS.
      + intros m Hm1 Hm2.
        destruct (Nat.lt_ge_cases m N) as [Hlt | Hge].
        * exact (Hcov m Hm1 Hlt).
        * destruct (HC (m - N)%nat ltac:(lia)) as (cm & Hcm & Hin).
          exists cm. split; [|exact Hin].
          replace m with (N + (m - N))%nat by lia.
          rewrite stepn_add, Hstep. exact Hcm. }
  assert (Hrec : forall t, In t F -> forall B,
    exists m cm, (B <= m)%nat /\ stepn tm m InitES = Some cm /\
                 trans_of cm = t).
  { intros t Hin B.
    destruct (Htiles B) as (N & v & HN & Hv & Hstep & _).
    destruct (Hcycle v Hv) as (n & Hn1 & _ & _ & HX).
    destruct (HX t Hin) as (m' & cm & Hm' & Hcm & Htr).
    exists (N + m')%nat, cm.
    split; [lia|]. split; [|exact Htr].
    rewrite stepn_add, Hstep. exact Hcm. }
  intros t0 Hf B.
  assert (Ht0 : In t0 F).
  { destruct Hf as (n0 & cn & Hcn & Htc).
    destruct (Nat.lt_ge_cases n0 anchor) as [Hlt | Hge].
    - (* prefix: the instruction-mask gate *)
      destruct (stepn_csteps tm n0 cn Hcn) as (ccn & Hccn & Hlift).
      assert (Hm : tvm_get tvis (cinstr ccn) = true)
        by (eapply csteps_tvis_complete; eauto).
      rewrite <- cinstr_lift, Hlift, Htc in Hm.
      rewrite forallb_forall in Hpre.
      specialize (Hpre t0 (all_Instr_complete t0)).
      rewrite Hm in Hpre. simpl in Hpre.
      apply tr_in_sound. destruct (tr_in t0 F); [reflexivity|].
      discriminate.
    - (* from the anchor on: covered by the cycles *)
      destruct (Htiles (n0 + 1 - anchor)%nat)
        as (N & v & HN & Hv & Hstep & Hcov).
      destruct (Hcov n0 Hge ltac:(lia)) as (cm & Hcm & Hin).
      rewrite Hcn in Hcm. injection Hcm as <-.
      rewrite trans_of_instr_of, Htc in Hin. exact Hin. }
  destruct (Hrec t0 Ht0 B) as (m & cm & Hm & Hcm & Htr).
  exists m. split; [exact Hm|].
  exists cm. split; [exact Hcm|].
  rewrite <- trans_of_instr_of. exact Htr.
Qed.
