(** * Counters.LoopConjTr: a [LoopRunTr] lap family carried to a conjugate
    machine whose blank run enters the family elsewhere (SCOPING_INSTR 7.4.LE10).

    [CConjCoverTr] needs the two blank runs to fall into lockstep.  A
    state-renamed or mirrored copy of a boarded row can instead enter the
    same counter family at a width the source never visits (another residue
    of the lap's step).  When the source's lap is proved for EVERY member of
    the family ([Cg x ->+ Cg y], every instruction firing from every
    [Cg x]), [CConjugateReachTr.cconj_reach_neverqhtr] carries it over.  The
    destination needs only a concrete boot into the conjugate of some [Cg x].

    Axiom footprint: [functional_extensionality_dep], via [CTape.lift]. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import CConjugateTr CConjugateReachTr TriReachTr NestCountTr.
Import ListNotations.

Theorem conj_family_neverqhtr : forall (src dst : TM) (p : St -> St) (flip : bool)
    (Cg : nat -> cconf),
  (forall q s, dst (p q) s = option_map (tconj p flip) (src q s)) ->
  (forall q, exists q0, p q0 = q) ->
  (exists T x, stepn dst T InitES = Some (lift (cconj p flip (Cg x)))) ->
  (forall x, exists y, Reach1 (tm_wrap_trs src []) (Cg x) (Cg y)) ->
  (forall x t, Fires (tm_wrap_trs src []) (Cg x) t) ->
  NeverQuasiHaltsTr dst.
Proof.
  intros src dst p flip Cg Htab Honto Hboot Hprog Hfire.
  apply (cconj_reach_neverqhtr src dst p flip Htab nat Cg Honto Hboot).
  - intros x. destruct (Hprog x) as (y & m & Hm & H). exists y, m. split; [exact Hm|]. exact H.
  - intros x t. destruct (Hfire x t) as (k & c & Hc & Ht).
    exists k, (lift c). split.
    + exact (csteps_lift (tm_wrap_trs src []) k _ _ Hc).
    + rewrite cinstr_lift. exact Ht.
Qed.

(** a boot by computation: the destination's blank run, compared after [lift] *)
Lemma conj_boot_ok : forall (dst : TM) p flip c T,
  match csteps dst T CTape.c0 with Some c' => ceqb c' (cconj p flip c) | None => false end = true ->
  stepn dst T InitES = Some (lift (cconj p flip c)).
Proof.
  intros dst p flip c T H. destruct (csteps dst T CTape.c0) as [c'|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift dst T _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.
