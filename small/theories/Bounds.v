From Coq Require Import Arith Lia Bool List.
From SmallBB Require Import Statement StatementTr CTape ClosureTr.
From SmallBB.Checkers Require Import Cycle.
Import ListNotations.

Definition QHBound (B : nat) (tm : TM) :=
  forall q s, QuietAfter tm q s -> S s <= B.
Definition QHBoundTr (B : nat) (tm : TM) :=
  forall tg s, QuietAfterTr tm tg s -> S s <= B.
Section BoundParameters.
Variable bs bi : nat.

Definition Bounds (tm : TM) := QHBound bs tm /\ QHBoundTr bi tm.

Definition prefix_gate (tm : TM) (t : nat)
    (states : St -> bool) (instrs : Instr -> bool) : bool :=
  (match csteps tm bs c0 with
   | None => true
   | Some c => forallb (fun q => implb (cvisits tm c (t - bs) q) (states q)) all_St
   end) &&
  (match csteps tm bi c0 with
   | None => true
   | Some c => forallb (fun tg => implb (cfires tm c (t - bi) tg) (instrs tg)) all_Instr
   end).

Definition tail_states (Sl : list cconf) (q : St) :=
  existsb (fun a => st_eqb (fst a) q) Sl.
Definition tail_instrs (Sl : list cconf) (tg : Instr) :=
  existsb (fun a => instr_eqb (cinstr a) tg) Sl.

Lemma state_instr : forall Sl q,
  tail_states Sl q = true -> exists a, tail_instrs Sl (q,a) = true.
Proof.
  intros Sl q H. apply existsb_exists in H as (c & Hin & Hq).
  apply st_eqb_spec in Hq.
  exists (snd (cinstr c)). apply existsb_exists. exists c. split; [exact Hin|].
  apply instr_eqb_spec. destruct c as [p [[l h] r]]. simpl in *. now subst.
Qed.

Lemma visits_computable : forall tm s q,
  VisitsAt tm q s -> exists c, csteps tm s c0 = Some c /\ fst c = q.
Proof.
  intros tm s q (c & Hr & Hq).
  destruct (stepn_csteps tm s c Hr) as (cc & Hcc & Hl).
  exists cc. split; [exact Hcc|]. rewrite <- Hq, <- Hl. reflexivity.
Qed.

Lemma fires_computable : forall tm s tg,
  FiresAt tm tg s -> exists c, csteps tm s c0 = Some c /\ cinstr c = tg.
Proof.
  intros tm s tg (c & Hr & Hq).
  destruct (stepn_csteps tm s c Hr) as (cc & Hcc & Hl).
  exists cc. split; [exact Hcc|]. rewrite <- Hq, <- Hl. symmetry. apply cinstr_lift.
Qed.

Lemma tail_bounds : forall tm t Sl,
  prefix_gate tm t (tail_states Sl) (tail_instrs Sl) = true ->
  (forall s tg, t <= s -> FiresAt tm tg s -> tail_instrs Sl tg = true) ->
  (forall tg, tail_instrs Sl tg = true -> forall N,
    exists k, N <= k /\ FiresAt tm tg k) ->
  Bounds tm.
Proof.
  intros tm t Sl Hpre Hcover Hrec.
  unfold prefix_gate in Hpre. apply andb_prop in Hpre as [Hs Hi].
  split.
  - intros q s [Hv Hquiet]. destruct (lt_dec s bs); [lia|].
    assert (Hpresent : tail_states Sl q = true).
    { destruct (le_lt_dec t s) as [Hts|Hst].
      - apply visits_fires in Hv as (a & Hf).
        specialize (Hcover s (q,a) Hts Hf).
        apply existsb_exists in Hcover as (cc & Hin & Heq).
        apply instr_eqb_spec in Heq.
        apply existsb_exists. exists cc. split; [exact Hin|].
        apply st_eqb_spec. apply (f_equal fst) in Heq. exact Heq.
      - destruct (visits_computable tm s q Hv) as (cc & Hcc & Hq).
        destruct (csteps_prefix tm bs s c0 cc ltac:(lia) Hcc) as (cb & Hb & Hbs).
        rewrite Hb in Hs. rewrite forallb_forall in Hs.
        specialize (Hs q (all_St_complete q)).
        assert (E : cvisits tm cb (t-bs) q = true).
        { eapply cvisits_complete; [|exact Hbs|exact Hq]. lia. }
        rewrite E in Hs. exact Hs. }
    destruct (state_instr Sl q Hpresent) as (a & Ha).
    destruct (Hrec (q,a) Ha (S s)) as (k & Hk & Hf).
    exfalso. apply (Hquiet k); [lia|]. eapply fires_visits; eauto.
  - intros tg s [Hf Hquiet]. destruct (lt_dec s bi); [lia|].
    assert (Hpresent : tail_instrs Sl tg = true).
    { destruct (le_lt_dec t s) as [Hts|Hst].
      - exact (Hcover s tg Hts Hf).
      - destruct (fires_computable tm s tg Hf) as (cc & Hcc & Htg).
        destruct (csteps_prefix tm bi s c0 cc ltac:(lia) Hcc) as (cb & Hb & Hbs).
        rewrite Hb in Hi. rewrite forallb_forall in Hi.
        specialize (Hi tg (all_Instr_complete tg)).
        assert (E : cfires tm cb (t-bi) tg = true).
        { eapply cfires_complete; [|exact Hbs|exact Htg]. lia. }
        rewrite E in Hi. exact Hi. }
    destruct (Hrec tg Hpresent (S s)) as (k & Hk & Hv).
    exfalso. apply (Hquiet k); [lia|exact Hv].
Qed.

End BoundParameters.
