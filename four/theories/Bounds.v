(** Binary candidate bounds. A recurrent suffix anchored before the bound
    suffices; no checker simulates up to the enormous bound itself. *)
From Coq Require Import Arith Lia Bool List NArith.
From BBB24 Require Import Statement StatementTr Spec CTape Instructions.
Import ListNotations.
Definition Bounds (bs bi:N) tm := QHBound (N.to_nat bs) tm /\ QHBoundTr (N.to_nat bi) tm.
Definition prefix_gate (bs bi:N) (tm:TM) (t:nat)
    (states:St->bool) (instrs:Instr->bool) :=
  (N.of_nat t <=? bs)%N && (N.of_nat t <=? bi)%N.
Definition tail_states (Sl:list cconf) q := existsb (fun a=>st_eqb (fst a) q) Sl.
Definition tail_instrs (Sl:list cconf) tg := existsb (fun a=>instr_eqb (cinstr a) tg) Sl.
Lemma state_instr : forall Sl q,
  tail_states Sl q=true -> exists a, tail_instrs Sl (q,a)=true.
Proof.
  intros Sl q H. apply existsb_exists in H as (c&Hin&Hq). apply st_eqb_spec in Hq.
  exists (snd (cinstr c)). apply existsb_exists. exists c; split; [exact Hin|].
  apply instr_eqb_spec. destruct c as [p [[l h] r]]; cbn in *; now subst.
Qed.
Lemma tail_bounds : forall bs bi tm t Sl,
  prefix_gate bs bi tm t (tail_states Sl) (tail_instrs Sl)=true ->
  (forall s tg,t<=s->FiresAt tm tg s->tail_instrs Sl tg=true) ->
  (forall tg,tail_instrs Sl tg=true->forall N,exists k,N<=k /\ FiresAt tm tg k) ->
  Bounds bs bi tm.
Proof.
  intros bs bi tm t Sl Hpre Hcover Hrec.
  unfold prefix_gate in Hpre. apply andb_prop in Hpre as [Hs Hi].
  apply N.leb_le in Hs,Hi. unfold Bounds. split.
  - intros q s [Hv Hquiet]. destruct (lt_dec s t); [lia|].
    apply visits_fires in Hv as (a&Hf).
    specialize (Hcover s (q,a) ltac:(lia) Hf).
    destruct (Hrec (q,a) Hcover (S s)) as (k&Hk&Hf').
    exfalso. apply (Hquiet k); [lia|]. eapply fires_visits; exact Hf'.
  - intros tg s [Hf Hquiet]. destruct (lt_dec s t); [lia|].
    specialize (Hcover s tg ltac:(lia) Hf).
    destruct (Hrec tg Hcover (S s)) as (k&Hk&Hf').
    exfalso. apply (Hquiet k); [lia|exact Hf'].
Qed.
