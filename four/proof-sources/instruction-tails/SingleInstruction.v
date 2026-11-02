(** A suffix firing one fixed instruction has no late last instruction.
    State attainment also supplies an instruction attaining the same index. *)
From Coq Require Import Arith Lia.
From BBB24 Require Import Statement StatementTr Spec.

Theorem single_instruction_tail_bound : forall tm t tg,
 (forall n,t<=n -> FiresAt tm tg n) -> QHBoundTr t tm.
Proof.
 intros tm t tg Htail other s[Hfire Hquiet].
 destruct(lt_dec s t);[lia|].
 destruct Hfire as(c&Ec&Hc).
 destruct(Htail s ltac:(lia))as(d&Ed&Hd).
 rewrite Ec in Ed;injection Ed as <-.
 assert(E:other=tg)by congruence.
 exfalso;apply(Hquiet(S s));[lia|rewrite E;apply Htail;lia].
Qed.

Theorem state_attainment_instruction : forall tm B,
 AttainsSt tm B -> AttainsTr tm B.
Proof.
 intros tm B(q&s&[Hv Hquiet]&HB).
 apply visits_fires in Hv as(a&Hfire).
 exists(q,a),s;split;[split;[exact Hfire|]|exact HB].
 intros n Hn Hfire';apply(Hquiet n Hn);eapply fires_visits;exact Hfire'.
Qed.

Print Assumptions single_instruction_tail_bound.
Print Assumptions state_attainment_instruction.
