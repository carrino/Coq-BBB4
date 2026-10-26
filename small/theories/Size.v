From Coq Require Import Arith Lia Bool List.
From SmallBB Require Import Statement StatementTr.
Import ListNotations.

Definition st_index q := match q with StA => 0 | StB => 1 | StC => 2 end.
Definition sym_index s := match s with S0 => 0 | S1 => 1 | S2 => 2 end.
Definition supported ns ms := (ns = 2 /\ ms = 2) \/ (ns = 2 /\ ms = 3) \/ (ns = 3 /\ ms = 2).
Definition output_ok ns ms (tr : Trans) :=
  st_index (t_next tr) < ns /\ sym_index (t_write tr) < ms.
(** Inactive table cells are undefined; every defined transition stays
    in the active state and symbol sets. Thus this is exactly the usual
    n-state, m-symbol table, embedded in the common 3-by-3 carrier. *)
Definition Admissible ns ms (tm : TM) :=
  (forall q s tr, tm q s = Some tr -> output_ok ns ms tr) /\
  (forall q s, ns <= st_index q \/ ms <= sym_index s -> tm q s = None).
Lemma admissible_output : forall ns ms tm,
  Admissible ns ms tm -> forall q s tr, tm q s = Some tr -> output_ok ns ms tr.
Proof. intros ns ms tm [H _]. exact H. Qed.

Definition nat_trans ns v : option Trans :=
  if v <? 6 * ns then
    Some (mkTrans (match v / (2*ns) with 0 => S0 | 1 => S1 | _ => S2 end)
      (if Nat.even (v / ns) then DL else DR)
      (match v mod ns with 0 => StA | 1 => StB | _ => StC end))
  else None.
Definition machine_of_codes ns ms (xs : list nat) : TM :=
  fun q s => if (st_index q <? ns) && (sym_index s <? ms)
    then nat_trans ns (nth (ms * st_index q + sym_index s) xs (6*ns))
    else None.

Lemma codes_complete : forall ns ms,
  supported ns ms -> forall tr, output_ok ns ms tr ->
  exists v, In v (seq 0 (2*ns*ms)) /\ nat_trans ns v = Some tr.
Proof.
  intros ns ms H [s d q] Hout.
  exists (2 * ns * sym_index s + (match d with DL => 0 | DR => ns end) + st_index q).
  destruct H as [[-> ->]|[[-> ->]|[-> ->]]]; destruct s,d,q;
    unfold output_ok in Hout; simpl in Hout;
    try (exfalso; lia);
    (split; [apply in_seq; cbn; lia|reflexivity]).
Qed.
