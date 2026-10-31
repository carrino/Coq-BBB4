(** * ChampionRun: the probable champion runs for more than
    119,112,334,170,342,541 steps.

    The fine-grained rules of [Champion] (with the accelerated A1 loop)
    are iterated on binary numbers by [vm_compute]: 2,808,416 rule
    applications from A1(0, 0, 1) (reached at step 2) carry the
    machine past the BB(3,3) champion's step count.  [ch_run_sound]
    turns the computed total into a [stepn] fact about the abstract
    machine; nothing here evaluates a unary number of that size. *)

From Coq Require Import Arith NArith Bool Lia List.
From SmallBB Require Import Statement CTape.
From BB33 Require Import Lib Champion.
Import ListNotations.

(** ** The accelerated rule function on binary numbers

    Family tags: 1 = A1, 2 = A2, anything else = B (the [n] slot of a
    B configuration is unused and kept at 0). *)

Open Scope N_scope.

Definition ch_rule_N (f m b n : N) : option (N * N * N * N * N) :=
  if f =? 1 then
    if andb (1 <=? m) (1 <=? n) then
      if andb (2 <=? m) (2 <=? n) then
        let d := N.div2 (N.min m n) in
        Some (1, m - 2 * d, b + 3 * d, n - 2 * d, 12 * d * d + 4 * d + 8 * b * d)
      else Some (2, m - 1, b + 1, n - 1, 5 + 4 * b)
    else if 1 <=? m then Some (1, m - 1, 0, b + 2, 5 + 4 * b)
    else if b =? 0 then Some (3, 2, n, 0, 5)
    else if n =? 0 then Some (1, 2, b, 1, 7)
    else if n =? 1 then Some (1, 2, b + 1, 0, 7)
    else if N.even n then Some (2, 1, b + n + 1, 0, 12 + 4 * b + 5 * n)
    else Some (1, 1, 0, b + n + 2, 11 + 4 * b + 5 * n)
  else if f =? 2 then
    if andb (1 <=? m) (1 <=? n) then Some (1, m - 1, b + 2, n - 1, 7 + 4 * b)
    else if 1 <=? m then Some (3, m - 1, b + 2, 0, 7 + 4 * b)
    else if 1 <=? n then Some (3, 2 * b + 4, n - 1, 0, 6 + 2 * b)
    else Some (3, 2 * b + 3, 0, 0, 5 + 2 * b)
  else
    if m =? 0 then None
    else if b =? 0 then Some (1, m, 0, 1, 2)
    else if b =? 1 then Some (1, m, 1, 0, 2)
    else if N.even b then Some (2, m - 1, b + 1, 0, 5 * b + 7)
    else Some (1, m - 1, 0, b + 2, 5 * b + 6).

Close Scope N_scope.

Definition confN (f m b n : N) : cconf :=
  match N.to_nat f with
  | 1 => A1c (N.to_nat m) (N.to_nat b) (N.to_nat n)
  | 2 => A2c (N.to_nat m) (N.to_nat b) (N.to_nat n)
  | _ => Bc (N.to_nat m) (N.to_nat b)
  end.

Definition ch_spec (f m b n : N) : Prop :=
  match ch_rule_N f m b n with
  | Some (f', m', b', n', s) => RL (N.to_nat s) (confN f m b n) (confN f' m' b' n')
  | None => True
  end.

(** Parity of a binary number, as a nat equation. *)
Lemma N_even_nat : forall n : N, N.even n = true -> exists k, N.to_nat n = 2 * k.
Proof.
  intros n H. apply N.even_spec in H. destruct H as [k Hk]. exists (N.to_nat k). lia.
Qed.
Lemma N_odd_nat : forall n : N, N.even n = false -> exists k, N.to_nat n = 2 * k + 1.
Proof.
  intros n H. destruct (N.Even_or_Odd n) as [He | [k Hk]].
  - apply N.even_spec in He. congruence.
  - exists (N.to_nat k). lia.
Qed.

Ltac rl_rule L :=
  apply RL_csteps; eapply csteps_conf_eq;
  [apply L | f_equal | f_equal]; first [lia | reflexivity | idtac].

Lemma ch_rule_N_sound : forall f m b n, ch_spec f m b n.
Proof.
  intros f m b n. unfold ch_spec, ch_rule_N, confN.
  destruct (f =? 1)%N eqn:Hf1.
  { apply N.eqb_eq in Hf1. subst f. change (N.to_nat 1) with 1. change (N.to_nat 2) with 2.
    change (N.to_nat 3) with 3.
    destruct (andb (1 <=? m) (1 <=? n))%N eqn:H11.
    - apply andb_prop in H11 as [Hm Hn]. apply N.leb_le in Hm, Hn.
      destruct (andb (2 <=? m) (2 <=? n))%N eqn:H22.
      + (* the accelerated loop *)
        apply andb_prop in H22 as [Hm2 Hn2]. apply N.leb_le in Hm2, Hn2.
        set (d := N.div2 (N.min m n)).
        assert (Hd : N.to_nat d = Nat.div2 (Nat.min (N.to_nat m) (N.to_nat n))).
        { unfold d. rewrite N2Nat.inj_div2, N2Nat.inj_min. reflexivity. }
        pose proof (Nat.le_min_l (N.to_nat m) (N.to_nat n)) as Hminl.
        pose proof (Nat.le_min_r (N.to_nat m) (N.to_nat n)) as Hminr.
        assert (Hmin2 : 2 <= Nat.min (N.to_nat m) (N.to_nat n)) by (apply Nat.min_glb; lia).
        clearbody d.
        set (mn := Nat.min (N.to_nat m) (N.to_nat n)) in *.
        pose proof (Nat.div2_odd mn) as Hodd.
        assert (Hb2n : Nat.b2n (Nat.odd mn) <= 1) by (destruct (Nat.odd mn); simpl; lia).
        set (dd := Nat.div2 mn) in *.
        assert (Hd1 : 1 <= N.to_nat d) by lia.
        assert (Hdm : 2 * N.to_nat d <= N.to_nat m) by lia.
        assert (Hdn : 2 * N.to_nat d <= N.to_nat n) by lia.
        replace (N.to_nat (12 * d * d + 4 * d + 8 * b * d))
          with (12 * N.to_nat d * N.to_nat d + 4 * N.to_nat d + 8 * N.to_nat b * N.to_nat d) by nia.
        apply RL_csteps.
        eapply csteps_conf_eq;
          [apply (loop_A1 (N.to_nat d) (N.to_nat (m - 2 * d)) (N.to_nat b) (N.to_nat (n - 2 * d)))
          | apply A1c_eq; lia | apply A1c_eq; lia].
      + (* R1 *)
        destruct (N.to_nat m) as [|m'] eqn:Em; [lia|]. destruct (N.to_nat n) as [|n'] eqn:En; [lia|].
        replace (N.to_nat (5 + 4 * b)) with (5 + 4 * N.to_nat b) by lia.
        apply RL_csteps. eapply csteps_conf_eq; [apply (R1 m' (N.to_nat b) n') | reflexivity | apply A2c_eq; lia].
    - apply andb_false_iff in H11.
      destruct (1 <=? m)%N eqn:Hm.
      + (* R2: n = 0 *)
        apply N.leb_le in Hm. assert (Hn : n = 0%N) by (destruct H11 as [H|H]; [congruence | apply N.leb_gt in H; lia]).
        subst n. change (N.to_nat 0) with 0.
        destruct (N.to_nat m) as [|m'] eqn:Em; [lia|].
        replace (N.to_nat (5 + 4 * b)) with (5 + 4 * N.to_nat b) by lia.
        eapply RL_eq; [apply (R2 m' (N.to_nat b)) | reflexivity | f_equal; apply A1c_eq; lia].
      + apply N.leb_gt in Hm. assert (Hm0 : m = 0%N) by lia. subst m. change (N.to_nat 0) with 0.
        destruct (b =? 0)%N eqn:Hb0.
        * (* R5 *)
          apply N.eqb_eq in Hb0. subst b. change (N.to_nat 0) with 0. change (N.to_nat 5) with 5.
          apply RL_csteps. apply R5.
        * apply N.eqb_neq in Hb0.
          destruct (N.to_nat b) as [|b'] eqn:Eb; [lia|].
          destruct (n =? 0)%N eqn:Hn0.
          { (* R6 *)
            apply N.eqb_eq in Hn0. subst n. change (N.to_nat 0) with 0. change (N.to_nat 7) with 7.
            change (N.to_nat 1) with 1.
            eapply RL_eq; [apply (R6 b') | reflexivity | f_equal; apply A1c_eq; lia]. }
          apply N.eqb_neq in Hn0.
          destruct (n =? 1)%N eqn:Hn1.
          { (* R7 *)
            apply N.eqb_eq in Hn1. subst n. change (N.to_nat 1) with 1. change (N.to_nat 7) with 7.
            change (N.to_nat 0) with 0.
            eapply RL_eq; [apply (R7 b') | reflexivity | f_equal; apply A1c_eq; lia]. }
          apply N.eqb_neq in Hn1.
          destruct (N.even n) eqn:He.
          { (* R8 *)
            destruct (N_even_nat n He) as [k Hk].
            assert (Hk1 : 1 <= k) by lia.
            replace (N.to_nat (12 + 4 * b + 5 * n)) with (4 * b' + 10 * (k - 1) + 26) by lia.
            apply RL_csteps.
            eapply csteps_conf_eq; [apply (R8 b' (k - 1)) | apply A1c_eq; lia | apply A2c_eq; lia]. }
          { (* R9 *)
            destruct (N_odd_nat n He) as [k Hk].
            assert (Hk1 : 1 <= k) by lia.
            replace (N.to_nat (11 + 4 * b + 5 * n)) with (4 * b' + 10 * (k - 1) + 30) by lia.
            eapply RL_eq; [apply (R9 b' (k - 1)) | f_equal; apply A1c_eq; lia | f_equal; apply A1c_eq; lia]. } }
  destruct (f =? 2)%N eqn:Hf2.
  { apply N.eqb_eq in Hf2. subst f. change (N.to_nat 1) with 1. change (N.to_nat 2) with 2.
    change (N.to_nat 3) with 3.
    destruct (andb (1 <=? m) (1 <=? n))%N eqn:H11.
    - (* R3 *)
      apply andb_prop in H11 as [Hm Hn]. apply N.leb_le in Hm, Hn.
      destruct (N.to_nat m) as [|m'] eqn:Em; [lia|]. destruct (N.to_nat n) as [|n'] eqn:En; [lia|].
      replace (N.to_nat (7 + 4 * b)) with (7 + 4 * N.to_nat b) by lia.
      apply RL_csteps. eapply csteps_conf_eq; [apply (R3 m' (N.to_nat b) n') | reflexivity | apply A1c_eq; lia].
    - apply andb_false_iff in H11.
      destruct (1 <=? m)%N eqn:Hm.
      + (* R4 *)
        apply N.leb_le in Hm. assert (Hn : n = 0%N) by (destruct H11 as [H|H]; [congruence | apply N.leb_gt in H; lia]).
        subst n. change (N.to_nat 0) with 0.
        destruct (N.to_nat m) as [|m'] eqn:Em; [lia|].
        replace (N.to_nat (7 + 4 * b)) with (7 + 4 * N.to_nat b) by lia.
        eapply RL_eq; [apply (R4 m' (N.to_nat b)) | reflexivity | f_equal; apply Bc_eq; lia].
      + apply N.leb_gt in Hm. assert (Hm0 : m = 0%N) by lia. subst m. change (N.to_nat 0) with 0.
        destruct (1 <=? n)%N eqn:Hn.
        * (* R10 *)
          apply N.leb_le in Hn. destruct (N.to_nat n) as [|n'] eqn:En; [lia|].
          replace (N.to_nat (6 + 2 * b)) with (6 + 2 * N.to_nat b) by lia.
          apply RL_csteps. eapply csteps_conf_eq; [apply (R10 (N.to_nat b) n') | reflexivity | apply Bc_eq; lia].
        * (* R11 *)
          apply N.leb_gt in Hn. assert (Hn0 : n = 0%N) by lia. subst n. change (N.to_nat 0) with 0.
          replace (N.to_nat (5 + 2 * b)) with (5 + 2 * N.to_nat b) by lia.
          eapply RL_eq; [apply (R11 (N.to_nat b)) | reflexivity | f_equal; apply Bc_eq; lia]. }
  (* the B family *)
  destruct (m =? 0)%N eqn:Hm0; [exact I|].
  apply N.eqb_neq in Hm0.
  assert (HfB : forall x y z, (match N.to_nat f with 1 => A1c x y z | 2 => A2c x y z | _ => Bc x y end) = Bc x y).
  { intros. apply N.eqb_neq in Hf1, Hf2.
    destruct (N.to_nat f) as [|[|[|k]]] eqn:Ef; try reflexivity; lia. }
  rewrite HfB. clear HfB.
  change (N.to_nat 1) with 1. change (N.to_nat 2) with 2. change (N.to_nat 3) with 3.
  destruct (N.to_nat m) as [|m'] eqn:Em; [lia|].
  destruct (b =? 0)%N eqn:Hb0.
  { (* R12 *)
    apply N.eqb_eq in Hb0. subst b. change (N.to_nat 0) with 0. change (N.to_nat 1) with 1.
    eapply RL_eq; [apply (R12 m') | reflexivity | f_equal; apply A1c_eq; lia]. }
  apply N.eqb_neq in Hb0.
  destruct (b =? 1)%N eqn:Hb1.
  { (* R13 *)
    apply N.eqb_eq in Hb1. subst b. change (N.to_nat 1) with 1. change (N.to_nat 0) with 0.
    eapply RL_eq; [apply (R13 m') | reflexivity | f_equal; apply A1c_eq; lia]. }
  apply N.eqb_neq in Hb1.
  destruct (N.even b) eqn:He.
  { (* R14 *)
    destruct (N_even_nat b He) as [k Hk].
    assert (Hk1 : 1 <= k) by lia.
    replace (N.to_nat (5 * b + 7)) with (10 * (k - 1) + 17) by lia.
    apply RL_csteps.
    eapply csteps_conf_eq; [apply (R14 m' (k - 1)) | apply Bc_eq; lia | apply A2c_eq; lia]. }
  { (* R15 *)
    destruct (N_odd_nat b He) as [k Hk].
    assert (Hk1 : 1 <= k) by lia.
    replace (N.to_nat (5 * b + 6)) with (10 * (k - 1) + 21) by lia.
    eapply RL_eq; [apply (R15 m' (k - 1)) | f_equal; apply Bc_eq; lia | f_equal; apply A1c_eq; lia]. }
Qed.

(** ** Iterating the rules *)

Definition ch_state : Type := (N * N * N * N * N)%type.   (* family, m, b, n, total steps *)

Definition ch_stepo (o : option ch_state) : option ch_state :=
  match o with
  | None => None
  | Some (f, m, b, n, acc) =>
    match ch_rule_N f m b n with
    | None => None
    | Some (f', m', b', n', s) => Some (f', m', b', n', (acc + s)%N)
    end
  end.

Definition ch_run (fuel : N) (o : option ch_state) : option ch_state := N.iter fuel ch_stepo o.

Lemma ch_stepo_sound : forall f m b n acc f' m' b' n' acc',
  ch_stepo (Some (f, m, b, n, acc)) = Some (f', m', b', n', acc') ->
  (acc <= acc')%N /\
  stepn champ (N.to_nat acc' - N.to_nat acc) (lift (confN f m b n)) = Some (lift (confN f' m' b' n')).
Proof.
  intros f m b n acc f' m' b' n' acc' H. unfold ch_stepo in H.
  pose proof (ch_rule_N_sound f m b n) as Hs. unfold ch_spec in Hs.
  destruct (ch_rule_N f m b n) as [[[[[f1 m1] b1] n1] s]|]; [|discriminate].
  injection H as <- <- <- <- <-.
  split; [lia|].
  replace (N.to_nat (acc + s) - N.to_nat acc) with (N.to_nat s) by lia.
  exact Hs.
Qed.

Lemma ch_run_sound : forall k f m b n acc f' m' b' n' acc',
  ch_run k (Some (f, m, b, n, acc)) = Some (f', m', b', n', acc') ->
  (acc <= acc')%N /\
  stepn champ (N.to_nat acc' - N.to_nat acc) (lift (confN f m b n)) = Some (lift (confN f' m' b' n')).
Proof.
  intros k. induction k using N.peano_ind; intros f m b n acc f' m' b' n' acc' H; unfold ch_run in H.
  - simpl in H. injection H as <- <- <- <- <-. split; [lia|]. rewrite Nat.sub_diag. reflexivity.
  - rewrite N.iter_succ in H.
    destruct (N.iter k ch_stepo (Some (f, m, b, n, acc))) as [[[[[f1 m1] b1] n1] acc1]|] eqn:E;
      [|discriminate].
    destruct (IHk _ _ _ _ _ _ _ _ _ _ E) as [Hle Hrun].
    destruct (ch_stepo_sound _ _ _ _ _ _ _ _ _ _ H) as [Hle2 Hrun2].
    split; [lia|].
    replace (N.to_nat acc' - N.to_nat acc)
      with ((N.to_nat acc1 - N.to_nat acc) + (N.to_nat acc' - N.to_nat acc1)) by lia.
    rewrite stepn_add, Hrun. exact Hrun2.
Qed.

(** ** The trajectory *)

(** 2,808,416 accelerated rule applications from A1(0, 0, 1) at step 2. *)
Definition ch_fuel : N := 2808416.

Lemma champion_run_value :
  ch_run ch_fuel (Some (1%N, 0%N, 0%N, 1%N, 2%N))
  = Some (1%N, 1021045%N, 1151187%N, 1%N, 119114045079717165%N).
Proof. vm_compute. reflexivity. Qed.

Lemma champion_total_ge : (bb33_champion_steps <=? 119114045079717165)%N = true.
Proof. vm_compute. reflexivity. Qed.

(** From the blank tape: A1(0, 0, 1) after 2 steps. *)
Lemma champion_2 : stepn champ 2 InitES = Some (lift (confN 1 0 0 1)).
Proof.
  rewrite <- lift_c0.
  assert (H : csteps champ 2 c0 = Some (StC, ([], S1, [S2]))) by (vm_compute; reflexivity).
  rewrite (csteps_lift _ _ _ _ H). f_equal.
  unfold confN. change (N.to_nat 1) with 1. change (N.to_nat 0) with 0.
  unfold A1c, LB. cbn [repeat app rep Nat.mul Nat.add].
  change [S2; S0] with ([S2] ++ [S0]). rewrite lift_rpad_L. reflexivity.
Qed.

Lemma champion_stepn_total :
  stepn champ (2 + (N.to_nat 119114045079717165 - N.to_nat 2)) InitES
  = Some (lift (confN 1 1021045 1151187 1)).
Proof.
  destruct (ch_run_sound _ _ _ _ _ _ _ _ _ _ _ champion_run_value) as [_ H].
  rewrite stepn_add, champion_2. exact H.
Qed.

(** ** The theorems *)

(** The probable champion is still running after more than 1.19 x 10^17
    steps; in particular it has not halted within the current
    champion's 119,112,334,170,342,541. *)
Theorem champion_runs_past_champion :
  exists n c, stepn champ n InitES = Some c /\ N.to_nat bb33_champion_steps <= n.
Proof.
  exists (2 + (N.to_nat 119114045079717165 - N.to_nat 2)), (lift (confN 1 1021045 1151187 1)).
  split; [apply champion_stepn_total | unfold bb33_champion_steps; lia].
Qed.

Theorem champion_no_halt_within_champion :
  forall m, m <= N.to_nat bb33_champion_steps -> stepn champ m InitES <> None.
Proof.
  intros m Hm Hnone.
  pose proof champion_stepn_total as H.
  assert (Hle : m <= 2 + (N.to_nat 119114045079717165 - N.to_nat 2))
    by (unfold bb33_champion_steps in Hm; lia).
  destruct (stepn_prefix champ m _ _ _ Hle H) as (cm & Hcm & _).
  congruence.
Qed.

(** If it halts at all (as is probviously expected), it does so after
    more than the current champion's step count. *)
Corollary champion_halt_is_late :
  forall n, stepn champ n InitES = None -> N.to_nat bb33_champion_steps < n.
Proof.
  intros n Hn.
  destruct (Nat.lt_ge_cases (N.to_nat bb33_champion_steps) n) as [Hlt|Hge]; [exact Hlt|].
  exfalso. apply (champion_no_halt_within_champion n Hge Hn).
Qed.
