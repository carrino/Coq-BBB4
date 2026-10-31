(** * BigfootRun: Bigfoot runs for more than 119,112,334,170,342,541 steps.

    The rules of [Bigfoot] are iterated on binary numbers ([N]) by
    [vm_compute]: 62 rule applications from A(2, 1, 2) (reached at step
    69) carry the machine past the BB(3,3) champion's step count
    without ever meeting the halting rule.  The soundness bridge
    [run_N_sound] turns the computed total into a [stepn] fact about
    the abstract machine; nothing here evaluates a unary number of
    that size. *)

From Coq Require Import Arith NArith Lia List.
From SmallBB Require Import Statement CTape.
From BB33 Require Import Lib Bigfoot.
Import ListNotations.

(** ** The rule function on binary numbers *)

Definition rule_N (a b c : N) : option (N * N * N * N) :=
  let k := (b / 6)%N in
  match N.to_nat (b mod 6) with
  | 0 => if (8 * k + c =? 0)%N then None
         else Some (a, 8 * k + c - 1, 2, 4 * a + 96 * k * k + 48 * k + 24 * k * c + 2 * c + 13)%N
  | 1 => if (8 * k + c =? 0)%N then None
         else Some (a + 1, 8 * k + c - 1, 3, 4 * a + 96 * k * k + 80 * k + 24 * k * c + 6 * c + 29)%N
  | 2 => if (a =? 0)%N then None
         else Some (a - 1, 8 * k + c + 3, 2, 4 * a + 96 * k * k + 144 * k + 24 * k * c + 14 * c + 51)%N
  | 3 => Some (a, 8 * k + c + 1, 5, 4 * a + 96 * k * k + 112 * k + 24 * k * c + 10 * c + 91)%N
  | 4 => Some (a + 1, 8 * k + c + 3, 2, 4 * a + 96 * k * k + 144 * k + 24 * k * c + 14 * c + 63)%N
  | _ => Some (a, 8 * k + c + 5, 3, 4 * a + 96 * k * k + 176 * k + 24 * k * c + 18 * c + 103)%N
  end.

Lemma some4_eq : forall (a b c s a' b' c' s' : nat),
  a = a' -> b = b' -> c = c' -> s = s' -> Some (a, b, c, s) = Some (a', b', c', s').
Proof. intros; subst; reflexivity. Qed.

Definition to_nat4 (o : option (N * N * N * N)) : option (nat * nat * nat * nat) :=
  match o with
  | None => None
  | Some (a, b, c, s) => Some (N.to_nat a, N.to_nat b, N.to_nat c, N.to_nat s)
  end.

(** [rule_N] is [rule_nat] under [N.to_nat]. *)
Lemma rule_N_nat : forall a b c,
  rule_nat (N.to_nat a) (N.to_nat b) (N.to_nat c) = to_nat4 (rule_N a b c).
Proof.
  intros a b c. unfold rule_N, rule_nat.
  change (N.to_nat b / 6) with (N.to_nat b / N.to_nat 6).
  change (N.to_nat b mod 6) with (N.to_nat b mod N.to_nat 6).
  rewrite <- N2Nat.inj_div, <- N2Nat.inj_mod.
  set (k := (b / 6)%N) in *.
  destruct (N.to_nat (b mod 6)) as [|[|[|[|[|[|r']]]]]].
  - destruct (8 * k + c =? 0)%N eqn:E.
    + apply N.eqb_eq in E. destruct (8 * N.to_nat k + N.to_nat c) as [|d] eqn:Hd; [reflexivity | lia].
    + apply N.eqb_neq in E. destruct (8 * N.to_nat k + N.to_nat c) as [|d] eqn:Hd; [lia|].
      cbv [to_nat4]. apply some4_eq; nia.
  - destruct (8 * k + c =? 0)%N eqn:E.
    + apply N.eqb_eq in E. destruct (8 * N.to_nat k + N.to_nat c) as [|d] eqn:Hd; [reflexivity | lia].
    + apply N.eqb_neq in E. destruct (8 * N.to_nat k + N.to_nat c) as [|d] eqn:Hd; [lia|].
      cbv [to_nat4]. apply some4_eq; nia.
  - destruct (a =? 0)%N eqn:E.
    + apply N.eqb_eq in E. destruct (N.to_nat a) as [|a0] eqn:Ha; [reflexivity | lia].
    + apply N.eqb_neq in E. destruct (N.to_nat a) as [|a0] eqn:Ha; [lia|].
      cbv [to_nat4]. apply some4_eq; nia.
  - cbv [to_nat4]. apply some4_eq; nia.
  - cbv [to_nat4]. apply some4_eq; nia.
  - cbv [to_nat4]. apply some4_eq; nia.
  - cbv [to_nat4]. apply some4_eq; nia.
Qed.

Definition A_N (a b c : N) : cconf := A (N.to_nat a) (N.to_nat b) (N.to_nat c).

Lemma rule_N_sound : forall a b c a' b' c' s,
  rule_N a b c = Some (a', b', c', s) ->
  csteps bigfoot (N.to_nat s) (A_N a b c) = Some (A_N a' b' c').
Proof.
  intros a b c a' b' c' s H. apply rule_nat_sound.
  rewrite rule_N_nat, H. reflexivity.
Qed.

(** ** Iterating the rules, accumulating the step count *)

Fixpoint run_N (n : nat) (a b c acc : N) : option (N * N * N * N) :=
  match n with
  | O => Some (a, b, c, acc)
  | S n' => match rule_N a b c with
            | None => None
            | Some (a', b', c', s) => run_N n' a' b' c' (acc + s)
            end
  end.

Lemma run_N_sound : forall n a b c acc a' b' c' acc',
  run_N n a b c acc = Some (a', b', c', acc') ->
  (acc <= acc')%N /\
  csteps bigfoot (N.to_nat acc' - N.to_nat acc) (A_N a b c) = Some (A_N a' b' c').
Proof.
  induction n as [|n IH]; intros a b c acc a' b' c' acc' H; simpl in H.
  - injection H as <- <- <- <-. split; [lia|].
    rewrite Nat.sub_diag. reflexivity.
  - destruct (rule_N a b c) as [[[[a1 b1] c1] s]|] eqn:E; [|discriminate].
    destruct (IH _ _ _ _ _ _ _ _ H) as [Hle Hrun].
    split; [lia|].
    eapply csteps_trans_eq; [apply (rule_N_sound _ _ _ _ _ _ _ E) | exact Hrun | lia].
Qed.

(** ** The trajectory *)

(** 62 rule applications from A(2, 1, 2) at step 69: a never drops
    below 2 and the running total passes the champion. *)
Lemma bigfoot_run_62 :
  run_N 62 2 1 2 69 = Some (17%N, 219012156%N, 3%N, 164455975202918183%N).
Proof. vm_compute. reflexivity. Qed.

Lemma bigfoot_total_ge : (bb33_champion_steps <=? 164455975202918183)%N = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bigfoot_csteps_total :
  csteps bigfoot (69 + (N.to_nat 164455975202918183 - N.to_nat 69)) c0
  = Some (A_N 17 219012156 3).
Proof.
  destruct (run_N_sound _ _ _ _ _ _ _ _ _ bigfoot_run_62) as [_ H].
  eapply csteps_trans; [apply bigfoot_69 | exact H].
Qed.

(** ** The theorems *)

(** Bigfoot is still running after more than 1.6 x 10^17 steps; in
    particular it has not halted within the champion's 119,112,334,170,342,541. *)
Theorem bigfoot_runs_past_champion :
  exists n c, stepn bigfoot n InitES = Some c /\ N.to_nat bb33_champion_steps <= n.
Proof.
  exists (69 + (N.to_nat 164455975202918183 - N.to_nat 69)), (lift (A_N 17 219012156 3)).
  split.
  - rewrite <- lift_c0. apply csteps_lift_stepn, bigfoot_csteps_total.
  - unfold bb33_champion_steps. lia.
Qed.

Theorem bigfoot_no_halt_within_champion :
  forall m, m <= N.to_nat bb33_champion_steps -> stepn bigfoot m InitES <> None.
Proof.
  intros m Hm.
  eapply csteps_c0_no_halt; [apply bigfoot_csteps_total | unfold bb33_champion_steps in Hm; lia].
Qed.

(** If Bigfoot halts at all, it halts after more than the champion's step count. *)
Corollary bigfoot_halt_is_late :
  forall n, stepn bigfoot n InitES = None -> N.to_nat bb33_champion_steps < n.
Proof.
  intros n Hn.
  destruct (Nat.lt_ge_cases (N.to_nat bb33_champion_steps) n) as [Hlt|Hge]; [exact Hlt|].
  exfalso. apply (bigfoot_no_halt_within_champion n Hge Hn).
Qed.
