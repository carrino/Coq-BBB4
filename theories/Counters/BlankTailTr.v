(** * BlankTailTr: the one-state march on blank tape, at instruction level.

    The transition-level twin of [Counters.BlankTail].  After a finite
    prefix of [N0] steps the machine is in a state [q], the cell under the
    head is blank, the half-tape AHEAD (in the direction [q] moves on a
    blank) is blank, and [tm q S0 = Some (mkTrans w d q)] is a self-loop.
    From there every step reads a blank in [q]: the only instruction that
    fires from [N0] on is [(q, S0)].  Every other instruction is quiet from
    [N0], so [QHBoundTr B] holds for every [B >= N0]; the instruction
    [(StA, S0)] fired at index 0 is quiet from [N0] when [q <> StA].

    This is the route of the BBB(4) champion [1RB1LD_1RC1RB_1LC1LA_0RC0RD]
    (N0 = 32,779,478, exactly [B_close]) and of the previous champion
    [1RB0LD_1LC0LA_1LA0LC_1RD1RC] (N0 = 66,349).  The prefix runs on the
    BINARY fuel of [TCyclerN.cstepsN], so the champion's 32.8M steps are
    one [vm_compute] (~10 s) and never a unary [nat].

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List NArith PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.CensusTr Require Import TNF_QHTr.
From BBB4.Checkers Require Import TCyclerN.
From BBB4.Counters Require Import BlankTail.
Import ListNotations.

Set Default Goal Selector "!".

(** ** Large bounds without unary numerals

    A bare [nat] literal past 5,000 (the closeout's [B_close = 32779478])
    is kept as [Nat.of_num_uint] of its decimal digits, which [lia] cannot
    see through and which must never be forced to 32.8M constructors.
    [N_le_dec] compares a binary [N] with such a literal by comparing the
    binary numerals ([N.of_uint] of the same digits computes cheaply). *)

Lemma of_uint_acc_N : forall d acc,
  Nat.of_uint_acc d (Pos.to_nat acc) = Pos.to_nat (Pos.of_uint_acc d acc).
Proof.
  induction d as [|d IH|d IH|d IH|d IH|d IH|d IH|d IH|d IH|d IH|d IH]; intro acc;
    cbn [Nat.of_uint_acc Pos.of_uint_acc]; [reflexivity| ..];
    rewrite <- IH; f_equal; rewrite Nat.tail_mul_spec;
    rewrite ?Pos2Nat.inj_add, ?Pos2Nat.inj_mul, ?Pos2Nat.inj_1; simpl Pos.to_nat; lia.
Qed.

Lemma of_uint_N : forall d, Nat.of_uint d = N.to_nat (N.of_uint d).
Proof.
  unfold Nat.of_uint, N.of_uint.
  induction d as [|d IH|d IH|d IH|d IH|d IH|d IH|d IH|d IH|d IH|d IH];
    cbn [Nat.of_uint_acc Pos.of_uint]; [reflexivity|exact IH| ..];
    cbn [N.to_nat]; rewrite <- of_uint_acc_N; f_equal.
Qed.

Lemma N_le_dec : forall n d,
  (n <=? N.of_uint d)%N = true ->
  N.to_nat n <= Nat.of_num_uint (Number.UIntDecimal d).
Proof.
  intros n d H. cbv [Nat.of_num_uint]. rewrite of_uint_N.
  apply N.leb_le in H. lia.
Qed.

(** ** The march keeps a blank under the head *)

Lemma march_L_head : forall tm q w n l r,
  tm q S0 = Some (mkTrans w DL q) ->
  blank_list l ->
  exists l' r', csteps tm n (q, (l, S0, r)) = Some (q, (l', S0, r')).
Proof.
  intros tm q w n. induction n as [|n IH]; intros l r H Hb.
  - exists l, r. reflexivity.
  - cbn [csteps]. rewrite (march_L_step tm q w l r H Hb).
    apply (IH (ctl l) (w :: r) H (ctl_blank l Hb)).
Qed.

Lemma march_R_head : forall tm q w n l r,
  tm q S0 = Some (mkTrans w DR q) ->
  blank_list r ->
  exists l' r', csteps tm n (q, (l, S0, r)) = Some (q, (l', S0, r')).
Proof.
  intros tm q w n. induction n as [|n IH]; intros l r H Hb.
  - exists l, r. reflexivity.
  - cbn [csteps]. rewrite (march_R_step tm q w l r H Hb).
    apply (IH (w :: l) (ctl r) H (ctl_blank r Hb)).
Qed.

(** ** From the prefix onward only [(q, S0)] fires *)

Section TailTr.

Variable tm : TM.
Variable q : St.
Variable N0 : nat.
Variable ct : ctape.

Hypothesis Hpre  : csteps tm N0 c0 = Some (q, ct).
Hypothesis Hloop : forall n, exists l' r',
  csteps tm n (q, ct) = Some (q, (l', S0, r')).

Lemma tail_fires : forall n, N0 <= n -> FiresAt tm (q, S0) n.
Proof.
  intros n Hn.
  replace n with (N0 + (n - N0)) by lia.
  destruct (Hloop (n - N0)) as (l' & r' & Hm).
  exists (lift (q, (l', S0, r'))). split.
  - rewrite stepn_add, <- lift_c0, (csteps_lift _ _ _ _ Hpre).
    exact (csteps_lift _ _ _ _ Hm).
  - reflexivity.
Qed.

Lemma tail_only : forall t n, N0 <= n -> FiresAt tm t n -> t = (q, S0).
Proof.
  intros t n Hn (c & Hc & Ht).
  destruct (tail_fires n Hn) as (c' & Hc' & Ht').
  rewrite Hc in Hc'. injection Hc' as <-. congruence.
Qed.

Lemma tail_loop_st : forall n, exists ct',
  csteps tm n (q, ct) = Some (q, ct').
Proof.
  intro n. destruct (Hloop n) as (l' & r' & H). exists (l', S0, r'). exact H.
Qed.

Theorem tail_tr_board : forall B, N0 <= B -> q <> StA ->
  NonHalt tm /\ QHBoundTr B tm /\ QuasiHaltsTr tm.
Proof.
  intros B HB HqA. split; [| split].
  - exact (tail_nonhalt tm q N0 ct Hpre tail_loop_st).
  - intros t s [Hf Hq].
    destruct (le_lt_dec N0 s) as [Hle|Hlt]; [|lia].
    exfalso.
    pose proof (tail_only t s Hle Hf) as ->.
    apply (Hq (S s)); [lia|].
    apply tail_fires. lia.
  - exists (StA, S0). split.
    + exists 0. exists InitES. split; reflexivity.
    + exists N0. intros n Hn Hf.
      pose proof (tail_only (StA, S0) n Hn Hf) as E.
      injection E as E. congruence.
Qed.

End TailTr.

(** ** Boolean interface, on binary fuel *)

Definition blank_tail_tr_checkb (dir : Dir) (tm : TM) (q : St) (N0 : N) : bool :=
  match cstepsN tm N0 c0 with
  | Some (q', (l, h, r)) =>
      st_eqb q' q && sym_eqb h S0 &&
      (match dir with DL => blank_listb l | DR => blank_listb r end)
  | None => false
  end.

Theorem blank_tail_tr_board : forall tm q w d N0 B,
  tm q S0 = Some (mkTrans w d q) ->
  st_eqb q StA = false ->
  blank_tail_tr_checkb d tm q N0 = true ->
  N.to_nat N0 <= B ->
  NonHalt tm /\ QHBoundTr B tm /\ QuasiHaltsTr tm.
Proof.
  intros tm q w d N0 B Hq HqA Hchk HB.
  assert (HqA' : q <> StA).
  { intro E. subst q.
    rewrite (proj2 (st_eqb_spec StA StA) eq_refl) in HqA. discriminate. }
  unfold blank_tail_tr_checkb in Hchk. rewrite cstepsN_nat in Hchk.
  destruct (csteps tm (N.to_nat N0) c0) as [[q' [[l h] r]]|] eqn:Epre;
    [|discriminate].
  apply andb_prop in Hchk as [Hchk Hside].
  apply andb_prop in Hchk as [Hq' Hh].
  apply st_eqb_spec in Hq'. apply sym_eqb_spec in Hh. subst q' h.
  apply (tail_tr_board tm q (N.to_nat N0) (l, S0, r) Epre); [|exact HB|exact HqA'].
  intro n. destruct d.
  - exact (march_L_head tm q w n l r Hq (blank_listb_spec l Hside)).
  - exact (march_R_head tm q w n l r Hq (blank_listb_spec r Hside)).
Qed.
