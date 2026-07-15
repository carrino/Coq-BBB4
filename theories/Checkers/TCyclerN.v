(** * TCyclerN: binary-fuel front end for the translated-cycler checker.

    The [tcycler_check_neverqh] checker takes its anchor as a unary
    [nat]; under [vm_compute] the fuel numeral itself materializes
    (~16 bytes per step), so a 3*10^8-step anchor costs ~5 GB before
    the first step is taken -- and the four [cvisits] passes repeat
    the cost.  One upstream tcycler certificate
    (1RB0LD_1RC1LD_1LD0RC_0LA1LB, anchor 309,417,105) is beyond that
    budget.

    This file adds [N]-fueled drivers ([cstepsN], [cvisitsN]) built
    on [N.iter] -- the VM iterates on the binary numeral without
    materializing it -- and a wrapper checker whose soundness proof
    is just the [Nat.iter]/[N.iter] equivalence plus the existing
    soundness theorem.  The trusted simulation semantics ([cstep],
    [csteps]) are unchanged. *)

From Coq Require Import Arith Lia Bool List NArith.
From BBB4 Require Import BBB4_Statement CTape GTape Mirror.
From BBB4.Checkers Require Import Cycle TCycler.
Import ListNotations.

(** ** N-fueled stepping *)

Definition cstep_o (tm : TM) (oc : option cconf) : option cconf :=
  match oc with
  | Some c => cstep tm c
  | None => None
  end.

Definition cstepsN (tm : TM) (n : N) (c : cconf) : option cconf :=
  N.iter n (cstep_o tm) (Some c).

Lemma iter_cstep_o_none : forall tm m,
  Nat.iter m (cstep_o tm) None = None.
Proof.
  induction m; simpl; [reflexivity | rewrite IHm; reflexivity].
Qed.

Lemma csteps_iter : forall tm n c,
  csteps tm n c = Nat.iter n (cstep_o tm) (Some c).
Proof.
  induction n as [|m IH]; intros c.
  - reflexivity.
  - rewrite Nat.iter_succ_r.
    cbn [cstep_o].
    simpl csteps.
    destruct (cstep tm c) as [c'|].
    + apply IH.
    + symmetry. apply iter_cstep_o_none.
Qed.

Lemma cstepsN_nat : forall tm n c,
  cstepsN tm n c = csteps tm (N.to_nat n) c.
Proof.
  intros. unfold cstepsN.
  rewrite csteps_iter, <- N2Nat.inj_iter. reflexivity.
Qed.

(** ** N-fueled visit scanning *)

Definition cv_body (tm : TM) (q : St) (st : option cconf * bool)
  : option cconf * bool :=
  match st with
  | (Some c, b) => (cstep tm c, b || st_eqb (fst c) q)
  | (None, b) => (None, b)
  end.

Definition cvisitsN (tm : TM) (c : cconf) (len : N) (q : St) : bool :=
  snd (N.iter len (cv_body tm q) (Some c, false)).

Lemma cvisits_iter : forall tm q n oc b,
  snd (Nat.iter n (cv_body tm q) (oc, b))
  = b || match oc with
         | Some c => cvisits tm c n q
         | None => false
         end.
Proof.
  induction n as [|m IH]; intros oc b.
  - destruct oc; simpl; now rewrite orb_false_r.
  - rewrite Nat.iter_succ_r.
    destruct oc as [c|]; cbn [cv_body].
    + rewrite IH. cbn [cvisits].
      destruct (cstep tm c); rewrite ?orb_assoc; reflexivity.
    + rewrite IH. now rewrite orb_false_r.
Qed.

Lemma cvisitsN_nat : forall tm c len q,
  cvisitsN tm c len q = cvisits tm c (N.to_nat len) q.
Proof.
  intros. unfold cvisitsN.
  rewrite N2Nat.inj_iter, cvisits_iter. reflexivity.
Qed.

(** ** The binary-fuel checker *)

Definition tcycler_check_neverqh_N (tm : TM) (n1 P : N) (W : nat) : bool :=
  (0 <? P)%N &&
  match cstepsN tm n1 c0 with
  | Some (q1, (l1, h1, r1)) =>
      let g1 : cconf := (q1, (firstn_pad W l1, h1, r1)) in
      match gsteps tm (N.to_nat P) g1 with
      | Some g2 =>
          gmatch g1 g2 &&
          forallb (fun q => implb (cvisitsN tm c0 (n1 + P) q)
                                  (gvisits tm g1 (N.to_nat P) q)) all_St
      | None => false
      end
  | None => false
  end.

Theorem tcycler_check_neverqh_N_sound : forall tm n1 P W,
  tcycler_check_neverqh_N tm n1 P W = true -> NeverQuasiHaltsSt tm.
Proof.
  intros tm n1 P W H.
  apply (tcycler_check_neverqh_sound tm (N.to_nat n1) (N.to_nat P) W).
  unfold tcycler_check_neverqh_N in H.
  unfold tcycler_check_neverqh.
  rewrite cstepsN_nat in H.
  apply andb_prop in H as [HP H].
  apply andb_true_intro. split.
  { apply N.ltb_lt in HP. apply Nat.ltb_lt. lia. }
  destruct (csteps tm (N.to_nat n1) c0) as [[q1 [[l1 h1] r1]]|];
    [|discriminate].
  destruct (gsteps tm (N.to_nat P) (q1, (firstn_pad W l1, h1, r1)));
    [|discriminate].
  apply andb_prop in H as [Hg Hf].
  apply andb_true_intro. split; [exact Hg|].
  rewrite forallb_forall in Hf. apply forallb_forall.
  intros q Hq. specialize (Hf q Hq).
  rewrite cvisitsN_nat, N2Nat.inj_add in Hf.
  exact Hf.
Qed.

Corollary tcycler_check_neverqh_N_sound_L : forall tm n1 P W,
  tcycler_check_neverqh_N (mirror_tm tm) n1 P W = true ->
  NeverQuasiHaltsSt tm.
Proof.
  intros. apply mirror_never_qh.
  eapply tcycler_check_neverqh_N_sound; eauto.
Qed.
