(** Three exact rules for 1RB2LA1RA1LB_0LB2RB3RB1LA. *)
From Coq Require Import Arith Lia List.
From BBB24 Require Import Statement Spec CTape Gap.
Import ListNotations.
Ltac left_atomic := first
  [ solve [apply left_step with (d:=DL); reflexivity]
  | solve [apply left_step with (d:=DR); reflexivity] ].
Ltac right_atomic := first
  [ solve [apply right_step with (d:=DL); reflexivity]
  | solve [apply right_step with (d:=DR); reflexivity] ].

Lemma pair3_one : forall q l r,
  Runs champion 2 (leftward q (S3::S3::l) r)
    (leftward q l (S1::S1::r)).
Proof.
  intros; change 2 with (1+1); destruct q.
  all: eapply runs_add; [left_atomic|left_atomic].
Qed.

Lemma consume1_one : forall n l r,
  Runs champion (2*n+3)
    (leftward StA (S2::l) (repeat S2 n ++ S1::r))
    (leftward StA l (repeat S2 (n+2) ++ r)).
Proof.
  intros n l r. replace (2*n+3) with (1+(n+(1+(n+1)))) by lia.
  eapply runs_add; [left_atomic|].
  eapply runs_add; [apply chain_right; reflexivity|].
  eapply runs_add; [right_atomic|].
  rewrite repeat_snoc.
  replace (n+1) with (S n) by lia. replace (n+2) with (S (S n)) by lia.
  pose proof (chain_left champion StA S1 S2 (S n) l (S2::r) eq_refl) as H.
  cbn [repeat app] in H |- *. rewrite repeat_snoc in H. exact H.
Qed.

Lemma grow2_front : forall n l,
  Runs champion (2*n+9)
    (leftward StA (S2::l) (repeat S2 n))
    (leftward StA l (repeat S2 (n+1) ++ [S1;S0])).
Proof.
  intros n l. replace (2*n+9) with (1+(n+(1+(1+(1+(1+(1+(1+(1+(n+1)))))))))) by lia.
  eapply runs_add; [left_atomic|].
  rewrite <- (app_nil_r (repeat S2 n)).
  eapply runs_add; [apply chain_right; reflexivity|].
  eapply runs_add; [first [solve [apply right_step with (s:=S0) (r:=[]) (d:=DL); reflexivity] | solve [apply right_step with (s:=S0) (r:=[]) (d:=DR); reflexivity]]|].
  eapply runs_add; [first [solve [apply right_step with (s:=S0) (r:=[]) (d:=DL); reflexivity] | solve [apply right_step with (s:=S0) (r:=[]) (d:=DR); reflexivity]]|].
  eapply runs_add; [left_atomic|].
  eapply runs_add; [right_atomic|].
  eapply runs_add; [left_atomic|].
  eapply runs_add; [right_atomic|].
  eapply runs_add; [left_atomic|].
  rewrite repeat_snoc. replace (n+1) with (S n) by lia.
  exact (chain_left champion StA S1 S2 (S n) l [S1;S0] eq_refl).
Qed.

Lemma grow2_one : forall n l,
  Runs champion (4*n+14)
    (leftward StA (S2::S2::l) (repeat S2 n))
    (leftward StA l (repeat S2 (n+3))).
Proof.
  intros. replace (4*n+14) with ((2*n+9)+(2*(n+1)+3)) by lia.
  eapply runs_add; [apply grow2_front|].
  pose proof (consume1_one (n+1) l [S0]) as H.
  replace (n+1+2) with (n+3) in H by lia.
  rewrite leftward_pad_right in H. exact H.
Qed.

Lemma pair3_many : forall k q l r,
  Runs champion (2*k) (leftward q (repeat S3 (2*k) ++ l) r)
    (leftward q l (repeat S1 (2*k) ++ r)).
Proof.
  induction k as [|k IH]; intros q l r; [apply runs_zero|].
  replace (2*S k) with (2+2*k) by lia. cbn [repeat app].
  eapply runs_add; [apply pair3_one|].
  change (Runs champion (2*k)
    (leftward q (repeat S3 (2*k) ++ l) (S1::S1::r))
    (leftward q l (S1::S1::(repeat S1 (2*k) ++ r)))).
  rewrite <- (repeat_snoc S1 (2*k) r), <- (repeat_snoc S1 (2*k) (S1::r)).
  apply IH.
Qed.

Lemma grow2_many : forall k n l,
  Runs champion (6*k*k+(4*n+8)*k)
    (leftward StA (repeat S2 (2*k) ++ l) (repeat S2 n))
    (leftward StA l (repeat S2 (n+3*k))).
Proof.
  induction k as [|k IH]; intros n l.
  - replace (6*0*0+(4*n+8)*0) with 0 by lia.
    replace (n+3*0) with n by lia. apply runs_zero.
  - replace (6*S k*S k+(4*n+8)*S k)
      with ((4*n+14)+(6*k*k+(4*(n+3)+8)*k)) by nia.
    replace (2*S k) with (S (S (2*k))) by lia. cbn [repeat app].
    eapply runs_add; [apply grow2_one|].
    replace (n+3*S k) with ((n+3)+3*k) by lia. apply IH.
Qed.

Lemma consume1_many : forall k n l r,
  Runs champion (2*k*k+(2*n+1)*k)
    (leftward StA (repeat S2 k ++ l)
      (repeat S2 n ++ repeat S1 k ++ r))
    (leftward StA l (repeat S2 (n+2*k) ++ r)).
Proof.
  induction k as [|k IH]; intros n l r.
  - replace (2*0*0+(2*n+1)*0) with 0 by lia.
    replace (n+2*0) with n by lia. apply runs_zero.
  - replace (2*S k*S k+(2*n+1)*S k)
      with ((2*n+3)+(2*k*k+(2*(n+2)+1)*k)) by nia.
    cbn [repeat app]. eapply runs_add; [apply consume1_one|].
    replace (n+2*S k) with ((n+2)+2*k) by lia. apply IH.
Qed.
