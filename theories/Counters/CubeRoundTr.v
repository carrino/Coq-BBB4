(** * Termination of the non-firing rounds of a ternary cube counter.

    At the two-parameter round entrance, division by three transfers
    mass into an accumulator.  A reset increases the first parameter by
    the number of divisions plus two.  Grouping two resets when necessary
    strictly decreases the ternary valuation; this is a semantic ranking
    across whole rounds, rather than a fixed affine ranking on each edge. *)
From Coq Require Import Arith Lia Bool List.
From BBB4.Counters Require Import TriNuTr.

Lemma cube_pow_pos : forall r, 0 < 3 ^ r.
Proof. intro r. apply Nat.neq_0_lt_0, Nat.pow_nonzero. lia. Qed.

Lemma cube_factor : forall x, 0 < x -> exists u,
  0 < u /\ u mod 3 <> 0 /\ x = 3 ^ (nu 3 x) * u.
Proof.
  induction x as [x IH] using lt_wf_ind. intro Hx.
  destruct (Nat.eq_dec (x mod 3) 0) as [Hm|Hm].
  - pose proof (Nat.div_mod x 3 ltac:(lia)) as Hdiv.
    assert (He : x = 3 * (x/3)) by lia.
    assert (Hy : 0 < x/3) by nia.
    assert (Hlt : x/3 < x) by (apply Nat.div_lt; lia).
    destruct (IH (x/3) Hlt Hy) as (u & Hu & Hum & Heu).
    exists u. repeat split; try assumption.
    rewrite He at 1 2. rewrite (nu_mul 3 ltac:(lia) _ Hy).
    cbn [Nat.pow]. rewrite <- Nat.mul_assoc, <- Heu. reflexivity.
  - exists x. repeat split; try assumption.
    rewrite (nu_zero_mod 3 ltac:(lia) x Hx Hm). cbn. lia.
Qed.

Lemma cube_nu_small_offset : forall r u d,
  0 < d -> d < 3 ^ r -> nu 3 (3 ^ r * u + d) < r.
Proof.
  intros r u d Hd Hdp.
  pose proof (cube_pow_pos r) as Hp.
  destruct (cube_factor (3^r*u+d) ltac:(nia)) as (v & Hv & _ & Ev).
  destruct (Nat.lt_ge_cases (nu 3 (3^r*u+d)) r) as [H|H]; [exact H|].
  assert (En : nu 3 (3^r*u+d) = r + (nu 3 (3^r*u+d)-r)) by lia.
  rewrite En, Nat.pow_add_r in Ev.
  set (z := 3^(nu 3 (3^r*u+d)-r)*v) in *.
  assert (Ez : 3^r*u+d = 3^r*z) by (unfold z; nia).
  destruct (Nat.le_gt_cases z u); nia.
Qed.

Lemma cube_pow_large : forall r, 2 <= r -> r+4 < 3^r.
Proof.
  induction r as [|r IH]; intro Hr; [lia|].
  destruct (Nat.eq_dec r 1) as [->|Hne]; [cbn; lia|].
  assert (H2 : 2 <= r) by lia. specialize (IH H2).
  cbn [Nat.pow]. nia.
Qed.

Section ShiftedRounds.
Variable Q : nat -> nat -> Prop.
Hypothesis Qhit : forall k b, Q (3*k+2) b.
Hypothesis Qdiv : forall x b, 0 < x -> Q x (b+2*x+1) -> Q (3*x) b.
Hypothesis Qreset : forall k b, Q (3*k+b+3) 0 -> Q (3*k+1) b.

Lemma cube_carry : forall r u b, 0 < u ->
  Q u (b+(3^r*u-u)+r) -> Q (3^r*u) b.
Proof.
  induction r as [|r IH]; intros u b Hu H.
  - replace (b+(3^0*u-u)+0) with b in H by (cbn; lia).
    replace (3^0*u) with u by (cbn; lia). exact H.
  - replace (3^S r*u) with (3*(3^r*u)) by (cbn [Nat.pow]; nia).
    apply Qdiv; [pose proof (cube_pow_pos r); nia|].
    apply IH; [exact Hu|].
    pose proof (cube_pow_pos r).
    replace (b+2*(3^r*u)+1+(3^r*u-u)+r)
      with (b+(3^S r*u-u)+S r) by (cbn [Nat.pow]; nia).
    exact H.
Qed.

Lemma cube_reset_round : forall r k b,
  Q (3^r*(3*k+1)+b+r+2) 0 -> Q (3^r*(3*k+1)) b.
Proof.
  intros r k b H. apply cube_carry; [lia|]. apply Qreset.
  pose proof (cube_pow_pos r).
  replace (3*k+(b+(3^r*(3*k+1)-(3*k+1))+r)+3)
    with (3^r*(3*k+1)+b+r+2) by nia. exact H.
Qed.

Lemma cube_hit_round : forall r k b, Q (3^r*(3*k+2)) b.
Proof. intros. apply cube_carry; [lia|]. apply Qhit. Qed.

Lemma cube_divisible : forall r x,
  0 < x -> nu 3 x = r -> x mod 3 = 0 -> Q x 0.
Proof.
  induction r as [r IH] using lt_wf_ind. intros x Hx Hr Hxm.
  destruct (cube_factor x Hx) as (u & Hu & Hum & Hxu).
  rewrite Hr in Hxu.
  assert (Hrpos : 0 < r).
  { destruct r; [|lia]. assert (E : x=u) by (cbn in Hxu; lia).
    rewrite E in Hxm. exfalso. exact (Hum Hxm). }
  pose proof (Nat.mod_upper_bound u 3 ltac:(lia)) as Hub.
  pose proof (Nat.div_mod u 3 ltac:(lia)) as Hdu.
  destruct (Nat.eq_dec (u mod 3) 2) as [Hu2|Hu2].
  - assert (Eu : u = 3*(u/3)+2) by lia.
    rewrite Hxu, Eu. apply cube_hit_round.
  - assert (Eu : u = 3*(u/3)+1) by lia.
    rewrite Hxu, Eu. apply cube_reset_round.
    replace (3^r*(3*(u/3)+1)+0+r+2) with (x+r+2) by nia.
    assert (Hlower : forall d, 0 < d -> d < 3^r ->
      (x+d) mod 3 = 0 -> Q (x+d) 0).
    { intros d Hd Hdp Hm. apply (IH (nu 3 (x+d))).
      - rewrite Hxu. apply cube_nu_small_offset; assumption.
      - lia.
      - reflexivity.
      - exact Hm. }
    pose proof (Nat.div_mod x 3 ltac:(lia)) as Hdx.
    pose proof (Nat.div_mod r 3 ltac:(lia)) as Hdr.
    pose proof (Nat.mod_upper_bound r 3 ltac:(lia)) as Hrb.
    destruct (Nat.eq_dec (r mod 3) 0) as [Hm0|Hm0].
    + replace (x+r+2) with (3*(x/3+r/3)+2) by lia. apply Qhit.
    + destruct (Nat.eq_dec (r mod 3) 1) as [Hm1|Hm1].
      * destruct (Nat.eq_dec r 1) as [->|Hne].
        -- replace (x+1+2) with (3*(3*(u/3)+2)) by (cbn in Hxu; nia).
           apply Qdiv; [lia|]. apply Qhit.
        -- replace (x+r+2) with (x+(r+2)) by lia.
           apply Hlower; [lia| |].
           ++ pose proof (cube_pow_large r ltac:(lia)); lia.
           ++ replace (x+(r+2)) with ((x/3+r/3+1)*3) by lia.
              apply Nat.Div0.mod_mul.
      * assert (Hm2 : r mod 3 = 2) by lia.
        replace (x+r+2) with (3*(x/3+r/3+1)+1) by lia.
        apply Qreset.
        replace (3*(x/3+r/3+1)+0+3) with (x+(r+4)) by lia.
        apply Hlower; [lia|apply cube_pow_large; lia|].
        replace (x+(r+4)) with ((x/3+r/3+2)*3) by lia.
        apply Nat.Div0.mod_mul.
Qed.

Lemma cube_shifted_zero : forall x, 0 < x -> Q x 0.
Proof.
  intros x Hx. pose proof (Nat.div_mod x 3 ltac:(lia)) as Hdx.
  pose proof (Nat.mod_upper_bound x 3 ltac:(lia)) as Hxb.
  destruct (Nat.eq_dec (x mod 3) 0) as [Hm0|Hm0].
  - apply (cube_divisible (nu 3 x)); auto.
  - destruct (Nat.eq_dec (x mod 3) 2) as [Hm2|Hm2].
    + replace x with (3*(x/3)+2) by lia. apply Qhit.
    + assert (Hm1 : x mod 3 = 1) by lia.
      replace x with (3*(x/3)+1) at 1 by lia. apply Qreset.
      apply (cube_divisible (nu 3 (3*(x/3)+0+3))); [lia|reflexivity|].
      replace (3*(x/3)+0+3) with ((x/3+1)*3) by lia.
      apply Nat.Div0.mod_mul.
Qed.

Theorem cube_shifted_total : forall x b, 0 < x -> Q x b.
Proof.
  intros x b Hx. destruct (cube_factor x Hx) as (u & Hu & Hum & Hxu).
  pose proof (Nat.div_mod u 3 ltac:(lia)) as Hdu.
  pose proof (Nat.mod_upper_bound u 3 ltac:(lia)) as Hub.
  destruct (Nat.eq_dec (u mod 3) 2) as [Hm2|Hm2].
  - assert (Eu : u = 3*(u/3)+2) by lia.
    rewrite Hxu, Eu. apply cube_hit_round.
  - assert (Eu : u = 3*(u/3)+1) by lia.
    rewrite Hxu, Eu. apply cube_reset_round. apply cube_shifted_zero.
    pose proof (cube_pow_pos (nu 3 x)). nia.
Qed.
End ShiftedRounds.

Definition cube_shift (P : nat -> nat -> Prop) (x b : nat) : Prop :=
  match x with 0 => True | 1 => P (b+1) 0 | S (S a) => P a b end.

Section CubeRounds.
Variable P : nat -> nat -> Prop.
Hypothesis H0 : forall b, P 0 b.
Hypothesis H3 : forall k b, P (3*k+3) b.
Hypothesis H1 : forall b, P (b+4) 0 -> P 1 b.
Hypothesis H2 : forall b, P (b+4) 0 -> P 2 b.
Hypothesis H4 : forall k b, P k (b+2*k+5) -> P (3*k+4) b.
Hypothesis H5 : forall k b, P (3*k+b+7) 0 -> P (3*k+5) b.

Lemma cube_shift_hit : forall k b, cube_shift P (3*k+2) b.
Proof.
  intros [|k] b.
  - apply H0.
  - replace (3*S k+2) with (S(S(3*k+3))) by lia. apply H3.
Qed.

Lemma cube_shift_div : forall x b, 0 < x ->
  cube_shift P x (b+2*x+1) -> cube_shift P (3*x) b.
Proof.
  intros [|[|k]] b Hx H; [lia| |].
  - cbn [cube_shift] in *. apply H1.
    replace (b+2*1+1+1) with (b+4) in H by lia. exact H.
  - replace (3*S(S k)) with (S(S(3*k+4))) by lia.
    cbn [cube_shift] in *. apply H4.
    replace (b+2*S(S k)+1) with (b+2*k+5) in H by lia. exact H.
Qed.

Lemma cube_shift_reset : forall k b,
  cube_shift P (3*k+b+3) 0 -> cube_shift P (3*k+1) b.
Proof.
  intros [|[|k]] b H.
  - replace (3*0+b+3) with (S(S(b+1))) in H by lia. exact H.
  - replace (3*1+b+3) with (S(S(b+4))) in H by lia. apply H2. exact H.
  - replace (3*S(S k)+b+3) with (S(S(3*k+b+7))) in H by lia.
    replace (3*S(S k)+1) with (S(S(3*k+5))) by lia. apply H5. exact H.
Qed.

Theorem cube_round_total : forall a b, P a b.
Proof.
  intros a b. change (cube_shift P (S(S a)) b).
  apply cube_shifted_total; try assumption.
  - apply cube_shift_hit.
  - apply cube_shift_div.
  - apply cube_shift_reset.
  - lia.
Qed.
End CubeRounds.
