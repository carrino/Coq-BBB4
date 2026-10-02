(** * Transport a boarded row to its state-permuted / mirrored conjugates.

    [dst] is [src] with its states renamed by a bijection [p] and,
    optionally, its moves mirrored.  The two machines start in different
    states, so their blank-tape runs differ at first; they are compared at
    a pair of boots instead: [src] reaches [a] after [m] steps, [dst]
    reaches [cconj p flip a] (up to blanks) after [n0].  From there the
    runs are in lockstep (CConjugateTr's [cconj_step]).

    - [cconj_coverstr]: with [n0 <= m], [coversTr src -> coversTr dst],
      whatever proved [src] (never-quasihalting or a bounded quasihalt).
      A completion of [dst] is the conjugate of a completion of [src]; a
      quiet instruction of it last fires either in its boot (before [n0])
      or [m - n0] steps EARLIER than its preimage's last fire.
    - [cconj_nqhtr]: any [m], [n0], [NeverQuasiHaltsTr src ->
      NeverQuasiHaltsTr dst], given a finite check that every instruction
      [dst] fires in its boot fires again within [K] steps after it. *)
From Coq Require Import Arith Lia List Bool.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape Mirror.
From BBB4.Census Require Import TNF_QH.
From BBB4.CensusTr Require Import TNF_QHTr.
From BBB4.CloseoutTr Require Import CloseoutKitTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import CConjugateTr.
Import ListNotations.

Lemma stepn_lift_csteps : forall tm k c e,
  stepn tm k (lift c) = Some e -> exists d, csteps tm k c = Some d /\ lift d = e.
Proof.
  induction k as [|k IH]; intros c e H.
  - injection H as <-. exists c. split; reflexivity.
  - cbn [stepn] in H. destruct (step tm (lift c)) as [e1|] eqn:E; [|discriminate].
    destruct (cstep_lift_rev tm c e1 E) as (c1 & Hc1 & <-).
    destruct (IH c1 e H) as (d & Hd & He).
    exists d. split; [|exact He]. cbn [csteps]. rewrite Hc1. exact Hd.
Qed.

Lemma TM_le_csteps : forall h tm n c d,
  TM_le h tm -> csteps h n c = Some d -> csteps tm n c = Some d.
Proof.
  intros h tm n. induction n as [|n IH]; intros c d Hle H; [exact H|].
  cbn [csteps] in H |- *.
  destruct c as [q [[l s] r]]. unfold cstep in H |- *.
  destruct (h q s) as [tr|] eqn:E; [|discriminate].
  destruct (Hle q s) as [Hn|Ht]; [congruence|]. rewrite Ht, E.
  exact (IH _ _ Hle H).
Qed.

Lemma csteps_cconj_eq : forall src dst p flip,
  (forall q s, dst (p q) s = option_map (tconj p flip) (src q s)) ->
  forall n c, csteps dst n (cconj p flip c) = option_map (cconj p flip) (csteps src n c).
Proof.
  intros src dst p flip Ht n. induction n as [|n IH]; intro c; [reflexivity|].
  cbn [csteps]. rewrite (cconj_step src dst p flip Ht).
  destruct (cstep src c) as [c'|]; [apply IH|reflexivity].
Qed.

Lemma stepn_c0_csteps : forall tm n c,
  csteps tm n c0 = Some c -> stepn tm n InitES = Some (lift c).
Proof. intros tm n c H. rewrite <- lift_c0. exact (csteps_lift _ _ _ _ H). Qed.

Section Conj.
Variable src dst : TM.
Variable p pinv : St -> St.
Variable flip : bool.
Hypothesis Hpinv : forall q, pinv (p q) = q.
Hypothesis Hppinv : forall q, p (pinv q) = q.
Hypothesis Htable : forall q s,
  dst (p q) s = option_map (tconj p flip) (src q s).
Variable m n0 : nat.
Variable a b : cconf.
Hypothesis Hsrc : csteps src m c0 = Some a.
Hypothesis Hdst : csteps dst n0 c0 = Some b.
Hypothesis Hab : ceqb b (cconj p flip a) = true.

(** the lockstep, at the level of [FiresAt], for any conjugate pair of
    machines that run [src]'s and [dst]'s boots *)
Section Lock.
Variable s1 d1 : TM.
Hypothesis Ht1 : forall q s, d1 (p q) s = option_map (tconj p flip) (s1 q s).
Hypothesis Hs1 : csteps s1 m c0 = Some a.
Hypothesis Hd1 : csteps d1 n0 c0 = Some b.

Lemma lock_fwd : forall j t,
  FiresAt s1 t (m + j) -> FiresAt d1 (p (fst t), snd t) (n0 + j).
Proof.
  intros j t (e & He & Hi).
  rewrite stepn_add, (stepn_c0_csteps _ _ _ Hs1) in He.
  destruct (stepn_lift_csteps _ _ _ _ He) as (d & Hd & <-).
  exists (lift (cconj p flip d)). split.
  - rewrite stepn_add, (stepn_c0_csteps _ _ _ Hd1), (ceqb_lift _ _ Hab).
    apply csteps_lift. rewrite (csteps_cconj_eq s1 d1 p flip Ht1), Hd. reflexivity.
  - rewrite cinstr_lift, (cconj_instr s1 d1 p flip Ht1). rewrite cinstr_lift in Hi. rewrite Hi. reflexivity.
Qed.

Lemma lock_bwd : forall j t',
  FiresAt d1 t' (n0 + j) ->
  exists t, t' = (p (fst t), snd t) /\ FiresAt s1 t (m + j).
Proof.
  intros j t' (e & He & Hi).
  rewrite stepn_add, (stepn_c0_csteps _ _ _ Hd1), (ceqb_lift _ _ Hab) in He.
  destruct (stepn_lift_csteps _ _ _ _ He) as (d' & Hd' & <-).
  rewrite (csteps_cconj_eq s1 d1 p flip Ht1) in Hd'.
  destruct (csteps s1 j a) as [d|] eqn:Hd; [|discriminate]. injection Hd' as <-.
  exists (cinstr d). split.
  - rewrite <- Hi, cinstr_lift, (cconj_instr s1 d1 p flip Ht1). reflexivity.
  - exists (lift d). split; [|apply cinstr_lift].
    rewrite stepn_add, (stepn_c0_csteps _ _ _ Hs1). apply csteps_lift, Hd.
Qed.
End Lock.

Lemma tconj_inv : forall x, tconj p flip (tconj pinv flip x) = x.
Proof.
  intros [w d q]. unfold tconj; cbn. rewrite Hppinv.
  destruct flip; [destruct d|]; reflexivity.
Qed.

Lemma tconj_inv' : forall x, tconj pinv flip (tconj p flip x) = x.
Proof.
  intros [w d q]. unfold tconj; cbn. rewrite Hpinv.
  destruct flip; [destruct d|]; reflexivity.
Qed.

Theorem cconj_coverstr :
  n0 <= m -> n0 <= B_close -> coversTr src -> coversTr dst.
Proof.
  intros Hnm HB Hcov tm' Hle'.
  set (tm := fun q s => option_map (tconj pinv flip) (tm' (p q) s)).
  assert (Ht2 : forall q s, tm' (p q) s = option_map (tconj p flip) (tm q s)).
  { intros q s. unfold tm. destruct (tm' (p q) s) as [x|]; [|reflexivity].
    cbn. rewrite tconj_inv. reflexivity. }
  assert (Hle : TM_le src tm).
  { intros q s. destruct (src q s) as [x|] eqn:E; [right|left; reflexivity].
    destruct (Hle' (p q) s) as [Hn|He].
    - rewrite Htable, E in Hn. discriminate.
    - unfold tm. rewrite He, Htable, E. cbn. rewrite tconj_inv'. reflexivity. }
  pose proof (Hcov tm Hle) as Hq.
  pose proof (TM_le_csteps _ _ _ _ _ Hle Hsrc) as Hs1.
  pose proof (TM_le_csteps _ _ _ _ _ Hle' Hdst) as Hd1.
  intros t' s' [Hf Hquiet].
  destruct (lt_dec s' n0) as [Hlt|Hge]; [lia|].
  replace s' with (n0 + (s' - n0)) in Hf, Hquiet by lia.
  destruct (lock_bwd tm tm' Ht2 Hs1 Hd1 _ _ Hf) as (t & -> & Hft).
  assert (S (m + (s' - n0)) <= B_close); [|lia].
  apply (Hq t). split; [exact Hft|].
  intros n Hn Hfn. replace n with (m + (n - m)) in Hfn by lia.
  apply (Hquiet (n0 + (n - m))); [lia|].
  exact (lock_fwd tm tm' Ht2 Hs1 Hd1 _ _ Hfn).
Qed.

(** the never-quasihalting transport: any boot offset *)
Definition fires_late (tm : TM) (lo K : nat) (t : Instr) : bool :=
  existsb (fun j => match csteps tm j c0 with
                    | Some c => instr_eqb (cinstr c) t
                    | None => false end) (seq lo K).

Definition boot_ok (tm : TM) (n K : nat) : bool :=
  forallb (fun i => match csteps tm i c0 with
                    | Some c => fires_late tm n K (cinstr c)
                    | None => true end) (seq 0 n).

Lemma boot_ok_sound : forall tm n K i t,
  boot_ok tm n K = true -> i < n -> FiresAt tm t i ->
  exists j, n <= j /\ FiresAt tm t j.
Proof.
  intros tm n K i t Hb Hi (e & He & Ht).
  destruct (stepn_csteps _ _ _ He) as (c & Hc & <-).
  unfold boot_ok in Hb. rewrite forallb_forall in Hb.
  specialize (Hb i ltac:(apply in_seq; lia)). rewrite Hc in Hb.
  unfold fires_late in Hb. apply existsb_exists in Hb as (j & Hj & Hjc).
  apply in_seq in Hj.
  destruct (csteps tm j c0) as [c'|] eqn:Ec'; [|discriminate].
  apply instr_eqb_spec in Hjc.
  exists j. split; [lia|]. exists (lift c'). split; [apply stepn_c0_csteps, Ec'|].
  rewrite cinstr_lift, Hjc, <- Ht, cinstr_lift. reflexivity.
Qed.

Theorem cconj_nqhtr : forall K,
  boot_ok dst n0 K = true -> NeverQuasiHaltsTr src -> NeverQuasiHaltsTr dst.
Proof.
  intros K Hb Hnq.
  assert (Hlate : forall t' i, n0 <= i -> FiresAt dst t' i ->
            forall N, exists n, N <= n /\ FiresAt dst t' n).
  { intros t' i Hi Hf N.
    replace i with (n0 + (i - n0)) in Hf by lia.
    destruct (lock_bwd src dst Htable Hsrc Hdst _ _ Hf) as (t & -> & Hft).
    destruct (Hnq t (ex_intro _ _ Hft) (m + N)) as (n & Hn & Hfn).
    replace n with (m + (n - m)) in Hfn by lia.
    exists (n0 + (n - m)). split; [lia|].
    exact (lock_fwd src dst Htable Hsrc Hdst _ _ Hfn). }
  intros t' [i Hf] N.
  destruct (lt_dec i n0) as [Hlt|Hge].
  - destruct (boot_ok_sound _ _ _ _ _ Hb Hlt Hf) as (j & Hj & Hfj).
    exact (Hlate t' j Hj Hfj N).
  - exact (Hlate t' i ltac:(lia) Hf N).
Qed.
End Conj.

(** [B_close = 32779478]; the unary comparison is made once here *)
Lemma conj_le_B_close : forall n, Nat.leb n 1048576 = true -> n <= B_close.
Proof.
  intros n H. apply Nat.leb_le in H.
  apply (Nat.le_trans _ _ _ H). apply Nat.leb_le. unfold B_close.
  vm_cast_no_check (eq_refl true).
Qed.

(** the batch-facing forms: both boots and their agreement by one
    computation *)
Definition conj_boot (src dst : TM) (p : St -> St) (flip : bool) (m n0 : nat) : bool :=
  match csteps src m c0, csteps dst n0 c0 with
  | Some a, Some b => ceqb b (cconj p flip a)
  | _, _ => false
  end.

Theorem cconj_cover_run : forall src dst p pinv flip m n0,
  (forall q, pinv (p q) = q) -> (forall q, p (pinv q) = q) ->
  (forall q s, dst (p q) s = option_map (tconj p flip) (src q s)) ->
  conj_boot src dst p flip m n0 = true ->
  Nat.leb n0 m = true -> Nat.leb n0 1048576 = true ->
  coversTr src -> coversTr dst.
Proof.
  intros src dst p pinv flip m n0 H1 H2 Ht Hb Hnm HB.
  unfold conj_boot in Hb.
  destruct (csteps src m c0) as [a|] eqn:Ea; [|discriminate].
  destruct (csteps dst n0 c0) as [b|] eqn:Eb; [|discriminate].
  apply Nat.leb_le in Hnm. apply conj_le_B_close in HB.
  exact (cconj_coverstr src dst p pinv flip H1 H2 Ht m n0 a b Ea Eb Hb Hnm HB).
Qed.

Theorem cconj_nqh_run : forall src dst p pinv flip m n0 K,
  (forall q, pinv (p q) = q) -> (forall q, p (pinv q) = q) ->
  (forall q s, dst (p q) s = option_map (tconj p flip) (src q s)) ->
  conj_boot src dst p flip m n0 = true ->
  boot_ok dst n0 K = true ->
  NeverQuasiHaltsTr src -> NeverQuasiHaltsTr dst.
Proof.
  intros src dst p pinv flip m n0 K H1 H2 Ht Hb Hok.
  unfold conj_boot in Hb.
  destruct (csteps src m c0) as [a|] eqn:Ea; [|discriminate].
  destruct (csteps dst n0 c0) as [b|] eqn:Eb; [|discriminate].
  exact (cconj_nqhtr src dst p flip Ht m n0 a b Ea Eb Hb K Hok).
Qed.
