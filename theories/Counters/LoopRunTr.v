(** * Counters.LoopRunTr: hand-stated counter laps checked by concrete runs
    (SCOPING_INSTR 7.4.LE10).

    LE8 left counters whose carries and overflows run LOOPS of inner counts.
    The loops differ from row to row, so there is no single family to fit.
    Here a row's proof is a set of ordinary Coq lemmas about [Reach0] /
    [Reach1] ([NestCountTr]).  Each lemma is about configurations whose far
    parts are opaque lists, and is proved by induction (on a width, a count,
    a loop index) from:

    - [r0_run] / [r1_run] (tactic [rr n]): [n] concrete machine steps,
      computed by [cbn] on the configuration; the opaque tails are never
      read, or the computation gets stuck and the proof fails;
    - [sweepR] / [sweepL]: a head that crosses a repeated word [rep w n]
      in one state, from the single-word fact;
    - [reach0_lift_l] / [_r], [lift_padR] / [lift_padL]: blank padding at
      the far ends;
    - [boot_ok]: the boot, by computing [csteps] from the blank tape.

    [cR q L R] / [cL q L R]: the head on the first cell of [R] / of [L]
    (lists nearest-first).  The board is [BoardSeqTr]: any configurations
    [Cf i] with a lap [Cf i ->+ Cf (S i)] and every unpinned instruction
    firing from every [Cf i]; never-QH and QH closers as in
    [NestCountTr.BoardCountTr].

    Nothing landed is modified.  Axiom footprint: [functional_extensionality_dep],
    via [CTape.lift]. *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr.
From BBB4.Counters Require Import WTape.
From BBB4.Checkers Require Import WrapTr LadderCheckTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
From BBB4.Counters Require Import NestCountTr.
Import ListNotations.

Definition cR (q : St) (L R : list Sym) : cconf := (q, (L, chd R, ctl R)).
Definition cL (q : St) (L R : list Sym) : cconf := (q, (ctl L, chd L, R)).

Section Run.
Variable tm : TM.

Lemma r0_run : forall n c c1 c2, csteps tm n c = Some c1 -> Reach0 tm c1 c2 -> Reach0 tm c c2.
Proof.
  intros n c c1 c2 H (m & Hm). exists (n + m). rewrite stepn_add.
  rewrite (csteps_lift tm n c c1 H). exact Hm.
Qed.

Lemma r1_run : forall n c c1 c2, 0 < n -> csteps tm n c = Some c1 -> Reach0 tm c1 c2 -> Reach1 tm c c2.
Proof.
  intros n c c1 c2 Hn H (m & Hm). exists (n + m). split; [lia|]. rewrite stepn_add.
  rewrite (csteps_lift tm n c c1 H). exact Hm.
Qed.

Lemma fires_here : forall c t, cinstr c = t -> Fires tm c t.
Proof. intros c t H. exists 0, c. split; [reflexivity | exact H]. Qed.

Lemma rep_comm : forall (w : list Sym) n, rep w n ++ w = w ++ rep w n.
Proof.
  intros w n. induction n as [|n IH]; cbn [rep]; [rewrite app_nil_r; reflexivity|].
  rewrite <- app_assoc, IH. reflexivity.
Qed.

Lemma sweepR : forall q w w',
  (forall L R, Reach0 tm (cR q L (w ++ R)) (cR q (w' ++ L) R)) ->
  forall n L R, Reach0 tm (cR q L (rep w n ++ R)) (cR q (rep w' n ++ L) R).
Proof.
  intros q w w' H n. induction n as [|n IH]; intros L R; [apply reach0_refl|].
  cbn [rep]. rewrite <- app_assoc.
  eapply reach0_trans; [apply H|]. eapply reach0_trans; [apply IH|].
  rewrite app_assoc, rep_comm. apply reach0_refl.
Qed.

Lemma sweepL : forall q w w',
  (forall L R, Reach0 tm (cL q (w ++ L) R) (cL q L (w' ++ R))) ->
  forall n L R, Reach0 tm (cL q (rep w n ++ L) R) (cL q L (rep w' n ++ R)).
Proof.
  intros q w w' H n. induction n as [|n IH]; intros L R; [apply reach0_refl|].
  cbn [rep]. rewrite <- app_assoc.
  eapply reach0_trans; [apply H|]. eapply reach0_trans; [apply IH|].
  rewrite app_assoc, rep_comm. apply reach0_refl.
Qed.

Lemma reach0_lift_r : forall a b b', lift b = lift b' -> Reach0 tm a b' -> Reach0 tm a b.
Proof. intros a b b' H (m & Hm). exists m. rewrite H. exact Hm. Qed.

Lemma reach0_lift_l : forall a a' b, lift a = lift a' -> Reach0 tm a' b -> Reach0 tm a b.
Proof. intros a a' b H (m & Hm). exists m. rewrite H. exact Hm. Qed.

End Run.

(** blank padding at the far ends *)
Lemma lift_padR : forall m q L h R, lift (q, (L, h, R ++ rep [S0] m)) = lift (q, (L, h, R)).
Proof.
  intros. replace (rep [S0] m) with (repeat S0 m); [apply lift_fixR_padn|].
  induction m; cbn; [reflexivity | rewrite IHm; reflexivity].
Qed.

Lemma lift_padL : forall m q L h R, lift (q, (L ++ rep [S0] m, h, R)) = lift (q, (L, h, R)).
Proof.
  intros. replace (rep [S0] m) with (repeat S0 m); [apply lift_fixL_padn|].
  induction m; cbn; [reflexivity | rewrite IHm; reflexivity].
Qed.

Ltac rr n := first
  [ eapply (r1_run _ n); [lia | cbn; reflexivity | ]
  | eapply (r0_run _ n); [cbn; reflexivity | ] ].
Ltac r0 := apply reach0_refl.
Ltac rt H := eapply reach0_trans; [first [apply H | apply reach1_0; apply H]|].
Ltac rt1 H := eapply reach10; [apply H|].
Ltac rt01 H := eapply reach01; [apply H|].

Ltac feq := first [ reflexivity | lia | progress f_equal; feq ].
Ltac rfix := unfold cL, cR; cbn [chd ctl]; match goal with |- Reach0 _ ?a ?b => replace b with a; [apply reach0_refl | feq] end.

Lemma boot_ok : forall tm n c,
  match csteps tm n CTape.c0 with Some c' => ceqb c' c | None => false end = true ->
  stepn tm n InitES = Some (lift c).
Proof.
  intros tm n c H. destruct (csteps tm n CTape.c0) as [c'|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift tm n _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** A board from any lap sequence *)
Section BoardSeqTr.
Variable tm0 : TM.
Variable pins : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).
Variable Cf : nat -> cconf.
Hypothesis Hlap : forall i, Reach1 tm (Cf i) (Cf (S i)).
Hypothesis Hfire : forall t, ~ In t pins -> forall i, Fires tm (Cf i) t.

Lemma lapS_n : forall i, exists m c',
  csteps tm m (Cf i) = Some c' /\ lift c' = lift (Cf (S i)) /\ 0 < m.
Proof.
  intros i. destruct (reach1_csteps tm _ _ (Hlap i)) as (m & c' & Hm & Hc & Hl).
  exists m, c'. split; [exact Hc | split; [exact Hl | exact Hm]].
Qed.

Theorem boardS_neverqhtr : forall s0,
  stepn tm s0 InitES = Some (lift (Cf 0)) -> NeverQuasiHaltsTr tm0.
Proof.
  intros s0 Hboot.
  apply (glue_neverqhtrN tm0 pins Cf).
  - exists s0. exact Hboot.
  - exact lapS_n.
  - intros t Hnp N. destruct (Hfire t Hnp N) as (k & c' & Hc & Ht).
    exists N, k, c'. split; [lia | split; assumption].
Qed.

Theorem boardS_qhtr : forall s0 Bd,
  stepn tm0 s0 InitES = Some (lift (Cf 0)) ->
  existsb (fun tg => cfires tm0 CTape.c0 s0 tg) pins = true ->
  (s0 <=? Bd) = true ->
  NonHalt tm0 /\ QHBoundTr Bd tm0 /\ QuasiHaltsTr tm0.
Proof.
  intros s0 Bd Hboot Hwit Hle.
  apply (lap_qh_stage tm0 pins (fun p => Cf (Nat.pred (Pos.to_nat p))) 1%positive s0 Bd).
  - exact Hboot.
  - intros p _.
    destruct (lapS_n (Nat.pred (Pos.to_nat p))) as (m & c' & Hrun & Hl & Hm).
    exists m, c'. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (Hfire t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.
End BoardSeqTr.


Lemma rep_snoc : forall (w : list Sym) n l, rep w n ++ w ++ l = w ++ rep w n ++ l.
Proof. intros. rewrite app_assoc, rep_comm, <- app_assoc. reflexivity. Qed.

Lemma rep1_snoc : forall (a : Sym) n l, rep [a] n ++ a :: l = a :: rep [a] n ++ l.
Proof. intros. exact (rep_snoc [a] n l). Qed.

(** a fire witness by stepping until the instruction is the one asked for
    (at most [n] steps, each computed on the concrete part) *)
Ltac fire_find_n n :=
  match n with
  | O => fail
  | S ?m => first [ apply fires_here; reflexivity
                  | eapply fire_back; [rr 1; apply reach0_refl | ]; fire_find_n m ]
  end.
Ltac fire_find := fire_find_n 64.

Lemma rep_pair : forall (a : Sym) n, rep [a; a] n = rep [a] (n + n).
Proof.
  intros a n. induction n as [|n IH]; [reflexivity|].
  replace (S n + S n) with (S (S (n + n))) by lia. cbn [rep app]. rewrite IH. reflexivity.
Qed.

(** an inner count from its carries, the carries needed only below the width *)
Lemma count_from_carry_lt : forall tm (mk : list Sym -> cconf) (Z O : list Sym) w,
  (forall k Y, k < w -> Reach1 tm (mk (rep O k ++ Z ++ Y)) (mk (rep Z k ++ O ++ Y))) ->
  forall Y, Reach0 tm (mk (rep Z w ++ Y)) (mk (rep O w ++ Y)).
Proof.
  intros tm mk Z O w. induction w as [|w IH]; intros Hc Y; [apply reach0_refl|].
  rewrite !rep_S_r, <- !app_assoc.
  assert (Hc' : forall k Y, k < w -> Reach1 tm (mk (rep O k ++ Z ++ Y)) (mk (rep Z k ++ O ++ Y)))
    by (intros k Y' Hk; apply Hc; lia).
  apply (reach0_trans tm _ (mk (rep O w ++ Z ++ Y))); [exact (IH Hc' (Z ++ Y))|].
  apply (reach0_trans tm _ (mk (rep Z w ++ O ++ Y))); [apply reach1_0, Hc; lia|].
  exact (IH Hc' (O ++ Y)).
Qed.

(** step until the configuration is the target (at most [n] steps) *)
Ltac rgo_n n :=
  match n with
  | O => fail
  | S ?m => first [ apply reach0_refl | rr 1; rgo_n m ]
  end.
Ltac rgo := rgo_n 80.

(** [rr i; tac] for the least [i <= n] where [tac] then succeeds *)
Ltac rr_upto n tac :=
  match n with
  | O => fail
  | S ?m => first [ rr_upto m tac | rr n; tac ]
  end.

(** an alternating word read one cell later *)
Lemma rep_shift : forall (a b : Sym) k l, a :: rep [b; a] k ++ l = rep [a; b] k ++ a :: l.
Proof.
  intros a b k. induction k as [|k IH]; intros l; [reflexivity|].
  cbn [rep app]. f_equal. f_equal. apply IH.
Qed.

(** a sweep in any configuration shape [F L R] (the head's neighbourhood
    fixed by [F]): one word [u] off [L] becomes [v] on [R], and conversely *)
Lemma sweepFL : forall tm (F : list Sym -> list Sym -> cconf) (u v : list Sym),
  (forall L R, Reach0 tm (F (u ++ L) R) (F L (v ++ R))) ->
  forall n L R, Reach0 tm (F (rep u n ++ L) R) (F L (rep v n ++ R)).
Proof.
  intros tm F u v H n. induction n as [|n IH]; intros L R; [apply reach0_refl|].
  cbn [rep]. rewrite <- app_assoc.
  eapply reach0_trans; [apply H|]. eapply reach0_trans; [apply IH|].
  rewrite app_assoc, rep_comm. apply reach0_refl.
Qed.

Lemma sweepFR : forall tm (F : list Sym -> list Sym -> cconf) (u v : list Sym),
  (forall L R, Reach0 tm (F L (u ++ R)) (F (v ++ L) R)) ->
  forall n L R, Reach0 tm (F L (rep u n ++ R)) (F (rep v n ++ L) R).
Proof.
  intros tm F u v H n. induction n as [|n IH]; intros L R; [apply reach0_refl|].
  cbn [rep]. rewrite <- app_assoc.
  eapply reach0_trans; [apply H|]. eapply reach0_trans; [apply IH|].
  rewrite app_assoc, rep_comm. apply reach0_refl.
Qed.

(** a repeated word read one cell later *)
Lemma rep_rot : forall (a : Sym) w k l, rep (a :: w) k ++ a :: l = a :: rep (w ++ [a]) k ++ l.
Proof.
  intros a w k. induction k as [|k IH]; intros l; [reflexivity|].
  cbn [rep]. rewrite <- app_assoc. cbn [app]. f_equal. rewrite IH, <- !app_assoc. reflexivity.
Qed.

Lemma rep_app_dbl : forall (w : list Sym) k, rep (w ++ w) k = rep w (k + k).
Proof.
  intros w k. induction k as [|k IH]; [reflexivity|].
  replace (S k + S k) with (S (S (k + k))) by lia. cbn [rep]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma rep_triple : forall (a : Sym) n, rep [a; a; a] n = rep [a] (n + n + n).
Proof.
  intros a n. induction n as [|n IH]; [reflexivity|].
  replace (S n + S n + S n) with (S (S (S (n + n + n)))) by lia. cbn [rep app]. rewrite IH. reflexivity.
Qed.

Lemma rep1_fold : forall (a : Sym) n l, a :: rep [a] n ++ l = rep [a] (S n) ++ l.
Proof. reflexivity. Qed.
