(** * LP_1RB1LD_0RC0RB_1LC0LA_1LA0LA (SCOPING_INSTR 7.4.LE11)

    The two-level binary mirror counter of [Counters.TwoLevelTr] with
    another right encoding.  The anchor is [A [0]] at the junction; the
    right side is the junction's right neighbour [0], then [y] (LSB first,
    digits [01] / [11]), then a single [1] marker.  A right carry is a
    3-step unit ([A0], [B0], [C1]) that moves one cell right per [1]
    ([usweep]), then a 5-step turn and the A/D walk back to the left; the
    left walks are those of [LP_1RB1LD_1RC0RB_1LA1RC_1LA0LA] (same [A],
    [D] and [B1] rules), and two steps ([B0], [C1]) bring the head back
    to the next junction.  [D1] fires only in steps whose [y] is odd.

    Hand-stated, kernel-checked.  Axiom footprint: [functional_extensionality_dep]. *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr LoopMirrorTr TwoLevelTr.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Definition tm_1RB1LD_0RC0RB_1LC0LA_1LA0LA : TM := fun q s => match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB) | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DR StC) | StB, S1 => Some (mkTrans S0 DR StB)
  | StC, S0 => Some (mkTrans S1 DL StC) | StC, S1 => Some (mkTrans S0 DL StA)
  | StD, S0 => Some (mkTrans S1 DL StA) | StD, S1 => Some (mkTrans S0 DL StA)
  end.
Local Notation tm := (tm_wrap_trs tm_1RB1LD_0RC0RB_1LC0LA_1LA0LA []).

(** ** Cells *)

Definition yc (y : list bool) : list Sym := bcells [S0; S1] [S1; S1] y.

Definition enc (s : ast) : cconf :=
  let '(u, v, y) := s in (StA, (xc u ++ S1 :: xc v, S0, S0 :: yc y ++ [S1])).

Lemma yc_ff : forall k r, yc (repeat false k ++ r) = rep [S0; S1] k ++ yc r.
Proof. intros. apply bcells_ff. Qed.
Lemma yc_tt : forall k r, yc (repeat true k ++ r) = rep [S1; S1] k ++ yc r.
Proof. intros. apply bcells_tt. Qed.

(** ** Machine pieces *)

Lemma bsweep : forall n L R, Reach0 tm (cR StB L (rep [S1] n ++ R)) (cR StB (rep [S0] n ++ L) R).
Proof. apply sweepR. intros L R. rr 1. r0. Qed.

Lemma adwalk : forall n L R, Reach0 tm (cL StA (rep [S1; S1] n ++ L) R) (cL StA L (rep [S0; S1] n ++ R)).
Proof. apply sweepL. intros L R. rr 2. r0. Qed.

Lemma adwalkx : forall n L R, Reach0 tm (cL StA (rep [S1; S0] n ++ L) R) (cL StA L (rep [S1; S1] n ++ R)).
Proof. apply sweepL. intros L R. rr 2. r0. Qed.

Ltac tocR := match goal with |- Reach0 _ (?q, (?L, chd ?X, ctl ?X)) _ => change (q, (L, chd X, ctl X)) with (cR q L X) end.
Ltac tocL := match goal with |- Reach0 _ (?q, (ctl ?X, chd ?X, ?R)) _ => change (q, (ctl X, chd X, R)) with (cL q X R) end.

Lemma pairs1 : forall (a : Sym) k l, a :: rep [a] (k + k) ++ a :: l = rep [a; a] (S k) ++ l.
Proof.
  intros a k l. rewrite rep1_snoc, rep_pair. replace (S k + S k) with (S (S (k + k))) by lia. reflexivity.
Qed.

Lemma walk_a : forall k r v Y,
  Reach0 tm (cL StA (xc (repeat true k ++ false :: r) ++ S1 :: xc v) (S0 :: Y))
            (StB, (xc (repeat false k ++ true :: r) ++ S1 :: xc v, S0, Y)).
Proof.
  intros k r v Y. rewrite xc_tt, xc_ff. cbn [xc bcells flat_map]. fold (xc r).
  rewrite <- !app_assoc. cbn [app].
  rt (adwalkx k (S0 :: S0 :: xc r ++ S1 :: xc v) (S0 :: Y)).
  rr 1. rewrite rep_pair. tocR. rt (bsweep (k + k) (S1 :: S0 :: xc r ++ S1 :: xc v) (S0 :: Y)).
  rewrite <- rep_pair. r0.
Qed.

Lemma walk_c : forall k v1 Y,
  Reach0 tm (cL StA (xc (repeat true k) ++ S1 :: xc (true :: v1)) (S0 :: Y))
            (StB, (S1 :: xc v1, S0, rep [S1; S1] k ++ S1 :: S0 :: Y)).
Proof.
  intros k v1 Y. rewrite xc_all, ?xc_t, ?xc_f.
  rt (adwalkx k (S1 :: S1 :: S0 :: xc v1) (S0 :: Y)).
  rr 3. rewrite rep_pair, rep1_snoc, <- rep_pair. r0.
Qed.

Lemma walk_d : forall k v1 Y,
  Reach0 tm (cL StA (xc (repeat true k) ++ S1 :: xc (false :: v1)) (S0 :: Y))
            (StB, (xc (repeat false (S k)) ++ S1 :: xc v1, S0, Y)).
Proof.
  intros k v1 Y. rewrite xc_all, ?xc_t, ?xc_f.
  rt (adwalkx k (S1 :: S0 :: S0 :: xc v1) (S0 :: Y)).
  rr 3. change (StB, (S1 :: xc v1, S1, S1 :: rep [S1; S1] k ++ S0 :: Y))
    with (cR StB (S1 :: xc v1) (rep [S1; S1] (S k) ++ S0 :: Y)).
  rewrite rep_pair. rt (bsweep (S k + S k) (S1 :: xc v1) (S0 :: Y)).
  rewrite xc_none, rep_pair. r0.
Qed.

Lemma walk_b : forall k Y,
  Reach0 tm (cL StA (xc (repeat true k) ++ [S1]) (S0 :: Y))
            (StB, (xc (repeat false (S k)) ++ [S1], S0, Y)).
Proof.
  intros k Y. rewrite xc_all.
  rt (adwalkx k [S1] (S0 :: Y)).
  rr 3. change (StB, ([S1], S1, S1 :: rep [S1; S1] k ++ S0 :: Y))
    with (cR StB [S1] (rep [S1; S1] (S k) ++ S0 :: Y)).
  rewrite rep_pair. rt (bsweep (S k + S k) [S1] (S0 :: Y)).
  rewrite xc_none, rep_pair. r0.
Qed.

Lemma padx : forall q L h R, lift (q, (L ++ [S1; S0], h, R)) = lift (q, (L ++ [S1], h, R)).
Proof.
  intros. replace (L ++ [S1; S0]) with ((L ++ [S1]) ++ rep [S0] 1) by (rewrite <- app_assoc; reflexivity).
  apply lift_padL.
Qed.

Lemma walk_fires : forall u v Y t, 
  ((exists j r, u = true :: repeat true j ++ false :: r) \/
   (allt u = true /\ (v = [] \/ exists v1, v = false :: v1))) ->
  t = (StA, S0) \/ t = (StA, S1) \/ t = (StD, S0) \/ t = (StB, S1) ->
  Fires tm (cL StA (xc u ++ S1 :: xc v) (S0 :: Y)) t.
Proof.
  intros u v Y t Hg Ht. destruct Hg as [(j & r & ->) | (Hu & Hv)].
  - rewrite xc_t, xc_tt, xc_f. cbn [app]. rewrite <- ?app_assoc. cbn [app].
    destruct Ht as [-> | [-> | [-> | ->]]]; [| fire_find | fire_find |].
    all: change (S1 :: S0 :: rep [S1; S0] j ++ S0 :: S0 :: xc r ++ S1 :: xc v)
           with (rep [S1; S0] (S j) ++ S0 :: S0 :: xc r ++ S1 :: xc v).
    all: eapply fire_back; [apply adwalkx|]; fire_find.
  - destruct (allt_dec u) as [[_ Eu] | [Hu' _]]; [|congruence].
    rewrite Eu, xc_all. destruct Hv as [-> | (v1 & ->)]; rewrite ?xc_nil, ?xc_f;
    (eapply fire_back; [apply adwalkx|]); destruct Ht as [-> | [-> | [-> | ->]]]; fire_find.
Qed.

Definition F (L R : list Sym) : cconf := (StA, (L, S0, S0 :: R)).

Lemma usweep : forall n L R, Reach0 tm (F L (rep [S1] n ++ R)) (F (rep [S1] n ++ L) R).
Proof. apply (sweepFR tm F). intros L R. unfold F. rr 3. r0. Qed.

(** the right carry, up to the turn *)
Lemma armR_u : forall k r L M,
  Reach0 tm (F L (yc (repeat true k ++ false :: r) ++ M))
            (F (rep [S1] (k + k) ++ L) (S0 :: S1 :: yc r ++ M)).
Proof.
  intros k r L M. rewrite yc_tt, rep_pair. cbn [yc bcells flat_map]. fold (yc r).
  rewrite <- !app_assoc. cbn [app]. apply usweep.
Qed.

Lemma armR : forall k r L M,
  Reach1 tm (F L (yc (repeat true k ++ false :: r) ++ M))
            (cL StA L (S0 :: S1 :: yc (repeat false k ++ true :: r) ++ M)).
Proof.
  intros k r L M. eapply reach01; [apply armR_u|]. unfold F.
  rr 5. tocL. rewrite <- rep_pair. rt (adwalk k L (S0 :: S1 :: S1 :: S1 :: yc r ++ M)).
  rewrite yc_ff. unfold yc at 2. cbn [bcells flat_map]. fold (yc r).
  rewrite <- app_assoc. cbn [app]. fold (yc r).
  pose proof (rep_snoc [S0; S1] k (S1 :: S1 :: yc r ++ M)) as E. cbn [app] in E. rewrite E. r0.
Qed.

(** the overflow: the walk enters the left as D *)
Definition RO (w : nat) : list Sym := S1 :: rep [S0; S1] w ++ [S0; S1; S1].

Lemma armO : forall w L,
  Reach1 tm (F L (yc (repeat true w) ++ [S1])) (cL StD L (RO w)).
Proof.
  intros w L. unfold yc. rewrite bcells_alltrue, rep_pair.
  replace (rep [S1] (w + w) ++ [S1]) with (rep [S1] (S (w + w)) ++ [])
    by (rewrite app_nil_r, rep_comm; reflexivity).
  eapply reach01; [apply usweep|]. unfold F.
  rr 5. change (StA, (rep [S1] (w + w) ++ L, S1, [S0; S1; S1]))
    with (cL StA (S1 :: rep [S1] (w + w) ++ L) [S0; S1; S1]).
  rewrite <- rep1_snoc, <- rep_pair. rt (adwalk w (S1 :: L) [S0; S1; S1]). rr 1. r0.
Qed.

Lemma ovf_e : forall u1 w,
  Reach1 tm (cL StD (xc (true :: u1) ++ [S1]) (RO w))
            (StA, (S1 :: xc u1 ++ [S1], S0, S0 :: yc (repeat false (S w)) ++ [S1])).
Proof.
  intros u1 w. rewrite xc_t. unfold RO. rr 4. unfold yc. rewrite bcells_allfalse.
  rewrite rep_S_r, <- !app_assoc. r0.
Qed.

Lemma ovf_f : forall u1 w,
  Reach1 tm (cL StD (xc (false :: u1) ++ [S1]) (RO w))
            (StA, (S0 :: S0 :: S1 :: xc u1 ++ [S1], S0, S0 :: yc (repeat false w) ++ [S1])).
Proof.
  intros u1 w. rewrite xc_f. unfold RO.
  pose proof (rep_snoc [S0; S1] w [S1]) as E. cbn [app] in E. rewrite E. rr 6. unfold yc. rewrite bcells_allfalse. r0.
Qed.

Lemma ovf_g : forall w,
  Reach1 tm (cL StD [S1] (RO w)) (StA, ([S1], S0, S0 :: yc (repeat false (S w)) ++ [S1])).
Proof.
  intros w. unfold RO. rr 4. unfold yc. rewrite bcells_allfalse.
  rewrite rep_S_r, <- !app_assoc. r0.
Qed.

(** back to the next junction *)
Lemma close : forall L Z, Reach1 tm (StB, (L, S0, S1 :: Z)) (StA, (L, S0, S0 :: Z)).
Proof. intros L Z. rr 2. r0. Qed.

(** ** One macro step *)

Lemma macro : forall u v y, (allt y = true -> v = []) ->
  Reach1 tm (enc (u, v, y)) (enc (astep (u, v, y))).
Proof.
  intros u v y Hv. destruct (allt_dec y) as [[Hy Ey] | [Hy (k & r & Ey)]].
  - rewrite (Hv Hy). cbn [astep]. rewrite Hy. unfold enc at 1. rewrite Ey, ?repeat_length.
    change (StA, (xc u ++ S1 :: xc [], S0, S0 :: yc (repeat true (length y)) ++ [S1]))
      with (F (xc u ++ S1 :: xc []) (yc (repeat true (length y)) ++ [S1])).
    eapply reach10; [apply armO|].
    destruct u as [|[|] u1].
    + rewrite xc_nil. cbn [app]. apply reach1_0. unfold enc. rewrite !xc_nil. cbn [app]. apply ovf_g.
    + rewrite xc_nil.
      eapply reach0_trans; [apply reach1_0, ovf_e|]. unfold enc. rewrite xc_nil, xc_app, xc_t, xc_nil.
      cbn [app]. apply reach0_lift. symmetry. exact (padx _ (S1 :: xc u1) _ _).
    + rewrite xc_nil.
      eapply reach0_trans; [apply reach1_0, ovf_f|]. unfold enc. rewrite xc_f, xc_nil, xc_app, xc_t, xc_nil.
      cbn [app]. apply reach0_lift. symmetry. exact (padx _ (S0 :: S0 :: S1 :: xc u1) _ _).
  - cbn [astep]. rewrite Hy. unfold enc at 1. rewrite Ey.
    change (StA, (xc u ++ S1 :: xc v, S0, S0 :: yc (repeat true k ++ false :: r) ++ [S1]))
      with (F (xc u ++ S1 :: xc v) (yc (repeat true k ++ false :: r) ++ [S1])).
    eapply reach10; [apply armR|]. rewrite <- binc_int, <- Ey.
    destruct (allt_dec u) as [[Hu Eu] | [Hu (j & r' & Eu)]]; rewrite Hu.
    + rewrite Eu at 1. destruct v as [|[|] v1].
      * rewrite xc_nil. rt (walk_b (length u) (S1 :: yc (binc y) ++ [S1])).
        apply reach1_0, close.
      * rt (walk_c (length u) v1 (S1 :: yc (binc y) ++ [S1])).
        rewrite rep_pair, rep1_snoc. eapply reach1_0, reach10; [apply close|].
        unfold enc. rewrite xc_nil, yc_tt, rep_pair. cbn [app]. unfold yc at 2. cbn [bcells flat_map].
        fold (yc (binc y)). rewrite <- app_assoc. r0.
      * rt (walk_d (length u) v1 (S1 :: yc (binc y) ++ [S1])). apply reach1_0, close.
    + rewrite Eu. rt (walk_a j r' v (S1 :: yc (binc y) ++ [S1])). rewrite <- binc_int.
      apply reach1_0, close.
Qed.

(** ** Fire witnesses *)

Lemma to_walk : forall u v y, allt y = false ->
  Reach0 tm (enc (u, v, y)) (cL StA (xc u ++ S1 :: xc v) (S0 :: S1 :: yc (binc y) ++ [S1])).
Proof.
  intros u v y Hy. destruct (allt_dec y) as [[H _] | [_ (k & r & ->)]]; [congruence|].
  rewrite binc_int. apply reach1_0, armR.
Qed.

Lemma fires_turn : forall u v y t, allt y = false ->
  t = (StC, S0) \/ t = (StC, S1) -> Fires tm (enc (u, v, y)) t.
Proof.
  intros u v y t Hy Ht. destruct (allt_dec y) as [[H _] | [_ (k & r & ->)]]; [congruence|].
  eapply fire_back; [apply armR_u|]. unfold F. destruct Ht as [-> | ->]; fire_find.
Qed.

Lemma good_fires : forall s, good s -> forall t, t <> (StD, S1) -> Fires tm (enc s) t.
Proof.
  intros [[u v] y] (Hy & Hg) [q a] Ht.
  destruct q, a;
  first [ apply fires_here; reflexivity
        | unfold enc; eapply fire_back; [rr 1; apply reach0_refl|]; apply fires_here; reflexivity
        | apply fires_turn; [exact Hy | tauto]
        | eapply fire_back; [apply (to_walk u v y Hy)|]; apply walk_fires; [exact Hg | tauto]
        | congruence ].
Qed.

Lemma good2_fires : forall s, good2 s -> Fires tm (enc s) (StD, S1).
Proof.
  intros [[u v] y] Hy. unfold good2 in Hy.
  destruct (allt_dec y) as [[H E] | [H (k & r & E)]].
  - remember (length y) as w eqn:Ew. clear Ew. subst y.
    destruct w as [|w]; [discriminate|]. unfold enc.
    change (StA, (xc u ++ S1 :: xc v, S0, S0 :: yc (repeat true (S w)) ++ [S1]))
      with (F (xc u ++ S1 :: xc v) (yc (repeat true (S w)) ++ [S1])).
    unfold yc. rewrite bcells_alltrue, rep_pair.
    replace (rep [S1] (S w + S w) ++ [S1]) with (rep [S1] (S (S w + S w)) ++ [])
      by (rewrite app_nil_r, rep_comm; reflexivity).
    eapply fire_back; [apply usweep|]. unfold F. rewrite Nat.add_succ_r. fire_find.
  - subst y. destruct k as [|k]; [discriminate|]. unfold enc.
    change (StA, (xc u ++ S1 :: xc v, S0, S0 :: yc (repeat true (S k) ++ false :: r) ++ [S1]))
      with (F (xc u ++ S1 :: xc v) (yc (repeat true (S k) ++ false :: r) ++ [S1])).
    eapply fire_back; [apply armR_u|]. unfold F. rewrite Nat.add_succ_r. fire_find.
Qed.

(** ** The board: from the era start at step 79,674 *)

Definition s0 : ast := ([], [], [false; true; true; false; false; true; true; true; false; false; false; false;
                                 true; true; false; false; false; false; false; false; false; false; false; false]).

Lemma Inv_s0 : Inv s0.
Proof. apply Inv_start; reflexivity. Qed.

Theorem nqhtr_1RB1LD_0RC0RB_1LC0LA_1LA0LA : NeverQuasiHaltsTr tm_1RB1LD_0RC0RB_1LC0LA_1LA0LA.
Proof.
  apply (two_level_neverqhtr _ enc macro) with (s0 := s0) (b := 79674).
  2: exact Inv_s0.
  - intros [q a]. destruct (st_eqb q StD && sym_eqb a S1) eqn:E.
    + right. destruct q, a; try discriminate. exact good2_fires.
    + left. intros s Hs. apply good_fires; [exact Hs|]. destruct q, a; try discriminate; congruence.
  - apply boot_ok. vm_compute. reflexivity.
Qed.
