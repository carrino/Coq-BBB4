(** * LP_1RB1LD_1RC0RB_1LA1RC_1LA0LA (SCOPING_INSTR 7.4.LE11)

    The two-level binary mirror counter of [Counters.TwoLevelTr].  The
    anchor is [B [0]] at the junction; the right side is [y] (LSB first,
    digits [10] / [11]) and a [11] marker.  One macro step is the C sweep
    right over the 1s, the A/D walk back left (A keeps a 1 and goes on, D
    flips its cell, A stops at a 0 and writes 1) and the B sweep right
    clearing 1s to the next junction ([macro]: [armR] / [armO], then
    [walk_a] .. [walk_d] or [ovf_e] .. [ovf_g]).  Every instruction fires
    in the "good" steps of [TwoLevelTr.good] ([good_fires]).

    Hand-stated, kernel-checked.  Axiom footprint: [functional_extensionality_dep]. *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr LoopMirrorTr TwoLevelTr.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Definition tm_1RB1LD_1RC0RB_1LA1RC_1LA0LA : TM := fun q s => match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB) | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DR StC) | StB, S1 => Some (mkTrans S0 DR StB)
  | StC, S0 => Some (mkTrans S1 DL StA) | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StA) | StD, S1 => Some (mkTrans S0 DL StA)
  end.
Local Notation tm := (tm_wrap_trs tm_1RB1LD_1RC0RB_1LA1RC_1LA0LA []).

(** ** Cells *)

Definition yc (y : list bool) : list Sym := bcells [S1; S0] [S1; S1] y.

Definition enc (s : ast) : cconf :=
  let '(u, v, y) := s in (StB, (xc u ++ S1 :: xc v, S0, yc y ++ [S1; S1])).

Lemma yc_ff : forall k r, yc (repeat false k ++ r) = rep [S1; S0] k ++ yc r.
Proof. intros. apply bcells_ff. Qed.
Lemma yc_tt : forall k r, yc (repeat true k ++ r) = rep [S1; S1] k ++ yc r.
Proof. intros. apply bcells_tt. Qed.

(** ** Machine pieces *)

Lemma csweep : forall n L R, Reach0 tm (cR StC L (rep [S1] n ++ R)) (cR StC (rep [S1] n ++ L) R).
Proof. apply sweepR. intros L R. rr 1. r0. Qed.

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

(** the right carry, up to the C turn *)
Lemma armR_c : forall k r L M,
  Reach1 tm (StB, (L, S0, yc (repeat true k ++ false :: r) ++ M))
            (cR StC (rep [S1] (S (k + k)) ++ S1 :: L) (S0 :: yc r ++ M)).
Proof.
  intros k r L M. rewrite yc_tt, rep_pair. cbn [yc bcells flat_map]. fold (yc r).
  rr 1. rewrite <- !app_assoc. cbn [app]. rewrite rep1_snoc, rep1_fold. tocR.
  rt (csweep (S (k + k)) (S1 :: L) (S0 :: yc r ++ M)). r0.
Qed.

(** the right carry: [y] incremented, A on the left's first cell *)
Lemma armR : forall k r L M,
  Reach1 tm (StB, (L, S0, yc (repeat true k ++ false :: r) ++ M))
            (cL StA L (S0 :: yc (repeat false k ++ true :: r) ++ M)).
Proof.
  intros k r L M. eapply reach10; [apply armR_c|].
  rr 1. change (StA, (rep [S1] (k + k) ++ S1 :: L, S1, S1 :: yc r ++ M))
    with (cL StA (S1 :: rep [S1] (k + k) ++ S1 :: L) (S1 :: yc r ++ M)).
  rewrite pairs1. rt (adwalk (S k) L (S1 :: yc r ++ M)).
  cbn [rep app]. rewrite (rep_shift S1 S0 k), yc_ff. unfold yc at 2. cbn [bcells flat_map]. fold (yc r).
  rewrite <- app_assoc. r0.
Qed.

Lemma yc_all : forall w, yc (repeat true w) ++ [S1; S1] = rep [S1] (S w + S w).
Proof.
  intros w. unfold yc. rewrite bcells_alltrue. rewrite rep_comm, <- rep_pair. reflexivity.
Qed.

(** the overflow: [y] all 1s, the walk enters the left as D *)
Lemma armO : forall w L,
  Reach1 tm (StB, (L, S0, yc (repeat true w) ++ [S1; S1]))
            (cL StD L (S1 :: rep [S0; S1] (S w) ++ [S1])).
Proof.
  intros w L. rewrite yc_all.
  rr 1. change (StC, (S1 :: L, S1, rep [S1] (w + S w))) with (cR StC (S1 :: L) (rep [S1] (S w + S w))).
  pose proof (csweep (S w + S w) (S1 :: L) []) as H. rewrite app_nil_r in H. rt H.
  rr 1. change (StA, (rep [S1] (w + S w) ++ S1 :: L, S1, [S1]))
    with (cL StA (rep [S1] (S w + S w) ++ S1 :: L) [S1]).
  rewrite <- rep_pair. rt (adwalk (S w) (S1 :: L) [S1]). rr 1. r0.
Qed.

(** the left walks after a right carry (A on the left's first cell) *)
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

(** after the overflow: the walk enters the left one cell out of step *)
Definition RO (w : nat) : list Sym := S1 :: rep [S0; S1] (S w) ++ [S1].

Lemma RO_yc : forall w, RO w = yc (repeat false (S w)) ++ [S1; S1].
Proof. intros w. unfold RO, yc. rewrite bcells_allfalse, rep_shift. reflexivity. Qed.

Lemma RO_yc' : forall w, rep [S0; S1] w ++ [S1] = S0 :: yc (repeat false w) ++ [S1; S1] \/ True.
Proof. right. exact I. Qed.

Lemma ovf_e : forall u1 w,
  Reach0 tm (cL StD (xc (true :: u1) ++ [S1]) (RO w)) (StB, (S1 :: xc u1 ++ [S1], S0, RO w)).
Proof. intros u1 w. rewrite xc_t. rr 2. r0. Qed.

Lemma ovf_f : forall u1 w,
  Reach0 tm (cL StD (xc (false :: u1) ++ [S1]) (RO w))
            (StB, (S0 :: S0 :: S1 :: xc u1 ++ [S1], S0, yc (repeat false w) ++ [S1; S1])).
Proof.
  intros u1 w. rewrite xc_f. unfold RO. rr 4. unfold yc. rewrite bcells_allfalse.
  rewrite rep_shift. r0.
Qed.

Lemma ovf_g : forall w, Reach0 tm (cL StD [S1] (RO w)) (StB, ([S1], S0, RO w)).
Proof. intros w. rr 2. r0. Qed.

(** ** One macro step *)

Lemma padx : forall q L h R, lift (q, (L ++ [S1; S0], h, R)) = lift (q, (L ++ [S1], h, R)).
Proof.
  intros. replace (L ++ [S1; S0]) with ((L ++ [S1]) ++ rep [S0] 1) by (rewrite <- app_assoc; reflexivity).
  apply lift_padL.
Qed.

Lemma macro : forall u v y, (allt y = true -> v = []) ->
  Reach1 tm (enc (u, v, y)) (enc (astep (u, v, y))).
Proof.
  intros u v y Hv. destruct (allt_dec y) as [[Hy Ey] | [Hy (k & r & Ey)]].
  - rewrite (Hv Hy). cbn [astep]. rewrite Hy. unfold enc at 1. rewrite Ey, ?repeat_length.
    eapply reach10; [apply armO|]. fold (RO (length y)).
    destruct u as [|[|] u1].
    + rewrite xc_nil. cbn [app]. rt (ovf_g (length y)). unfold enc. rewrite RO_yc. r0.
    + rt (ovf_e u1 (length y)). unfold enc. rewrite RO_yc, xc_nil, xc_app, xc_t, xc_nil.
      cbn [app]. apply reach0_lift. symmetry. exact (padx _ (S1 :: xc u1) _ _).
    + rt (ovf_f u1 (length y)). unfold enc. rewrite xc_f, xc_nil, xc_app, xc_t, xc_nil.
      cbn [app]. apply reach0_lift. symmetry. exact (padx _ (S0 :: S0 :: S1 :: xc u1) _ _).
  - cbn [astep]. rewrite Hy. unfold enc at 1. rewrite Ey.
    eapply reach10; [apply armR|]. rewrite <- binc_int, <- Ey.
    destruct (allt_dec u) as [[Hu Eu] | [Hu (j & r' & Eu)]]; rewrite Hu.
    + rewrite Eu at 1. destruct v as [|[|] v1].
      * rewrite xc_nil. rt (walk_b (length u) (yc (binc y) ++ [S1; S1])). unfold enc. rewrite xc_nil. r0.
      * rt (walk_c (length u) v1 (yc (binc y) ++ [S1; S1])). unfold enc.
        rewrite xc_nil, yc_tt. cbn [app]. unfold yc at 2. cbn [bcells flat_map]. fold (yc (binc y)).
        rewrite <- app_assoc. r0.
      * rt (walk_d (length u) v1 (yc (binc y) ++ [S1; S1])). unfold enc. r0.
    + rewrite Eu. rt (walk_a j r' v (yc (binc y) ++ [S1; S1])). rewrite <- binc_int. unfold enc. r0.
Qed.

Lemma to_walk : forall u v y, allt y = false ->
  Reach0 tm (enc (u, v, y)) (cL StA (xc u ++ S1 :: xc v) (S0 :: yc (binc y) ++ [S1; S1])).
Proof.
  intros u v y Hy. destruct (allt_dec y) as [[H _] | [_ (k & r & ->)]]; [congruence|].
  rewrite binc_int. apply reach1_0, armR.
Qed.

Lemma fires_right : forall u v y t, allt y = false ->
  t = (StC, S0) \/ t = (StA, S1) \/ t = (StD, S1) -> Fires tm (enc (u, v, y)) t.
Proof.
  intros u v y t Hy Ht. destruct (allt_dec y) as [[H _] | [_ (k & r & ->)]]; [congruence|].
  unfold enc. eapply fire_back; [apply reach1_0, armR_c|].
  destruct Ht as [-> | [-> | ->]]; [fire_find | fire_find | destruct k; fire_find].
Qed.

Lemma fires_c1 : forall u v y, Fires tm (enc (u, v, y)) (StC, S1).
Proof.
  intros u v y. unfold enc. eapply fire_back; [rr 1; apply reach0_refl|].
  destruct y as [|[|] y]; cbn; apply fires_here; reflexivity.
Qed.

Lemma walk_fires : forall u v Y t, 
  ((exists j r, u = true :: repeat true j ++ false :: r) \/
   (allt u = true /\ (v = [] \/ exists v1, v = false :: v1))) ->
  t = (StA, S0) \/ t = (StD, S0) \/ t = (StB, S1) ->
  Fires tm (cL StA (xc u ++ S1 :: xc v) (S0 :: Y)) t.
Proof.
  intros u v Y t Hg Ht. destruct Hg as [(j & r & ->) | (Hu & Hv)].
  - rewrite xc_t, xc_tt, xc_f. cbn [app]. rewrite <- ?app_assoc. cbn [app].
    destruct Ht as [-> | [-> | ->]]; [| fire_find |].
    all: change (S1 :: S0 :: rep [S1; S0] j ++ S0 :: S0 :: xc r ++ S1 :: xc v)
           with (rep [S1; S0] (S j) ++ S0 :: S0 :: xc r ++ S1 :: xc v).
    all: eapply fire_back; [apply adwalkx|]; fire_find.
  - destruct (allt_dec u) as [[_ Eu] | [Hu' _]]; [|congruence].
    rewrite Eu, xc_all. destruct Hv as [-> | (v1 & ->)]; rewrite ?xc_nil, ?xc_f;
    (eapply fire_back; [apply adwalkx|]); destruct Ht as [-> | [-> | ->]]; fire_find.
Qed.

Lemma good_fires : forall s, good s -> forall t, Fires tm (enc s) t.
Proof.
  intros [[u v] y] (Hy & Hg) [q a].
  destruct q, a;
  first [ apply fires_here; reflexivity
        | apply fires_c1
        | apply fires_right; [exact Hy | tauto]
        | eapply fire_back; [apply (to_walk u v y Hy)|]; apply walk_fires; [exact Hg | tauto] ].
Qed.


(** ** The board: from the era start at step 1,045 *)

Definition s0 : ast := ([], [], [false; true; false; true; false; false; true; true; false; false; false; false]).

Lemma Inv_s0 : Inv s0.
Proof. apply Inv_start; reflexivity. Qed.

Theorem nqhtr_1RB1LD_1RC0RB_1LA1RC_1LA0LA : NeverQuasiHaltsTr tm_1RB1LD_1RC0RB_1LA1RC_1LA0LA.
Proof.
  apply (two_level_neverqhtr _ enc macro (fun t => or_introl (fun s Hs => good_fires s Hs t)) s0 Inv_s0 1045).
  apply boot_ok. vm_compute. reflexivity.
Qed.
