(** * IRules.RulesBlkPfx: prefix (near-head) block rules, remainder
    binding drains, and residue-lattice runs (Phase 2: v6 [rulepfx] +
    [rmdok], v7 [rulerunm]).

    A fork of [RulesBlk] for the v6/v7 certificate features:

    - [rulepfx]: a rule side flagged as a PREFIX matches only its
      declared near-head runs of the configuration; the untouched rest
      is spliced back.  The rule's own validation treats its prefix
      sides as opaque sentinels (engine: [EngineKS.beng_stepS]), so the
      validated [Reach] holds for EVERY continuation of those sides --
      the semantics [brule_semP] quantifies over suffix cell streams.
      A NON-prefix rule side must match exactly and must never match a
      sentinel side of the current replay (the [verify.c:3215-3218]
      guard): "exact" on a truncated side is not exact on its
      extension.
    - [rmdok] (v6+): the binding drain may leave a constant remainder
      [rmd = (e - lb) mod d]; only [find_bindingP] (UNTRUSTED) changes.
      Soundness never reads the binding search: the per-decrement
      survival re-check in [appBlkPfx_side] already validates ANY
      [Rex], and the drained run's terminal constant [lb + rmd - d]
      is produced by the same uniform [eaddmul] (the run's
      coefficients are divisible by [d], so the floor-divided [Rex]
      collapses it to a constant).
    - [rulerunm] (v7): a var run confined to a residue lattice
      [md*w + rs] ([BVm]).  Its start/end/lb encodings are scaled and
      offset; matching a configuration count requires the lattice
      residue guard (checked in the applier, so the denotation lemmas
      get exact division from the inversion).

    [RulesBlk] (Phase 1) is untouched; the applier, replay driver and
    rule validation are re-derived here against the suffix-extended
    semantics [EngineKS.bsemX]. *)

From Coq Require Import Arith ZArith Lia Bool List Setoid.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules RulesK EngineK
     RulesBlk EngineKS.
Import ListNotations.
Open Scope Z_scope.

(** ** Prefix block rules and their denotation *)

(** Run-count shapes: constant, plain variable (delta, lower bound),
    residue-lattice variable (delta, lower bound, modulus, residue). *)
Inductive BRCP : Set :=
  | BC (v : Z)
  | BV (d lb : Z)
  | BVm (d lb md rs : Z).

Definition BRRunP : Set := (BSym * BRCP)%type.

Record BRuleP : Set := mkBRuleP {
  brp_st : St;
  brp_hs : Sym;
  brp_L : list BRRunP;
  brp_R : list BRRunP;
  brp_pfx : bool * bool
}.

(** The lattice count expression [md * w + rs]. *)
Definition elatt (md rs : Z) (vid : nat) : Expr :=
  eaddc (eaddmul (econst 0) md (evar vid)) rs.

Lemma eval_elatt : forall nu md rs vid,
  eval nu (elatt md rs vid) = md * nu vid + rs.
Proof.
  intros. unfold elatt.
  rewrite eval_eaddc, eval_eaddmul, eval_econst, eval_evar. lia.
Qed.

Fixpoint brstartP (vid : nat) (rr : list BRRunP) : list BRun :=
  match rr with
  | [] => []
  | (s, BC v) :: t => (s, econst v) :: brstartP vid t
  | (s, BV _ _) :: t => (s, evar vid) :: brstartP (S vid) t
  | (s, BVm _ _ md rs) :: t => (s, elatt md rs vid) :: brstartP (S vid) t
  end.

Fixpoint brendP (vid : nat) (rr : list BRRunP) : list BRun :=
  match rr with
  | [] => []
  | (s, BC v) :: t => (s, econst v) :: brendP vid t
  | (s, BV d _) :: t => (s, eaddc (evar vid) d) :: brendP (S vid) t
  | (s, BVm d _ md rs) :: t =>
      (s, eaddc (elatt md rs vid) d) :: brendP (S vid) t
  end.

Fixpoint brlbsP (rr : list BRRunP) : list Z :=
  match rr with
  | [] => []
  | (_, BC _) :: t => brlbsP t
  | (_, BV _ lb) :: t => lb :: brlbsP t
  | (_, BVm _ lb md rs) :: t => ((lb - rs) / md) :: brlbsP t
  end.

Definition brule_lbsP (r : BRuleP) : list Z :=
  brlbsP (brp_L r) ++ brlbsP (brp_R r).

Definition brulep_start_cfg (r : BRuleP) : BCfg :=
  mkBCfg (brp_st r) (brp_hs r)
         (brstartP 0 (brp_L r))
         (brstartP (length (brlbsP (brp_L r))) (brp_R r)).

Definition brulep_end_cfg (r : BRuleP) : BCfg :=
  mkBCfg (brp_st r) (brp_hs r)
         (brendP 0 (brp_L r))
         (brendP (length (brlbsP (brp_L r))) (brp_R r)).

(** The semantic content of a validated prefix rule: the [Reach] holds
    for EVERY suffix continuation of its prefix sides (and only the
    empty continuation of its exact sides). *)
Definition brule_semP (tm : TM) (tbl : BTbl) (r : BRuleP) (F : list Tr)
  : Prop :=
  forall u : nat -> Z, bge (brule_lbsP r) u ->
  forall YL YR : list Sym,
  (fst (brp_pfx r) = false -> YL = []) ->
  (snd (brp_pfx r) = false -> YR = []) ->
  exists n, (1 <= n)%nat /\
    Reach tm F n (bsemX tbl u (brulep_start_cfg r) YL YR)
                 (bsemX tbl u (brulep_end_cfg r) YL YR).

(** ** Lattice arithmetic helpers *)

Lemma add_mod0 : forall a b m, m <> 0 ->
  a mod m = 0 -> b mod m = 0 -> (a + b) mod m = 0.
Proof.
  intros a b m Hm Ha Hb.
  rewrite Z.add_mod, Ha, Hb by exact Hm.
  simpl. apply Z.mod_0_l; exact Hm.
Qed.

Lemma mul_mod0_l : forall a b m, m <> 0 ->
  a mod m = 0 -> (a * b) mod m = 0.
Proof.
  intros a b m Hm Ha.
  rewrite Z.mul_mod, Ha, Z.mul_0_l by exact Hm.
  apply Z.mod_0_l; exact Hm.
Qed.

Lemma dot_mod0 : forall md cf nu i, md <> 0 ->
  forallb (fun c => (c mod md) =? 0) cf = true ->
  (dot cf nu i) mod md = 0.
Proof.
  intros md cf. induction cf as [|c t IH]; intros nu i Hm H; simpl.
  - apply Z.mod_0_l; exact Hm.
  - simpl in H. apply andb_prop in H as [Hc Ht].
    apply Z.eqb_eq in Hc.
    apply add_mod0; [exact Hm | | apply IH; assumption].
    apply mul_mod0_l; assumption.
Qed.

Lemma latt_val_mod0 : forall md rs d e nu j, md <> 0 ->
  (e_c0 e - rs) mod md = 0 -> d mod md = 0 ->
  forallb (fun c => (c mod md) =? 0) (e_cf e) = true ->
  (eval nu e + d * j - rs) mod md = 0.
Proof.
  intros md rs d e nu j Hm Hc0 Hd Hcf.
  unfold eval.
  replace (e_c0 e + dot (e_cf e) nu 0 + d * j - rs)
    with ((e_c0 e - rs) + (dot (e_cf e) nu 0 + d * j)) by lia.
  apply add_mod0; [exact Hm | exact Hc0 |].
  apply add_mod0; [exact Hm | apply dot_mod0; assumption |].
  apply mul_mod0_l; assumption.
Qed.

Lemma latt_div_eval : forall md rs x, md <> 0 -> (x - rs) mod md = 0 ->
  md * ((x - rs) / md) + rs = x.
Proof.
  intros md rs x Hm Hmod.
  pose proof (proj2 (Z.div_exact (x - rs) md Hm) Hmod). lia.
Qed.

(** The lattice guard: structural certificate facts plus the
    configuration count's residue precondition (verify.c:3245-3254,
    1023-1056), checked in the applier so the denotation lemmas can
    read exact division off the inversion. *)
Definition latt_ok (md rs d lb : Z) (e : Expr) : bool :=
  (2 <=? md) && (0 <=? rs) && (rs <? md) &&
  ((d mod md) =? 0) && (((lb - rs) mod md) =? 0) &&
  (((e_c0 e - rs) mod md) =? 0) &&
  forallb (fun c => (c mod md) =? 0) (e_cf e).

Lemma latt_ok_facts : forall md rs d lb e, latt_ok md rs d lb e = true ->
  0 < md /\ d mod md = 0 /\ (lb - rs) mod md = 0 /\
  (forall nu j, (eval nu e + d * j - rs) mod md = 0).
Proof.
  intros md rs d lb e H. unfold latt_ok in H.
  apply andb_prop in H as [H Hcf].
  apply andb_prop in H as [H Hc0].
  apply andb_prop in H as [H Hlb].
  apply andb_prop in H as [H Hd].
  apply andb_prop in H as [H _].
  apply andb_prop in H as [Hmd _].
  apply Z.leb_le in Hmd.
  apply Z.eqb_eq in Hd, Hlb, Hc0.
  split; [lia|]. split; [exact Hd|]. split; [exact Hlb|].
  intros nu j. apply latt_val_mod0; try assumption. lia.
Qed.

(** ** The per-run values along the drain *)

Fixpoint bvvalsP (nu : nat -> Z) (j : Z) (rr : list BRRunP)
    (mr : list BRun) : list Z :=
  match rr, mr with
  | (_, BC _) :: rt, _ :: mt => bvvalsP nu j rt mt
  | (_, BV d _) :: rt, (_, e) :: mt =>
      (eval nu e + d * j) :: bvvalsP nu j rt mt
  | (_, BVm d _ md rs) :: rt, (_, e) :: mt =>
      ((eval nu e + d * j - rs) / md) :: bvvalsP nu j rt mt
  | _, _ => []
  end.

(** ** The prefix per-side rewrite *)

Fixpoint appBlkPfx_side (pfx : bool) (lo : list Z) (Rex : Expr)
    (rr : list BRRunP) (mr : list BRun) : option (list BRun) :=
  match rr, mr with
  | [], mt => if pfx then Some mt
              else match mt with [] => Some [] | _ :: _ => None end
  | (s, BC v) :: rt, (s', e) :: mt =>
      if Nat.eqb s s' && eeqb e (econst v)
      then option_map (cons (s', e)) (appBlkPfx_side pfx lo Rex rt mt)
      else None
  | (s, BV d lb) :: rt, (s', e) :: mt =>
      if Nat.eqb s s' && expr_ge lo e lb then
        if 0 <=? d then
          option_map (cons (s', eaddmul e d Rex))
                     (appBlkPfx_side pfx lo Rex rt mt)
        else if expr_ge lo (eaddmul e d Rex) (lb + d) then
          if eeqb (eaddmul e d Rex) (econst 0)
          then appBlkPfx_side pfx lo Rex rt mt
          else option_map (cons (s', eaddmul e d Rex))
                          (appBlkPfx_side pfx lo Rex rt mt)
        else None
      else None
  | (s, BVm d lb md rs) :: rt, (s', e) :: mt =>
      if Nat.eqb s s' && latt_ok md rs d lb e && expr_ge lo e lb then
        if 0 <=? d then
          option_map (cons (s', eaddmul e d Rex))
                     (appBlkPfx_side pfx lo Rex rt mt)
        else if expr_ge lo (eaddmul e d Rex) (lb + d) then
          if eeqb (eaddmul e d Rex) (econst 0)
          then appBlkPfx_side pfx lo Rex rt mt
          else option_map (cons (s', eaddmul e d Rex))
                          (appBlkPfx_side pfx lo Rex rt mt)
        else None
      else None
  | _ :: _, [] => None
  end.

(** ** Inversion *)

Lemma appBlkP_side_cons_inv : forall pfx lo Rex s rc rt s' e mt out,
  appBlkPfx_side pfx lo Rex ((s, rc) :: rt) ((s', e) :: mt) = Some out ->
  s = s' /\
  match rc with
  | BC v =>
      eeqb e (econst v) = true /\
      exists o, appBlkPfx_side pfx lo Rex rt mt = Some o /\ out = (s', e) :: o
  | BV d lb =>
      expr_ge lo e lb = true /\
      exists o, appBlkPfx_side pfx lo Rex rt mt = Some o /\
      ((0 <= d /\ out = (s', eaddmul e d Rex) :: o) \/
       (d < 0 /\ expr_ge lo (eaddmul e d Rex) (lb + d) = true /\
        ((eeqb (eaddmul e d Rex) (econst 0) = true /\ out = o) \/
         (eeqb (eaddmul e d Rex) (econst 0) = false /\
          out = (s', eaddmul e d Rex) :: o))))
  | BVm d lb md rs =>
      latt_ok md rs d lb e = true /\
      expr_ge lo e lb = true /\
      exists o, appBlkPfx_side pfx lo Rex rt mt = Some o /\
      ((0 <= d /\ out = (s', eaddmul e d Rex) :: o) \/
       (d < 0 /\ expr_ge lo (eaddmul e d Rex) (lb + d) = true /\
        ((eeqb (eaddmul e d Rex) (econst 0) = true /\ out = o) \/
         (eeqb (eaddmul e d Rex) (econst 0) = false /\
          out = (s', eaddmul e d Rex) :: o))))
  end.
Proof.
  intros pfx lo Rex s rc rt s' e mt out H.
  destruct rc as [v | d lb | d lb md rs]; cbn [appBlkPfx_side] in H.
  - destruct (Nat.eqb s s') eqn:Hs; cbn beta iota in H; [|discriminate].
    apply Nat.eqb_eq in Hs.
    destruct (eeqb e (econst v)) eqn:He; cbn beta iota in H; [|discriminate].
    destruct (appBlkPfx_side pfx lo Rex rt mt) as [o|] eqn:Ha;
      cbn beta iota in H; [|discriminate].
    injection H as <-. split; [auto|]. split; [auto|]. eauto.
  - destruct (Nat.eqb s s') eqn:Hs; cbn beta iota in H; [|discriminate].
    apply Nat.eqb_eq in Hs.
    destruct (expr_ge lo e lb) eqn:Hge; cbn beta iota in H; [|discriminate].
    split; [auto|]. split; [auto|].
    destruct (0 <=? d) eqn:Hd.
    + apply Z.leb_le in Hd.
      destruct (appBlkPfx_side pfx lo Rex rt mt) as [o|] eqn:Ha;
        cbn beta iota in H; [|discriminate].
      injection H as <-. exists o. split; [auto|]. left. auto.
    + apply Z.leb_gt in Hd.
      destruct (expr_ge lo (eaddmul e d Rex) (lb + d)) eqn:Hsv;
        cbn beta iota in H; [|discriminate].
      destruct (eeqb (eaddmul e d Rex) (econst 0)) eqn:Hz;
        cbn beta iota in H.
      * exists out. split; [auto|]. right. split; [lia|]. split; [auto|].
        left. auto.
      * destruct (appBlkPfx_side pfx lo Rex rt mt) as [o|] eqn:Ha;
          cbn beta iota in H; [|discriminate].
        injection H as <-. exists o. split; [auto|].
        right. split; [lia|]. split; [auto|]. right. auto.
  - destruct (Nat.eqb s s') eqn:Hs; cbn beta iota in H; [|discriminate].
    apply Nat.eqb_eq in Hs.
    destruct (latt_ok md rs d lb e) eqn:Hlat; cbn beta iota in H;
      [|discriminate].
    destruct (expr_ge lo e lb) eqn:Hge; cbn beta iota in H; [|discriminate].
    split; [auto|]. split; [auto|]. split; [auto|].
    destruct (0 <=? d) eqn:Hd.
    + apply Z.leb_le in Hd.
      destruct (appBlkPfx_side pfx lo Rex rt mt) as [o|] eqn:Ha;
        cbn beta iota in H; [|discriminate].
      injection H as <-. exists o. split; [auto|]. left. auto.
    + apply Z.leb_gt in Hd.
      destruct (expr_ge lo (eaddmul e d Rex) (lb + d)) eqn:Hsv;
        cbn beta iota in H; [|discriminate].
      destruct (eeqb (eaddmul e d Rex) (econst 0)) eqn:Hz;
        cbn beta iota in H.
      * exists out. split; [auto|]. right. split; [lia|]. split; [auto|].
        left. auto.
      * destruct (appBlkPfx_side pfx lo Rex rt mt) as [o|] eqn:Ha;
          cbn beta iota in H; [|discriminate].
        injection H as <-. exists o. split; [auto|].
        right. split; [lia|]. split; [auto|]. right. auto.
Qed.

(** ** The prefix decomposition: a prefix application is an exact
    application on the matched near-head runs plus a spliced rest *)

Lemma appBlkPfx_decomp : forall pfx lo Rex rr mr out,
  appBlkPfx_side pfx lo Rex rr mr = Some out ->
  exists m1 rest o1,
    mr = m1 ++ rest /\ out = o1 ++ rest /\
    appBlkPfx_side false lo Rex rr m1 = Some o1 /\
    (pfx = false -> rest = []).
Proof.
  intros pfx lo Rex rr. induction rr as [|[s rc] rt IH]; intros mr out H.
  - cbn [appBlkPfx_side] in H. destruct pfx.
    + injection H as <-. exists [], mr, []. cbn.
      split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. discriminate.
    + destruct mr as [|x mt]; [|discriminate].
      injection H as <-. exists [], [], []. cbn.
      split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. reflexivity.
  - destruct mr as [|[s' e] mt]; [destruct rc; cbn in H; discriminate|].
    destruct (appBlkP_side_cons_inv _ _ _ _ _ _ _ _ _ _ H) as [Hs Hrest].
    subst s'.
    destruct rc as [v | d lb | d lb md rs].
    + destruct Hrest as (He & o & Ha & ->).
      destruct (IH mt o Ha) as (m1 & rest & o1 & Hm & Ho & Hex & Hnil).
      exists ((s, e) :: m1), rest, ((s, e) :: o1).
      subst mt o. split; [reflexivity|]. split; [reflexivity|]. split.
      * cbn [appBlkPfx_side]. rewrite Nat.eqb_refl, He. cbn.
        rewrite Hex. reflexivity.
      * exact Hnil.
    + destruct Hrest as (Hge & o & Ha & Hout).
      destruct (IH mt o Ha) as (m1 & rest & o1 & Hm & Ho & Hex & Hnil).
      subst mt.
      assert (Hrun : appBlkPfx_side false lo Rex
                       (((s, BV d lb) : BRRunP) :: rt)
                       ((s, e) :: m1) =
                     match (if (0 <=? d) then false else
                            eeqb (eaddmul e d Rex) (econst 0)) with
                     | true => Some o1
                     | false => Some ((s, eaddmul e d Rex) :: o1)
                     end).
      { cbn [appBlkPfx_side]. rewrite Nat.eqb_refl, Hge. cbn [andb].
        destruct (0 <=? d) eqn:Hd.
        - rewrite Hex. reflexivity.
        - destruct Hout as [(Hd' & _) | (_ & Hsv & Hz)];
            [apply Z.leb_gt in Hd; lia|].
          rewrite Hsv.
          destruct Hz as [(Hz & _) | (Hz & _)]; rewrite Hz;
            [exact Hex | rewrite Hex; reflexivity]. }
      destruct Hout as [(Hd & ->) | (Hd0 & Hsv & Hz)].
      * exists ((s, e) :: m1), rest, ((s, eaddmul e d Rex) :: o1).
        subst o. split; [reflexivity|]. split; [reflexivity|].
        split; [|exact Hnil].
        rewrite Hrun.
        destruct (0 <=? d) eqn:Hdb; [reflexivity | apply Z.leb_gt in Hdb; lia].
      * assert (Hdb : (0 <=? d) = false) by (apply Z.leb_gt; lia).
        destruct Hz as [(Hz & ->) | (Hz & ->)].
        -- exists ((s, e) :: m1), rest, o1.
           subst o. split; [reflexivity|]. split; [reflexivity|].
           split; [|exact Hnil].
           rewrite Hrun, Hdb, Hz. reflexivity.
        -- exists ((s, e) :: m1), rest, ((s, eaddmul e d Rex) :: o1).
           subst o. split; [reflexivity|]. split; [reflexivity|].
           split; [|exact Hnil].
           rewrite Hrun, Hdb, Hz. reflexivity.
    + destruct Hrest as (Hlat & Hge & o & Ha & Hout).
      destruct (IH mt o Ha) as (m1 & rest & o1 & Hm & Ho & Hex & Hnil).
      subst mt.
      assert (Hrun : appBlkPfx_side false lo Rex
                       (((s, BVm d lb md rs) : BRRunP) :: rt)
                       ((s, e) :: m1) =
                     match (if (0 <=? d) then false else
                            eeqb (eaddmul e d Rex) (econst 0)) with
                     | true => Some o1
                     | false => Some ((s, eaddmul e d Rex) :: o1)
                     end).
      { cbn [appBlkPfx_side]. rewrite Nat.eqb_refl, Hlat, Hge. cbn [andb].
        destruct (0 <=? d) eqn:Hd.
        - rewrite Hex. reflexivity.
        - destruct Hout as [(Hd' & _) | (_ & Hsv & Hz)];
            [apply Z.leb_gt in Hd; lia|].
          rewrite Hsv.
          destruct Hz as [(Hz & _) | (Hz & _)]; rewrite Hz;
            [exact Hex | rewrite Hex; reflexivity]. }
      destruct Hout as [(Hd & ->) | (Hd0 & Hsv & Hz)].
      * exists ((s, e) :: m1), rest, ((s, eaddmul e d Rex) :: o1).
        subst o. split; [reflexivity|]. split; [reflexivity|].
        split; [|exact Hnil].
        rewrite Hrun.
        destruct (0 <=? d) eqn:Hdb; [reflexivity | apply Z.leb_gt in Hdb; lia].
      * assert (Hdb : (0 <=? d) = false) by (apply Z.leb_gt; lia).
        destruct Hz as [(Hz & ->) | (Hz & ->)].
        -- exists ((s, e) :: m1), rest, o1.
           subst o. split; [reflexivity|]. split; [reflexivity|].
           split; [|exact Hnil].
           rewrite Hrun, Hdb, Hz. reflexivity.
        -- exists ((s, e) :: m1), rest, ((s, eaddmul e d Rex) :: o1).
           subst o. split; [reflexivity|]. split; [reflexivity|].
           split; [|exact Hnil].
           rewrite Hrun, Hdb, Hz. reflexivity.
Qed.

(** ** Denotation lemmas for the EXACT application (the matched prefix) *)

Lemma appBlkP_side_vlen : forall lo Rex rr mr out nu j,
  appBlkPfx_side false lo Rex rr mr = Some out ->
  length (bvvalsP nu j rr mr) = length (brlbsP rr).
Proof.
  induction rr as [|[s rc] rt IH]; intros mr out nu j H.
  - destruct mr; [reflexivity|]. cbn in H. discriminate.
  - destruct mr as [|[s' e] mt].
    + destruct rc; cbn in H; discriminate.
    + destruct (appBlkP_side_cons_inv _ _ _ _ _ _ _ _ _ _ H) as [Hs Hrest].
      destruct rc as [v | d lb | d lb md rs]; simpl.
      * destruct Hrest as (_ & o & Ha & _). eapply IH; eauto.
      * destruct Hrest as (_ & o & Ha & _). f_equal. eapply IH; eauto.
      * destruct Hrest as (_ & _ & o & Ha & _). f_equal. eapply IH; eauto.
Qed.

Lemma appBlkP_side_den0 : forall tbl lo Rex rr mr out nu,
  appBlkPfx_side false lo Rex rr mr = Some out ->
  forall pre ext,
  bdside tbl (fun i => nth i (pre ++ bvvalsP nu 0 rr mr ++ ext) 1)
        (brstartP (length pre) rr)
  = bdside tbl nu mr.
Proof.
  induction rr as [|[s rc] rt IH]; intros mr out nu H pre ext.
  - destruct mr; [reflexivity | cbn in H; discriminate].
  - destruct mr as [|[s' e] mt];
      [destruct rc; cbn in H; discriminate|].
    destruct (appBlkP_side_cons_inv _ _ _ _ _ _ _ _ _ _ H) as [Hs Hrest].
    subst s'.
    destruct rc as [v | d lb | d lb md rs]; simpl bvvalsP; simpl brstartP;
      rewrite !bdside_cons.
    + destruct Hrest as (He & o & Ha & _).
      f_equal.
      * f_equal. unfold cnt.
        rewrite eval_econst, (eeqb_eval _ _ nu He), eval_econst. reflexivity.
      * eapply IH; eauto.
    + destruct Hrest as (Hge & o & Ha & _).
      f_equal.
      * f_equal. unfold cnt. rewrite eval_evar, nth_mid2. f_equal. lia.
      * etransitivity;
          [apply bdside_ext with
             (g := fun i => nth i ((pre ++ [eval nu e + d * 0])
                                     ++ bvvalsP nu 0 rt mt ++ ext) 1)|].
        { intro i. f_equal. rewrite <- app_assoc. reflexivity. }
        replace (S (length pre))
          with (length (pre ++ [eval nu e + d * 0]))
          by (rewrite app_length; simpl; lia).
        eapply IH; eauto.
    + destruct Hrest as (Hlat & Hge & o & Ha & _).
      destruct (latt_ok_facts _ _ _ _ _ Hlat) as (Hmd & Hdm & Hlbm & Hallm).
      f_equal.
      * f_equal. unfold cnt.
        rewrite eval_elatt, nth_mid2.
        rewrite (latt_div_eval md rs (eval nu e + d * 0)
                   ltac:(lia) (Hallm nu 0)).
        f_equal. lia.
      * etransitivity;
          [apply bdside_ext with
             (g := fun i => nth i ((pre ++ [(eval nu e + d * 0 - rs) / md])
                                     ++ bvvalsP nu 0 rt mt ++ ext) 1)|].
        { intro i. f_equal. rewrite <- app_assoc. reflexivity. }
        replace (S (length pre))
          with (length (pre ++ [(eval nu e + d * 0 - rs) / md]))
          by (rewrite app_length; simpl; lia).
        eapply IH; eauto.
Qed.

Lemma appBlkP_side_denS : forall tbl lo Rex rr mr out nu j,
  appBlkPfx_side false lo Rex rr mr = Some out ->
  forall pre pre' ext ext', length pre = length pre' ->
  bdside tbl (fun i => nth i (pre ++ bvvalsP nu j rr mr ++ ext) 1)
        (brendP (length pre) rr)
  = bdside tbl (fun i => nth i (pre' ++ bvvalsP nu (j + 1) rr mr ++ ext') 1)
          (brstartP (length pre') rr).
Proof.
  induction rr as [|[s rc] rt IH]; intros mr out nu j H pre pre' ext
    ext' Hlen.
  - destruct mr; [reflexivity | cbn in H; discriminate].
  - destruct mr as [|[s' e] mt];
      [destruct rc; cbn in H; discriminate|].
    destruct (appBlkP_side_cons_inv _ _ _ _ _ _ _ _ _ _ H) as [Hs Hrest].
    subst s'.
    destruct rc as [v | d lb | d lb md rs]; simpl bvvalsP; simpl brstartP;
      simpl brendP; rewrite !bdside_cons.
    + destruct Hrest as (_ & o & Ha & _). f_equal. eapply IH; eauto.
    + destruct Hrest as (_ & o & Ha & _).
      f_equal.
      * f_equal. unfold cnt.
        rewrite eval_eaddc, eval_evar, eval_evar, !nth_mid2. f_equal. lia.
      * etransitivity;
          [apply bdside_ext with
             (g := fun i => nth i ((pre ++ [eval nu e + d * j])
                                     ++ bvvalsP nu j rt mt ++ ext) 1)|].
        { intro i. f_equal. rewrite <- app_assoc. reflexivity. }
        etransitivity;
          [|apply bdside_ext with
              (f := fun i => nth i ((pre' ++ [eval nu e + d * (j + 1)])
                                      ++ bvvalsP nu (j + 1) rt mt
                                      ++ ext') 1)].
        2:{ intro i. f_equal. rewrite <- app_assoc. reflexivity. }
        replace (S (length pre))
          with (length (pre ++ [eval nu e + d * j]))
          by (rewrite app_length; simpl; lia).
        replace (S (length pre'))
          with (length (pre' ++ [eval nu e + d * (j + 1)]))
          by (rewrite app_length; simpl; lia).
        eapply IH; eauto.
        rewrite !app_length; simpl; lia.
    + destruct Hrest as (Hlat & _ & o & Ha & _).
      destruct (latt_ok_facts _ _ _ _ _ Hlat) as (Hmd & Hdm & Hlbm & Hallm).
      f_equal.
      * f_equal. unfold cnt.
        rewrite eval_eaddc, !eval_elatt, !nth_mid2.
        rewrite (latt_div_eval md rs (eval nu e + d * j)
                   ltac:(lia) (Hallm nu j)).
        rewrite (latt_div_eval md rs (eval nu e + d * (j + 1))
                   ltac:(lia) (Hallm nu (j + 1))).
        f_equal. lia.
      * etransitivity;
          [apply bdside_ext with
             (g := fun i => nth i ((pre ++ [(eval nu e + d * j - rs) / md])
                                     ++ bvvalsP nu j rt mt ++ ext) 1)|].
        { intro i. f_equal. rewrite <- app_assoc. reflexivity. }
        etransitivity;
          [|apply bdside_ext with
              (f := fun i => nth i ((pre' ++ [(eval nu e + d * (j + 1) - rs)
                                                / md])
                                      ++ bvvalsP nu (j + 1) rt mt
                                      ++ ext') 1)].
        2:{ intro i. f_equal. rewrite <- app_assoc. reflexivity. }
        replace (S (length pre))
          with (length (pre ++ [(eval nu e + d * j - rs) / md]))
          by (rewrite app_length; simpl; lia).
        replace (S (length pre'))
          with (length (pre' ++ [(eval nu e + d * (j + 1) - rs) / md]))
          by (rewrite app_length; simpl; lia).
        eapply IH; eauto.
        rewrite !app_length; simpl; lia.
Qed.

Lemma appBlkP_side_denR : forall tbl lo Rex rr mr out nu,
  appBlkPfx_side false lo Rex rr mr = Some out ->
  forall pre ext,
  bdside tbl (fun i => nth i (pre ++ bvvalsP nu (eval nu Rex) rr mr ++ ext) 1)
        (brstartP (length pre) rr)
  = bdside tbl nu out.
Proof.
  induction rr as [|[s rc] rt IH]; intros mr out nu H pre ext.
  - destruct mr; cbn in H; [injection H as <-; reflexivity | discriminate].
  - destruct mr as [|[s' e] mt];
      [destruct rc; cbn in H; discriminate|].
    destruct (appBlkP_side_cons_inv _ _ _ _ _ _ _ _ _ _ H) as [Hs Hrest].
    subst s'.
    destruct rc as [v | d lb | d lb md rs]; simpl bvvalsP; simpl brstartP;
      rewrite !bdside_cons.
    + destruct Hrest as (He & o & Ha & ->).
      rewrite bdside_cons.
      f_equal.
      * f_equal. unfold cnt.
        rewrite eval_econst, (eeqb_eval _ _ nu He), eval_econst. reflexivity.
      * eapply IH; eauto.
    + destruct Hrest as (Hge & o & Ha & Hout).
      assert (Hhead : nth (length pre)
                (pre ++ ((eval nu e + d * eval nu Rex)
                           :: bvvalsP nu (eval nu Rex) rt mt) ++ ext) 1
              = eval nu e + d * eval nu Rex) by apply nth_mid2.
      assert (Htail : bdside tbl
          (fun i => nth i (pre ++ ((eval nu e + d * eval nu Rex)
                    :: bvvalsP nu (eval nu Rex) rt mt) ++ ext) 1)
          (brstartP (S (length pre)) rt) = bdside tbl nu o).
      { etransitivity;
          [apply bdside_ext with
             (g := fun i => nth i ((pre ++ [eval nu e + d * eval nu Rex])
                                     ++ bvvalsP nu (eval nu Rex) rt mt
                                     ++ ext) 1)|].
        { intro i. f_equal. rewrite <- app_assoc. reflexivity. }
        replace (S (length pre))
          with (length (pre ++ [eval nu e + d * eval nu Rex]))
          by (rewrite app_length; simpl; lia).
        eapply IH; eauto. }
      destruct Hout as [(Hd & ->) | (Hd0 & Hsv & Hdrop)].
      * rewrite bdside_cons. f_equal.
        -- f_equal. unfold cnt. rewrite eval_evar, Hhead, eval_eaddmul.
           reflexivity.
        -- exact Htail.
      * destruct Hdrop as [(Hz & ->) | (Hz & ->)].
        -- replace (cnt (fun i => nth i (pre ++ ((eval nu e + d * eval nu Rex)
                     :: bvvalsP nu (eval nu Rex) rt mt) ++ ext) 1)
                     (evar (length pre))) with 0%nat.
           2:{ unfold cnt. rewrite eval_evar, Hhead.
               pose proof (eeqb_eval _ _ nu Hz) as HzE.
               rewrite eval_eaddmul, eval_econst in HzE. lia. }
           simpl repeat. simpl app. exact Htail.
        -- rewrite bdside_cons. f_equal.
           ++ f_equal. unfold cnt. rewrite eval_evar, Hhead, eval_eaddmul.
              reflexivity.
           ++ exact Htail.
    + destruct Hrest as (Hlat & Hge & o & Ha & Hout).
      destruct (latt_ok_facts _ _ _ _ _ Hlat) as (Hmd & Hdm & Hlbm & Hallm).
      assert (Hhead : nth (length pre)
                (pre ++ (((eval nu e + d * eval nu Rex - rs) / md)
                           :: bvvalsP nu (eval nu Rex) rt mt) ++ ext) 1
              = (eval nu e + d * eval nu Rex - rs) / md) by apply nth_mid2.
      assert (Htail : bdside tbl
          (fun i => nth i (pre ++ (((eval nu e + d * eval nu Rex - rs) / md)
                    :: bvvalsP nu (eval nu Rex) rt mt) ++ ext) 1)
          (brstartP (S (length pre)) rt) = bdside tbl nu o).
      { etransitivity;
          [apply bdside_ext with
             (g := fun i => nth i ((pre ++ [(eval nu e + d * eval nu Rex - rs)
                                              / md])
                                     ++ bvvalsP nu (eval nu Rex) rt mt
                                     ++ ext) 1)|].
        { intro i. f_equal. rewrite <- app_assoc. reflexivity. }
        replace (S (length pre))
          with (length (pre ++ [(eval nu e + d * eval nu Rex - rs) / md]))
          by (rewrite app_length; simpl; lia).
        eapply IH; eauto. }
      assert (Hcnthead : cnt (fun i => nth i
                (pre ++ (((eval nu e + d * eval nu Rex - rs) / md)
                           :: bvvalsP nu (eval nu Rex) rt mt) ++ ext) 1)
                (elatt md rs (length pre))
              = cnt nu (eaddmul e d Rex)).
      { unfold cnt. rewrite eval_elatt, Hhead.
        rewrite (latt_div_eval md rs (eval nu e + d * eval nu Rex)
                   ltac:(lia) (Hallm nu (eval nu Rex))).
        rewrite eval_eaddmul. reflexivity. }
      destruct Hout as [(Hd & ->) | (Hd0 & Hsv & Hdrop)].
      * rewrite bdside_cons. f_equal.
        -- f_equal. exact Hcnthead.
        -- exact Htail.
      * destruct Hdrop as [(Hz & ->) | (Hz & ->)].
        -- replace (cnt (fun i => nth i
                     (pre ++ (((eval nu e + d * eval nu Rex - rs) / md)
                                :: bvvalsP nu (eval nu Rex) rt mt) ++ ext) 1)
                     (elatt md rs (length pre))) with 0%nat.
           2:{ rewrite Hcnthead. unfold cnt.
               pose proof (eeqb_eval _ _ nu Hz) as HzE.
               rewrite eval_econst in HzE. rewrite HzE. reflexivity. }
           simpl repeat. simpl app. exact Htail.
        -- rewrite bdside_cons. f_equal.
           ++ f_equal. exact Hcnthead.
           ++ exact Htail.
Qed.

Lemma appBlkP_side_bge : forall lo Rex rr mr out nu j,
  appBlkPfx_side false lo Rex rr mr = Some out -> bge lo nu ->
  0 <= j -> j <= eval nu Rex - 1 ->
  forall i, nth i (brlbsP rr) 0 <= nth i (bvvalsP nu j rr mr) 1.
Proof.
  induction rr as [|[s rc] rt IH]; intros mr out nu j H Hb Hj0 Hj1 i.
  - destruct mr; cbn in H; [|discriminate]. simpl. destruct i; simpl; lia.
  - destruct mr as [|[s' e] mt];
      [destruct rc; cbn in H; discriminate|].
    destruct (appBlkP_side_cons_inv _ _ _ _ _ _ _ _ _ _ H) as [Hs Hrest].
    destruct rc as [v | d lb | d lb md rs]; simpl.
    + destruct Hrest as (_ & o & Ha & _). eapply IH; eauto.
    + destruct Hrest as (Hge & o & Ha & Hout).
      destruct i as [|i']; simpl.
      * pose proof (expr_ge_sound lo e lb nu Hge Hb) as Hlbe.
        destruct Hout as [(Hd & _) | (Hd0 & Hsv & _)].
        -- nia.
        -- pose proof (expr_ge_sound lo _ _ nu Hsv Hb) as Hsurv.
           rewrite eval_eaddmul in Hsurv. nia.
      * eapply IH; eauto.
    + destruct Hrest as (Hlat & Hge & o & Ha & Hout).
      destruct (latt_ok_facts _ _ _ _ _ Hlat) as (Hmd & Hdm & Hlbm & Hallm).
      destruct i as [|i']; simpl.
      * apply Z.div_le_mono; [lia|].
        pose proof (expr_ge_sound lo e lb nu Hge Hb) as Hlbe.
        destruct Hout as [(Hd & _) | (Hd0 & Hsv & _)].
        -- nia.
        -- pose proof (expr_ge_sound lo _ _ nu Hsv Hb) as Hsurv.
           rewrite eval_eaddmul in Hsurv. nia.
      * eapply IH; eauto.
Qed.

(** ** The remainder-tolerant binding search (UNTRUSTED)

    Mirror of verify.c's v6+ binding drain (3299-3348): the remainder
    [rmd = (e_c0 - lb) mod d] may be nonzero, every coefficient of
    [e - lb] must be divisible by [d], and [Rex >= 1] (which is exactly
    the [min e >= lb + rmd] guard).  [appBlkPfx_side]'s per-decrement
    survival re-check makes ANY produced [Rex] sound, so nothing here
    carries proof weight ([rexOf]/[surviveb] reused from [RulesK]). *)

Fixpoint decs_sideP (rr : list BRRunP) (mr : list BRun)
  : list (Z * Z * Expr) :=
  match rr, mr with
  | (_, BV d lb) :: rt, (_, e) :: mt =>
      if d <=? -1 then (d, lb, e) :: decs_sideP rt mt else decs_sideP rt mt
  | (_, BVm d lb _ _) :: rt, (_, e) :: mt =>
      if d <=? -1 then (d, lb, e) :: decs_sideP rt mt else decs_sideP rt mt
  | _ :: rt, _ :: mt => decs_sideP rt mt
  | _, _ => []
  end.

Definition bindsbP (lo : list Z) (all : list (Z * Z * Expr))
    (t : Z * Z * Expr) : bool :=
  let '(d, lb, e) := t in
  let dj := - d in
  let r := eaddc e (- lb) in
  ((dj <=? lb) &&
   forallb (fun c => (c mod dj) =? 0) (e_cf r) &&
   expr_ge lo (rexOf t) 1 &&
   forallb (surviveb lo (rexOf t)) all)%bool.

Fixpoint find_bindingP (lo : list Z) (cands all : list (Z * Z * Expr))
  : option Expr :=
  match cands with
  | [] => None
  | t :: rest =>
      if bindsbP lo all t then Some (rexOf t) else find_bindingP lo rest all
  end.

(** ** The prefix rule application *)

Definition btrimS (sent : bool) (rs : list BRun) : list BRun :=
  if sent then rs else btrim_blanks rs.

Definition ruleBlkPfx_apply (lo : list Z) (sent : bool * bool)
    (r : BRuleP) (c : BCfg) : option BCfg :=
  let '(pL, pR) := brp_pfx r in
  let '(sL, sR) := sent in
  if st_eqb (b_st c) (brp_st r) && sym_eqb (b_hs c) (brp_hs r) &&
     (pL || negb sL) && (pR || negb sR) then
    let decs := decs_sideP (brp_L r) (b_L c)
                ++ decs_sideP (brp_R r) (b_R c) in
    match find_bindingP lo decs decs with
    | None => None
    | Some Rex =>
        if expr_ge lo Rex 1 then
          match appBlkPfx_side pL lo Rex (brp_L r) (b_L c),
                appBlkPfx_side pR lo Rex (brp_R r) (b_R c) with
          | Some outL, Some outR =>
              match bmerge_adj lo outL, bmerge_adj lo outR with
              | Some mL, Some mR =>
                  Some (mkBCfg (b_st c) (b_hs c)
                               (btrimS sL mL) (btrimS sR mR))
              | _, _ => None
              end
          | _, _ => None
          end
        else None
    end
  else None.

Theorem ruleBlkPfx_apply_sound : forall tm tbl lo r F c c' sent,
  raw_ok tbl ->
  ruleBlkPfx_apply lo sent r c = Some c' ->
  brule_semP tm tbl r F ->
  forall nu, bge lo nu ->
  forall XL XR,
  (fst sent = false -> XL = []) -> (snd sent = false -> XR = []) ->
  exists n, (1 <= n)%nat /\
    Reach tm F n (bsemX tbl nu c XL XR) (bsemX tbl nu c' XL XR).
Proof.
  intros tm tbl lo r F c c' sent Hraw H Hsem nu Hb XL XR HXL HXR.
  unfold ruleBlkPfx_apply in H.
  destruct (brp_pfx r) as [pL pR] eqn:Hpfx.
  destruct sent as [sL sR]. simpl in HXL, HXR.
  cbv beta iota in H.
  destruct (st_eqb (b_st c) (brp_st r) && sym_eqb (b_hs c) (brp_hs r) &&
            (pL || negb sL) && (pR || negb sR)) eqn:Hguard; [|discriminate].
  apply andb_prop in Hguard as [Hguard HpsR].
  apply andb_prop in Hguard as [Hguard HpsL].
  apply andb_prop in Hguard as [Hst Hhs].
  apply st_eqb_spec in Hst. apply sym_eqb_spec in Hhs.
  cbv zeta in H.
  destruct (find_bindingP lo
              (decs_sideP (brp_L r) (b_L c) ++ decs_sideP (brp_R r) (b_R c))
              (decs_sideP (brp_L r) (b_L c) ++ decs_sideP (brp_R r) (b_R c)))
    as [Rex|]; [|discriminate].
  destruct (expr_ge lo Rex 1) eqn:HR1; [|discriminate].
  destruct (appBlkPfx_side pL lo Rex (brp_L r) (b_L c)) as [outL|]
    eqn:HappL; [|discriminate].
  destruct (appBlkPfx_side pR lo Rex (brp_R r) (b_R c)) as [outR|]
    eqn:HappR; [|discriminate].
  destruct (bmerge_adj lo outL) as [mL|] eqn:HmL; [|discriminate].
  destruct (bmerge_adj lo outR) as [mR|] eqn:HmR; [|discriminate].
  injection H as <-.
  pose proof (expr_ge_sound lo Rex 1 nu HR1 Hb) as HrZ.
  destruct (appBlkPfx_decomp _ _ _ _ _ _ HappL)
    as (mL1 & restL & oL1 & HdecL & HoutL & HexL & HnilL).
  destruct (appBlkPfx_decomp _ _ _ _ _ _ HappR)
    as (mR1 & restR & oR1 & HdecR & HoutR & HexR & HnilR).
  set (YL := bdside tbl nu restL ++ XL).
  set (YR := bdside tbl nu restR ++ XR).
  assert (HYL : fst (brp_pfx r) = false -> YL = []).
  { rewrite Hpfx. simpl. intro HpL. subst pL.
    unfold YL. rewrite (HnilL eq_refl).
    simpl in HpsL. apply negb_true_iff in HpsL.
    rewrite (HXL HpsL). reflexivity. }
  assert (HYR : snd (brp_pfx r) = false -> YR = []).
  { rewrite Hpfx. simpl. intro HpR. subst pR.
    unfold YR. rewrite (HnilR eq_refl).
    simpl in HpsR. apply negb_true_iff in HpsR.
    rewrite (HXR HpsR). reflexivity. }
  pose (VL := fun j => bvvalsP nu j (brp_L r) mL1).
  pose (VR := fun j => bvvalsP nu j (brp_R r) mR1).
  pose (U := fun j (i : nat) => nth i (VL j ++ VR j) 1).
  assert (HlenL : forall j, length (VL j) = length (brlbsP (brp_L r)))
    by (intro j; eapply appBlkP_side_vlen; eauto).
  assert (HL0 : bdside tbl (U 0) (brstartP 0 (brp_L r))
                = bdside tbl nu mL1)
    by exact (appBlkP_side_den0 tbl _ _ _ _ _ _ HexL [] (VR 0)).
  assert (HR0 : bdside tbl (U 0) (brstartP (length (brlbsP (brp_L r)))
                                           (brp_R r))
                = bdside tbl nu mR1).
  { etransitivity;
      [apply bdside_ext with (g := fun i => nth i (VL 0 ++ VR 0 ++ []) 1)|].
    { intro i. f_equal. rewrite app_nil_r. reflexivity. }
    rewrite <- (HlenL 0).
    exact (appBlkP_side_den0 tbl _ _ _ _ _ _ HexR (VL 0) []). }
  assert (Claim0 : bsemX tbl nu c XL XR
                   = bsemX tbl (U 0) (brulep_start_cfg r) YL YR).
  { unfold bsemX, brulep_start_cfg. cbn [b_st b_hs b_L b_R].
    rewrite Hst, Hhs, HL0, HR0.
    unfold YL, YR.
    rewrite HdecL, HdecR, !bdside_app, <- !app_assoc. reflexivity. }
  assert (ClaimS : forall j,
    bsemX tbl (U j) (brulep_end_cfg r) YL YR
    = bsemX tbl (U (j + 1)) (brulep_start_cfg r) YL YR).
  { intro j.
    assert (EL : bdside tbl (U j) (brendP 0 (brp_L r))
                 = bdside tbl (U (j + 1)) (brstartP 0 (brp_L r)))
      by exact (appBlkP_side_denS tbl _ _ _ _ _ _ j HexL [] [] (VR j)
                  (VR (j + 1)) eq_refl).
    assert (ER : bdside tbl (U j) (brendP (length (brlbsP (brp_L r)))
                                          (brp_R r))
                 = bdside tbl (U (j + 1))
                     (brstartP (length (brlbsP (brp_L r))) (brp_R r))).
    { etransitivity;
        [apply bdside_ext with (g := fun i => nth i (VL j ++ VR j ++ []) 1)|].
      { intro i. f_equal. rewrite app_nil_r. reflexivity. }
      etransitivity;
        [|apply bdside_ext with
            (f := fun i => nth i (VL (j + 1) ++ VR (j + 1) ++ []) 1)].
      2:{ intro i. f_equal. rewrite app_nil_r. reflexivity. }
      rewrite <- (HlenL j) at 1.
      rewrite <- (HlenL (j + 1)).
      apply (appBlkP_side_denS tbl lo Rex (brp_R r) mR1 oR1 nu j HexR
               (VL j) (VL (j + 1)) [] []).
      rewrite !HlenL. reflexivity. }
    unfold bsemX, brulep_end_cfg, brulep_start_cfg.
    cbn [b_st b_hs b_L b_R].
    rewrite EL, ER. reflexivity. }
  assert (ClaimR : bsemX tbl (U (eval nu Rex)) (brulep_start_cfg r) YL YR
                   = bsemX tbl nu (mkBCfg (b_st c) (b_hs c) outL outR)
                           XL XR).
  { assert (EL : bdside tbl (U (eval nu Rex)) (brstartP 0 (brp_L r))
                 = bdside tbl nu oL1)
      by exact (appBlkP_side_denR tbl _ _ _ _ _ _ HexL [] (VR (eval nu Rex))).
    assert (ER : bdside tbl (U (eval nu Rex))
                   (brstartP (length (brlbsP (brp_L r))) (brp_R r))
                 = bdside tbl nu oR1).
    { etransitivity;
        [apply bdside_ext with
           (g := fun i => nth i (VL (eval nu Rex)
                                   ++ VR (eval nu Rex) ++ []) 1)|].
      { intro i. f_equal. rewrite app_nil_r. reflexivity. }
      rewrite <- (HlenL (eval nu Rex)).
      exact (appBlkP_side_denR tbl _ _ _ _ _ _ HexR (VL (eval nu Rex)) []). }
    unfold bsemX, brulep_start_cfg. cbn [b_st b_hs b_L b_R].
    rewrite Hst, Hhs, EL, ER.
    unfold YL, YR.
    rewrite HoutL, HoutR, !bdside_app, <- !app_assoc. reflexivity. }
  assert (Hbge : forall j, 0 <= j -> j <= eval nu Rex - 1 ->
                 bge (brule_lbsP r) (U j)).
  { intros j Hj0 Hj1 i.
    unfold brule_lbsP.
    apply nth_app_le.
    - symmetry. apply HlenL.
    - intro i'. eapply appBlkP_side_bge; eauto.
    - intro i'. eapply appBlkP_side_bge; eauto. }
  assert (Hiter : forall m, (1 <= m)%nat -> Z.of_nat m <= eval nu Rex ->
    exists n, (1 <= n)%nat /\
      Reach tm F n (bsemX tbl (U 0) (brulep_start_cfg r) YL YR)
                   (bsemX tbl (U (Z.of_nat m)) (brulep_start_cfg r) YL YR)).
  { induction m as [|m IHm]; intros Hm1 Hmr; [lia|].
    destruct m as [|m'].
    - destruct (Hsem (U 0) (Hbge 0 ltac:(lia) ltac:(lia)) YL YR HYL HYR)
        as (n & Hn & HRch).
      exists n. split; [exact Hn|].
      setoid_rewrite (ClaimS 0) in HRch. exact HRch.
    - assert (Hmr' : Z.of_nat (S m') <= eval nu Rex) by lia.
      destruct (IHm ltac:(lia) Hmr') as (n1 & Hn1 & HRch1).
      destruct (Hsem (U (Z.of_nat (S m')))
                  (Hbge (Z.of_nat (S m')) ltac:(lia) ltac:(lia))
                  YL YR HYL HYR)
        as (n2 & Hn2 & HRch2).
      setoid_rewrite (ClaimS (Z.of_nat (S m'))) in HRch2.
      replace (Z.of_nat (S m') + 1) with (Z.of_nat (S (S m')))
        in HRch2 by lia.
      exists (n1 + n2)%nat. split; [lia|].
      apply (Reach_set tm F (F ++ F));
        [intro t; rewrite in_app_iff; tauto|].
      exact (Reach_compose _ _ _ _ _ _ _ _ HRch1 HRch2). }
  destruct (Hiter (Z.to_nat (eval nu Rex)) ltac:(lia) ltac:(lia))
    as (n & Hn & HRch).
  exists n. split; [exact Hn|].
  replace (Z.of_nat (Z.to_nat (eval nu Rex))) with (eval nu Rex)
    in HRch by lia.
  setoid_rewrite ClaimR in HRch.
  setoid_rewrite <- Claim0 in HRch.
  assert (Hreb : bsemX tbl nu (mkBCfg (b_st c) (b_hs c)
                            (btrimS sL mL) (btrimS sR mR)) XL XR
                 = bsemX tbl nu (mkBCfg (b_st c) (b_hs c) outL outR) XL XR).
  { unfold bsemX. cbn [b_st b_hs b_L b_R].
    rewrite !lift_cc.
    assert (SL : lift_side (bdside tbl nu (btrimS sL mL) ++ XL)
                 = lift_side (bdside tbl nu outL ++ XL)).
    { unfold btrimS. destruct sL.
      - rewrite (bmerge_adj_den tbl lo outL mL nu HmL Hb). reflexivity.
      - rewrite (HXL eq_refl), !app_nil_r.
        rewrite (btrim_blanks_den tbl _ nu Hraw).
        rewrite (bmerge_adj_den tbl lo outL mL nu HmL Hb). reflexivity. }
    assert (SR : lift_side (bdside tbl nu (btrimS sR mR) ++ XR)
                 = lift_side (bdside tbl nu outR ++ XR)).
    { unfold btrimS. destruct sR.
      - rewrite (bmerge_adj_den tbl lo outR mR nu HmR Hb). reflexivity.
      - rewrite (HXR eq_refl), !app_nil_r.
        rewrite (btrim_blanks_den tbl _ nu Hraw).
        rewrite (bmerge_adj_den tbl lo outR mR nu HmR Hb). reflexivity. }
    rewrite SL, SR. reflexivity. }
  setoid_rewrite Hreb.
  exact HRch.
Qed.

(** ** The meta-cycle replay with the sentinel engine *)

Fixpoint try_rulesBlkP (lo : list Z) (sent : bool * bool)
    (rules : list (BRuleP * list Tr)) (c : BCfg) : option (BCfg * list Tr) :=
  match rules with
  | [] => None
  | (r, F) :: rest =>
      match ruleBlkPfx_apply lo sent r c with
      | Some c' => Some (c', F)
      | None => try_rulesBlkP lo sent rest c
      end
  end.

Lemma bcanon_bsemX : forall lo tbl blks c nu XL XR,
  raw_ok tbl -> bge lo nu ->
  bsemX tbl nu (bcanon lo tbl blks c) XL XR = bsemX tbl nu c XL XR.
Proof.
  intros lo tbl blks c nu XL XR Hraw Hb. unfold bcanon, bsemX.
  cbn [b_st b_hs b_L b_R].
  rewrite !(bcanon_side_den lo tbl blks _ nu Hraw Hb). reflexivity.
Qed.

Lemma bscfg_eqb_bsemX : forall tbl a b nu XL XR,
  bscfg_eqb a b = true -> bsemX tbl nu a XL XR = bsemX tbl nu b XL XR.
Proof.
  intros tbl a b nu XL XR H.
  apply andb_prop in H as [H HR].
  apply andb_prop in H as [H HL].
  apply andb_prop in H as [Hst Hhs].
  apply st_eqb_spec in Hst. apply sym_eqb_spec in Hhs.
  unfold bsemX.
  rewrite Hst, Hhs, (bruns_eqb_den tbl _ _ nu HL),
    (bruns_eqb_den tbl _ _ nu HR).
  reflexivity.
Qed.

Fixpoint breplayKP (tm : TM) (tbl : BTbl) (blks : list (nat * list Sym))
    (lo : list Z) (cfuel : nat) (rules : list (BRuleP * list Tr))
    (endt : BCfg -> bool) (sent : bool * bool) (fuel : nat)
    (stepped : bool) (c : BCfg) : option (BCfg * list Tr) :=
  match fuel with
  | O => None
  | S fuel' =>
      if stepped && endt c then Some (c, [])
      else
        match try_rulesBlkP lo sent rules c with
        | Some (c', F) =>
            match breplayKP tm tbl blks lo cfuel rules endt sent fuel'
                    stepped c' with
            | Some (cend, F') => Some (cend, F ++ F')
            | None => None
            end
        | None =>
            match beng_stepS tm tbl blks lo (fst sent) (snd sent) cfuel c with
            | Some (c', F) =>
                match breplayKP tm tbl blks lo cfuel rules endt sent fuel'
                        true (bcanon lo tbl blks c') with
                | Some (cend, F') => Some (cend, F ++ F')
                | None => None
                end
            | None => None
            end
        end
  end.

Lemma breplayKP_sound : forall tm tbl blks lo cfuel rules endt sent fuel
                               stepped c cend F,
  raw_ok tbl ->
  breplayKP tm tbl blks lo cfuel rules endt sent fuel stepped c
    = Some (cend, F) ->
  forall nu XL XR, bge lo nu ->
  (fst sent = false -> XL = []) -> (snd sent = false -> XR = []) ->
  (forall r Fr c1 c2, In (r, Fr) rules ->
     ruleBlkPfx_apply lo sent r c1 = Some c2 ->
     exists n, (1 <= n)%nat /\
       Reach tm Fr n (bsemX tbl nu c1 XL XR) (bsemX tbl nu c2 XL XR)) ->
  endt cend = true /\
  exists n, Reach tm F n (bsemX tbl nu c XL XR) (bsemX tbl nu cend XL XR) /\
            (stepped = false -> (1 <= n)%nat).
Proof.
  intros tm tbl blks lo cfuel rules endt sent fuel.
  induction fuel as [|fuel IH]; intros stepped c cend F Hraw H nu XL XR Hb
    HXL HXR Happ; simpl in H; [discriminate|].
  destruct (stepped && endt c) eqn:Hend.
  - injection H as <- <-.
    apply andb_prop in Hend as [Hst Hendc].
    split; [exact Hendc|].
    exists O. split; [apply Reach_refl|].
    intro Hf; rewrite Hf in Hst; discriminate.
  - destruct (try_rulesBlkP lo sent rules c) as [[c' Fr]|] eqn:Htry.
    + destruct (breplayKP tm tbl blks lo cfuel rules endt sent fuel
                  stepped c')
        as [[cend' F']|] eqn:Hrec; [|discriminate].
      injection H as <- <-.
      destruct (IH stepped c' cend' F' Hraw Hrec nu XL XR Hb HXL HXR Happ)
        as (Hende & n2 & HR2 & _).
      assert (Hget : exists r0, In (r0, Fr) rules /\
                     ruleBlkPfx_apply lo sent r0 c = Some c').
      { clear -Htry. induction rules as [|[r0 F0] rest IHr];
          simpl in Htry; [discriminate|].
        destruct (ruleBlkPfx_apply lo sent r0 c) eqn:Ha.
        - injection Htry as <- <-. exists r0. split; [left|]; auto.
        - destruct (IHr Htry) as (r1 & Hin & Ha1).
          exists r1. split; [right|]; assumption. }
      destruct Hget as (r0 & Hin & Ha).
      destruct (Happ r0 Fr c c' Hin Ha) as (n1 & Hn1 & HR1).
      split; [exact Hende|].
      exists (n1 + n2)%nat. split.
      * exact (Reach_compose _ _ _ _ _ _ _ _ HR1 HR2).
      * intro; lia.
    + destruct (beng_stepS tm tbl blks lo (fst sent) (snd sent) cfuel c)
        as [[c' Fe]|] eqn:Hstep; [|discriminate].
      destruct (breplayKP tm tbl blks lo cfuel rules endt sent fuel true
                  (bcanon lo tbl blks c'))
        as [[cend' F']|] eqn:Hrec; [|discriminate].
      injection H as <- <-.
      destruct (IH true (bcanon lo tbl blks c') cend' F' Hraw Hrec nu XL XR
                  Hb HXL HXR Happ)
        as (Hende & n2 & HR2 & _).
      destruct (beng_stepS_sound tm tbl blks lo (fst sent) (snd sent) cfuel
                  c c' Fe Hraw Hstep nu XL XR Hb HXL HXR)
        as (n1 & Hn1 & HR1).
      rewrite <- (bcanon_bsemX lo tbl blks c' nu XL XR Hraw Hb) in HR1.
      split; [exact Hende|].
      exists (n1 + n2)%nat. split.
      * exact (Reach_compose _ _ _ _ _ _ _ _ HR1 HR2).
      * intro; lia.
Qed.

(** ** Rule validation (with rule-in-rule application, one level) *)

Definition bruleBlkP_check (tm : TM) (tbl : BTbl)
    (blks : list (nat * list Sym)) (cfuel fuel : nat)
    (prior : list (BRuleP * list Tr)) (r : BRuleP) : option (list Tr) :=
  match breplayKP tm tbl blks (brule_lbsP r) cfuel prior
          (fun c => bscfg_eqb c (brulep_end_cfg r)) (brp_pfx r)
          fuel false (brulep_start_cfg r) with
  | Some (_, F) => Some F
  | None => None
  end.

Lemma bruleBlkP_check_sound : forall tm tbl blks cfuel fuel prior r F,
  raw_ok tbl ->
  (forall r' F', In (r', F') prior -> brule_semP tm tbl r' F') ->
  bruleBlkP_check tm tbl blks cfuel fuel prior r = Some F ->
  brule_semP tm tbl r F.
Proof.
  intros tm tbl blks cfuel fuel prior r F Hraw Hprior H u Hu YL YR HYL HYR.
  unfold bruleBlkP_check in H.
  destruct (breplayKP tm tbl blks (brule_lbsP r) cfuel prior
              (fun c => bscfg_eqb c (brulep_end_cfg r)) (brp_pfx r)
              fuel false (brulep_start_cfg r)) as [[cend F']|] eqn:Hrep;
    [|discriminate].
  injection H as <-.
  destruct (breplayKP_sound tm tbl blks (brule_lbsP r) cfuel prior _
              (brp_pfx r) fuel false
              (brulep_start_cfg r) cend F' Hraw Hrep u YL YR Hu HYL HYR
              (fun r0 Fr c1 c2 Hin Happ =>
                 ruleBlkPfx_apply_sound tm tbl (brule_lbsP r) r0 Fr c1 c2
                   (brp_pfx r) Hraw Happ (Hprior r0 Fr Hin) u Hu YL YR
                   HYL HYR))
    as (Hend & n & HR & Hpos).
  exists n. split; [apply Hpos; reflexivity|].
  rewrite <- (bscfg_eqb_bsemX tbl cend (brulep_end_cfg r) u YL YR Hend).
  exact HR.
Qed.

Fixpoint check_rulesBlkP_aux (tm : TM) (tbl : BTbl)
    (blks : list (nat * list Sym)) (cfuel fuel : nat)
    (acc : list (BRuleP * list Tr)) (rules : list BRuleP)
  : option (list (BRuleP * list Tr)) :=
  match rules with
  | [] => Some acc
  | r :: rest =>
      match bruleBlkP_check tm tbl blks cfuel fuel acc r with
      | Some F =>
          check_rulesBlkP_aux tm tbl blks cfuel fuel (acc ++ [(r, F)]) rest
      | None => None
      end
  end.

Definition check_rulesBlkP (tm : TM) (tbl : BTbl)
    (blks : list (nat * list Sym)) (cfuel fuel : nat) (rules : list BRuleP)
  : option (list (BRuleP * list Tr)) :=
  check_rulesBlkP_aux tm tbl blks cfuel fuel [] rules.

Lemma check_rulesBlkP_aux_sound : forall tm tbl blks cfuel fuel rules acc
                                         vrules,
  raw_ok tbl ->
  check_rulesBlkP_aux tm tbl blks cfuel fuel acc rules = Some vrules ->
  (forall r F, In (r, F) acc -> brule_semP tm tbl r F) ->
  forall r F, In (r, F) vrules -> brule_semP tm tbl r F.
Proof.
  intros tm tbl blks cfuel fuel rules. induction rules as [|r0 rest IH];
    intros acc vrules Hraw H Hacc; simpl in H.
  - injection H as <-. exact Hacc.
  - destruct (bruleBlkP_check tm tbl blks cfuel fuel acc r0) as [F0|] eqn:Hc;
      [|discriminate].
    apply (IH (acc ++ [(r0, F0)]) vrules Hraw H).
    intros r F Hin. apply in_app_or in Hin as [Hin | Hin].
    + apply Hacc; exact Hin.
    + destruct Hin as [Heq | []]. injection Heq as <- <-.
      exact (bruleBlkP_check_sound tm tbl blks cfuel fuel acc r0 F0 Hraw
               Hacc Hc).
Qed.

Theorem check_rulesBlkP_sound : forall tm tbl blks cfuel fuel rules vrules,
  raw_ok tbl ->
  check_rulesBlkP tm tbl blks cfuel fuel rules = Some vrules ->
  forall r F, In (r, F) vrules -> brule_semP tm tbl r F.
Proof.
  intros tm tbl blks cfuel fuel rules vrules Hraw H.
  apply (check_rulesBlkP_aux_sound tm tbl blks cfuel fuel rules [] vrules
           Hraw H).
  intros r F [].
Qed.
