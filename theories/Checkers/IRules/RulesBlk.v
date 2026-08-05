(** * IRules.RulesBlk: general-delta rule application for BLOCK runs.

    A fork of [RulesK] whose configurations are [BCfg] (run symbols over
    [nat], [>= 2] a block id) denoted by [EngineK.bdside tbl], and whose
    engine op is [EngineK.beng_step] (concrete step + chain hops + block
    hops + block peels).  The applier is symbol-matching, so its
    definition is [RulesK.ruleK_apply] transliterated to [nat] symbols;
    only the denotation lemmas are re-proved against [bdside tbl] (the
    syntax is unchanged, only the meaning of a run changed).  The
    binding-run search ([find_binding] and friends) is symbol-agnostic
    and reused verbatim from [RulesK].

    Everything is parametric in the untrusted block table [tbl] (with
    [raw_ok tbl]) and the association list [blks] feeding the hop's
    lookup; soundness holds for any table.

    [Print Assumptions ruleBlk_apply_sound] is
    [functional_extensionality_dep] only. *)

From Coq Require Import Arith ZArith Lia Bool List Setoid.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules RulesK EngineK.
Import ListNotations.
Open Scope Z_scope.

(** ** Block rules and their denotation *)

Definition BRRun : Set := (BSym * RCnt)%type.

Record BRule : Set := mkBRule {
  br_st : St;
  br_hs : Sym;
  br_L : list BRRun;
  br_R : list BRRun
}.

Fixpoint brstart (vid : nat) (rr : list BRRun) : list BRun :=
  match rr with
  | [] => []
  | (s, RC v) :: t => (s, econst v) :: brstart vid t
  | (s, RV _ _) :: t => (s, evar vid) :: brstart (S vid) t
  end.

Fixpoint brend (vid : nat) (rr : list BRRun) : list BRun :=
  match rr with
  | [] => []
  | (s, RC v) :: t => (s, econst v) :: brend vid t
  | (s, RV d _) :: t => (s, eaddc (evar vid) d) :: brend (S vid) t
  end.

Fixpoint brlbs (rr : list BRRun) : list Z :=
  match rr with
  | [] => []
  | (_, RC _) :: t => brlbs t
  | (_, RV _ lb) :: t => lb :: brlbs t
  end.

Definition brule_lbs (r : BRule) : list Z := brlbs (br_L r) ++ brlbs (br_R r).

Definition brule_start_cfg (r : BRule) : BCfg :=
  mkBCfg (br_st r) (br_hs r)
         (brstart 0 (br_L r))
         (brstart (length (brlbs (br_L r))) (br_R r)).

Definition brule_end_cfg (r : BRule) : BCfg :=
  mkBCfg (br_st r) (br_hs r)
         (brend 0 (br_L r))
         (brend (length (brlbs (br_L r))) (br_R r)).

(** The semantic content of a validated block rule, w.r.t. [bdside tbl]. *)
Definition brule_sem (tm : TM) (tbl : BTbl) (r : BRule) (F : list Tr) : Prop :=
  forall u : nat -> Z, bge (brule_lbs r) u ->
  exists n, (1 <= n)%nat /\
    Reach tm F n (bsem tbl u (brule_start_cfg r))
                 (bsem tbl u (brule_end_cfg r)).

Fixpoint bvvals (nu : nat -> Z) (j : Z) (rr : list BRRun) (mr : list BRun)
  : list Z :=
  match rr, mr with
  | (_, RC _) :: rt, _ :: mt => bvvals nu j rt mt
  | (_, RV d _) :: rt, (_, e) :: mt =>
      (eval nu e + d * j) :: bvvals nu j rt mt
  | _, _ => []
  end.

(** ** Configuration equality (decidable, denotation-sound) *)

Fixpoint bruns_eqb (a b : list BRun) : bool :=
  match a, b with
  | [], [] => true
  | (s, e) :: ta, (s', e') :: tb =>
      Nat.eqb s s' && eeqb e e' && bruns_eqb ta tb
  | _, _ => false
  end.

Lemma bruns_eqb_den : forall tbl a b nu,
  bruns_eqb a b = true -> bdside tbl nu a = bdside tbl nu b.
Proof.
  induction a as [|[s e] ta IH]; intros b nu H;
    destruct b as [|[s' e'] tb]; simpl in H; try discriminate.
  - reflexivity.
  - apply andb_prop in H as [H Ht].
    apply andb_prop in H as [Hs He].
    apply Nat.eqb_eq in Hs; subst s'.
    rewrite !bdside_cons, (cnt_eeqb e e' nu He), (IH tb nu Ht).
    reflexivity.
Qed.

Definition bscfg_eqb (a b : BCfg) : bool :=
  st_eqb (b_st a) (b_st b) && sym_eqb (b_hs a) (b_hs b) &&
  bruns_eqb (b_L a) (b_L b) && bruns_eqb (b_R a) (b_R b).

Lemma bscfg_eqb_bsem : forall tbl a b nu,
  bscfg_eqb a b = true -> bsem tbl nu a = bsem tbl nu b.
Proof.
  intros tbl a b nu H.
  apply andb_prop in H as [H HR].
  apply andb_prop in H as [H HL].
  apply andb_prop in H as [Hst Hhs].
  apply st_eqb_spec in Hst. apply sym_eqb_spec in Hhs.
  unfold bsem, bdcfg.
  rewrite Hst, Hhs, (bruns_eqb_den _ _ _ nu HL), (bruns_eqb_den _ _ _ nu HR).
  reflexivity.
Qed.

(** ** The general-delta per-side rewrite (symbol-matching on [nat]) *)

Fixpoint appBlk_side (lo : list Z) (Rex : Expr) (rr : list BRRun)
    (mr : list BRun) : option (list BRun) :=
  match rr, mr with
  | [], [] => Some []
  | (s, RC v) :: rt, (s', e) :: mt =>
      if Nat.eqb s s' && eeqb e (econst v)
      then option_map (cons (s', e)) (appBlk_side lo Rex rt mt)
      else None
  | (s, RV d lb) :: rt, (s', e) :: mt =>
      if Nat.eqb s s' && expr_ge lo e lb then
        if 0 <=? d then
          option_map (cons (s', eaddmul e d Rex)) (appBlk_side lo Rex rt mt)
        else if expr_ge lo (eaddmul e d Rex) (lb + d) then
          if eeqb (eaddmul e d Rex) (econst 0)
          then appBlk_side lo Rex rt mt
          else option_map (cons (s', eaddmul e d Rex))
                          (appBlk_side lo Rex rt mt)
        else None
      else None
  | _, _ => None
  end.

Fixpoint decs_side_blk (rr : list BRRun) (mr : list BRun)
  : list (Z * Z * Expr) :=
  match rr, mr with
  | (_, RV d lb) :: rt, (_, e) :: mt =>
      if d <=? -1 then (d, lb, e) :: decs_side_blk rt mt else decs_side_blk rt mt
  | _ :: rt, _ :: mt => decs_side_blk rt mt
  | _, _ => []
  end.

Definition ruleBlk_apply (lo : list Z) (r : BRule) (c : BCfg)
  : option BCfg :=
  if st_eqb (b_st c) (br_st r) && sym_eqb (b_hs c) (br_hs r) then
    let decs := decs_side_blk (br_L r) (b_L c) ++ decs_side_blk (br_R r) (b_R c) in
    match find_binding lo decs decs with
    | None => None
    | Some Rex =>
        if expr_ge lo Rex 1 then
          match appBlk_side lo Rex (br_L r) (b_L c),
                appBlk_side lo Rex (br_R r) (b_R c) with
          | Some outL, Some outR =>
              match bmerge_adj lo outL, bmerge_adj lo outR with
              | Some mL, Some mR =>
                  Some (mkBCfg (b_st c) (b_hs c)
                               (btrim_blanks mL) (btrim_blanks mR))
              | _, _ => None
              end
          | _, _ => None
          end
        else None
    end
  else None.

(** ** [appBlk_side] inversion (mirror [RulesK.appK_side_cons_inv]) *)

Lemma appBlk_side_cons_inv : forall lo Rex s rc rt s' e mt out,
  appBlk_side lo Rex ((s, rc) :: rt) ((s', e) :: mt) = Some out ->
  s = s' /\
  match rc with
  | RC v =>
      eeqb e (econst v) = true /\
      exists o, appBlk_side lo Rex rt mt = Some o /\ out = (s', e) :: o
  | RV d lb =>
      expr_ge lo e lb = true /\
      exists o, appBlk_side lo Rex rt mt = Some o /\
      ((0 <= d /\ out = (s', eaddmul e d Rex) :: o) \/
       (d < 0 /\ expr_ge lo (eaddmul e d Rex) (lb + d) = true /\
        ((eeqb (eaddmul e d Rex) (econst 0) = true /\ out = o) \/
         (eeqb (eaddmul e d Rex) (econst 0) = false /\
          out = (s', eaddmul e d Rex) :: o))))
  end.
Proof.
  intros lo Rex s rc rt s' e mt out H.
  destruct rc as [v | d lb]; cbn [appBlk_side] in H.
  - destruct (Nat.eqb s s') eqn:Hs; cbn beta iota in H; [|discriminate].
    apply Nat.eqb_eq in Hs.
    destruct (eeqb e (econst v)) eqn:He; cbn beta iota in H; [|discriminate].
    destruct (appBlk_side lo Rex rt mt) as [o|] eqn:Ha; cbn beta iota in H;
      [|discriminate].
    injection H as <-. split; [auto|]. split; [auto|]. eauto.
  - destruct (Nat.eqb s s') eqn:Hs; cbn beta iota in H; [|discriminate].
    apply Nat.eqb_eq in Hs.
    destruct (expr_ge lo e lb) eqn:Hge; cbn beta iota in H; [|discriminate].
    split; [auto|]. split; [auto|].
    destruct (0 <=? d) eqn:Hd.
    + apply Z.leb_le in Hd.
      destruct (appBlk_side lo Rex rt mt) as [o|] eqn:Ha; cbn beta iota in H;
        [|discriminate].
      injection H as <-. exists o. split; [auto|]. left. auto.
    + apply Z.leb_gt in Hd.
      destruct (expr_ge lo (eaddmul e d Rex) (lb + d)) eqn:Hsv;
        cbn beta iota in H; [|discriminate].
      destruct (eeqb (eaddmul e d Rex) (econst 0)) eqn:Hz;
        cbn beta iota in H.
      * exists out. split; [auto|]. right. split; [lia|]. split; [auto|].
        left. auto.
      * destruct (appBlk_side lo Rex rt mt) as [o|] eqn:Ha; cbn beta iota in H;
          [|discriminate].
        injection H as <-. exists o. split; [auto|].
        right. split; [lia|]. split; [auto|]. right. auto.
Qed.

Lemma appBlk_side_vlen : forall lo Rex rr mr out nu j,
  appBlk_side lo Rex rr mr = Some out ->
  length (bvvals nu j rr mr) = length (brlbs rr).
Proof.
  induction rr as [|[s rc] rt IH]; intros mr out nu j H.
  - destruct mr; [reflexivity|]. simpl in H. discriminate.
  - destruct mr as [|[s' e] mt].
    + destruct rc; simpl in H; discriminate.
    + destruct (appBlk_side_cons_inv _ _ _ _ _ _ _ _ _ H) as [Hs Hrest].
      destruct rc as [v | d lb]; simpl.
      * destruct Hrest as (_ & o & Ha & _). eapply IH; eauto.
      * destruct Hrest as (_ & o & Ha & _).
        simpl. f_equal. eapply IH; eauto.
Qed.

(** ** Denotation lemmas (mirror [RulesK.appK_side_den*] against [bdside]) *)

Lemma bdside_ext : forall tbl rs f g,
  (forall j, f j = g j) -> bdside tbl f rs = bdside tbl g rs.
Proof.
  induction rs as [|[s e] t IH]; intros f g H; [reflexivity|].
  rewrite !bdside_cons, (cnt_ext e f g H), (IH f g H). reflexivity.
Qed.
Lemma appBlk_side_den0 : forall tbl lo Rex rr mr out nu,
  appBlk_side lo Rex rr mr = Some out ->
  forall pre ext,
  bdside tbl (fun i => nth i (pre ++ bvvals nu 0 rr mr ++ ext) 1)
        (brstart (length pre) rr)
  = bdside tbl nu mr.
Proof.
  induction rr as [|[s rc] rt IH]; intros mr out nu H pre ext.
  - destruct mr; [reflexivity | simpl in H; discriminate].
  - destruct mr as [|[s' e] mt];
      [destruct rc; simpl in H; discriminate|].
    destruct (appBlk_side_cons_inv _ _ _ _ _ _ _ _ _ H) as [Hs Hrest].
    subst s'.
    destruct rc as [v | d lb]; simpl bvvals; simpl brstart;
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
                                     ++ bvvals nu 0 rt mt ++ ext) 1)|].
        { intro i. f_equal. rewrite <- app_assoc. reflexivity. }
        replace (S (length pre))
          with (length (pre ++ [eval nu e + d * 0]))
          by (rewrite app_length; simpl; lia).
        eapply IH; eauto.
Qed.

Lemma appBlk_side_denS : forall tbl lo Rex rr mr out nu j,
  appBlk_side lo Rex rr mr = Some out ->
  forall pre pre' ext ext', length pre = length pre' ->
  bdside tbl (fun i => nth i (pre ++ bvvals nu j rr mr ++ ext) 1)
        (brend (length pre) rr)
  = bdside tbl (fun i => nth i (pre' ++ bvvals nu (j + 1) rr mr ++ ext') 1)
          (brstart (length pre') rr).
Proof.
  induction rr as [|[s rc] rt IH]; intros mr out nu j H pre pre' ext
    ext' Hlen.
  - destruct mr; [reflexivity | simpl in H; discriminate].
  - destruct mr as [|[s' e] mt];
      [destruct rc; simpl in H; discriminate|].
    destruct (appBlk_side_cons_inv _ _ _ _ _ _ _ _ _ H) as [Hs Hrest].
    subst s'.
    destruct rc as [v | d lb]; simpl bvvals; simpl brstart; simpl brend;
      rewrite !bdside_cons.
    + destruct Hrest as (_ & o & Ha & _). f_equal. eapply IH; eauto.
    + destruct Hrest as (_ & o & Ha & _).
      f_equal.
      * f_equal. unfold cnt.
        rewrite eval_eaddc, eval_evar, eval_evar, !nth_mid2. f_equal. lia.
      * etransitivity;
          [apply bdside_ext with
             (g := fun i => nth i ((pre ++ [eval nu e + d * j])
                                     ++ bvvals nu j rt mt ++ ext) 1)|].
        { intro i. f_equal. rewrite <- app_assoc. reflexivity. }
        etransitivity;
          [|apply bdside_ext with
              (f := fun i => nth i ((pre' ++ [eval nu e + d * (j + 1)])
                                      ++ bvvals nu (j + 1) rt mt
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
Qed.

Lemma appBlk_side_denR : forall tbl lo Rex rr mr out nu,
  appBlk_side lo Rex rr mr = Some out ->
  forall pre ext,
  bdside tbl (fun i => nth i (pre ++ bvvals nu (eval nu Rex) rr mr ++ ext) 1)
        (brstart (length pre) rr)
  = bdside tbl nu out.
Proof.
  induction rr as [|[s rc] rt IH]; intros mr out nu H pre ext.
  - destruct mr; simpl in H; [injection H as <-; reflexivity | discriminate].
  - destruct mr as [|[s' e] mt];
      [destruct rc; simpl in H; discriminate|].
    destruct (appBlk_side_cons_inv _ _ _ _ _ _ _ _ _ H) as [Hs Hrest].
    subst s'.
    destruct rc as [v | d lb]; simpl bvvals; simpl brstart;
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
                           :: bvvals nu (eval nu Rex) rt mt) ++ ext) 1
              = eval nu e + d * eval nu Rex) by apply nth_mid2.
      assert (Htail : bdside tbl
          (fun i => nth i (pre ++ ((eval nu e + d * eval nu Rex)
                    :: bvvals nu (eval nu Rex) rt mt) ++ ext) 1)
          (brstart (S (length pre)) rt) = bdside tbl nu o).
      { etransitivity;
          [apply bdside_ext with
             (g := fun i => nth i ((pre ++ [eval nu e + d * eval nu Rex])
                                     ++ bvvals nu (eval nu Rex) rt mt
                                     ++ ext) 1)|].
        { intro i. f_equal. rewrite <- app_assoc. reflexivity. }
        replace (S (length pre))
          with (length (pre ++ [eval nu e + d * eval nu Rex]))
          by (rewrite app_length; simpl; lia).
        eapply IH; eauto. }
      destruct Hout as [(Hd & ->) | (Hd0 & Hsv & Hdrop)].
      * (* increment: step, keep *)
        rewrite bdside_cons. f_equal.
        -- f_equal. unfold cnt. rewrite eval_evar, Hhead, eval_eaddmul.
           reflexivity.
        -- exact Htail.
      * destruct Hdrop as [(Hz & ->) | (Hz & ->)].
        -- (* decrement drained to constant 0: dropped *)
           replace (cnt (fun i => nth i (pre ++ ((eval nu e + d * eval nu Rex)
                     :: bvvals nu (eval nu Rex) rt mt) ++ ext) 1)
                     (evar (length pre))) with 0%nat.
           2:{ unfold cnt. rewrite eval_evar, Hhead.
               pose proof (eeqb_eval _ _ nu Hz) as HzE.
               rewrite eval_eaddmul, eval_econst in HzE. lia. }
           simpl repeat. simpl app. exact Htail.
        -- (* decrement, nonzero: step, keep *)
           rewrite bdside_cons. f_equal.
           ++ f_equal. unfold cnt. rewrite eval_evar, Hhead, eval_eaddmul.
              reflexivity.
           ++ exact Htail.
Qed.

Lemma appBlk_side_bge : forall lo Rex rr mr out nu j,
  appBlk_side lo Rex rr mr = Some out -> bge lo nu ->
  0 <= j -> j <= eval nu Rex - 1 ->
  forall i, nth i (brlbs rr) 0 <= nth i (bvvals nu j rr mr) 1.
Proof.
  induction rr as [|[s rc] rt IH]; intros mr out nu j H Hb Hj0 Hj1 i.
  - destruct mr; simpl in H; [|discriminate]. simpl. destruct i; simpl; lia.
  - destruct mr as [|[s' e] mt];
      [destruct rc; simpl in H; discriminate|].
    destruct (appBlk_side_cons_inv _ _ _ _ _ _ _ _ _ H) as [Hs Hrest].
    destruct rc as [v | d lb]; simpl.
    + destruct Hrest as (_ & o & Ha & _). eapply IH; eauto.
    + destruct Hrest as (Hge & o & Ha & Hout).
      destruct i as [|i']; simpl.
      * pose proof (expr_ge_sound lo e lb nu Hge Hb) as Hlbe.
        destruct Hout as [(Hd & _) | (Hd0 & Hsv & _)].
        -- nia.
        -- pose proof (expr_ge_sound lo _ _ nu Hsv Hb) as Hsurv.
           rewrite eval_eaddmul in Hsurv. nia.
      * eapply IH; eauto.
Qed.

Theorem ruleBlk_apply_sound : forall tm tbl lo r F c c',
  raw_ok tbl ->
  ruleBlk_apply lo r c = Some c' -> brule_sem tm tbl r F ->
  forall nu, bge lo nu ->
  exists n, (1 <= n)%nat /\ Reach tm F n (bsem tbl nu c) (bsem tbl nu c').
Proof.
  intros tm tbl lo r F c c' Hraw H Hsem nu Hb.
  unfold ruleBlk_apply in H.
  destruct (st_eqb (b_st c) (br_st r) && sym_eqb (b_hs c) (br_hs r))
    eqn:Hsh; [|discriminate].
  apply andb_prop in Hsh as [Hst Hhs].
  apply st_eqb_spec in Hst. apply sym_eqb_spec in Hhs.
  cbv zeta in H.
  destruct (find_binding lo
              (decs_side_blk (br_L r) (b_L c) ++ decs_side_blk (br_R r) (b_R c))
              (decs_side_blk (br_L r) (b_L c) ++ decs_side_blk (br_R r) (b_R c)))
    as [Rex|]; [|discriminate].
  destruct (expr_ge lo Rex 1) eqn:HR1; [|discriminate].
  destruct (appBlk_side lo Rex (br_L r) (b_L c)) as [outL|] eqn:HappL;
    [|discriminate].
  destruct (appBlk_side lo Rex (br_R r) (b_R c)) as [outR|] eqn:HappR;
    [|discriminate].
  destruct (bmerge_adj lo outL) as [mL|] eqn:HmL; [|discriminate].
  destruct (bmerge_adj lo outR) as [mR|] eqn:HmR; [|discriminate].
  injection H as <-.
  pose proof (expr_ge_sound lo Rex 1 nu HR1 Hb) as HrZ.
  pose (VL := fun j => bvvals nu j (br_L r) (b_L c)).
  pose (VR := fun j => bvvals nu j (br_R r) (b_R c)).
  pose (U := fun j (i : nat) => nth i (VL j ++ VR j) 1).
  assert (HlenL : forall j, length (VL j) = length (brlbs (br_L r)))
    by (intro j; eapply appBlk_side_vlen; eauto).
  assert (HL0 : bdside tbl (U 0) (brstart 0 (br_L r)) = bdside tbl nu (b_L c))
    by exact (appBlk_side_den0 _ _ _ _ _ _ _ HappL [] (VR 0)).
  assert (HR0 : bdside tbl (U 0) (brstart (length (brlbs (br_L r))) (br_R r))
                = bdside tbl nu (b_R c)).
  { etransitivity;
      [apply bdside_ext with (g := fun i => nth i (VL 0 ++ VR 0 ++ []) 1)|].
    { intro i. f_equal. rewrite app_nil_r. reflexivity. }
    rewrite <- (HlenL 0).
    exact (appBlk_side_den0 _ _ _ _ _ _ _ HappR (VL 0) []). }
  assert (Claim0 : bsem tbl nu c = bsem tbl (U 0) (brule_start_cfg r)).
  { unfold bsem, bdcfg, brule_start_cfg.
    cbn [b_st b_hs b_L b_R].
    rewrite Hst, Hhs, HL0, HR0. reflexivity. }
  assert (ClaimS : forall j,
    bsem tbl (U j) (brule_end_cfg r) = bsem tbl (U (j + 1)) (brule_start_cfg r)).
  { intro j.
    assert (EL : bdside tbl (U j) (brend 0 (br_L r))
                 = bdside tbl (U (j + 1)) (brstart 0 (br_L r)))
      by exact (appBlk_side_denS _ _ _ _ _ _ _ j HappL [] [] (VR j)
                  (VR (j + 1)) eq_refl).
    assert (ER : bdside tbl (U j) (brend (length (brlbs (br_L r))) (br_R r))
                 = bdside tbl (U (j + 1))
                     (brstart (length (brlbs (br_L r))) (br_R r))).
    { etransitivity;
        [apply bdside_ext with (g := fun i => nth i (VL j ++ VR j ++ []) 1)|].
      { intro i. f_equal. rewrite app_nil_r. reflexivity. }
      etransitivity;
        [|apply bdside_ext with
            (f := fun i => nth i (VL (j + 1) ++ VR (j + 1) ++ []) 1)].
      2:{ intro i. f_equal. rewrite app_nil_r. reflexivity. }
      rewrite <- (HlenL j) at 1.
      rewrite <- (HlenL (j + 1)).
      apply (appBlk_side_denS tbl lo Rex (br_R r) (b_R c) outR nu j HappR
               (VL j) (VL (j + 1)) [] []).
      rewrite !HlenL. reflexivity. }
    unfold bsem, bdcfg, brule_end_cfg, brule_start_cfg.
    cbn [b_st b_hs b_L b_R].
    rewrite EL, ER. reflexivity. }
  assert (ClaimR : bsem tbl (U (eval nu Rex)) (brule_start_cfg r)
                   = bsem tbl nu (mkBCfg (b_st c) (b_hs c) outL outR)).
  { assert (EL : bdside tbl (U (eval nu Rex)) (brstart 0 (br_L r))
                 = bdside tbl nu outL)
      by exact (appBlk_side_denR _ _ _ _ _ _ _ HappL [] (VR (eval nu Rex))).
    assert (ER : bdside tbl (U (eval nu Rex))
                   (brstart (length (brlbs (br_L r))) (br_R r))
                 = bdside tbl nu outR).
    { etransitivity;
        [apply bdside_ext with
           (g := fun i => nth i (VL (eval nu Rex)
                                   ++ VR (eval nu Rex) ++ []) 1)|].
      { intro i. f_equal. rewrite app_nil_r. reflexivity. }
      rewrite <- (HlenL (eval nu Rex)).
      exact (appBlk_side_denR _ _ _ _ _ _ _ HappR (VL (eval nu Rex)) []). }
    unfold bsem, bdcfg, brule_start_cfg.
    cbn [b_st b_hs b_L b_R].
    rewrite Hst, Hhs, EL, ER. reflexivity. }
  assert (Hbge : forall j, 0 <= j -> j <= eval nu Rex - 1 ->
                 bge (brule_lbs r) (U j)).
  { intros j Hj0 Hj1 i.
    unfold brule_lbs.
    apply nth_app_le.
    - symmetry. apply HlenL.
    - intro i'. eapply appBlk_side_bge; eauto.
    - intro i'. eapply appBlk_side_bge; eauto. }
  assert (Hiter : forall m, (1 <= m)%nat -> Z.of_nat m <= eval nu Rex ->
    exists n, (1 <= n)%nat /\
      Reach tm F n (bsem tbl (U 0) (brule_start_cfg r))
                   (bsem tbl (U (Z.of_nat m)) (brule_start_cfg r))).
  { induction m as [|m IHm]; intros Hm1 Hmr; [lia|].
    destruct m as [|m'].
    - destruct (Hsem (U 0) (Hbge 0 ltac:(lia) ltac:(lia)))
        as (n & Hn & HRch).
      exists n. split; [exact Hn|].
      setoid_rewrite (ClaimS 0) in HRch. exact HRch.
    - assert (Hmr' : Z.of_nat (S m') <= eval nu Rex) by lia.
      destruct (IHm ltac:(lia) Hmr') as (n1 & Hn1 & HRch1).
      destruct (Hsem (U (Z.of_nat (S m')))
                  (Hbge (Z.of_nat (S m')) ltac:(lia) ltac:(lia)))
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
  assert (Hreb : bsem tbl nu (mkBCfg (b_st c) (b_hs c)
                            (btrim_blanks mL) (btrim_blanks mR))
                 = bsem tbl nu (mkBCfg (b_st c) (b_hs c) outL outR)).
  { unfold bsem, bdcfg.
    cbn [b_st b_hs b_L b_R].
    rewrite !lift_cc, !(btrim_blanks_den tbl _ nu Hraw).
    rewrite (bmerge_adj_den tbl lo outL mL nu HmL Hb).
    rewrite (bmerge_adj_den tbl lo outR mR nu HmR Hb). reflexivity. }
  setoid_rewrite Hreb.
  exact HRch.
Qed.


(** ** Cell-stream end equality (sound, incomplete)

    A sound-but-simpler alternative to the C verifier's periodic
    stream walk that covers the block track's end-match need: expand
    every CONSTANT-count block run to its cells and coalesce adjacent
    equal-symbol runs; two run lists denoting the same cells then agree
    structurally.  Sound: [bstreams_eq] true implies equal [bdside]. *)

Definition eis_const (e : Expr) : bool := cf_zeros (e_cf e).

Lemma eis_const_cnt : forall e nu1 nu2,
  eis_const e = true -> cnt nu1 e = cnt nu2 e.
Proof.
  intros e nu1 nu2 H. unfold cnt, eval.
  rewrite !(cf_zeros_dot _ _ 0 H). reflexivity.
Qed.

Definition blk_expand (tbl : BTbl) (s : BSym) (n : nat) : list BRun :=
  concat (repeat (peel_cells tbl s) n).

Lemma bdside_blk_expand : forall tbl nu s n,
  raw_ok tbl -> bdside tbl nu (blk_expand tbl s n) = nreps (tbl s) n.
Proof.
  intros tbl nu s n Hraw. unfold blk_expand.
  induction n as [|n IH]; [reflexivity|].
  simpl repeat. cbn [concat].
  rewrite bdside_app, (bdside_peel_cells tbl nu s Hraw), IH, nreps_S.
  reflexivity.
Qed.

Fixpoint bexpand_const (tbl : BTbl) (rs : list BRun) : list BRun :=
  match rs with
  | [] => []
  | (s, e) :: t =>
      if (2 <=? length (tbl s))%nat && eis_const e
      then blk_expand tbl s (Z.to_nat (e_c0 e)) ++ bexpand_const tbl t
      else (s, e) :: bexpand_const tbl t
  end.

Lemma bexpand_const_den : forall tbl rs nu,
  raw_ok tbl -> bdside tbl nu (bexpand_const tbl rs) = bdside tbl nu rs.
Proof.
  induction rs as [|[s e] t IH]; intros nu Hraw; [reflexivity|].
  cbn [bexpand_const].
  destruct ((2 <=? length (tbl s))%nat && eis_const e) eqn:Hc.
  - apply andb_prop in Hc as [_ Hconst].
    rewrite bdside_app, (bdside_blk_expand tbl nu s _ Hraw), IH by assumption.
    rewrite bdside_cons. f_equal. f_equal.
    unfold cnt. f_equal. unfold eval.
    rewrite (cf_zeros_dot _ nu 0 Hconst). lia.
  - rewrite !bdside_cons, IH by assumption. reflexivity.
Qed.

Definition bcanon_rle (tbl : BTbl) (lo : list Z) (rs : list BRun)
  : list BRun :=
  match bmerge_adj lo (bexpand_const tbl rs) with
  | Some r => r
  | None => bexpand_const tbl rs
  end.

Lemma bcanon_rle_den : forall tbl lo rs nu,
  raw_ok tbl -> bge lo nu ->
  bdside tbl nu (bcanon_rle tbl lo rs) = bdside tbl nu rs.
Proof.
  intros tbl lo rs nu Hraw Hb. unfold bcanon_rle.
  destruct (bmerge_adj lo (bexpand_const tbl rs)) as [r|] eqn:Hm.
  - rewrite (bmerge_adj_den tbl lo _ r nu Hm Hb), bexpand_const_den by assumption.
    reflexivity.
  - rewrite bexpand_const_den by assumption. reflexivity.
Qed.

Definition bstreams_eq (tbl : BTbl) (lo : list Z) (xa xb : list BRun) : bool :=
  bruns_eqb (bcanon_rle tbl lo xa) (bcanon_rle tbl lo xb).

Lemma bstreams_eq_sound : forall tbl lo xa xb nu,
  raw_ok tbl -> bge lo nu ->
  bstreams_eq tbl lo xa xb = true ->
  bdside tbl nu xa = bdside tbl nu xb.
Proof.
  intros tbl lo xa xb nu Hraw Hb H. unfold bstreams_eq in H.
  rewrite <- (bcanon_rle_den tbl lo xa nu Hraw Hb).
  rewrite <- (bcanon_rle_den tbl lo xb nu Hraw Hb).
  apply (bruns_eqb_den tbl _ _ nu H).
Qed.

(** End-match: strict, or provable cell-stream equality of both sides. *)
Definition bend_eqb (tbl : BTbl) (lo : list Z) (c want : BCfg) : bool :=
  bscfg_eqb c want ||
  (st_eqb (b_st c) (b_st want) && sym_eqb (b_hs c) (b_hs want) &&
   bstreams_eq tbl lo (b_L c) (b_L want) &&
   bstreams_eq tbl lo (b_R c) (b_R want)).

Lemma bend_eqb_bsem : forall tbl lo c want nu,
  raw_ok tbl -> bge lo nu ->
  bend_eqb tbl lo c want = true -> bsem tbl nu c = bsem tbl nu want.
Proof.
  intros tbl lo c want nu Hraw Hb H. unfold bend_eqb in H.
  apply orb_prop in H as [H | H].
  - apply (bscfg_eqb_bsem tbl _ _ nu H).
  - apply andb_prop in H as [H HR].
    apply andb_prop in H as [H HL].
    apply andb_prop in H as [Hst Hhs].
    apply st_eqb_spec in Hst. apply sym_eqb_spec in Hhs.
    unfold bsem, bdcfg. rewrite Hst, Hhs.
    rewrite (bstreams_eq_sound tbl lo _ _ nu Hraw Hb HL).
    rewrite (bstreams_eq_sound tbl lo _ _ nu Hraw Hb HR). reflexivity.
Qed.

(** ** Canonical re-blocking (UNTRUSTED candidate, verified by bstreams)

    Mirror of the C verifier's iv_reblock_side: re-encode the concrete
    single-cell constant near-prefix into block runs via the prover's
    greedy factorisation.  The result is UNTRUSTED -- it is accepted only
    after [bstreams_eq] re-verifies it denotes the same cells, so
    soundness never depends on the factorisation being correct. *)

(* leading copies of word [w] (length L>=1) in [buf] *)
Fixpoint lead_reps (w buf : list Sym) (L fuel : nat) : nat :=
  match fuel with
  | O => O
  | S fu =>
      if (L <=? length buf)%nat && lsym_eqb w (firstn L buf)
      then S (lead_reps w (skipn L buf) L fu)
      else O
  end.

(* try block lengths L=2..8 at the front of buf; return (blockid, L, reps)
   for the first L giving a primitive word repeating with reps*L >= 16 *)
Fixpoint benc_try (blks : list (nat * list Sym)) (buf : list Sym)
    (L : nat) : option (nat * nat * nat) :=
  match L with
  | O => None
  | S L' =>
      match benc_try blks buf L' with
      | Some r => Some r        (* smaller L already found: keep it *)
      | None =>
          if (2 <=? L)%nat && (L + L <=? length buf)%nat &&
             (prim_root_len (firstn L buf) =? L)%nat
          then
            let w := firstn L buf in
            let reps := lead_reps w buf L (length buf) in
            if (2 <=? reps)%nat && (16 <=? reps * L)%nat
            then let id := blk_find blks w in
                 if (2 <=? id)%nat then Some (id, L, reps) else None
            else None
          else None
      end
  end.

Fixpoint benc_side (blks : list (nat * list Sym)) (buf : list Sym)
    (fuel : nat) : list BRun :=
  match fuel with
  | O => []
  | S fu =>
      match buf with
      | [] => []
      | s :: _ =>
          match benc_try blks buf 8 with
          | Some (id, L, reps) =>
              (id, econst (Z.of_nat reps)) :: benc_side blks (skipn (reps * L) buf) fu
          | None =>
              let r := lead_reps [s] buf 1 (length buf) in
              (sym_to_nat s, econst (Z.of_nat r)) :: benc_side blks (skipn r buf) fu
          end
      end
  end.

(* split off the maximal constant single-cell prefix as concrete cells *)
Fixpoint bconst_prefix (tbl : BTbl) (rs : list BRun) : (list Sym * list BRun) :=
  match rs with
  | (s, e) :: t =>
      if (length (tbl s) =? 1)%nat && eis_const e && (0 <=? e_c0 e) then
        let '(cells, rest) := bconst_prefix tbl t in
        (repeat (bcell tbl s) (Z.to_nat (e_c0 e)) ++ cells, rest)
      else ([], rs)
  | [] => ([], [])
  end.

Definition breblock_side (tbl : BTbl) (blks : list (nat * list Sym))
    (lo : list Z) (rs : list BRun) : list BRun :=
  let '(cells, rest) := bconst_prefix tbl rs in
  if (16 <=? length cells)%nat then
    let cand := benc_side blks cells (length cells) ++ rest in
    if bstreams_eq tbl lo cand rs then cand else rs
  else rs.

Lemma breblock_side_den : forall tbl blks lo rs nu,
  raw_ok tbl -> bge lo nu ->
  bdside tbl nu (breblock_side tbl blks lo rs) = bdside tbl nu rs.
Proof.
  intros tbl blks lo rs nu Hraw Hb. unfold breblock_side.
  destruct (bconst_prefix tbl rs) as [cells rest] eqn:Hpre.
  destruct (16 <=? length cells)%nat; [|reflexivity].
  destruct (bstreams_eq tbl lo (benc_side blks cells (length cells) ++ rest) rs)
    eqn:Hv; [|reflexivity].
  exact (bstreams_eq_sound tbl lo _ _ nu Hraw Hb Hv).
Qed.

(** ** Whole-copy absorb (proven denotation-preserving)

    Fold a complete concrete single-cell copy of block [B] sitting
    immediately before the first block run [(B, e)] into that run,
    yielding [(B, e+1)] -- mirror of the C verifier's whole-copy
    [iv_absorb_side].  Proven denotation-preserving directly (the copy's
    cells re-express one more period of the block, using [expr_ge lo e 0]
    so the count increments soundly for every [nu >= lo]). *)

(** ** Partial (symbolic-remainder) absorb

    The C verifier's [iv_absorb_side] also folds a block copy whose
    leading cells come from only PART of a single-cell run's count
    (const [cv > t] or symbolic with [iex_min >= need+2]): it takes
    [need+1] cells to finish the copy and leaves that run DECREMENTED,
    rather than requiring the whole copy to sit as separate count-1 runs.
    We model this uniformly and soundly: propose an UNTRUSTED leftover
    [new_acc] (peel exactly [L = length (tbl s)] concrete cells off the
    right of [acc], decrementing the leftmost touched single-cell run),
    then re-verify [bstreams_eq tbl lo acc (new_acc ++ peel_cells tbl s)]
    -- i.e. [acc] denotes [new_acc] followed by exactly one block copy.
    Soundness never depends on the peel being correct (a wrong [new_acc]
    just fails the re-check); the block-run count increment rides the
    same [expr_ge lo e 0] + [nreps_S] fold as the whole-copy case. *)

(* Untrusted: peel [budget] concrete cells off the FRONT of a reversed
   run list [rrs] (= the RIGHT end of [acc]), consuming single-cell
   constant runs; the leftmost touched run is decremented if only part
   of its cells are taken.  Returns the reversed leftover, or None. *)
Fixpoint bpeel_rev (tbl : BTbl) (budget : nat) (rrs : list BRun)
  : option (list BRun) :=
  match budget with
  | O => Some rrs
  | S _ =>
      match rrs with
      | [] => None
      | (s, e) :: t =>
          if (length (tbl s) =? 1)%nat && eis_const e && (0 <=? e_c0 e) then
            let c := Z.to_nat (e_c0 e) in
            if (c <=? budget)%nat then bpeel_rev tbl (budget - c) t
            else Some ((s, eaddc e (- Z.of_nat budget)) :: t)
          else None
      end
  end.

Definition babsorb_partial (lo : list Z) (tbl : BTbl)
    (acc : list BRun) (s : BSym) (e : Expr) (rest : list BRun)
  : option (list BRun) :=
  match bpeel_rev tbl (length (tbl s)) (rev acc) with
  | Some rrleft =>
      let new_acc := rev rrleft in
      if expr_ge lo e 0 &&
         bstreams_eq tbl lo acc (new_acc ++ peel_cells tbl s)
      then Some (new_acc ++ (s, eaddc e 1) :: rest)
      else None
  | None => None
  end.

Fixpoint babsorb_go (lo : list Z) (tbl : BTbl) (acc rs : list BRun)
  : option (list BRun) :=
  match rs with
  | [] => None
  | (s, e) :: rest =>
      if (2 <=? length (tbl s))%nat then
        (if (length (tbl s) <=? length acc)%nat && expr_ge lo e 0 &&
            bruns_eqb (skipn (length acc - length (tbl s)) acc)
                      (peel_cells tbl s)
         then Some (firstn (length acc - length (tbl s)) acc
                    ++ (s, eaddc e 1) :: rest)
         else babsorb_partial lo tbl acc s e rest)
      else babsorb_go lo tbl (acc ++ [(s, e)]) rest
  end.

Lemma cnt_succ : forall nu e,
  0 <= eval nu e -> cnt nu (eaddc e 1) = S (cnt nu e).
Proof.
  intros nu e He. unfold cnt. rewrite eval_eaddc. lia.
Qed.

Lemma babsorb_partial_den : forall lo tbl acc s e rest rs' nu,
  raw_ok tbl -> bge lo nu ->
  babsorb_partial lo tbl acc s e rest = Some rs' ->
  bdside tbl nu rs' = bdside tbl nu (acc ++ (s, e) :: rest).
Proof.
  intros lo tbl acc s e rest rs' nu Hraw Hb H.
  unfold babsorb_partial in H.
  destruct (bpeel_rev tbl (length (tbl s)) (rev acc)) as [rrleft|] eqn:Hpeel;
    [|discriminate].
  set (new_acc := rev rrleft) in *.
  destruct (expr_ge lo e 0 &&
            bstreams_eq tbl lo acc (new_acc ++ peel_cells tbl s)) eqn:Hcond;
    [|discriminate].
  injection H as <-.
  apply andb_prop in Hcond as [Hge0 Hstr].
  assert (Hacc : bdside tbl nu acc = bdside tbl nu new_acc ++ tbl s).
  { rewrite (bstreams_eq_sound tbl lo acc (new_acc ++ peel_cells tbl s)
                              nu Hraw Hb Hstr).
    rewrite bdside_app, (bdside_peel_cells tbl nu s Hraw). reflexivity. }
  rewrite (bdside_app tbl nu new_acc), bdside_cons.
  rewrite (cnt_succ nu e (expr_ge_sound lo e 0 nu Hge0 Hb)), nreps_S.
  rewrite (bdside_app tbl nu acc), bdside_cons, Hacc.
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma babsorb_go_den : forall tbl lo rs acc rs' nu,
  raw_ok tbl -> bge lo nu ->
  babsorb_go lo tbl acc rs = Some rs' ->
  bdside tbl nu rs' = bdside tbl nu (acc ++ rs).
Proof.
  intros tbl lo rs. induction rs as [|[s e] rest IH];
    intros acc rs' nu Hraw Hb H; cbn [babsorb_go] in H; [discriminate|].
  destruct (2 <=? length (tbl s))%nat eqn:Hblk.
  - destruct ((length (tbl s) <=? length acc)%nat && expr_ge lo e 0 &&
              bruns_eqb (skipn (length acc - length (tbl s)) acc)
                        (peel_cells tbl s)) eqn:Hcond;
      [|exact (babsorb_partial_den lo tbl acc s e rest rs' nu Hraw Hb H)].
    injection H as <-.
    apply andb_prop in Hcond as [Hcond Hbr].
    apply andb_prop in Hcond as [Hlen Hge0].
    apply Nat.leb_le in Hlen.
    set (L := length (tbl s)) in *.
    (* the last L runs of acc denote one copy of the block's cells *)
    assert (Hacc : bdside tbl nu acc =
                   bdside tbl nu (firstn (length acc - L) acc) ++ tbl s).
    { transitivity (bdside tbl nu (firstn (length acc - L) acc
                                   ++ skipn (length acc - L) acc)).
      - rewrite firstn_skipn. reflexivity.
      - rewrite bdside_app. f_equal.
        rewrite (bruns_eqb_den tbl _ _ nu Hbr).
        apply (bdside_peel_cells tbl nu s Hraw). }
    rewrite (bdside_app tbl nu (firstn (length acc - L) acc)), bdside_cons.
    rewrite (cnt_succ nu e (expr_ge_sound lo e 0 nu Hge0 Hb)), nreps_S.
    rewrite (bdside_app tbl nu acc), bdside_cons, Hacc.
    rewrite <- !app_assoc. reflexivity.
  - specialize (IH (acc ++ [(s, e)]) rs' nu Hraw Hb H).
    rewrite IH, <- app_assoc. reflexivity.
Qed.

Fixpoint babsorb_iter (lo : list Z) (tbl : BTbl) (fuel : nat)
    (rs : list BRun) : list BRun :=
  match fuel with
  | O => rs
  | S fu =>
      match babsorb_go lo tbl [] rs with
      | Some rs' => babsorb_iter lo tbl fu rs'
      | None => rs
      end
  end.

Lemma babsorb_iter_den : forall tbl lo fuel rs nu,
  raw_ok tbl -> bge lo nu ->
  bdside tbl nu (babsorb_iter lo tbl fuel rs) = bdside tbl nu rs.
Proof.
  intros tbl lo fuel. induction fuel as [|fuel IH]; intros rs nu Hraw Hb;
    [reflexivity|].
  cbn [babsorb_iter].
  destruct (babsorb_go lo tbl [] rs) as [rs'|] eqn:Hgo; [|reflexivity].
  rewrite (IH rs' nu Hraw Hb).
  rewrite (babsorb_go_den tbl lo rs [] rs' nu Hraw Hb Hgo). reflexivity.
Qed.

(** ** The driver canonicalization: re-block then absorb, both sides *)

Definition bcanon_side (lo : list Z) (tbl : BTbl)
    (blks : list (nat * list Sym)) (rs : list BRun) : list BRun :=
  babsorb_iter lo tbl (length rs) (breblock_side tbl blks lo rs).

Lemma bcanon_side_den : forall lo tbl blks rs nu,
  raw_ok tbl -> bge lo nu ->
  bdside tbl nu (bcanon_side lo tbl blks rs) = bdside tbl nu rs.
Proof.
  intros lo tbl blks rs nu Hraw Hb. unfold bcanon_side.
  rewrite (babsorb_iter_den tbl lo _ _ nu Hraw Hb).
  apply (breblock_side_den tbl blks lo rs nu Hraw Hb).
Qed.

Definition bcanon (lo : list Z) (tbl : BTbl)
    (blks : list (nat * list Sym)) (c : BCfg) : BCfg :=
  mkBCfg (b_st c) (b_hs c)
         (bcanon_side lo tbl blks (b_L c))
         (bcanon_side lo tbl blks (b_R c)).

Lemma bcanon_bsem : forall lo tbl blks c nu,
  raw_ok tbl -> bge lo nu ->
  bsem tbl nu (bcanon lo tbl blks c) = bsem tbl nu c.
Proof.
  intros lo tbl blks c nu Hraw Hb. unfold bcanon, bsem, bdcfg.
  cbn [b_st b_hs b_L b_R].
  rewrite !(bcanon_side_den lo tbl blks _ nu Hraw Hb). reflexivity.
Qed.

(** ** The meta-cycle replay with the block engine

    A fork of [RulesK.replayK]: [try_rulesBlk] fires [ruleBlk_apply];
    the engine op is [beng_step] (block hops), parameterised by the
    table [tbl], the lookup list [blks], and a per-op cross fuel. *)

Fixpoint try_rulesBlk (lo : list Z) (rules : list (BRule * list Tr))
    (c : BCfg) : option (BCfg * list Tr) :=
  match rules with
  | [] => None
  | (r, F) :: rest =>
      match ruleBlk_apply lo r c with
      | Some c' => Some (c', F)
      | None => try_rulesBlk lo rest c
      end
  end.

Fixpoint breplayK (tm : TM) (tbl : BTbl) (blks : list (nat * list Sym))
    (lo : list Z) (cfuel : nat) (rules : list (BRule * list Tr))
    (endt : BCfg -> bool) (fuel : nat) (stepped : bool) (c : BCfg)
  : option (BCfg * list Tr) :=
  match fuel with
  | O => None
  | S fuel' =>
      if stepped && endt c then Some (c, [])
      else
        match try_rulesBlk lo rules c with
        | Some (c', F) =>
            match breplayK tm tbl blks lo cfuel rules endt fuel' stepped c' with
            | Some (cend, F') => Some (cend, tr_union F F')
            | None => None
            end
        | None =>
            match beng_step tm tbl blks lo cfuel c with
            | Some (c', F) =>
                match breplayK tm tbl blks lo cfuel rules endt fuel' true
                        (bcanon lo tbl blks c') with
                | Some (cend, F') => Some (cend, tr_union F F')
                | None => None
                end
            | None => None
            end
        end
  end.

Lemma breplayK_sound : forall tm tbl blks lo cfuel rules endt fuel stepped
                               c cend F,
  raw_ok tbl ->
  breplayK tm tbl blks lo cfuel rules endt fuel stepped c = Some (cend, F) ->
  forall nu, bge lo nu ->
  (forall r Fr c1 c2, In (r, Fr) rules -> ruleBlk_apply lo r c1 = Some c2 ->
     exists n, (1 <= n)%nat /\ Reach tm Fr n (bsem tbl nu c1) (bsem tbl nu c2)) ->
  endt cend = true /\
  exists n, Reach tm F n (bsem tbl nu c) (bsem tbl nu cend) /\
            (stepped = false -> (1 <= n)%nat).
Proof.
  intros tm tbl blks lo cfuel rules endt fuel.
  induction fuel as [|fuel IH]; intros stepped c cend F Hraw H nu Hb
    Happ; simpl in H; [discriminate|].
  destruct (stepped && endt c) eqn:Hend.
  - injection H as <- <-.
    apply andb_prop in Hend as [Hst Hendc].
    split; [exact Hendc|].
    exists O. split; [apply Reach_refl|].
    intro Hf; rewrite Hf in Hst; discriminate.
  - destruct (try_rulesBlk lo rules c) as [[c' Fr]|] eqn:Htry.
    + destruct (breplayK tm tbl blks lo cfuel rules endt fuel stepped c')
        as [[cend' F']|] eqn:Hrec; [|discriminate].
      injection H as <- <-.
      destruct (IH stepped c' cend' F' Hraw Hrec nu Hb Happ)
        as (Hende & n2 & HR2 & _).
      assert (Hget : exists r0, In (r0, Fr) rules /\
                     ruleBlk_apply lo r0 c = Some c').
      { clear -Htry. induction rules as [|[r0 F0] rest IHr];
          simpl in Htry; [discriminate|].
        destruct (ruleBlk_apply lo r0 c) eqn:Ha.
        - injection Htry as <- <-. exists r0. split; [left|]; auto.
        - destruct (IHr Htry) as (r1 & Hin & Ha1).
          exists r1. split; [right|]; assumption. }
      destruct Hget as (r0 & Hin & Ha).
      destruct (Happ r0 Fr c c' Hin Ha) as (n1 & Hn1 & HR1).
      split; [exact Hende|].
      exists (n1 + n2)%nat. split.
      * eapply (Reach_set _ _ (Fr ++ F'));
          [intro t; rewrite tr_union_in, in_app_iff; tauto|].
        exact (Reach_compose _ _ _ _ _ _ _ _ HR1 HR2).
      * intro; lia.
    + destruct (beng_step tm tbl blks lo cfuel c) as [[c' Fe]|] eqn:Hstep;
        [|discriminate].
      destruct (breplayK tm tbl blks lo cfuel rules endt fuel true
                  (bcanon lo tbl blks c'))
        as [[cend' F']|] eqn:Hrec; [|discriminate].
      injection H as <- <-.
      destruct (IH true (bcanon lo tbl blks c') cend' F' Hraw Hrec nu Hb Happ)
        as (Hende & n2 & HR2 & _).
      destruct (beng_step_sound tm tbl blks lo cfuel c c' Fe Hraw Hstep nu Hb)
        as (n1 & Hn1 & HR1).
      rewrite <- (bcanon_bsem lo tbl blks c' nu Hraw Hb) in HR1.
      split; [exact Hende|].
      exists (n1 + n2)%nat. split.
      * eapply (Reach_set _ _ (Fe ++ F'));
          [intro t; rewrite tr_union_in, in_app_iff; tauto|].
        exact (Reach_compose _ _ _ _ _ _ _ _ HR1 HR2).
      * intro; lia.
Qed.

(** ** Rule validation with rule-in-rule application (one level) *)

Definition bruleBlk_check (tm : TM) (tbl : BTbl)
    (blks : list (nat * list Sym)) (cfuel fuel : nat)
    (prior : list (BRule * list Tr)) (r : BRule) : option (list Tr) :=
  match breplayK tm tbl blks (brule_lbs r) cfuel prior
          (fun c => bscfg_eqb c (brule_end_cfg r))
          fuel false (brule_start_cfg r) with
  | Some (_, F) => Some F
  | None => None
  end.

Lemma bruleBlk_check_sound : forall tm tbl blks cfuel fuel prior r F,
  raw_ok tbl ->
  (forall r' F', In (r', F') prior -> brule_sem tm tbl r' F') ->
  bruleBlk_check tm tbl blks cfuel fuel prior r = Some F ->
  brule_sem tm tbl r F.
Proof.
  intros tm tbl blks cfuel fuel prior r F Hraw Hprior H u Hu.
  unfold bruleBlk_check in H.
  destruct (breplayK tm tbl blks (brule_lbs r) cfuel prior
              (fun c => bscfg_eqb c (brule_end_cfg r))
              fuel false (brule_start_cfg r)) as [[cend F']|] eqn:Hrep;
    [|discriminate].
  injection H as <-.
  destruct (breplayK_sound tm tbl blks (brule_lbs r) cfuel prior _ fuel false
              (brule_start_cfg r) cend F' Hraw Hrep u Hu
              (fun r0 Fr c1 c2 Hin Happ =>
                 ruleBlk_apply_sound tm tbl (brule_lbs r) r0 Fr c1 c2 Hraw Happ
                   (Hprior r0 Fr Hin) u Hu))
    as (Hend & n & HR & Hpos).
  exists n. split; [apply Hpos; reflexivity|].
  rewrite <- (bscfg_eqb_bsem tbl cend (brule_end_cfg r) u Hend). exact HR.
Qed.

Fixpoint check_rulesBlk_aux (tm : TM) (tbl : BTbl)
    (blks : list (nat * list Sym)) (cfuel fuel : nat)
    (acc : list (BRule * list Tr)) (rules : list BRule)
  : option (list (BRule * list Tr)) :=
  match rules with
  | [] => Some acc
  | r :: rest =>
      match bruleBlk_check tm tbl blks cfuel fuel acc r with
      | Some F => check_rulesBlk_aux tm tbl blks cfuel fuel (acc ++ [(r, F)]) rest
      | None => None
      end
  end.

Definition check_rulesBlk (tm : TM) (tbl : BTbl)
    (blks : list (nat * list Sym)) (cfuel fuel : nat) (rules : list BRule)
  : option (list (BRule * list Tr)) :=
  check_rulesBlk_aux tm tbl blks cfuel fuel [] rules.

Lemma check_rulesBlk_aux_sound : forall tm tbl blks cfuel fuel rules acc vrules,
  raw_ok tbl ->
  check_rulesBlk_aux tm tbl blks cfuel fuel acc rules = Some vrules ->
  (forall r F, In (r, F) acc -> brule_sem tm tbl r F) ->
  forall r F, In (r, F) vrules -> brule_sem tm tbl r F.
Proof.
  intros tm tbl blks cfuel fuel rules. induction rules as [|r0 rest IH];
    intros acc vrules Hraw H Hacc; simpl in H.
  - injection H as <-. exact Hacc.
  - destruct (bruleBlk_check tm tbl blks cfuel fuel acc r0) as [F0|] eqn:Hc;
      [|discriminate].
    apply (IH (acc ++ [(r0, F0)]) vrules Hraw H).
    intros r F Hin. apply in_app_or in Hin as [Hin | Hin].
    + apply Hacc; exact Hin.
    + destruct Hin as [Heq | []]. injection Heq as <- <-.
      exact (bruleBlk_check_sound tm tbl blks cfuel fuel acc r0 F0 Hraw Hacc Hc).
Qed.

Theorem check_rulesBlk_sound : forall tm tbl blks cfuel fuel rules vrules,
  raw_ok tbl ->
  check_rulesBlk tm tbl blks cfuel fuel rules = Some vrules ->
  forall r F, In (r, F) vrules -> brule_sem tm tbl r F.
Proof.
  intros tm tbl blks cfuel fuel rules vrules Hraw H.
  apply (check_rulesBlk_aux_sound tm tbl blks cfuel fuel rules [] vrules Hraw H).
  intros r F [].
Qed.
