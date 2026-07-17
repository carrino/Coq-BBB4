(** * IRules.RulesK: general step-size (multi-decrement) rule application.

    The v1 rule applier ([Rules.rule_apply]) fires a rule whose only
    decrementing run drains at step [d = -1] ([Rules.find_dec]
    hardcodes [d =? -1]).  This file generalises the applier to any
    negative constant delta, with the v3 binding-run semantics of BBB
    docs/irules2.md "Multi-decrement rules, general step sizes":

    application picks a *binding* run [j] (step [d_j = -delta_j])
    deterministically -- the first decrementing run, left side first,
    ascending index -- such that [d_j] divides [e_j - lb_j]
    coefficient-wise (so [R = (e_j - lb_j)/d_j + 1] is an exact affine
    expression), [lb_j >= d_j] (the drained run lands on
    [lb_j - d_j >= 0]), and every other decrementing run survives [R]
    rounds.

    The applier reuses the v1 rule type ([Rules.Rule] already carries a
    general [RV del lb]) and the whole denotation machinery
    ([Rules.rule_sem], [rstart]/[rend], [vvals], [scfg_eqb]); only the
    per-side rewrite [appK_side] and the count search [find_binding]
    are new.

    KEY soundness structure: [find_binding] is *untrusted*.  Whatever
    count [Rex] it returns, [ruleK_apply] guards [expr_ge lo Rex 1] and
    [appK_side] re-checks, at every decrementing run, that the run
    survives [R] rounds ([expr_ge lo (eaddmul e d Rex) (lb + d)] -- the
    run's minimum over the [R] rounds is its value in the last round).
    Those two facts make the [R]-fold application sound for ANY [Rex];
    the binding selection only has to PRODUCE the [Rex] that lands the
    drained run exactly (so the checker's end test matches).  The
    output is uniform: every variable run steps to [e + delta * Rex]
    and a decrementing run reaching the constant [0] is dropped
    (mirrors the drain-to-[lb-1] drop of the v1 applier: with
    [delta = -1] and the binding [Rex = e - lb + 1] one has
    [eaddmul e (-1) Rex = lb - 1], recovering v1 bit for bit).

    Soundness rests on the Coq checker alone; [Print Assumptions
    ruleK_apply_sound] is [functional_extensionality_dep] only. *)

From Coq Require Import Arith ZArith Lia Bool List Setoid.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules.
Import ListNotations.
Open Scope Z_scope.

(** ** The general-delta per-side rewrite

    Constant runs carry their constant; a variable run provably meets
    its lower bound; an incrementing run ([d >= 0]) steps to
    [e + d * Rex]; a decrementing run ([d < 0]) is required to survive
    the [R = eval Rex] rounds ([e + d * Rex >= lb + d], i.e. the last
    round still meets [lb]) and steps to [e + d * Rex], dropped when it
    reaches the constant [0]. *)
Fixpoint appK_side (lo : list Z) (Rex : Expr) (rr : list RRun)
    (mr : list SRun) : option (list SRun) :=
  match rr, mr with
  | [], [] => Some []
  | (s, RC v) :: rt, (s', e) :: mt =>
      if sym_eqb s s' && eeqb e (econst v)
      then option_map (cons (s', e)) (appK_side lo Rex rt mt)
      else None
  | (s, RV d lb) :: rt, (s', e) :: mt =>
      if sym_eqb s s' && expr_ge lo e lb then
        if 0 <=? d then
          option_map (cons (s', eaddmul e d Rex)) (appK_side lo Rex rt mt)
        else if expr_ge lo (eaddmul e d Rex) (lb + d) then
          if eeqb (eaddmul e d Rex) (econst 0)
          then appK_side lo Rex rt mt
          else option_map (cons (s', eaddmul e d Rex))
                          (appK_side lo Rex rt mt)
        else None
      else None
  | _, _ => None
  end.

(** ** Binding-run search (UNTRUSTED: [appK_side] re-validates)

    The decrementing runs, in scan order, carry [(delta, lb, e)].  A
    candidate [j] binds when [lb_j >= d_j], [d_j] divides [e_j - lb_j]
    (so [Rex] recovers exactly), [Rex >= 1], and every decrementing run
    survives [R = Rex] rounds. *)
Fixpoint decs_side (rr : list RRun) (mr : list SRun)
  : list (Z * Z * Expr) :=
  match rr, mr with
  | (_, RV d lb) :: rt, (_, e) :: mt =>
      if d <=? -1 then (d, lb, e) :: decs_side rt mt else decs_side rt mt
  | _ :: rt, _ :: mt => decs_side rt mt
  | _, _ => []
  end.

Definition ediv_expr (e : Expr) (d : Z) : Expr :=
  mkExpr (e_c0 e / d) (map (fun c => c / d) (e_cf e)).

Definition rexOf (t : Z * Z * Expr) : Expr :=
  let '(d, lb, e) := t in eaddc (ediv_expr (eaddc e (- lb)) (- d)) 1.

Definition surviveb (lo : list Z) (Rex : Expr) (t : Z * Z * Expr) : bool :=
  let '(d, lb, e) := t in expr_ge lo (eaddmul e d Rex) (lb + d).

Definition bindsb (lo : list Z) (all : list (Z * Z * Expr))
    (t : Z * Z * Expr) : bool :=
  let '(d, lb, e) := t in
  let Rex := rexOf t in
  (- d <=? lb) &&
  eeqb (eaddmul (econst 0) (- d) (eaddc Rex (-1))) (eaddc e (- lb)) &&
  expr_ge lo Rex 1 &&
  forallb (surviveb lo Rex) all.

Fixpoint find_binding (lo : list Z) (cands all : list (Z * Z * Expr))
  : option Expr :=
  match cands with
  | [] => None
  | t :: rest =>
      if bindsb lo all t then Some (rexOf t) else find_binding lo rest all
  end.

(** One general-delta rule application at the current configuration. *)
Definition ruleK_apply (lo : list Z) (r : Rule) (c : SCfg)
  : option SCfg :=
  if st_eqb (s_st c) (r_st r) && sym_eqb (s_hs c) (r_hs r) then
    let decs := decs_side (r_L r) (s_L c) ++ decs_side (r_R r) (s_R c) in
    match find_binding lo decs decs with
    | None => None
    | Some Rex =>
        if expr_ge lo Rex 1 then
          match appK_side lo Rex (r_L r) (s_L c),
                appK_side lo Rex (r_R r) (s_R c) with
          | Some outL, Some outR =>
              match merge_adj lo outL, merge_adj lo outR with
              | Some mL, Some mR =>
                  Some (mkSCfg (s_st c) (s_hs c)
                               (trim_blanks mL) (trim_blanks mR))
              | _, _ => None
              end
          | _, _ => None
          end
        else None
    end
  else None.

(** ** [appK_side] inversion *)

Lemma appK_side_cons_inv : forall lo Rex s rc rt s' e mt out,
  appK_side lo Rex ((s, rc) :: rt) ((s', e) :: mt) = Some out ->
  s = s' /\
  match rc with
  | RC v =>
      eeqb e (econst v) = true /\
      exists o, appK_side lo Rex rt mt = Some o /\ out = (s', e) :: o
  | RV d lb =>
      expr_ge lo e lb = true /\
      exists o, appK_side lo Rex rt mt = Some o /\
      ((0 <= d /\ out = (s', eaddmul e d Rex) :: o) \/
       (d < 0 /\ expr_ge lo (eaddmul e d Rex) (lb + d) = true /\
        ((eeqb (eaddmul e d Rex) (econst 0) = true /\ out = o) \/
         (eeqb (eaddmul e d Rex) (econst 0) = false /\
          out = (s', eaddmul e d Rex) :: o))))
  end.
Proof.
  intros lo Rex s rc rt s' e mt out H.
  destruct rc as [v | d lb]; cbn [appK_side] in H.
  - destruct (sym_eqb s s') eqn:Hs; cbn beta iota in H; [|discriminate].
    apply sym_eqb_spec in Hs.
    destruct (eeqb e (econst v)) eqn:He; cbn beta iota in H; [|discriminate].
    destruct (appK_side lo Rex rt mt) as [o|] eqn:Ha; cbn beta iota in H;
      [|discriminate].
    injection H as <-. split; [auto|]. split; [auto|]. eauto.
  - destruct (sym_eqb s s') eqn:Hs; cbn beta iota in H; [|discriminate].
    apply sym_eqb_spec in Hs.
    destruct (expr_ge lo e lb) eqn:Hge; cbn beta iota in H; [|discriminate].
    split; [auto|]. split; [auto|].
    destruct (0 <=? d) eqn:Hd.
    + apply Z.leb_le in Hd.
      destruct (appK_side lo Rex rt mt) as [o|] eqn:Ha; cbn beta iota in H;
        [|discriminate].
      injection H as <-. exists o. split; [auto|]. left. auto.
    + apply Z.leb_gt in Hd.
      destruct (expr_ge lo (eaddmul e d Rex) (lb + d)) eqn:Hsv;
        cbn beta iota in H; [|discriminate].
      destruct (eeqb (eaddmul e d Rex) (econst 0)) eqn:Hz;
        cbn beta iota in H.
      * exists out. split; [auto|]. right. split; [lia|]. split; [auto|].
        left. auto.
      * destruct (appK_side lo Rex rt mt) as [o|] eqn:Ha; cbn beta iota in H;
          [|discriminate].
        injection H as <-. exists o. split; [auto|].
        right. split; [lia|]. split; [auto|]. right. auto.
Qed.

Lemma appK_side_nil_inv : forall lo Rex rr mr out,
  appK_side lo Rex rr mr = Some out -> (rr = [] <-> mr = []).
Proof.
  intros lo Rex rr mr out H.
  destruct rr as [|[s rc] rt]; destruct mr as [|[s' e] mt];
    simpl in H; try discriminate;
    try (destruct rc; discriminate);
    split; intro; congruence.
Qed.

Lemma appK_side_vlen : forall lo Rex rr mr out nu j,
  appK_side lo Rex rr mr = Some out ->
  length (vvals nu j rr mr) = length (rlbs rr).
Proof.
  induction rr as [|[s rc] rt IH]; intros mr out nu j H.
  - destruct mr; [reflexivity|]. simpl in H. discriminate.
  - destruct mr as [|[s' e] mt].
    + destruct rc; simpl in H; discriminate.
    + destruct (appK_side_cons_inv _ _ _ _ _ _ _ _ _ H) as [Hs Hrest].
      destruct rc as [v | d lb]; simpl.
      * destruct Hrest as (_ & o & Ha & _). eapply IH; eauto.
      * destruct Hrest as (_ & o & Ha & _).
        simpl. f_equal. eapply IH; eauto.
Qed.

(** ** Denotation lemmas (mirror [Rules.app_side_den*]) *)

(** Iteration 0 of the generalisation is the matched configuration. *)
Lemma appK_side_den0 : forall lo Rex rr mr out nu,
  appK_side lo Rex rr mr = Some out ->
  forall pre ext,
  dside (fun i => nth i (pre ++ vvals nu 0 rr mr ++ ext) 1)
        (rstart (length pre) rr)
  = dside nu mr.
Proof.
  induction rr as [|[s rc] rt IH]; intros mr out nu H pre ext.
  - destruct mr; [reflexivity | simpl in H; discriminate].
  - destruct mr as [|[s' e] mt];
      [destruct rc; simpl in H; discriminate|].
    destruct (appK_side_cons_inv _ _ _ _ _ _ _ _ _ H) as [Hs Hrest].
    subst s'.
    destruct rc as [v | d lb]; simpl vvals; simpl rstart;
      rewrite !dside_cons.
    + destruct Hrest as (He & o & Ha & _).
      f_equal.
      * f_equal. unfold cnt.
        rewrite eval_econst, (eeqb_eval _ _ nu He), eval_econst. reflexivity.
      * eapply IH; eauto.
    + destruct Hrest as (Hge & o & Ha & _).
      f_equal.
      * f_equal. unfold cnt. rewrite eval_evar, nth_mid2. f_equal. lia.
      * etransitivity;
          [apply dside_ext with
             (g := fun i => nth i ((pre ++ [eval nu e + d * 0])
                                     ++ vvals nu 0 rt mt ++ ext) 1)|].
        { intro i. f_equal. rewrite <- app_assoc. reflexivity. }
        replace (S (length pre))
          with (length (pre ++ [eval nu e + d * 0]))
          by (rewrite app_length; simpl; lia).
        eapply IH; eauto.
Qed.

(** The end shape at iteration [j] is the start shape at [j+1]. *)
Lemma appK_side_denS : forall lo Rex rr mr out nu j,
  appK_side lo Rex rr mr = Some out ->
  forall pre pre' ext ext', length pre = length pre' ->
  dside (fun i => nth i (pre ++ vvals nu j rr mr ++ ext) 1)
        (rend (length pre) rr)
  = dside (fun i => nth i (pre' ++ vvals nu (j + 1) rr mr ++ ext') 1)
          (rstart (length pre') rr).
Proof.
  induction rr as [|[s rc] rt IH]; intros mr out nu j H pre pre' ext
    ext' Hlen.
  - destruct mr; [reflexivity | simpl in H; discriminate].
  - destruct mr as [|[s' e] mt];
      [destruct rc; simpl in H; discriminate|].
    destruct (appK_side_cons_inv _ _ _ _ _ _ _ _ _ H) as [Hs Hrest].
    subst s'.
    destruct rc as [v | d lb]; simpl vvals; simpl rstart; simpl rend;
      rewrite !dside_cons.
    + destruct Hrest as (_ & o & Ha & _). f_equal. eapply IH; eauto.
    + destruct Hrest as (_ & o & Ha & _).
      f_equal.
      * f_equal. unfold cnt.
        rewrite eval_eaddc, eval_evar, eval_evar, !nth_mid2. f_equal. lia.
      * etransitivity;
          [apply dside_ext with
             (g := fun i => nth i ((pre ++ [eval nu e + d * j])
                                     ++ vvals nu j rt mt ++ ext) 1)|].
        { intro i. f_equal. rewrite <- app_assoc. reflexivity. }
        etransitivity;
          [|apply dside_ext with
              (f := fun i => nth i ((pre' ++ [eval nu e + d * (j + 1)])
                                      ++ vvals nu (j + 1) rt mt
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

(** Iteration [eval nu Rex] is the post-application side. *)
Lemma appK_side_denR : forall lo Rex rr mr out nu,
  appK_side lo Rex rr mr = Some out ->
  forall pre ext,
  dside (fun i => nth i (pre ++ vvals nu (eval nu Rex) rr mr ++ ext) 1)
        (rstart (length pre) rr)
  = dside nu out.
Proof.
  induction rr as [|[s rc] rt IH]; intros mr out nu H pre ext.
  - destruct mr; simpl in H; [injection H as <-; reflexivity | discriminate].
  - destruct mr as [|[s' e] mt];
      [destruct rc; simpl in H; discriminate|].
    destruct (appK_side_cons_inv _ _ _ _ _ _ _ _ _ H) as [Hs Hrest].
    subst s'.
    destruct rc as [v | d lb]; simpl vvals; simpl rstart;
      rewrite !dside_cons.
    + destruct Hrest as (He & o & Ha & ->).
      rewrite dside_cons.
      f_equal.
      * f_equal. unfold cnt.
        rewrite eval_econst, (eeqb_eval _ _ nu He), eval_econst. reflexivity.
      * eapply IH; eauto.
    + destruct Hrest as (Hge & o & Ha & Hout).
      assert (Hhead : nth (length pre)
                (pre ++ ((eval nu e + d * eval nu Rex)
                           :: vvals nu (eval nu Rex) rt mt) ++ ext) 1
              = eval nu e + d * eval nu Rex) by apply nth_mid2.
      assert (Htail : dside
          (fun i => nth i (pre ++ ((eval nu e + d * eval nu Rex)
                    :: vvals nu (eval nu Rex) rt mt) ++ ext) 1)
          (rstart (S (length pre)) rt) = dside nu o).
      { etransitivity;
          [apply dside_ext with
             (g := fun i => nth i ((pre ++ [eval nu e + d * eval nu Rex])
                                     ++ vvals nu (eval nu Rex) rt mt
                                     ++ ext) 1)|].
        { intro i. f_equal. rewrite <- app_assoc. reflexivity. }
        replace (S (length pre))
          with (length (pre ++ [eval nu e + d * eval nu Rex]))
          by (rewrite app_length; simpl; lia).
        eapply IH; eauto. }
      destruct Hout as [(Hd & ->) | (Hd0 & Hsv & Hdrop)].
      * (* increment: step, keep *)
        rewrite dside_cons. f_equal.
        -- f_equal. unfold cnt. rewrite eval_evar, Hhead, eval_eaddmul.
           reflexivity.
        -- exact Htail.
      * destruct Hdrop as [(Hz & ->) | (Hz & ->)].
        -- (* decrement drained to constant 0: dropped *)
           replace (cnt (fun i => nth i (pre ++ ((eval nu e + d * eval nu Rex)
                     :: vvals nu (eval nu Rex) rt mt) ++ ext) 1)
                     (evar (length pre))) with 0%nat.
           2:{ unfold cnt. rewrite eval_evar, Hhead.
               pose proof (eeqb_eval _ _ nu Hz) as HzE.
               rewrite eval_eaddmul, eval_econst in HzE. lia. }
           simpl repeat. simpl app. exact Htail.
        -- (* decrement, nonzero: step, keep *)
           rewrite dside_cons. f_equal.
           ++ f_equal. unfold cnt. rewrite eval_evar, Hhead, eval_eaddmul.
              reflexivity.
           ++ exact Htail.
Qed.

(** The lower bounds hold at every iteration [0 <= j < eval nu Rex]. *)
Lemma appK_side_bge : forall lo Rex rr mr out nu j,
  appK_side lo Rex rr mr = Some out -> bge lo nu ->
  0 <= j -> j <= eval nu Rex - 1 ->
  forall i, nth i (rlbs rr) 0 <= nth i (vvals nu j rr mr) 1.
Proof.
  induction rr as [|[s rc] rt IH]; intros mr out nu j H Hb Hj0 Hj1 i.
  - destruct mr; simpl in H; [|discriminate]. simpl. destruct i; simpl; lia.
  - destruct mr as [|[s' e] mt];
      [destruct rc; simpl in H; discriminate|].
    destruct (appK_side_cons_inv _ _ _ _ _ _ _ _ _ H) as [Hs Hrest].
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

(** ** Application soundness

    A matching rule applied [R = eval nu Rex >= 1] times in one op.
    [find_binding] is untrusted: soundness uses only the guard
    [expr_ge lo Rex 1] and the per-run checks inside [appK_side]. *)
Theorem ruleK_apply_sound : forall tm lo r F c c',
  ruleK_apply lo r c = Some c' -> rule_sem tm r F ->
  forall nu, bge lo nu ->
  exists n, (1 <= n)%nat /\ Reach tm F n (asem nu c) (asem nu c').
Proof.
  intros tm lo r F c c' H Hsem nu Hb.
  unfold ruleK_apply in H.
  destruct (st_eqb (s_st c) (r_st r) && sym_eqb (s_hs c) (r_hs r))
    eqn:Hsh; [|discriminate].
  apply andb_prop in Hsh as [Hst Hhs].
  apply st_eqb_spec in Hst. apply sym_eqb_spec in Hhs.
  cbv zeta in H.
  destruct (find_binding lo
              (decs_side (r_L r) (s_L c) ++ decs_side (r_R r) (s_R c))
              (decs_side (r_L r) (s_L c) ++ decs_side (r_R r) (s_R c)))
    as [Rex|]; [|discriminate].
  destruct (expr_ge lo Rex 1) eqn:HR1; [|discriminate].
  destruct (appK_side lo Rex (r_L r) (s_L c)) as [outL|] eqn:HappL;
    [|discriminate].
  destruct (appK_side lo Rex (r_R r) (s_R c)) as [outR|] eqn:HappR;
    [|discriminate].
  destruct (merge_adj lo outL) as [mL|] eqn:HmL; [|discriminate].
  destruct (merge_adj lo outR) as [mR|] eqn:HmR; [|discriminate].
  injection H as <-.
  pose proof (expr_ge_sound lo Rex 1 nu HR1 Hb) as HrZ.
  pose (VL := fun j => vvals nu j (r_L r) (s_L c)).
  pose (VR := fun j => vvals nu j (r_R r) (s_R c)).
  pose (U := fun j (i : nat) => nth i (VL j ++ VR j) 1).
  assert (HlenL : forall j, length (VL j) = length (rlbs (r_L r)))
    by (intro j; eapply appK_side_vlen; eauto).
  assert (HL0 : dside (U 0) (rstart 0 (r_L r)) = dside nu (s_L c))
    by exact (appK_side_den0 _ _ _ _ _ _ HappL [] (VR 0)).
  assert (HR0 : dside (U 0) (rstart (length (rlbs (r_L r))) (r_R r))
                = dside nu (s_R c)).
  { etransitivity;
      [apply dside_ext with (g := fun i => nth i (VL 0 ++ VR 0 ++ []) 1)|].
    { intro i. f_equal. rewrite app_nil_r. reflexivity. }
    rewrite <- (HlenL 0).
    exact (appK_side_den0 _ _ _ _ _ _ HappR (VL 0) []). }
  assert (Claim0 : asem nu c = asem (U 0) (rule_start_cfg r)).
  { unfold asem, dcfg, rule_start_cfg.
    cbn [s_st s_hs s_L s_R].
    rewrite Hst, Hhs, HL0, HR0. reflexivity. }
  assert (ClaimS : forall j,
    asem (U j) (rule_end_cfg r) = asem (U (j + 1)) (rule_start_cfg r)).
  { intro j.
    assert (EL : dside (U j) (rend 0 (r_L r))
                 = dside (U (j + 1)) (rstart 0 (r_L r)))
      by exact (appK_side_denS _ _ _ _ _ _ j HappL [] [] (VR j)
                  (VR (j + 1)) eq_refl).
    assert (ER : dside (U j) (rend (length (rlbs (r_L r))) (r_R r))
                 = dside (U (j + 1))
                     (rstart (length (rlbs (r_L r))) (r_R r))).
    { etransitivity;
        [apply dside_ext with (g := fun i => nth i (VL j ++ VR j ++ []) 1)|].
      { intro i. f_equal. rewrite app_nil_r. reflexivity. }
      etransitivity;
        [|apply dside_ext with
            (f := fun i => nth i (VL (j + 1) ++ VR (j + 1) ++ []) 1)].
      2:{ intro i. f_equal. rewrite app_nil_r. reflexivity. }
      rewrite <- (HlenL j) at 1.
      rewrite <- (HlenL (j + 1)).
      apply (appK_side_denS lo Rex (r_R r) (s_R c) outR nu j HappR
               (VL j) (VL (j + 1)) [] []).
      rewrite !HlenL. reflexivity. }
    unfold asem, dcfg, rule_end_cfg, rule_start_cfg.
    cbn [s_st s_hs s_L s_R].
    rewrite EL, ER. reflexivity. }
  assert (ClaimR : asem (U (eval nu Rex)) (rule_start_cfg r)
                   = asem nu (mkSCfg (s_st c) (s_hs c) outL outR)).
  { assert (EL : dside (U (eval nu Rex)) (rstart 0 (r_L r))
                 = dside nu outL)
      by exact (appK_side_denR _ _ _ _ _ _ HappL [] (VR (eval nu Rex))).
    assert (ER : dside (U (eval nu Rex))
                   (rstart (length (rlbs (r_L r))) (r_R r))
                 = dside nu outR).
    { etransitivity;
        [apply dside_ext with
           (g := fun i => nth i (VL (eval nu Rex)
                                   ++ VR (eval nu Rex) ++ []) 1)|].
      { intro i. f_equal. rewrite app_nil_r. reflexivity. }
      rewrite <- (HlenL (eval nu Rex)).
      exact (appK_side_denR _ _ _ _ _ _ HappR (VL (eval nu Rex)) []). }
    unfold asem, dcfg, rule_start_cfg.
    cbn [s_st s_hs s_L s_R].
    rewrite Hst, Hhs, EL, ER. reflexivity. }
  assert (Hbge : forall j, 0 <= j -> j <= eval nu Rex - 1 ->
                 bge (rule_lbs r) (U j)).
  { intros j Hj0 Hj1 i.
    unfold rule_lbs.
    apply nth_app_le.
    - symmetry. apply HlenL.
    - intro i'. eapply appK_side_bge; eauto.
    - intro i'. eapply appK_side_bge; eauto. }
  assert (Hiter : forall m, (1 <= m)%nat -> Z.of_nat m <= eval nu Rex ->
    exists n, (1 <= n)%nat /\
      Reach tm F n (asem (U 0) (rule_start_cfg r))
                   (asem (U (Z.of_nat m)) (rule_start_cfg r))).
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
  assert (Hreb : asem nu (mkSCfg (s_st c) (s_hs c)
                            (trim_blanks mL) (trim_blanks mR))
                 = asem nu (mkSCfg (s_st c) (s_hs c) outL outR)).
  { unfold asem, dcfg.
    cbn [s_st s_hs s_L s_R].
    rewrite !lift_cc, !trim_blanks_den.
    rewrite (merge_adj_den lo outL mL nu HmL Hb).
    rewrite (merge_adj_den lo outR mR nu HmR Hb). reflexivity. }
  setoid_rewrite Hreb.
  exact HRch.
Qed.

(** ** The meta-cycle replay with the general-delta applier

    A fork of [Rules.replay] (which is wired to the v1 [rule_apply]);
    identical except [try_rulesK] fires [ruleK_apply]. *)
Fixpoint try_rulesK (lo : list Z) (rules : list (Rule * list Tr))
    (c : SCfg) : option (SCfg * list Tr) :=
  match rules with
  | [] => None
  | (r, F) :: rest =>
      match ruleK_apply lo r c with
      | Some c' => Some (c', F)
      | None => try_rulesK lo rest c
      end
  end.

Fixpoint replayK (tm : TM) (lo : list Z) (rules : list (Rule * list Tr))
    (endt : SCfg -> bool) (fuel : nat) (stepped : bool) (c : SCfg)
  : option (SCfg * list Tr) :=
  match fuel with
  | O => None
  | S fuel' =>
      if stepped && endt c then Some (c, [])
      else
        match try_rulesK lo rules c with
        | Some (c', F) =>
            match replayK tm lo rules endt fuel' stepped c' with
            | Some (cend, F') => Some (cend, F ++ F')
            | None => None
            end
        | None =>
            match eng_step tm lo c with
            | Some (c', F) =>
                match replayK tm lo rules endt fuel' true c' with
                | Some (cend, F') => Some (cend, F ++ F')
                | None => None
                end
            | None => None
            end
        end
  end.

Lemma replayK_sound : forall tm lo rules endt fuel stepped c cend F,
  replayK tm lo rules endt fuel stepped c = Some (cend, F) ->
  forall nu, bge lo nu ->
  (forall r Fr c1 c2, In (r, Fr) rules -> ruleK_apply lo r c1 = Some c2 ->
     exists n, (1 <= n)%nat /\ Reach tm Fr n (asem nu c1) (asem nu c2)) ->
  endt cend = true /\
  exists n, Reach tm F n (asem nu c) (asem nu cend) /\
            (stepped = false -> (1 <= n)%nat).
Proof.
  intros tm lo rules endt fuel.
  induction fuel as [|fuel IH]; intros stepped c cend F H nu Hb
    Happ; simpl in H; [discriminate|].
  destruct (stepped && endt c) eqn:Hend.
  - injection H as <- <-.
    apply andb_prop in Hend as [Hst Hendc].
    split; [exact Hendc|].
    exists O. split; [apply Reach_refl|].
    intro Hf; rewrite Hf in Hst; discriminate.
  - destruct (try_rulesK lo rules c) as [[c' Fr]|] eqn:Htry.
    + destruct (replayK tm lo rules endt fuel stepped c')
        as [[cend' F']|] eqn:Hrec; [|discriminate].
      injection H as <- <-.
      destruct (IH stepped c' cend' F' Hrec nu Hb Happ)
        as (Hende & n2 & HR2 & _).
      assert (Hget : exists r0, In (r0, Fr) rules /\
                     ruleK_apply lo r0 c = Some c').
      { clear -Htry. induction rules as [|[r0 F0] rest IHr];
          simpl in Htry; [discriminate|].
        destruct (ruleK_apply lo r0 c) eqn:Ha.
        - injection Htry as <- <-. exists r0. split; [left|]; auto.
        - destruct (IHr Htry) as (r1 & Hin & Ha1).
          exists r1. split; [right|]; assumption. }
      destruct Hget as (r0 & Hin & Ha).
      destruct (Happ r0 Fr c c' Hin Ha) as (n1 & Hn1 & HR1).
      split; [exact Hende|].
      exists (n1 + n2)%nat. split.
      * exact (Reach_compose _ _ _ _ _ _ _ _ HR1 HR2).
      * intro; lia.
    + destruct (eng_step tm lo c) as [[c' Fe]|] eqn:Hstep;
        [|discriminate].
      destruct (replayK tm lo rules endt fuel true c')
        as [[cend' F']|] eqn:Hrec; [|discriminate].
      injection H as <- <-.
      destruct (IH true c' cend' F' Hrec nu Hb Happ)
        as (Hende & n2 & HR2 & _).
      destruct (eng_step_sound tm lo c c' Fe Hstep nu Hb)
        as (n1 & Hn1 & HR1).
      split; [exact Hende|].
      exists (n1 + n2)%nat. split.
      * exact (Reach_compose _ _ _ _ _ _ _ _ HR1 HR2).
      * intro; lia.
Qed.

(** Sanity: [Print Assumptions] of the soundness theorem. *)
(* Print Assumptions ruleK_apply_sound. *)

(** ** Rule validation with rule-in-rule application (one level)

    Validating rule [r] replays it from the fresh-variable start, and
    may apply ALREADY-VALIDATED rules [prior] (of lower index) just as
    the meta replay applies rules -- an applied rule's fired set folds
    into [r]'s.  This is BBB docs/irules2.md "Rule-in-rule application
    (one level)": the dependencies are recorded in index order and
    validated first, so [r]'s soundness rests only on lower-index
    rules' soundness.  A single rule with no applicable dependency
    replays through the engine alone, identical to [Rules.rule_check].
    Soundness reuses [ruleK_apply_sound] to discharge [replayK_sound]'s
    per-rule Reach obligation. *)

Definition ruleK_check (tm : TM) (fuel : nat)
    (prior : list (Rule * list Tr)) (r : Rule) : option (list Tr) :=
  match replayK tm (rule_lbs r) prior
          (fun c => scfg_eqb c (rule_end_cfg r))
          fuel false (rule_start_cfg r) with
  | Some (_, F) => Some F
  | None => None
  end.

Lemma ruleK_check_sound : forall tm fuel prior r F,
  (forall r' F', In (r', F') prior -> rule_sem tm r' F') ->
  ruleK_check tm fuel prior r = Some F -> rule_sem tm r F.
Proof.
  intros tm fuel prior r F Hprior H u Hu.
  unfold ruleK_check in H.
  destruct (replayK tm (rule_lbs r) prior
              (fun c => scfg_eqb c (rule_end_cfg r))
              fuel false (rule_start_cfg r)) as [[cend F']|] eqn:Hrep;
    [|discriminate].
  injection H as <-.
  destruct (replayK_sound tm (rule_lbs r) prior _ fuel false
              (rule_start_cfg r) cend F' Hrep u Hu
              (fun r0 Fr c1 c2 Hin Happ =>
                 ruleK_apply_sound tm (rule_lbs r) r0 Fr c1 c2 Happ
                   (Hprior r0 Fr Hin) u Hu))
    as (Hend & n & HR & Hpos).
  exists n. split; [apply Hpos; reflexivity|].
  rewrite <- (scfg_eqb_asem cend (rule_end_cfg r) u Hend). exact HR.
Qed.

Fixpoint check_rulesK_aux (tm : TM) (fuel : nat)
    (acc : list (Rule * list Tr)) (rules : list Rule)
  : option (list (Rule * list Tr)) :=
  match rules with
  | [] => Some acc
  | r :: rest =>
      match ruleK_check tm fuel acc r with
      | Some F => check_rulesK_aux tm fuel (acc ++ [(r, F)]) rest
      | None => None
      end
  end.

Definition check_rulesK (tm : TM) (fuel : nat) (rules : list Rule)
  : option (list (Rule * list Tr)) :=
  check_rulesK_aux tm fuel [] rules.

Lemma check_rulesK_aux_sound : forall tm fuel rules acc vrules,
  check_rulesK_aux tm fuel acc rules = Some vrules ->
  (forall r F, In (r, F) acc -> rule_sem tm r F) ->
  forall r F, In (r, F) vrules -> rule_sem tm r F.
Proof.
  intros tm fuel rules. induction rules as [|r0 rest IH];
    intros acc vrules H Hacc; simpl in H.
  - injection H as <-. exact Hacc.
  - destruct (ruleK_check tm fuel acc r0) as [F0|] eqn:Hc;
      [|discriminate].
    apply (IH (acc ++ [(r0, F0)]) vrules H).
    intros r F Hin. apply in_app_or in Hin as [Hin | Hin].
    + apply Hacc; exact Hin.
    + destruct Hin as [Heq | []]. injection Heq as <- <-.
      exact (ruleK_check_sound tm fuel acc r0 F0 Hacc Hc).
Qed.

Theorem check_rulesK_sound : forall tm fuel rules vrules,
  check_rulesK tm fuel rules = Some vrules ->
  forall r F, In (r, F) vrules -> rule_sem tm r F.
Proof.
  intros tm fuel rules vrules H.
  apply (check_rulesK_aux_sound tm fuel rules [] vrules H).
  intros r F [].
Qed.
