(** * IRules.EngineKS: the sentinel-aware block engine (Phase 2 rulepfx).

    A fork of [EngineK]'s crossing loop / engine op for PREFIX rules
    (v5+ [rulepfx]): during a prefix rule's own validation its prefix
    sides are OPAQUE -- the configuration lists only the declared
    near-head runs, and an unknown rest lies beyond them.  The engine
    must therefore never read past the end of a sentinel side (the
    app-exhausted branch hard-fails), and never drop a blank pushed onto
    an empty sentinel side (beyond the end is the opaque rest, not
    blank background -- a trailing blank run is CONTENT there).

    Soundness is stated against the SUFFIX-EXTENDED semantics [bsemX]:
    each side denotes its runs followed by an arbitrary concrete cell
    suffix ([XL]/[XR]), which must be [[]] on non-sentinel sides.  A
    validated prefix rule therefore yields a [Reach] for EVERY
    continuation of its opaque sides, which is exactly what the
    prefix-splicing applier ([RulesBlkPfx]) needs.

    Everything from [EngineK] (denotation, hop machinery, push/merge)
    is reused; only the crossing loop, the blank-preserving push and
    the engine op are re-derived.  [EngineK] itself is untouched, so
    the Phase-1 checker stack is unaffected. *)

From Coq Require Import Arith ZArith Lia Bool List Setoid FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers.IRules Require Import Expr RLE Engine EngineK.
Import ListNotations.
Open Scope Z_scope.

(** ** The suffix-extended semantics *)

Definition blsemX (tbl : BTbl) (nu : nat -> Z) (q : St) (mv : Dir)
    (dep app : list BRun) (XD XA : list Sym) : ExecState :=
  let df := lift_side (bdside tbl nu dep ++ XD) in
  let af := lift_side (bdside tbl nu app ++ XA) in
  match mv with
  | DR => (q, mkTape df (af O) (tail_side af))
  | DL => (q, mkTape (tail_side af) (af O) df)
  end.

Lemma blsemX_concrete_R : forall tbl nu q dep app XD XA,
  blsemX tbl nu q DR dep app XD XA =
  lift (q, (bdside tbl nu dep ++ XD, chd (bdside tbl nu app ++ XA),
            ctl (bdside tbl nu app ++ XA))).
Proof.
  intros. unfold blsemX.
  rewrite lift_cc, lift_side_tl, lift_side_hd. reflexivity.
Qed.

Lemma blsemX_concrete_L : forall tbl nu q dep app XD XA,
  blsemX tbl nu q DL dep app XD XA =
  lift (q, (ctl (bdside tbl nu app ++ XA), chd (bdside tbl nu app ++ XA),
            bdside tbl nu dep ++ XD)).
Proof.
  intros. unfold blsemX.
  rewrite lift_cc, lift_side_tl, lift_side_hd. reflexivity.
Qed.

Lemma blsemX_nil : forall tbl nu q mv dep app,
  blsemX tbl nu q mv dep app [] [] = blsem tbl nu q mv dep app.
Proof.
  intros. unfold blsemX, blsem. rewrite !app_nil_r. reflexivity.
Qed.

(** The suffix-extended configuration semantics. *)
Definition bsemX (tbl : BTbl) (nu : nat -> Z) (c : BCfg) (XL XR : list Sym)
  : ExecState :=
  lift (b_st c, (bdside tbl nu (b_L c) ++ XL, b_hs c,
                 bdside tbl nu (b_R c) ++ XR)).

Lemma bsemX_nil : forall tbl nu c, bsemX tbl nu c [] [] = bsem tbl nu c.
Proof.
  intros. unfold bsemX, bsem, bdcfg. rewrite !app_nil_r. reflexivity.
Qed.

(** [bassemble] under the extended semantics: the [XD]/[XA] suffixes
    follow their sides through the move-direction reassembly. *)
Lemma basemX_bassemble : forall tbl nu q h mv dep app XD XA,
  bsemX tbl nu (bassemble q h mv dep app)
        (match mv with DR => XD | DL => XA end)
        (match mv with DR => XA | DL => XD end) =
  (match mv with
   | DR => lift (q, (bdside tbl nu dep ++ XD, h, bdside tbl nu app ++ XA))
   | DL => lift (q, (bdside tbl nu app ++ XA, h, bdside tbl nu dep ++ XD))
   end).
Proof. intros tbl nu q h [|] dep app XD XA; reflexivity. Qed.

(** ** The sentinel-preserving push

    Identical to [bpush] except that a blank pushed onto an EMPTY
    sentinel side is kept as a run (content before the opaque rest)
    instead of dropped (background). *)

Definition bpushS (sent : bool) (lo : list Z) (s : BSym) (e : Expr)
    (rs : list BRun) : option (list BRun) :=
  if negb (expr_ge lo e 0) then None else
  match rs with
  | [] => if Nat.eqb s 0 && negb sent then Some [] else Some [(s, e)]
  | (s', e') :: t =>
      if Nat.eqb s s'
      then if expr_ge lo e' 0 then Some ((s', eadd e e') :: t) else None
      else Some ((s, e) :: rs)
  end.

Lemma bpushS_denX : forall tbl sent lo s e rs rs' nu X,
  raw_ok tbl ->
  bpushS sent lo s e rs = Some rs' -> bge lo nu ->
  (sent = false -> X = []) ->
  lift_side (bdside tbl nu rs' ++ X) =
  lift_side (nreps (tbl s) (cnt nu e) ++ bdside tbl nu rs ++ X).
Proof.
  intros tbl sent lo s e rs rs' nu X Hraw H Hb HX.
  pose proof Hraw as [Hr0 Hr1].
  unfold bpushS in H.
  destruct (expr_ge lo e 0) eqn:Hge; simpl in H; [|discriminate].
  destruct rs as [|[s' e'] t].
  - destruct (Nat.eqb s 0 && negb sent) eqn:Hdrop; injection H as <-.
    + (* blank dropped: only on a non-sentinel side, where X = [] *)
      apply andb_prop in Hdrop as [Hs Hsent].
      apply Nat.eqb_eq in Hs; subst s.
      destruct sent; [discriminate|].
      rewrite (HX eq_refl).
      rewrite Hr0. simpl bdside.
      rewrite !app_nil_r, nreps_single, lift_side_blanks.
      apply lift_side_nil.
    + (* kept as a run: exact cell equality *)
      f_equal. rewrite bdside_cons.
      simpl bdside. rewrite !app_nil_r. reflexivity.
  - destruct (Nat.eqb s s') eqn:Hs.
    + destruct (expr_ge lo e' 0) eqn:Hge'; [|discriminate].
      injection H as <-.
      apply Nat.eqb_eq in Hs; subst s'.
      f_equal. rewrite !bdside_cons.
      rewrite cnt_add;
        [| eapply expr_ge_sound; eauto | eapply expr_ge_sound; eauto].
      rewrite nreps_add, !app_assoc. reflexivity.
    + injection H as <-. f_equal.
      rewrite bdside_cons, <- app_assoc. reflexivity.
Qed.

(** ** The sentinel-aware crossing loop

    [sd]/[sa] flag the departed/approached side as sentinels.  The
    app-exhausted branch fails on a sentinel approached side (it would
    read the opaque rest); pushes onto the departed side go through
    [bpushS sd]. *)

Fixpoint beng_crossS (tm : TM) (tbl : BTbl) (lo : list Z)
    (hopf : St -> Dir -> BSym -> option (BSym * nat * list Tr))
    (sd sa : bool) (q : St)
    (mv : Dir) (fuel : nat) (app dep : list BRun)
  : option (list BRun * list BRun * Sym * list Tr) :=
  match fuel with
  | O => None
  | S fuel' =>
    match app with
    | [] =>
        if sa then None
        else if chainable tm q S0 mv then None else Some ([], dep, S0, [])
    | (s, e) :: rest =>
        if (2 <=? length (tbl s))%nat then
          match hopf q mv s with
          | Some (nsym, factor, hF) =>
              if expr_ge lo e 1 then
                match bpushS sd lo nsym
                        (eaddmul (econst 0) (Z.of_nat factor) e) dep with
                | Some dep' =>
                    match beng_crossS tm tbl lo hopf sd sa q mv fuel' rest dep' with
                    | Some (app', dep'', h, F) => Some (app', dep'', h, hF ++ F)
                    | None => None
                    end
                | None => None
                end
              else None
          | None =>
              match (if eeqb e (econst 1) then Some rest
                     else if expr_ge lo e 2
                          then Some ((s, eaddc e (-1)) :: rest) else None) with
              | None => None
              | Some tl => beng_crossS tm tbl lo hopf sd sa q mv fuel'
                             (peel_cells tbl s ++ tl) dep
              end
          end
        else if (length (tbl s) =? 1)%nat then
          let c := bcell tbl s in
          if chainable tm q c mv then
            match tm q c with
            | Some tr =>
                if expr_ge lo e 1 then
                  match bpushS sd lo (sym_to_nat (t_write tr)) e dep with
                  | Some dep' =>
                      match beng_crossS tm tbl lo hopf sd sa q mv fuel' rest dep' with
                      | Some (app', dep'', h, F) =>
                          Some (app', dep'', h, (q, c) :: F)
                      | None => None
                      end
                  | None => None
                  end
                else None
            | None => None
            end
          else if eeqb e (econst 1) then Some (rest, dep, c, [])
          else if expr_ge lo e 2 then
            Some ((s, eaddc e (-1)) :: rest, dep, c, [])
          else None
        else None
    end
  end.

(** The block hop under the extended semantics (mirror of
    [EngineK.bhop_reach]; the hop machinery itself is reused, only the
    surrounding tape gains the suffixes). *)
Lemma bhop_reachS : forall tm tbl blks lo sd q mv s e rest dep nsym factor hF
                           dep' nu XD XA,
  raw_ok tbl -> bge lo nu ->
  bhop_result tm tbl blks q mv s = Some (nsym, factor, hF) ->
  expr_ge lo e 1 = true ->
  bpushS sd lo nsym (eaddmul (econst 0) (Z.of_nat factor) e) dep = Some dep' ->
  (sd = false -> XD = []) ->
  Reach tm hF (cnt nu e * length hF)
    (blsemX tbl nu q mv dep ((s, e) :: rest) XD XA)
    (blsemX tbl nu q mv dep' rest XD XA).
Proof.
  intros tm tbl blks lo sd q mv s e rest dep nsym factor hF dep' nu XD XA
    Hraw Hb Hhop Hge1 Hpush HXD.
  destruct (bhop_result_spec tm tbl blks q mv s nsym factor hF Hhop)
    as (hout & Hne & Hsim & Hveq).
  pose proof (expr_ge_sound lo e 1 nu Hge1 Hb) as He1.
  assert (Hce : exists m0, cnt nu e = S m0).
  { unfold cnt. exists (Z.to_nat (eval nu e) - 1)%nat. lia. }
  destruct Hce as [m0 Hm0].
  pose proof (hop_copies tm q mv 1024 (tbl s) hout hF Hne Hsim m0
                (bdside tbl nu dep ++ XD) (bdside tbl nu rest ++ XA)) as HC.
  assert (HblkS : blsemX tbl nu q mv dep ((s, e) :: rest) XD XA =
                  lift (blk_cfg mv q
                          (nreps (tbl s) (S m0) ++ (bdside tbl nu rest ++ XA))
                          (bdside tbl nu dep ++ XD))).
  { destruct mv;
      [rewrite blsemX_concrete_L | rewrite blsemX_concrete_R];
      rewrite bdside_cons, Hm0, <- app_assoc; reflexivity. }
  assert (HblkE : blsemX tbl nu q mv dep' rest XD XA =
                  lift (blk_cfg mv q (bdside tbl nu rest ++ XA)
                          (bdside tbl nu dep' ++ XD))).
  { destruct mv;
      [rewrite blsemX_concrete_L | rewrite blsemX_concrete_R]; reflexivity. }
  rewrite HblkS, HblkE, Hm0.
  assert (Hdep' : lift (blk_cfg mv q (bdside tbl nu rest ++ XA)
                          (nreps hout (S m0) ++ (bdside tbl nu dep ++ XD))) =
                  lift (blk_cfg mv q (bdside tbl nu rest ++ XA)
                          (bdside tbl nu dep' ++ XD))).
  { apply blk_cfg_lift_cong.
    rewrite (bpushS_denX tbl sd lo nsym (eaddmul (econst 0) (Z.of_nat factor) e)
               dep dep' nu XD Hraw Hpush Hb HXD).
    rewrite (cnt_factor nu factor e ltac:(lia)), Hm0.
    rewrite nreps_mul, Hveq. reflexivity. }
  rewrite <- Hdep'. exact HC.
Qed.

Lemma beng_crossS_sound : forall tm tbl lo hopf sd sa,
  raw_ok tbl ->
  (forall nu q mv s nsym factor hF e rest dep dep' XD XA,
     bge lo nu -> hopf q mv s = Some (nsym, factor, hF) ->
     expr_ge lo e 1 = true ->
     bpushS sd lo nsym (eaddmul (econst 0) (Z.of_nat factor) e) dep
       = Some dep' ->
     (sd = false -> XD = []) ->
     Reach tm hF (cnt nu e * length hF)
       (blsemX tbl nu q mv dep ((s, e) :: rest) XD XA)
       (blsemX tbl nu q mv dep' rest XD XA)) ->
  forall fuel q mv app dep app' dep' h F,
  beng_crossS tm tbl lo hopf sd sa q mv fuel app dep = Some (app', dep', h, F) ->
  forall nu XD XA, bge lo nu ->
  (sd = false -> XD = []) -> (sa = false -> XA = []) ->
  exists n,
    Reach tm F n (blsemX tbl nu q mv dep app XD XA)
                 (bsemX tbl nu (bassemble q h mv dep' app')
                        (match mv with DR => XD | DL => XA end)
                        (match mv with DR => XA | DL => XD end)).
Proof.
  intros tm tbl lo hopf sd sa Hraw Hhopf fuel.
  induction fuel as [|fuel IH];
    intros q mv app dep app' dep' h F H nu XD XA Hb HXD HXA;
    [cbn [beng_crossS] in H; discriminate|].
  cbn [beng_crossS] in H.
  destruct app as [|[s e] rest].
  - (* empty approached side: only on a non-sentinel side *)
    destruct sa; [discriminate|].
    destruct (chainable tm q S0 mv) eqn:Hch; [discriminate|].
    injection H as <- <- <- <-.
    exists O.
    rewrite (HXA eq_refl).
    assert (Heq : blsemX tbl nu q mv dep [] XD [] =
                  bsemX tbl nu (bassemble q S0 mv dep [])
                        (match mv with DR => XD | DL => [] end)
                        (match mv with DR => [] | DL => XD end)).
    { rewrite basemX_bassemble.
      destruct mv;
        [rewrite blsemX_concrete_L | rewrite blsemX_concrete_R]; reflexivity. }
    setoid_rewrite Heq. apply Reach_refl.
  - destruct (2 <=? length (tbl s))%nat eqn:Hblk.
    + (* block run *)
      destruct (hopf q mv s) as [[[nsym factor] hF0]|] eqn:Hhf.
      * (* block hop: cross all copies *)
        cbn iota in H.
        destruct (expr_ge lo e 1) eqn:Hge1; cbn iota in H; [|discriminate].
        destruct (bpushS sd lo nsym (eaddmul (econst 0) (Z.of_nat factor) e) dep)
          as [dep'0|] eqn:Hpush; cbn iota in H; [|discriminate].
        destruct (beng_crossS tm tbl lo hopf sd sa q mv fuel rest dep'0)
          as [[[[a d] hh] F0]|] eqn:Hrec; cbn iota in H; [|discriminate].
        injection H as <- <- <- <-.
        destruct (IH q mv rest dep'0 a d hh F0 Hrec nu XD XA Hb HXD HXA)
          as (n2 & HR2).
        pose proof (Hhopf nu q mv s nsym factor hF0 e rest dep dep'0 XD XA
                      Hb Hhf Hge1 Hpush HXD) as HR1.
        exists (cnt nu e * length hF0 + n2)%nat.
        exact (Reach_compose _ _ _ _ _ _ _ _ HR1 HR2).
      * (* no hop: peel one copy *)
        remember (if eeqb e (econst 1) then Some rest
                  else if expr_ge lo e 2 then Some ((s, eaddc e (-1)) :: rest)
                  else None) as opt eqn:Hopt.
        destruct opt as [tl|].
        2:{ cbn iota in H. discriminate H. }
        cbn iota in H.
        destruct (IH q mv (peel_cells tbl s ++ tl) dep app' dep' h F H
                    nu XD XA Hb HXD HXA) as (n & HR).
        exists n.
        assert (Heq : blsemX tbl nu q mv dep (peel_cells tbl s ++ tl) XD XA =
                      blsemX tbl nu q mv dep ((s, e) :: rest) XD XA).
        { unfold blsemX.
          rewrite (bdside_peel_eq tbl lo nu s e rest tl Hraw Hb Hblk
                     (eq_sym Hopt)). reflexivity. }
        rewrite Heq in HR. exact HR.
    + destruct (length (tbl s) =? 1)%nat eqn:Hlen1; [|discriminate].
      apply Nat.eqb_eq in Hlen1.
      set (c := bcell tbl s) in *.
      destruct (chainable tm q c mv) eqn:Hch.
      * (* chain hop over the raw run *)
        unfold chainable in Hch.
        destruct (tm q c) as [tr|] eqn:Htr; [|discriminate].
        apply andb_prop in Hch as [Hnx Hdir].
        apply st_eqb_spec in Hnx. apply dir_eqb_spec in Hdir.
        destruct (expr_ge lo e 1) eqn:Hge; [|discriminate].
        destruct (bpushS sd lo (sym_to_nat (t_write tr)) e dep) as [depP|]
          eqn:Hpush; [|discriminate].
        destruct (beng_crossS tm tbl lo hopf sd sa q mv fuel rest depP)
          as [[[[appX depX] hX] FX]|] eqn:Hrec; [|discriminate].
        injection H as <- <- <- <-.
        destruct (IH q mv rest depP appX depX hX FX Hrec nu XD XA Hb HXD HXA)
          as (n2 & HR2).
        pose proof (expr_ge_sound lo e 1 nu Hge Hb) as He1.
        assert (Hsplit : exists n0, cnt nu e = S n0).
        { unfold cnt. exists (Z.to_nat (eval nu e) - 1)%nat. lia. }
        destruct Hsplit as [n0 Hn1].
        destruct tr as [w d q']. simpl in Hnx, Hdir. subst d q'.
        pose proof (bpushS_denX tbl sd lo (sym_to_nat w) e dep depP nu XD Hraw
                      Hpush Hb HXD) as Hpden.
        rewrite (raw_tbl_sym_to_nat tbl w Hraw), nreps_single, Hn1 in Hpden.
        assert (HR1 : Reach tm [(q, c)] (S n0)
                  (blsemX tbl nu q mv dep ((s, e) :: rest) XD XA)
                  (blsemX tbl nu q mv depP rest XD XA)).
        { destruct mv.
          - (* DL *)
            assert (Hstart : blsemX tbl nu q DL dep ((s, e) :: rest) XD XA =
              lift (q, (repeat c n0 ++ (bdside tbl nu rest ++ XA), c,
                        bdside tbl nu dep ++ XD))).
            { rewrite blsemX_concrete_L,
                (bdside_raw_cons tbl nu s e rest Hlen1), Hn1, <- app_assoc.
              reflexivity. }
            assert (Hlend :
              lift (q, (ctl (bdside tbl nu rest ++ XA),
                        chd (bdside tbl nu rest ++ XA),
                        repeat w (S n0) ++ (bdside tbl nu dep ++ XD))) =
              blsemX tbl nu q DL depP rest XD XA).
            { rewrite blsemX_concrete_L, !lift_cc, Hpden. reflexivity. }
            split; [|split].
            + rewrite Hstart, <- Hlend.
              apply csteps_lift. apply chain_cc_L_end; exact Htr.
            + intros m Hm. rewrite Hstart. eexists. split.
              * apply csteps_lift.
                apply (chain_cc_L_mid tm q c w Htr m n0
                         (bdside tbl nu rest ++ XA)
                         (bdside tbl nu dep ++ XD) ltac:(lia)).
              * left. reflexivity.
            + intros t [<- | []].
              exists O. eexists. split; [lia|]. split; [reflexivity|].
              rewrite Hstart. reflexivity.
          - (* DR *)
            assert (Hstart : blsemX tbl nu q DR dep ((s, e) :: rest) XD XA =
              lift (q, (bdside tbl nu dep ++ XD, c,
                        repeat c n0 ++ (bdside tbl nu rest ++ XA)))).
            { rewrite blsemX_concrete_R,
                (bdside_raw_cons tbl nu s e rest Hlen1), Hn1, <- app_assoc.
              reflexivity. }
            assert (Hlend :
              lift (q, (repeat w (S n0) ++ (bdside tbl nu dep ++ XD),
                        chd (bdside tbl nu rest ++ XA),
                        ctl (bdside tbl nu rest ++ XA))) =
              blsemX tbl nu q DR depP rest XD XA).
            { rewrite blsemX_concrete_R, !lift_cc, Hpden. reflexivity. }
            split; [|split].
            + rewrite Hstart, <- Hlend.
              apply csteps_lift. apply chain_cc_R_end; exact Htr.
            + intros m Hm. rewrite Hstart. eexists. split.
              * apply csteps_lift.
                apply (chain_cc_R_mid tm q c w Htr m n0
                         (bdside tbl nu dep ++ XD)
                         (bdside tbl nu rest ++ XA) ltac:(lia)).
              * left. reflexivity.
            + intros t [<- | []].
              exists O. eexists. split; [lia|]. split; [reflexivity|].
              rewrite Hstart. reflexivity. }
        exists (S n0 + n2)%nat.
        change ((q, c) :: FX) with ([(q, c)] ++ FX).
        exact (Reach_compose _ _ _ _ _ _ _ _ HR1 HR2).
      * (* non-chain: head lands on this run *)
        destruct (eeqb e (econst 1)) eqn:He1.
        -- injection H as <- <- <- <-.
           exists O.
           assert (Hc1 : cnt nu e = 1%nat).
           { unfold cnt. rewrite (eeqb_eval _ _ nu He1), eval_econst.
             reflexivity. }
           assert (Heq : blsemX tbl nu q mv dep ((s, e) :: rest) XD XA =
                         bsemX tbl nu (bassemble q c mv dep rest)
                               (match mv with DR => XD | DL => XA end)
                               (match mv with DR => XA | DL => XD end)).
           { rewrite basemX_bassemble.
             destruct mv;
               [rewrite blsemX_concrete_L | rewrite blsemX_concrete_R];
               rewrite (bdside_raw_cons tbl nu s e rest Hlen1), Hc1;
               reflexivity. }
           setoid_rewrite Heq. apply Reach_refl.
        -- destruct (expr_ge lo e 2) eqn:Hge2; [|discriminate].
           injection H as <- <- <- <-.
           exists O.
           pose proof (expr_ge_sound lo e 2 nu Hge2 Hb) as He2.
           assert (Hcs : cnt nu e = S (cnt nu (eaddc e (-1)))).
           { unfold cnt. rewrite eval_eaddc. lia. }
           assert (Heq : blsemX tbl nu q mv dep ((s, e) :: rest) XD XA =
                         bsemX tbl nu (bassemble q c mv dep
                                         ((s, eaddc e (-1)) :: rest))
                               (match mv with DR => XD | DL => XA end)
                               (match mv with DR => XA | DL => XD end)).
           { rewrite basemX_bassemble.
             destruct mv;
               [rewrite blsemX_concrete_L | rewrite blsemX_concrete_R];
               rewrite (bdside_raw_cons tbl nu s e rest Hlen1),
                 (bdside_raw_cons tbl nu s (eaddc e (-1)) rest Hlen1), Hcs;
               reflexivity. }
           setoid_rewrite Heq. apply Reach_refl.
Qed.

(** ** The full sentinel-aware engine op

    [sl]/[sr] flag the LEFT/RIGHT side of the configuration as
    sentinels; the crossing's departed/approached flags are selected by
    the move direction. *)

Definition beng_stepS (tm : TM) (tbl : BTbl)
    (blks : list (nat * list Sym)) (lo : list Z) (sl sr : bool) (fuel : nat)
    (c : BCfg) : option (BCfg * list Tr) :=
  match tm (b_st c) (b_hs c) with
  | None => None
  | Some tr =>
      let q1 := t_next tr in
      let '(dep0, app0, sd, sa) :=
        match t_dir tr with
        | DR => (b_L c, b_R c, sl, sr)
        | DL => (b_R c, b_L c, sr, sl)
        end in
      match bpushS sd lo (sym_to_nat (t_write tr)) (econst 1) dep0 with
      | None => None
      | Some dep =>
          match beng_crossS tm tbl lo (bhop_result tm tbl blks) sd sa
                  q1 (t_dir tr) fuel app0 dep with
          | Some (app', dep', h, F) =>
              Some (bassemble q1 h (t_dir tr) dep' app',
                    (b_st c, b_hs c) :: F)
          | None => None
          end
      end
  end.

Theorem beng_stepS_sound : forall tm tbl blks lo sl sr fuel c c' F,
  raw_ok tbl ->
  beng_stepS tm tbl blks lo sl sr fuel c = Some (c', F) ->
  forall nu XL XR, bge lo nu ->
  (sl = false -> XL = []) -> (sr = false -> XR = []) ->
  exists n, (1 <= n)%nat /\
    Reach tm F n (bsemX tbl nu c XL XR) (bsemX tbl nu c' XL XR).
Proof.
  intros tm tbl blks lo sl sr fuel c c' F Hraw H nu XL XR Hb HXL HXR.
  unfold beng_stepS in H.
  destruct (tm (b_st c) (b_hs c)) as [tr|] eqn:Htr; [|discriminate].
  pose proof Hraw as [Hr0 Hr1].
  assert (Hhopf : forall sd0, forall nu' q mv s nsym factor hF e rest dep dep'
                    XD XA,
     bge lo nu' -> bhop_result tm tbl blks q mv s = Some (nsym, factor, hF) ->
     expr_ge lo e 1 = true ->
     bpushS sd0 lo nsym (eaddmul (econst 0) (Z.of_nat factor) e) dep
       = Some dep' ->
     (sd0 = false -> XD = []) ->
     Reach tm hF (cnt nu' e * length hF)
       (blsemX tbl nu' q mv dep ((s, e) :: rest) XD XA)
       (blsemX tbl nu' q mv dep' rest XD XA)).
  { intros. eapply bhop_reachS; eauto. }
  assert (Hdep_gen : forall sd0 dep0 dep X,
    bpushS sd0 lo (sym_to_nat (t_write tr)) (econst 1) dep0 = Some dep ->
    (sd0 = false -> X = []) ->
    lift_side (bdside tbl nu dep ++ X) =
    push_side (t_write tr) (lift_side (bdside tbl nu dep0 ++ X))).
  { intros sd0 dep0 dep X Hpush HXd.
    rewrite (bpushS_denX tbl sd0 lo (sym_to_nat (t_write tr)) (econst 1)
               dep0 dep nu X Hraw Hpush Hb HXd).
    rewrite (raw_tbl_sym_to_nat tbl (t_write tr) Hraw).
    change (cnt nu (econst 1)) with 1%nat. rewrite nreps_1.
    change ([t_write tr] ++ bdside tbl nu dep0 ++ X)
      with (t_write tr :: (bdside tbl nu dep0 ++ X)).
    apply lift_side_cons. }
  destruct (t_dir tr) eqn:Hdir.
  - (* DL: departed side is R, sentinel flags (sd, sa) = (sr, sl) *)
    destruct (bpushS sr lo (sym_to_nat (t_write tr)) (econst 1) (b_R c))
      as [dep|] eqn:Hpush; [|discriminate].
    destruct (beng_crossS tm tbl lo (bhop_result tm tbl blks) sr sl
                (t_next tr) DL fuel (b_L c) dep)
      as [[[[app' dep'] h] F']|] eqn:Hcr; [|discriminate].
    injection H as <- <-.
    destruct (beng_crossS_sound tm tbl lo (bhop_result tm tbl blks) sr sl Hraw
                (Hhopf sr) fuel (t_next tr) DL (b_L c) dep app' dep' h F' Hcr
                nu XR XL Hb HXR HXL)
      as (n2 & HR2).
    pose proof (Hdep_gen sr (b_R c) dep XR Hpush HXR) as Hdep.
    assert (Hstep : step tm (bsemX tbl nu c XL XR) =
                    Some (blsemX tbl nu (t_next tr) DL dep (b_L c) XR XL)).
    { unfold bsemX. rewrite lift_cc.
      unfold step. cbn [t_head fst snd]. rewrite Htr, Hdir.
      unfold blsemX, tape_move. rewrite Hdep. reflexivity. }
    assert (HR1 : Reach tm [(b_st c, b_hs c)] 1 (bsemX tbl nu c XL XR)
                    (blsemX tbl nu (t_next tr) DL dep (b_L c) XR XL)).
    { pose proof (Reach_one tm _ _ Hstep) as HRo.
      replace (trans_of (bsemX tbl nu c XL XR)) with (b_st c, b_hs c) in HRo;
        [exact HRo | reflexivity]. }
    exists (1 + n2)%nat. split; [lia|].
    change ((b_st c, b_hs c) :: F') with ([(b_st c, b_hs c)] ++ F').
    exact (Reach_compose _ _ _ _ _ _ _ _ HR1 HR2).
  - (* DR: departed side is L, sentinel flags (sd, sa) = (sl, sr) *)
    destruct (bpushS sl lo (sym_to_nat (t_write tr)) (econst 1) (b_L c))
      as [dep|] eqn:Hpush; [|discriminate].
    destruct (beng_crossS tm tbl lo (bhop_result tm tbl blks) sl sr
                (t_next tr) DR fuel (b_R c) dep)
      as [[[[app' dep'] h] F']|] eqn:Hcr; [|discriminate].
    injection H as <- <-.
    destruct (beng_crossS_sound tm tbl lo (bhop_result tm tbl blks) sl sr Hraw
                (Hhopf sl) fuel (t_next tr) DR (b_R c) dep app' dep' h F' Hcr
                nu XL XR Hb HXL HXR)
      as (n2 & HR2).
    pose proof (Hdep_gen sl (b_L c) dep XL Hpush HXL) as Hdep.
    assert (Hstep : step tm (bsemX tbl nu c XL XR) =
                    Some (blsemX tbl nu (t_next tr) DR dep (b_R c) XL XR)).
    { unfold bsemX. rewrite lift_cc.
      unfold step. cbn [t_head fst snd]. rewrite Htr, Hdir.
      unfold blsemX, tape_move. rewrite Hdep. reflexivity. }
    assert (HR1 : Reach tm [(b_st c, b_hs c)] 1 (bsemX tbl nu c XL XR)
                    (blsemX tbl nu (t_next tr) DR dep (b_R c) XL XR)).
    { pose proof (Reach_one tm _ _ Hstep) as HRo.
      replace (trans_of (bsemX tbl nu c XL XR)) with (b_st c, b_hs c) in HRo;
        [exact HRo | reflexivity]. }
    exists (1 + n2)%nat. split; [lia|].
    change ((b_st c, b_hs c) :: F') with ([(b_st c, b_hs c)] ++ F').
    exact (Reach_compose _ _ _ _ _ _ _ _ HR1 HR2).
Qed.
