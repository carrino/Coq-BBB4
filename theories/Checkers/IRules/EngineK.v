(** * IRules.EngineK: the block-run symbolic replay engine.

    A fork of [Engine] whose run symbols range over [nat] (0 = [S0],
    1 = [S1], and every id >= 2 a BLOCK defined by the certificate's
    (untrusted) block table [tbl : nat -> list Sym]).  A run [(b, e)]
    now denotes [cnt nu e] copies of [tbl b]'s cell sequence, not
    [cnt nu e] copies of a single symbol -- the CRUX of the block
    machinery (BBB docs/irules2.md "Block-level chain hops").

    The denotation [bdside tbl] is parametric in [tbl]; soundness holds
    for ANY table, so the table is never trusted.  A raw symbol [s < 2]
    is the degenerate block [tbl s = [nat_sym s]], so a raw-only side
    reduces exactly to [RLE.dside].

    This file layers, on top of a re-proof of the [Engine] concrete
    step + chain hops against [bdside]:

    - block hop: a bounded one-copy concrete replay ([hop_sim]) that,
      when the head exits the far side in the entry state, crosses ALL
      [e] copies in one op (induction on the copies);
    - block peel: expanding one copy of a block run into cells (a pure
      denotation-preserving re-representation, no concrete step);

    with the canonical re-blocking and cell-stream equality in the
    companion sections.  The Reach/csteps plumbing (concrete tape
    machinery, chain-crossing lemmas) is reused verbatim from
    [Engine]; only the denotation-facing parts are re-derived. *)

From Coq Require Import Arith ZArith Lia Bool List Setoid FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers.IRules Require Import Expr RLE Engine.
Import ListNotations.
Open Scope Z_scope.

(** ** Block symbols, the block table, and the block denotation *)

Definition BSym := nat.
Definition BRun : Set := (BSym * Expr)%type.
Definition BTbl := BSym -> list Sym.

Record BCfg : Set := mkBCfg {
  b_st : St;
  b_hs : Sym;
  b_L : list BRun;
  b_R : list BRun
}.

(** [nat] -> [Sym] for the two raw symbols (anything else is [S0]). *)
Definition nsym (n : nat) : Sym := match n with O => S0 | _ => S1 end.

(** [n] concatenated copies of a cell word. *)
Definition nreps (l : list Sym) (n : nat) : list Sym := concat (repeat l n).

Lemma nreps_0 : forall l, nreps l 0 = [].
Proof. reflexivity. Qed.

Lemma nreps_S : forall l n, nreps l (S n) = l ++ nreps l n.
Proof. reflexivity. Qed.

Lemma nreps_add : forall l a b, nreps l (a + b) = nreps l a ++ nreps l b.
Proof.
  intros l a b. induction a as [|a IH]; simpl.
  - reflexivity.
  - rewrite !nreps_S, IH, app_assoc. reflexivity.
Qed.

Lemma nreps_1 : forall l, nreps l 1 = l.
Proof. intro l. rewrite nreps_S, nreps_0, app_nil_r. reflexivity. Qed.

Lemma nreps_single : forall x n, nreps [x] n = repeat x n.
Proof.
  intros x n. induction n as [|n IH]; simpl; [reflexivity|].
  rewrite nreps_S, IH. reflexivity.
Qed.

(** The block denotation of a half-tape. *)
Definition bdside (tbl : BTbl) (nu : nat -> Z) (rs : list BRun) : list Sym :=
  flat_map (fun r => nreps (tbl (fst r)) (cnt nu (snd r))) rs.

Definition bdcfg (tbl : BTbl) (nu : nat -> Z) (c : BCfg) : cconf :=
  (b_st c, (bdside tbl nu (b_L c), b_hs c, bdside tbl nu (b_R c))).

Definition bsem (tbl : BTbl) (nu : nat -> Z) (c : BCfg) : ExecState :=
  lift (bdcfg tbl nu c).

Lemma bdside_cons : forall tbl nu s e t,
  bdside tbl nu ((s, e) :: t) =
  nreps (tbl s) (cnt nu e) ++ bdside tbl nu t.
Proof. reflexivity. Qed.

(** A canonical table: raw ids map to the singleton cell. *)
Definition raw_ok (tbl : BTbl) : Prop :=
  tbl O = [S0] /\ tbl (S O) = [S1].

(** ** Push / merge / trim on block runs (mirror of [RLE]) *)

Definition bpush (lo : list Z) (s : BSym) (e : Expr) (rs : list BRun)
  : option (list BRun) :=
  if negb (expr_ge lo e 0) then None else
  match rs with
  | [] => if Nat.eqb s 0 then Some [] else Some [(s, e)]
  | (s', e') :: t =>
      if Nat.eqb s s'
      then if expr_ge lo e' 0 then Some ((s', eadd e e') :: t) else None
      else Some ((s, e) :: rs)
  end.

Lemma bpush_den : forall tbl lo s e rs rs' nu,
  raw_ok tbl ->
  bpush lo s e rs = Some rs' -> bge lo nu ->
  lift_side (bdside tbl nu rs') =
  lift_side (nreps (tbl s) (cnt nu e) ++ bdside tbl nu rs).
Proof.
  intros tbl lo s e rs rs' nu [Hr0 Hr1] H Hb.
  unfold bpush in H.
  destruct (expr_ge lo e 0) eqn:Hge; simpl in H; [|discriminate].
  destruct rs as [|[s' e'] t].
  - destruct (Nat.eqb s 0) eqn:Hs; injection H as <-.
    + apply Nat.eqb_eq in Hs; subst s.
      rewrite Hr0. simpl bdside.
      rewrite app_nil_r, nreps_single, lift_side_blanks.
      apply lift_side_nil.
    + reflexivity.
  - destruct (Nat.eqb s s') eqn:Hs.
    + destruct (expr_ge lo e' 0) eqn:Hge'; [|discriminate].
      injection H as <-.
      apply Nat.eqb_eq in Hs; subst s'.
      rewrite !bdside_cons.
      rewrite cnt_add;
        [| eapply expr_ge_sound; eauto | eapply expr_ge_sound; eauto].
      rewrite nreps_add, app_assoc. reflexivity.
    + injection H as <-. rewrite bdside_cons. reflexivity.
Qed.

Fixpoint bmerge_adj (lo : list Z) (rs : list BRun) : option (list BRun) :=
  match rs with
  | [] => Some []
  | (s, e) :: t =>
      match bmerge_adj lo t with
      | None => None
      | Some [] => Some [(s, e)]
      | Some ((s', e') :: t') =>
          if Nat.eqb s s'
          then if expr_ge lo e 0 && expr_ge lo e' 0
               then Some ((s, eadd e e') :: t') else None
          else Some ((s, e) :: (s', e') :: t')
      end
  end.

Lemma bmerge_adj_den : forall tbl lo rs rs' nu,
  bmerge_adj lo rs = Some rs' -> bge lo nu ->
  bdside tbl nu rs' = bdside tbl nu rs.
Proof.
  induction rs as [|[s e] t IH]; intros rs' nu H Hb; simpl in H.
  - injection H as <-. reflexivity.
  - destruct (bmerge_adj lo t) as [mt|] eqn:Em; [|discriminate].
    specialize (IH mt nu eq_refl Hb).
    destruct mt as [|[s' e'] t'].
    + injection H as <-.
      rewrite !bdside_cons, <- IH. simpl. reflexivity.
    + destruct (Nat.eqb s s') eqn:Hs.
      * destruct (expr_ge lo e 0 && expr_ge lo e' 0) eqn:Hge;
          [|discriminate].
        apply andb_prop in Hge as [Hge1 Hge2].
        injection H as <-.
        apply Nat.eqb_eq in Hs; subst s'.
        rewrite !bdside_cons, <- IH, bdside_cons.
        rewrite cnt_add;
          [| eapply expr_ge_sound; eauto | eapply expr_ge_sound; eauto].
        rewrite nreps_add, app_assoc. reflexivity.
      * injection H as <-.
        rewrite !bdside_cons, <- IH. reflexivity.
Qed.

Lemma bdside_lift_cons_cong : forall tbl nu s e A B,
  lift_side (bdside tbl nu A) = lift_side (bdside tbl nu B) ->
  lift_side (bdside tbl nu ((s, e) :: A)) =
  lift_side (bdside tbl nu ((s, e) :: B)).
Proof.
  intros tbl nu s e A B H.
  rewrite !bdside_cons. apply lift_side_app. exact H.
Qed.

Fixpoint btrim_blanks (rs : list BRun) : list BRun :=
  match rs with
  | [] => []
  | (s, e) :: t =>
      match btrim_blanks t with
      | [] => if Nat.eqb s 0 then [] else [(s, e)]
      | t' => (s, e) :: t'
      end
  end.

Lemma btrim_blanks_den : forall tbl rs nu,
  raw_ok tbl ->
  lift_side (bdside tbl nu (btrim_blanks rs)) = lift_side (bdside tbl nu rs).
Proof.
  induction rs as [|[s e] t IH]; intros nu Hraw; [reflexivity|].
  destruct Hraw as [Hr0 Hr1].
  specialize (IH nu (conj Hr0 Hr1)).
  cbn [btrim_blanks].
  destruct (btrim_blanks t) as [|r' t'] eqn:Et.
  - assert (Hbl : lift_side (bdside tbl nu t) = blank_side).
    { rewrite <- IH. apply lift_side_nil. }
    destruct (Nat.eqb s 0) eqn:Hs.
    + apply Nat.eqb_eq in Hs; subst s.
      rewrite bdside_cons, Hr0, nreps_single.
      change (bdside tbl nu []) with (@nil Sym).
      rewrite lift_side_nil.
      symmetry. apply lift_side_blank_app. exact Hbl.
    + apply (bdside_lift_cons_cong tbl nu s e [] t).
      change (bdside tbl nu []) with (@nil Sym).
      rewrite lift_side_nil, Hbl. reflexivity.
  - apply (bdside_lift_cons_cong tbl nu s e (r' :: t') t). exact IH.
Qed.

(** ** The engine loop against [bdside]: concrete step, chain hops, and
    block PEEL (block HOP is added below).  The concrete-tape /
    [Reach] plumbing is reused verbatim from [Engine]. *)

Definition sym_to_nat (s : Sym) : BSym := match s with S0 => O | S1 => S O end.

Lemma raw_tbl_sym_to_nat : forall tbl s,
  raw_ok tbl -> tbl (sym_to_nat s) = [s].
Proof. intros tbl [|] [H0 H1]; simpl; assumption. Qed.

Definition bcell (tbl : BTbl) (s : BSym) : Sym := hd S0 (tbl s).

Lemma len1_eq : forall (l : list Sym), length l = 1%nat -> l = [hd S0 l].
Proof.
  intros [|x [|y t]] H; simpl in H; try discriminate. reflexivity.
Qed.

Definition bassemble (q : St) (h : Sym) (mv : Dir) (dep app : list BRun)
  : BCfg :=
  match mv with
  | DR => mkBCfg q h dep app
  | DL => mkBCfg q h app dep
  end.

Definition blsem (tbl : BTbl) (nu : nat -> Z) (q : St) (mv : Dir)
    (dep app : list BRun) : ExecState :=
  let df := lift_side (bdside tbl nu dep) in
  let af := lift_side (bdside tbl nu app) in
  match mv with
  | DR => (q, mkTape df (af O) (tail_side af))
  | DL => (q, mkTape (tail_side af) (af O) df)
  end.

Lemma blsem_concrete_R : forall tbl nu q dep app,
  blsem tbl nu q DR dep app =
  lift (q, (bdside tbl nu dep, chd (bdside tbl nu app),
            ctl (bdside tbl nu app))).
Proof.
  intros. unfold blsem.
  rewrite lift_cc, lift_side_tl, lift_side_hd. reflexivity.
Qed.

Lemma blsem_concrete_L : forall tbl nu q dep app,
  blsem tbl nu q DL dep app =
  lift (q, (ctl (bdside tbl nu app), chd (bdside tbl nu app),
            bdside tbl nu dep)).
Proof.
  intros. unfold blsem.
  rewrite lift_cc, lift_side_tl, lift_side_hd. reflexivity.
Qed.

Lemma basem_bassemble : forall tbl nu q h mv dep app,
  bsem tbl nu (bassemble q h mv dep app) =
  (match mv with
   | DR => lift (q, (bdside tbl nu dep, h, bdside tbl nu app))
   | DL => lift (q, (bdside tbl nu app, h, bdside tbl nu dep))
   end).
Proof. intros tbl nu q h [|] dep app; reflexivity. Qed.

(** Peel one copy of a block run into its cells, as singleton runs. *)
Definition peel_cells (tbl : BTbl) (s : BSym) : list BRun :=
  map (fun c => (sym_to_nat c, econst 1)) (tbl s).

Lemma bdside_peel_cells : forall tbl nu s,
  raw_ok tbl -> bdside tbl nu (peel_cells tbl s) = tbl s.
Proof.
  intros tbl nu s Hraw. unfold peel_cells, bdside.
  induction (tbl s) as [|c t IH]; simpl; [reflexivity|].
  rewrite (raw_tbl_sym_to_nat tbl c Hraw).
  change (cnt nu (econst 1)) with 1%nat. rewrite nreps_1.
  unfold bdside in IH. rewrite IH. reflexivity.
Qed.

Lemma bdside_app : forall tbl nu a b,
  bdside tbl nu (a ++ b) = bdside tbl nu a ++ bdside tbl nu b.
Proof. intros. unfold bdside. apply flat_map_app. Qed.

(** The engine crossing loop (fuel-bounded: block peel grows [app]). *)
Fixpoint beng_cross (tm : TM) (tbl : BTbl) (lo : list Z) (q : St)
    (mv : Dir) (fuel : nat) (app dep : list BRun)
  : option (list BRun * list BRun * Sym * list Tr) :=
  match fuel with
  | O => None
  | S fuel' =>
    match app with
    | [] =>
        if chainable tm q S0 mv then None else Some ([], dep, S0, [])
    | (s, e) :: rest =>
        if (2 <=? length (tbl s))%nat then
          (* block run: peel one copy (hop is handled by [beng_step]) *)
          match (if eeqb e (econst 1) then Some rest
                 else if expr_ge lo e 2 then Some ((s, eaddc e (-1)) :: rest)
                 else None) with
          | None => None
          | Some tl => beng_cross tm tbl lo q mv fuel'
                         (peel_cells tbl s ++ tl) dep
          end
        else if (length (tbl s) =? 1)%nat then
          let c := bcell tbl s in
          if chainable tm q c mv then
            match tm q c with
            | Some tr =>
                if expr_ge lo e 1 then
                  match bpush lo (sym_to_nat (t_write tr)) e dep with
                  | Some dep' =>
                      match beng_cross tm tbl lo q mv fuel' rest dep' with
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

Lemma bdside_raw_cons : forall tbl nu s e rest,
  length (tbl s) = 1%nat ->
  bdside tbl nu ((s, e) :: rest) =
  repeat (bcell tbl s) (cnt nu e) ++ bdside tbl nu rest.
Proof.
  intros tbl nu s e rest Hlen.
  rewrite bdside_cons. unfold bcell.
  rewrite (len1_eq (tbl s) Hlen) at 1. rewrite nreps_single. reflexivity.
Qed.

Lemma bdside_peel_eq : forall tbl lo nu s e rest tl,
  raw_ok tbl -> bge lo nu ->
  (2 <=? length (tbl s))%nat = true ->
  (if eeqb e (econst 1) then Some rest
   else if expr_ge lo e 2 then Some ((s, eaddc e (-1)) :: rest)
   else None) = Some tl ->
  bdside tbl nu (peel_cells tbl s ++ tl) = bdside tbl nu ((s, e) :: rest).
Proof.
  intros tbl lo nu s e rest tl Hraw Hb Hblk Htl.
  rewrite bdside_app, (bdside_peel_cells tbl nu s Hraw), bdside_cons.
  destruct (eeqb e (econst 1)) eqn:He1.
  - injection Htl as <-.
    assert (Hc : cnt nu e = 1%nat).
    { unfold cnt. rewrite (eeqb_eval _ _ nu He1), eval_econst. reflexivity. }
    rewrite Hc, nreps_1. reflexivity.
  - destruct (expr_ge lo e 2) eqn:Hge2; [|discriminate].
    injection Htl as <-.
    rewrite bdside_cons.
    pose proof (expr_ge_sound lo e 2 nu Hge2 Hb) as He2.
    assert (Hc : cnt nu e = S (cnt nu (eaddc e (-1)))).
    { unfold cnt. rewrite eval_eaddc. lia. }
    rewrite Hc, nreps_S, app_assoc. reflexivity.
Qed.

Lemma beng_cross_sound : forall tm tbl lo fuel q mv app dep app' dep' h F,
  raw_ok tbl ->
  beng_cross tm tbl lo q mv fuel app dep = Some (app', dep', h, F) ->
  forall nu, bge lo nu ->
  exists n,
    Reach tm F n (blsem tbl nu q mv dep app)
                 (bsem tbl nu (bassemble q h mv dep' app')).
Proof.
  intros tm tbl lo fuel.
  induction fuel as [|fuel IH]; intros q mv app dep app' dep' h F Hraw H nu Hb;
    [cbn [beng_cross] in H; discriminate|].
  cbn [beng_cross] in H.
  destruct app as [|[s e] rest].
  - (* empty approached side *)
    destruct (chainable tm q S0 mv) eqn:Hch; [discriminate|].
    injection H as <- <- <- <-.
    exists O.
    assert (Heq : blsem tbl nu q mv dep [] =
                  bsem tbl nu (bassemble q S0 mv dep [])).
    { rewrite basem_bassemble.
      destruct mv;
        [rewrite blsem_concrete_L | rewrite blsem_concrete_R]; reflexivity. }
    setoid_rewrite Heq. apply Reach_refl.
  - destruct (2 <=? length (tbl s))%nat eqn:Hblk.
    + (* block run: peel one copy *)
      remember (if eeqb e (econst 1) then Some rest
                else if expr_ge lo e 2 then Some ((s, eaddc e (-1)) :: rest)
                else None) as opt eqn:Hopt.
      destruct opt as [tl|].
      2:{ cbn iota in H. discriminate H. }
      cbn iota in H.
      destruct (IH q mv (peel_cells tbl s ++ tl) dep app' dep' h F Hraw H
                  nu Hb) as (n & HR).
      exists n.
      assert (Heq : blsem tbl nu q mv dep (peel_cells tbl s ++ tl) =
                    blsem tbl nu q mv dep ((s, e) :: rest)).
      { unfold blsem.
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
        destruct (bpush lo (sym_to_nat (t_write tr)) e dep) as [depP|]
          eqn:Hpush; [|discriminate].
        destruct (beng_cross tm tbl lo q mv fuel rest depP)
          as [[[[appX depX] hX] FX]|] eqn:Hrec; [|discriminate].
        injection H as <- <- <- <-.
        destruct (IH q mv rest depP appX depX hX FX Hraw Hrec nu Hb)
          as (n2 & HR2).
        pose proof (expr_ge_sound lo e 1 nu Hge Hb) as He1.
        assert (Hsplit : exists n0, cnt nu e = S n0).
        { unfold cnt. exists (Z.to_nat (eval nu e) - 1)%nat. lia. }
        destruct Hsplit as [n0 Hn1].
        destruct tr as [w d q']. simpl in Hnx, Hdir. subst d q'.
        pose proof (bpush_den tbl lo (sym_to_nat w) e dep depP nu Hraw
                      Hpush Hb) as Hpden.
        rewrite (raw_tbl_sym_to_nat tbl w Hraw), nreps_single, Hn1 in Hpden.
        assert (HR1 : Reach tm [(q, c)] (S n0)
                  (blsem tbl nu q mv dep ((s, e) :: rest))
                  (blsem tbl nu q mv depP rest)).
        { destruct mv.
          - (* DL *)
            assert (Hstart : blsem tbl nu q DL dep ((s, e) :: rest) =
              lift (q, (repeat c n0 ++ bdside tbl nu rest, c,
                        bdside tbl nu dep))).
            { rewrite blsem_concrete_L, (bdside_raw_cons tbl nu s e rest Hlen1),
                Hn1. reflexivity. }
            assert (Hlend :
              lift (q, (ctl (bdside tbl nu rest), chd (bdside tbl nu rest),
                        repeat w (S n0) ++ bdside tbl nu dep)) =
              blsem tbl nu q DL depP rest).
            { rewrite blsem_concrete_L, !lift_cc, Hpden. reflexivity. }
            split; [|split].
            + rewrite Hstart, <- Hlend.
              apply csteps_lift. apply chain_cc_L_end; exact Htr.
            + intros m Hm. rewrite Hstart. eexists. split.
              * apply csteps_lift.
                apply (chain_cc_L_mid tm q c w Htr m n0 (bdside tbl nu rest)
                         (bdside tbl nu dep) ltac:(lia)).
              * left. reflexivity.
            + intros t [<- | []].
              exists O. eexists. split; [lia|]. split; [reflexivity|].
              rewrite Hstart. reflexivity.
          - (* DR *)
            assert (Hstart : blsem tbl nu q DR dep ((s, e) :: rest) =
              lift (q, (bdside tbl nu dep, c,
                        repeat c n0 ++ bdside tbl nu rest))).
            { rewrite blsem_concrete_R, (bdside_raw_cons tbl nu s e rest Hlen1),
                Hn1. reflexivity. }
            assert (Hlend :
              lift (q, (repeat w (S n0) ++ bdside tbl nu dep,
                        chd (bdside tbl nu rest), ctl (bdside tbl nu rest))) =
              blsem tbl nu q DR depP rest).
            { rewrite blsem_concrete_R, !lift_cc, Hpden. reflexivity. }
            split; [|split].
            + rewrite Hstart, <- Hlend.
              apply csteps_lift. apply chain_cc_R_end; exact Htr.
            + intros m Hm. rewrite Hstart. eexists. split.
              * apply csteps_lift.
                apply (chain_cc_R_mid tm q c w Htr m n0 (bdside tbl nu dep)
                         (bdside tbl nu rest) ltac:(lia)).
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
           assert (Heq : blsem tbl nu q mv dep ((s, e) :: rest) =
                         bsem tbl nu (bassemble q c mv dep rest)).
           { rewrite basem_bassemble.
             destruct mv;
               [rewrite blsem_concrete_L | rewrite blsem_concrete_R];
               rewrite (bdside_raw_cons tbl nu s e rest Hlen1), Hc1;
               reflexivity. }
           setoid_rewrite Heq. apply Reach_refl.
        -- destruct (expr_ge lo e 2) eqn:Hge2; [|discriminate].
           injection H as <- <- <- <-.
           exists O.
           pose proof (expr_ge_sound lo e 2 nu Hge2 Hb) as He2.
           assert (Hcs : cnt nu e = S (cnt nu (eaddc e (-1)))).
           { unfold cnt. rewrite eval_eaddc. lia. }
           assert (Heq : blsem tbl nu q mv dep ((s, e) :: rest) =
                         bsem tbl nu (bassemble q c mv dep
                                        ((s, eaddc e (-1)) :: rest))).
           { rewrite basem_bassemble.
             destruct mv;
               [rewrite blsem_concrete_L | rewrite blsem_concrete_R];
               rewrite (bdside_raw_cons tbl nu s e rest Hlen1),
                 (bdside_raw_cons tbl nu s (eaddc e (-1)) rest Hlen1), Hcs;
               reflexivity. }
           setoid_rewrite Heq. apply Reach_refl.
Qed.

(** One engine op: the concrete step plus its chain hops / block peels. *)
Definition beng_step (tm : TM) (tbl : BTbl) (lo : list Z) (fuel : nat)
    (c : BCfg) : option (BCfg * list Tr) :=
  match tm (b_st c) (b_hs c) with
  | None => None
  | Some tr =>
      let q1 := t_next tr in
      let '(dep0, app0) :=
        match t_dir tr with
        | DR => (b_L c, b_R c)
        | DL => (b_R c, b_L c)
        end in
      match bpush lo (sym_to_nat (t_write tr)) (econst 1) dep0 with
      | None => None
      | Some dep =>
          match beng_cross tm tbl lo q1 (t_dir tr) fuel app0 dep with
          | Some (app', dep', h, F) =>
              Some (bassemble q1 h (t_dir tr) dep' app',
                    (b_st c, b_hs c) :: F)
          | None => None
          end
      end
  end.

Theorem beng_step_sound : forall tm tbl lo fuel c c' F,
  raw_ok tbl ->
  beng_step tm tbl lo fuel c = Some (c', F) ->
  forall nu, bge lo nu ->
  exists n, (1 <= n)%nat /\ Reach tm F n (bsem tbl nu c) (bsem tbl nu c').
Proof.
  intros tm tbl lo fuel c c' F Hraw H nu Hb.
  unfold beng_step in H.
  destruct (tm (b_st c) (b_hs c)) as [tr|] eqn:Htr; [|discriminate].
  pose proof Hraw as [Hr0 Hr1].
  assert (Hdep_gen : forall dep0 dep,
    bpush lo (sym_to_nat (t_write tr)) (econst 1) dep0 = Some dep ->
    lift_side (bdside tbl nu dep) =
    push_side (t_write tr) (lift_side (bdside tbl nu dep0))).
  { intros dep0 dep Hpush.
    rewrite (bpush_den tbl lo (sym_to_nat (t_write tr)) (econst 1) dep0 dep
               nu Hraw Hpush Hb).
    rewrite (raw_tbl_sym_to_nat tbl (t_write tr) Hraw).
    change (cnt nu (econst 1)) with 1%nat. rewrite nreps_1.
    change ([t_write tr] ++ bdside tbl nu dep0)
      with (t_write tr :: bdside tbl nu dep0).
    apply lift_side_cons. }
  destruct (t_dir tr) eqn:Hdir.
  - (* DL: departed side is R *)
    destruct (bpush lo (sym_to_nat (t_write tr)) (econst 1) (b_R c)) as [dep|]
      eqn:Hpush; [|discriminate].
    destruct (beng_cross tm tbl lo (t_next tr) DL fuel (b_L c) dep)
      as [[[[app' dep'] h] F']|] eqn:Hcr; [|discriminate].
    injection H as <- <-.
    destruct (beng_cross_sound tm tbl lo fuel (t_next tr) DL (b_L c) dep
                app' dep' h F' Hraw Hcr nu Hb) as (n2 & HR2).
    pose proof (Hdep_gen (b_R c) dep Hpush) as Hdep.
    assert (Hstep : step tm (bsem tbl nu c) =
                    Some (blsem tbl nu (t_next tr) DL dep (b_L c))).
    { unfold bsem, bdcfg. rewrite lift_cc.
      unfold step. cbn [t_head fst snd]. rewrite Htr, Hdir.
      unfold blsem, tape_move. rewrite Hdep. reflexivity. }
    assert (HR1 : Reach tm [(b_st c, b_hs c)] 1 (bsem tbl nu c)
                    (blsem tbl nu (t_next tr) DL dep (b_L c))).
    { pose proof (Reach_one tm _ _ Hstep) as HRo.
      replace (trans_of (bsem tbl nu c)) with (b_st c, b_hs c) in HRo;
        [exact HRo | reflexivity]. }
    exists (1 + n2)%nat. split; [lia|].
    change ((b_st c, b_hs c) :: F') with ([(b_st c, b_hs c)] ++ F').
    exact (Reach_compose _ _ _ _ _ _ _ _ HR1 HR2).
  - (* DR: departed side is L *)
    destruct (bpush lo (sym_to_nat (t_write tr)) (econst 1) (b_L c)) as [dep|]
      eqn:Hpush; [|discriminate].
    destruct (beng_cross tm tbl lo (t_next tr) DR fuel (b_R c) dep)
      as [[[[app' dep'] h] F']|] eqn:Hcr; [|discriminate].
    injection H as <- <-.
    destruct (beng_cross_sound tm tbl lo fuel (t_next tr) DR (b_R c) dep
                app' dep' h F' Hraw Hcr nu Hb) as (n2 & HR2).
    pose proof (Hdep_gen (b_L c) dep Hpush) as Hdep.
    assert (Hstep : step tm (bsem tbl nu c) =
                    Some (blsem tbl nu (t_next tr) DR dep (b_R c))).
    { unfold bsem, bdcfg. rewrite lift_cc.
      unfold step. cbn [t_head fst snd]. rewrite Htr, Hdir.
      unfold blsem, tape_move. rewrite Hdep. reflexivity. }
    assert (HR1 : Reach tm [(b_st c, b_hs c)] 1 (bsem tbl nu c)
                    (blsem tbl nu (t_next tr) DR dep (b_R c))).
    { pose proof (Reach_one tm _ _ Hstep) as HRo.
      replace (trans_of (bsem tbl nu c)) with (b_st c, b_hs c) in HRo;
        [exact HRo | reflexivity]. }
    exists (1 + n2)%nat. split; [lia|].
    change ((b_st c, b_hs c) :: F') with ([(b_st c, b_hs c)] ++ F').
    exact (Reach_compose _ _ _ _ _ _ _ _ HR1 HR2).
Qed.
