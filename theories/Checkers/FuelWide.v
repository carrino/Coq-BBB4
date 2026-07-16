(** * FuelWide: the class-refined n-gram instance for rule (c2).

    The completeness upgrade promised by Fuel.v's header: pair each
    n-gram context with the FuelClass capped LOWER-BOUND classes of
    the two half-tapes ([cconf * (fclass * fclass)]) and read the
    runner rule's "fuel >= 1" off the tracked class instead of the
    window.  The class updates are total, deterministic functions of
    the context alone: a step deposits the written symbol behind the
    move ([finc]) and crosses the window cell ahead of it ([fdec]) --
    both symbols sit inside the window, so no guessing is involved
    and the refined successor relation is the base one paired with
    one class update.

    Everything else is reused verbatim: the gram sets and their
    growth, the seeding, the lex measure vocabulary (values and
    deltas only ever read the base context), and the engine -- here
    the per-SCC runner engine of FuelSCC.v, since the machines this
    instance exists for (the 62 upstream neverqh_fuel holdouts) all
    have their runner SCCs strictly inside a lex-peeled graph.
    Left-runners go through [mirror_never_qh]. *)

From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement CTape PosEnc Records Closure.
From BBB4.Checkers Require Import ExactClosure NGram Fuel FuelClass FuelSCC.
Import ListNotations.

(** ** Refined contexts and their encoding *)

Definition fcconf : Type := (cconf * (fclass * fclass))%type.

Definition fcl_app (fc : fclass) (p : positive) : positive :=
  match fc with F0 => p~0~0 | F1 => p~0~1 | F2 => p~1~0 end%positive.

Lemma fcl_app_inj : forall x y p q,
  fcl_app x p = fcl_app y q -> x = y /\ p = q.
Proof.
  destruct x, y; simpl; intros p q H;
    solve [ split; congruence
          | discriminate
          | injection H as H; discriminate ].
Qed.

Definition fcconf_enc (a : fcconf) : positive :=
  fcl_app (fst (snd a)) (fcl_app (snd (snd a)) (cconf_enc (fst a))).

Lemma fcconf_enc_inj : forall a b, fcconf_enc a = fcconf_enc b -> a = b.
Proof.
  intros [b1 [l1 r1]] [b2 [l2 r2]] H; unfold fcconf_enc in H; simpl in H.
  apply fcl_app_inj in H as [Hl H].
  apply fcl_app_inj in H as [Hr H].
  apply cconf_enc_inj in H.
  congruence.
Qed.

Definition fw_state (a : fcconf) : St := ec_state (fst a).

(** ** Covering *)

Definition fw_covers (n : nat) (lset rset : gset)
    (a : fcconf) (c : ExecState) : Prop :=
  ng_covers n lset rset (fst a) c /\
  class_holds (fst (snd a)) (t_left (snd c)) /\
  class_holds (snd (snd a)) (t_right (snd c)).

Lemma fw_covers_state : forall n lset rset a c,
  fw_covers n lset rset a c -> fw_state a = fst c.
Proof.
  intros n lset rset a c (Hng & _ & _).
  apply (ng_covers_state n lset rset (fst a) c Hng).
Qed.

(** ** Successors: base branches, one deterministic class update *)

Definition fw_upd (tm : TM) (b : cconf) (fl fr : fclass)
    : fclass * fclass :=
  let '(q, (lw, s, rw)) := b in
  match tm q s with
  | None => (fl, fr)
  | Some tr =>
      match t_dir tr with
      | DR => (finc (nb (t_write tr)) fl, fdec (nb (chd rw)) fr)
      | DL => (fdec (nb (chd lw)) fl, finc (nb (t_write tr)) fr)
      end
  end.

Definition fw_succs (tm : TM) (lset rset : gset) (a : fcconf)
    : option (list fcconf) :=
  let '(b, fls) := a in
  match ng_succs tm lset rset b with
  | None => None
  | Some l =>
      let fls' := fw_upd tm b (fst fls) (snd fls) in
      Some (map (fun b' => (b', fls')) l)
  end.

Lemma fw_succs_sound : forall tm n lset rset a c,
  1 <= n ->
  fw_covers n lset rset a c ->
  match fw_succs tm lset rset a, step tm c with
  | Some l, Some c' => exists a', In a' l /\ fw_covers n lset rset a' c'
  | Some _, None => False
  | None, _ => True
  end.
Proof.
  intros tm n lset rset [b [fl fr]] c Hn (Hng & Hcl & Hcr).
  simpl in Hng, Hcl, Hcr.
  unfold fw_succs.
  destruct (ng_succs tm lset rset b) as [l|] eqn:Es; [|exact I].
  destruct (step tm c) as [c'|] eqn:Est;
    [| exact (ng_succs_nohalt tm lset rset n b c l Hng Es Est)].
  destruct (ng_succs_sound_some tm n lset rset b c l c' Hn Hng Es Est)
    as (b' & HInl & Hng').
  exists (b', fw_upd tm b fl fr).
  split.
  { apply in_map_iff. exists b'. split; [reflexivity | exact HInl]. }
  split; [exact Hng' |].
  (* the class updates track the concrete tape edit *)
  destruct b as [q [[lw s] rw]].
  destruct c as [qc tp].
  destruct Hng as (Hq & Hh & Hlw & Hrw & _).
  simpl in Hq, Hh, Hcl, Hcr. subst qc.
  unfold ng_succs in Es.
  destruct (tm q s) as [tr|] eqn:Etr; [|discriminate].
  unfold step in Est. rewrite Hh, Etr in Est.
  injection Est as <-.
  unfold fw_upd. rewrite Etr.
  destruct n as [|m]; [lia|].
  destruct (t_dir tr) eqn:Ed; cbn [tape_move t_left t_right snd fst].
  - (* DL: left crosses lw's head cell, right gains the write *)
    split.
    + rewrite Hlw, win_chd.
      apply (fdec_sound fl (t_left tp) Hcl).
    + apply (finc_sound (t_write tr) fr (t_right tp) Hcr).
  - (* DR: left gains the write, right crosses rw's head cell *)
    split.
    + apply (finc_sound (t_write tr) fl (t_left tp) Hcl).
    + rewrite Hrw, win_chd.
      apply (fdec_sound fr (t_right tp) Hcr).
Qed.

(** ** The runner node predicates, reading window OR class *)

Definition fwnode_moves_right (tm : TM) (a : fcconf) : bool :=
  fnode_moves_right tm (fst a).

Definition fwnode_rfuel_ge1 (a : fcconf) : bool :=
  fnode_rfuel_ge1 (fst a) || fc_ge1 (snd (snd a)).

Lemma fwnode_moves_right_sound : forall tm n lset rset a c,
  fwnode_moves_right tm a = true ->
  fw_covers n lset rset a c ->
  steps_right tm c.
Proof.
  intros tm n lset rset a c H (Hng & _ & _).
  exact (fnode_moves_right_sound tm n lset rset (fst a) c H Hng).
Qed.

Lemma fwnode_rfuel_ge1_sound : forall n lset rset a c,
  fwnode_rfuel_ge1 a = true ->
  fw_covers n lset rset a c ->
  has_right_nonblank (snd c).
Proof.
  intros n lset rset [b [fl fr]] c H (Hng & _ & Hcr).
  unfold fwnode_rfuel_ge1 in H. simpl in H, Hcr.
  apply orb_prop in H as [Hw | Hc].
  - exact (fnode_rfuel_ge1_sound n lset rset b c Hw Hng).
  - exact (fc_ge1_sound fr (t_right (snd c)) Hcr Hc).
Qed.

(** ** Seed classes: exact capped counts of the anchor sides *)

Definition class_of_count (k : nat) : fclass :=
  match k with 0 => F0 | 1 => F1 | _ => F2 end.

Definition class_of_list (l : list Sym) : fclass :=
  class_of_count (count1 l).

Lemma count1_ge1_side : forall l, 1 <= count1 l -> side_ge1 (lift_side l).
Proof.
  induction l as [|x t IH]; simpl; intros H; [lia|].
  destruct x.
  - destruct (IH H) as (j & Hj). exists (S j). exact Hj.
  - exists 0. discriminate.
Qed.

Lemma count1_ge2_side : forall l, 2 <= count1 l -> side_ge2 (lift_side l).
Proof.
  induction l as [|x t IH]; simpl; intros H; [lia|].
  destruct x.
  - destruct (IH H) as (i & j & Hij & Hi & Hj).
    exists (S i), (S j). repeat split; [lia | exact Hi | exact Hj].
  - destruct (count1_ge1_side t ltac:(lia)) as (j & Hj).
    exists 0, (S j). repeat split; [lia | discriminate | exact Hj].
Qed.

Lemma class_of_list_holds : forall l,
  class_holds (class_of_list l) (lift_side l).
Proof.
  intros l. unfold class_of_list, class_of_count.
  destruct (count1 l) as [|[|k]] eqn:Ec; simpl.
  - exact I.
  - apply count1_ge1_side. lia.
  - apply count1_ge2_side. lia.
Qed.

Definition fw_start (n : nat) (cc : cconf) : fcconf :=
  let '(q, (l, h, r)) := cc in
  (ng_start n cc, (class_of_list l, class_of_list r)).

Lemma fw_start_covers : forall n lset rset cc,
  ng_seed_ok n lset rset cc = true ->
  fw_covers n lset rset (fw_start n cc) (lift cc).
Proof.
  intros n lset rset [q [[l h] r]] H.
  split; [| split].
  - exact (ng_start_covers n lset rset (q, (l, h, r)) H).
  - apply class_of_list_holds.
  - apply class_of_list_holds.
Qed.

(** ** Certificate denotation: refined-key tables, base measures *)

Definition fpmape_get (m : PositiveMap.tree nat) (a : fcconf) : nat :=
  match PositiveMap.find (fcconf_enc a) m with
  | Some v => v
  | None => 0
  end.

Definition fw_comp_denote (tm : TM) (n : nat) (c : ngcomp)
    : lexcomp fcconf :=
  match c with
  | NgRank phi =>
      let pm := pmap_of cconf cconf_enc phi in
      LexRank fcconf (fun a => pmap_get cconf cconf_enc pm (fst a))
  | NgMeas m K phi gate =>
      let pm := pmap_of cconf cconf_enc phi in
      let gs := pset_of cconf cconf_enc gate in
      LexMeas fcconf (ngm_val m)
              (fun a a' => ngm_delta tm m (fst a) (fst a')) K
              (fun a => pmap_get cconf cconf_enc pm (fst a))
              (fun a => pset_mem cconf cconf_enc (fst a) gs)
  | NgRankE phi =>
      let pm := pmape_of phi in
      LexRank fcconf (fpmape_get pm)
  | NgPattE p rg K phi gate =>
      if pm_ok n p rg then
        let pm := pmape_of phi in
        let gs := psete_of gate in
        LexMeas fcconf (pm_val p rg)
                (fun a a' => pm_delta tm p rg (fst a) (fst a')) K
                (fpmape_get pm)
                (fun a => PositiveSet.mem (fcconf_enc a) gs)
      else LexRank fcconf (fun _ => 0)
  end.

Definition fw_cert_denote (tm : TM) (n : nat)
    (ct : list ngcomp * list positive)
    : list (lexcomp fcconf) * (fcconf -> bool) :=
  (map (fw_comp_denote tm n) (fst ct),
   let gs := psete_of (snd ct) in
   fun a => PositiveSet.mem (fcconf_enc a) gs).

(** ** The checker *)

Definition ngram_check_neverqh_fuelw (tm : TM) (n t fuel rounds : nat)
    (cert : St -> list ngcomp * list positive) : bool :=
  (1 <=? n) &&
  match csteps tm t c0 with
  | Some cc =>
      let '(q, (l, h, r)) := cc in
      let lset0 := gadds (ng_seed_side n l) gempty in
      let rset0 := gadds (ng_seed_side n r) gempty in
      let a0 := ng_start n cc in
      let '(lset, rset) := ng_grow tm a0 fuel rounds lset0 rset0 in
      ng_seed_ok n lset rset cc &&
      closure_check_neverqh_fuelscc tm fcconf fcconf_enc fw_state
        (fw_succs tm lset rset)
        (fwnode_moves_right tm) fwnode_rfuel_ge1
        t fuel (fw_start n cc)
        (fun q => fw_cert_denote tm n (cert q))
  | None => false
  end.

Theorem ngram_check_neverqh_fuelw_sound : forall tm n t fuel rounds cert,
  ngram_check_neverqh_fuelw tm n t fuel rounds cert = true ->
  NeverQuasiHaltsSt tm.
Proof.
  intros tm n t fuel rounds cert H.
  unfold ngram_check_neverqh_fuelw in H.
  apply andb_prop in H as [Hn H].
  apply Nat.leb_le in Hn.
  destruct (csteps tm t c0) as [[q [[l h] r]]|] eqn:Et; [|discriminate].
  match type of H with
  | (let '(_, _) := ?G in _) = true => destruct G as [lset rset] eqn:Eg
  end.
  cbv beta iota zeta in H.
  apply andb_prop in H as [Hseed Hcheck].
  apply (closure_check_neverqh_fuelscc_sound tm fcconf fcconf_enc fw_state
           (fw_succs tm lset rset)
           (fwnode_moves_right tm) fwnode_rfuel_ge1
           (fw_covers n lset rset)) in Hcheck;
    [assumption | | | | | | |].
  - exact fcconf_enc_inj.
  - intros a c Hc. eapply fw_covers_state; eauto.
  - intros a c Hc. apply fw_succs_sound; assumption.
  - intros a c Hmr Hc. eapply fwnode_moves_right_sound; eauto.
  - intros a c Hrf Hc. eapply fwnode_rfuel_ge1_sound; eauto.
  - intros ct' Hct'. rewrite Et in Hct'. injection Hct' as <-.
    apply fw_start_covers. exact Hseed.
  - intros q0. apply Forall_forall. intros comp Hin.
    cbn [fw_cert_denote fst] in Hin.
    apply in_map_iff in Hin. destruct Hin as (c & <- & _).
    destruct c as [phi | m K phi gate | phi | pp rg K phi gate]; simpl.
    + exact I.
    + intros a cc a' cc' sl Hca Hca' Hstep Es HInl.
      apply (ngm_exact tm n lset rset m (fst a) cc (fst a') cc' Hn
               (proj1 Hca) Hstep).
    + exact I.
    + destruct (pm_ok n pp rg) eqn:Epm; [|exact I].
      apply andb_prop in Epm as [He Hb].
      intros a cc a' cc' sl Hca Hca' Hstep Es HInl.
      apply (pm_exact tm n lset rset pp rg (fst a) cc (fst a') cc');
        try assumption.
      * apply existsb_exists in He as (x & Hx & Hx1).
        apply sym_eqb_spec in Hx1. subst x. assumption.
      * destruct rg; apply Nat.leb_le; assumption.
      * exact (proj1 Hca).
Qed.
