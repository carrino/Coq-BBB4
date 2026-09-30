(** * TriNuTr: TriGlueTr's block families with an l-adic liveness.

    [TriGlueTr] proves that an instruction fires from every anchor by an
    affine ranking per node (leaf, values mod [P]) that drops at every
    step between two leaves that do not fire it.  On the Collatz-like rows
    (SCOPING_INSTR.md §7.4.TA) no such ranking exists at any [P]: a round
    ends on a residue of a growing parameter, only one residue case fires
    the rare instruction, and the non-firing case maps the parameter by
    [c -> 3c/2] (in a shifted coordinate).  The run of non-firing rounds
    is finite because each one divides [c] by two, so it is bounded by the
    2-adic valuation of the start, which no ranking in the values sees.

    Here the families, dispatch trees, leaves, chains, node set and boot
    are TriGlueTr's, checked by TriGlueTr's own [fams_ok] / [boot_ok] and
    enumerated by its [tnxt]; only the liveness is new.  Per instruction
    [t] the certificate carries a modulus [l >= 2] and per node a LEVEL, an
    affine form [E >= 1] and an affine ranking [V].  On every step from a
    node to a node, neither of whose leaves fires [t], either the level
    drops, or it stays and

      [B * E(src z) = A * E'(tgt z)] coefficient-wise, [gcd B l = 1],
      [A = l^j * b], [gcd b l = 1],

    so [nu_l (E') = nu_l (E) - j], and when [j = 0] the ranking drops by
    one.  [(level, nu_l E, V)] then decreases lexicographically, and [t]
    fires.  [A] and [B] are computed from the contents of the two forms;
    soundness only uses the checked equation.  With [E = 1] and one level
    this is TriGlueTr's liveness.

    Only axiom: [functional_extensionality_dep] (through [CTape]). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr Mirror.
From BBB4.Checkers Require Import WrapTr LapDecider.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Checkers Require Import TCyclerQHTr.
From BBB4.Counters Require Import WTape LapCertGlueLift LapGlueTr SweepGlueTr TriGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

(** ** The l-adic valuation *)

Fixpoint nuf (l fuel x : nat) : nat :=
  match fuel with
  | 0 => 0
  | S f => if (0 <? x) && (x mod l =? 0) then S (nuf l f (x / l)) else 0
  end.

Definition nu (l x : nat) : nat := nuf l x x.

Section Nu.

Variable l : nat.
Hypothesis Hl : 2 <= l.

Lemma nuf_fuel : forall f1 f2 x, x <= f1 -> x <= f2 -> nuf l f1 x = nuf l f2 x.
Proof.
  induction f1 as [|f1 IH]; intros [|f2] x H1 H2; cbn [nuf].
  - reflexivity.
  - assert (x = 0) by lia. subst. reflexivity.
  - assert (x = 0) by lia. subst. reflexivity.
  - destruct ((0 <? x) && (x mod l =? 0)) eqn:E; [|reflexivity].
    apply andb_prop in E as [E _]. apply Nat.ltb_lt in E.
    assert (x / l < x) by (apply Nat.div_lt; lia).
    f_equal. apply IH; lia.
Qed.

Lemma nu_zero_mod : forall x, 0 < x -> x mod l <> 0 -> nu l x = 0.
Proof.
  intros x Hx Hm. unfold nu. destruct x as [|x]; [lia|]. cbn [nuf].
  destruct (S x mod l =? 0) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - rewrite andb_false_r. reflexivity.
Qed.

Lemma nu_mul : forall x, 0 < x -> nu l (l * x) = S (nu l x).
Proof.
  intros x Hx. unfold nu at 1.
  destruct (l * x) as [|n] eqn:En; [lia|]. cbn [nuf].
  rewrite <- En.
  assert (Hm : l * x mod l = 0) by (rewrite Nat.mul_comm; apply Nat.Div0.mod_mul).
  assert (Hd : l * x / l = x) by (rewrite Nat.mul_comm; apply Nat.div_mul; lia).
  replace ((0 <? l * x) && (l * x mod l =? 0)) with true
    by (symmetry; apply andb_true_intro; split; [apply Nat.ltb_lt; lia | apply Nat.eqb_eq; exact Hm]).
  rewrite Hd. f_equal. unfold nu. apply nuf_fuel; nia.
Qed.

Lemma nu_pow : forall j y, 0 < y -> nu l (l ^ j * y) = j + nu l y.
Proof.
  induction j as [|j IH]; intros y Hy; cbn [Nat.pow].
  - rewrite Nat.mul_1_l. reflexivity.
  - rewrite <- Nat.mul_assoc.
    assert (Hp : 0 < l ^ j * y)
      by (apply Nat.mul_pos_pos; [apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia | exact Hy]).
    rewrite (nu_mul _ Hp), (IH y Hy). reflexivity.
Qed.

Lemma nu_coprime : forall b x, Nat.gcd b l = 1 -> 0 < x -> nu l (b * x) = nu l x.
Proof.
  intros b x Hb. induction x as [x IH] using lt_wf_ind. intros Hx.
  assert (Hb0 : 0 < b).
  { destruct b; [|lia]. rewrite Nat.gcd_0_l in Hb. lia. }
  destruct (Nat.eq_dec (x mod l) 0) as [Hm | Hm].
  - apply Nat.Div0.mod_divides in Hm as (y & ->).
    assert (Hy : 0 < y) by nia.
    replace (b * (l * y)) with (l * (b * y)) by ring.
    rewrite !nu_mul by nia. f_equal. apply IH; nia.
  - rewrite (nu_zero_mod x Hx Hm).
    apply nu_zero_mod; [nia|].
    intros Hbm. apply Hm.
    apply Nat.Div0.mod_divides in Hbm as (k & Hk).
    assert (Hdiv : Nat.divide l (b * x)) by (exists k; lia).
    apply Nat.gauss in Hdiv; [| rewrite Nat.gcd_comm; exact Hb].
    destruct Hdiv as (m & ->). rewrite Nat.Div0.mod_mul. reflexivity.
Qed.

End Nu.

(** [A = l^j * b] *)
Fixpoint lstrip (l fuel A : nat) : nat * nat :=
  match fuel with
  | 0 => (0, A)
  | S f =>
      if (0 <? A) && (A mod l =? 0)
      then let jb := lstrip l f (A / l) in (S (fst jb), snd jb)
      else (0, A)
  end.

Lemma lstrip_ok : forall l fuel A, A = l ^ fst (lstrip l fuel A) * snd (lstrip l fuel A).
Proof.
  intros l. induction fuel as [|f IH]; intros A; cbn [lstrip].
  - cbn. lia.
  - destruct ((0 <? A) && (A mod l =? 0)) eqn:E; [|cbn; lia].
    apply andb_prop in E as [_ E]. apply Nat.eqb_eq in E.
    cbn [fst snd Nat.pow]. rewrite <- Nat.mul_assoc, <- IH.
    apply Nat.Div0.div_exact. exact E.
Qed.

(** the gcd of a form's coefficients; soundness never looks inside *)
Definition acont (N : nat) (e : aexp) : nat :=
  fold_left Nat.gcd (map (fun k => tcoef k (a_t e)) (seq 0 N)) (a_c e).

Definition nu_edge (l : nat) (e1 e2 : aexp) (vd : bool) : bool :=
  let N := Nat.max (tbound (a_t e1)) (tbound (a_t e2)) in
  let g1 := acont N e1 in
  let g2 := acont N e2 in
  let d := Nat.gcd g1 g2 in
  let B := g2 / d in
  let A := g1 / d in
  let jb := lstrip l A A in
  ale (ascale B e1) (ascale A e2) && ale (ascale A e2) (ascale B e1)
  && (Nat.gcd B l =? 1) && (Nat.gcd (snd jb) l =? 1)
  && ((1 <=? fst jb) || vd).

Lemma nu_edge_sound : forall l e1 e2 vd z, 2 <= l -> nu_edge l e1 e2 vd = true ->
  0 < aeval z e1 -> 0 < aeval z e2 ->
  nu l (aeval z e2) < nu l (aeval z e1) \/ (nu l (aeval z e2) = nu l (aeval z e1) /\ vd = true).
Proof.
  intros l e1 e2 vd z Hl H H1 H2. unfold nu_edge in H.
  set (N := Nat.max (tbound (a_t e1)) (tbound (a_t e2))) in H.
  set (B := acont N e2 / Nat.gcd (acont N e1) (acont N e2)) in H.
  set (A := acont N e1 / Nat.gcd (acont N e1) (acont N e2)) in H.
  apply andb_prop in H as [H Hj]. apply andb_prop in H as [H Hb].
  apply andb_prop in H as [H HB]. apply andb_prop in H as [Hle1 Hle2].
  apply Nat.eqb_eq in Hb, HB.
  pose proof (ale_sound z _ _ Hle1) as E1. pose proof (ale_sound z _ _ Hle2) as E2.
  rewrite !aeval_ascale in E1, E2.
  assert (Heq : B * aeval z e1 = A * aeval z e2) by lia.
  pose proof (lstrip_ok l A A) as HA.
  set (j := fst (lstrip l A A)) in *. set (b := snd (lstrip l A A)) in *.
  assert (Hb0 : 0 < b).
  { destruct b as [|b']; [|lia]. rewrite Nat.gcd_0_l in Hb. lia. }
  assert (Hnu : nu l (aeval z e1) = j + nu l (aeval z e2)).
  { rewrite <- (nu_coprime l Hl B (aeval z e1) HB H1), Heq, HA.
    replace (l ^ j * b * aeval z e2) with (l ^ j * (b * aeval z e2)) by ring.
    rewrite nu_pow by (exact Hl || nia).
    rewrite nu_coprime by (exact Hl || exact Hb || exact H2). reflexivity. }
  destruct (Nat.eq_dec j 0) as [Hj0 | Hj0]; [|left; lia].
  right. split; [lia|].
  apply orb_prop in Hj as [Hj | Hj]; [apply Nat.leb_le in Hj; lia | exact Hj].
Qed.

(** ** Lexicographic order on lists of naturals of one length *)

Fixpoint lexlt (a b : list nat) : Prop :=
  match a, b with
  | x :: a', y :: b' => x < y \/ (x = y /\ lexlt a' b')
  | _, _ => False
  end.

Lemma lex_ind : forall K (Q : list nat -> Prop),
  (forall b, length b = K -> (forall a, length a = K -> lexlt a b -> Q a) -> Q b) ->
  forall b, length b = K -> Q b.
Proof.
  induction K as [|K IH]; intros Q Hstep b Hb.
  - apply Hstep; [exact Hb|]. intros a Ha Hab. destruct b; [|discriminate].
    destruct a; cbn in Hab; contradiction.
  - destruct b as [|y b']; [discriminate|]. cbn in Hb. injection Hb as Hb.
    revert b' Hb. induction y as [y IHy] using lt_wf_ind. intros b' Hb.
    apply (IH (fun c => Q (y :: c))); [|exact Hb].
    intros c Hc Hinner. cbv beta in Hinner. apply Hstep; [cbn; rewrite Hc; reflexivity|].
    intros a Ha Hab. destruct a as [|x a']; [discriminate|]. cbn in Ha. injection Ha as Ha.
    cbn in Hab. destruct Hab as [Hlt | [-> Hab]].
    + exact (IHy x Hlt a' Ha).
    + exact (Hinner a' Ha Hab).
Qed.

(** ** The certificate *)

(** per node: a level, the form [E], and the rankings [V_0 .. V_(K-1)] *)
Definition nrow := (nat * (nat * list nat) * list (nat * list nat))%type.

Record ncert := mkNC {
  nc_tc   : tcert;                                   (** TriGlueTr's, its ranks unused *)
  nc_live : list (Instr * (nat * nat * list nrow))   (** per instruction: l, K, per node *)
}.

Definition nrank_of (lv : list (Instr * (nat * nat * list nrow))) (t : Instr)
  : nat * nat * list nrow :=
  match find (fun p => instr_eqb (fst p) t) lv with Some p => snd p | None => (2, 0, []) end.

Definition nrow_at (rows : list nrow) (i : nat) : nrow := nth i rows (0, (1, []), []).

(** the rankings drop lexicographically along an edge *)
Fixpoint vlexd (ks : list nat) (Vs Vs' : list (nat * list nat)) (src tgt : list aexp) : bool :=
  match ks with
  | [] => false
  | k :: ks' =>
      let v := veval (nth k Vs (0, [])) src in
      let v' := veval (nth k Vs' (0, [])) tgt in
      ale (aaddc v' 1) v || (ale v' v && vlexd ks' Vs Vs' src tgt)
  end.

Definition vvec (ks : list nat) (Vs : list (nat * list nat)) (vals : list nat) : list nat :=
  map (fun k => vval (nth k Vs (0, [])) vals) ks.

Lemma vlexd_sound : forall ks Vs Vs' src tgt z, vlexd ks Vs Vs' src tgt = true ->
  lexlt (vvec ks Vs' (map (aeval z) tgt)) (vvec ks Vs (map (aeval z) src)).
Proof.
  induction ks as [|k ks IH]; intros Vs Vs' src tgt z H; cbn [vlexd] in H; [discriminate|].
  unfold vvec. cbn [map lexlt]. fold (vvec ks Vs' (map (aeval z) tgt)).
  fold (vvec ks Vs (map (aeval z) src)).
  apply orb_prop in H as [H | H].
  - left. pose proof (ale_sound z _ _ H) as Hle. rewrite aeval_aaddc, !veval_ok in Hle. lia.
  - apply andb_prop in H as [H1 H2]. pose proof (ale_sound z _ _ H1) as Hle.
    rewrite !veval_ok in Hle.
    destruct (Nat.eq_dec (vval (nth k Vs' (0, [])) (map (aeval z) tgt))
                         (vval (nth k Vs (0, [])) (map (aeval z) src))) as [He | He].
    + right. split; [exact He | exact (IH _ _ _ _ z H2)].
    + left. lia.
Qed.

Definition nstep_ok (l K : nat) (r r' : nrow) (src tgt : list aexp) : bool :=
  match r, r' with
  | (lv, E, Vs), (lv', E', Vs') =>
      (2 <=? l) && (1 <=? fst E) && (1 <=? fst E')
      && ((lv' <? lv)
          || ((lv' =? lv) && nu_edge l (veval E src) (veval E' tgt)
                                     (vlexd (seq 0 K) Vs Vs' src tgt)))
  end.

Definition nmeas_row (l K : nat) (r : nrow) (vals : list nat) : list nat :=
  match r with (lv, E, Vs) => lv :: nu l (vval E vals) :: vvec (seq 0 K) Vs vals end.

Lemma nmeas_row_length : forall l K r vals, length (nmeas_row l K r vals) = S (S K).
Proof.
  intros l K [[lv E] Vs] vals. cbn [nmeas_row length]. unfold vvec.
  rewrite map_length, seq_length. reflexivity.
Qed.

Lemma vval_ge_c : forall V vals, fst V <= vval V vals.
Proof. intros [c vs] vals. unfold vval. cbn [fst snd]. lia. Qed.

Lemma nstep_sound : forall l K r r' src tgt z, nstep_ok l K r r' src tgt = true ->
  lexlt (nmeas_row l K r' (map (aeval z) tgt)) (nmeas_row l K r (map (aeval z) src)).
Proof.
  intros l K [[lv E] Vs] [[lv' E'] Vs'] src tgt z H. unfold nstep_ok in H.
  apply andb_prop in H as [H Hm]. apply andb_prop in H as [H HE'].
  apply andb_prop in H as [Hl HE]. apply Nat.leb_le in Hl, HE, HE'.
  cbn [nmeas_row lexlt].
  apply orb_prop in Hm as [Hm | Hm].
  - left. apply Nat.ltb_lt in Hm. exact Hm.
  - apply andb_prop in Hm as [Hlv Hm]. apply Nat.eqb_eq in Hlv. right. split; [exact Hlv|].
    assert (P1 : 0 < aeval z (veval E src))
      by (rewrite veval_ok; pose proof (vval_ge_c E (map (aeval z) src)); lia).
    assert (P2 : 0 < aeval z (veval E' tgt))
      by (rewrite veval_ok; pose proof (vval_ge_c E' (map (aeval z) tgt)); lia).
    destruct (nu_edge_sound l _ _ _ z Hl Hm P1 P2) as [Hd | [Hd Hv]];
      rewrite !veval_ok in Hd; [left; exact Hd|].
    right. split; [exact Hd|]. exact (vlexd_sound _ _ _ _ _ z Hv).
Qed.

Definition nlive_node_ok (tmw : TM) (nw : ncert) (fired : list (list Instr))
    (i : nat) (lr : nat * list nat) : bool :=
  let w := nc_tc nw in
  let P := tc_P w in
  let lvs := tc_leaves w in
  match nth_error lvs (fst lr) with
  | None => false
  | Some lf =>
      let fl := nth (fst lr) fired [] in
      forallb (fun s =>
        let sub := zsub P s in
        let src := map (asubst sub) (rsub (tl_reg lf)) in
        let tgt := map (asubst sub) (tl_tgt lf) in
        let rho' := map (fun e => a_c e mod P) tgt in
        forallb (pdiv P) tgt
        && forallb (fun l' =>
             match nth_error lvs l' with
             | None => true
             | Some lf' =>
                 if (tl_f lf' =? tl_g lf) && compat P (tl_reg lf') tgt then
                   match nidx (tc_S w) l' rho' with
                   | None => false
                   | Some i' =>
                       let fl' := nth l' fired [] in
                       forallb (fun t =>
                         tr_inb t (tc_pins w) || tr_inb t fl || tr_inb t fl'
                         || let lr := nrank_of (nc_live nw) t in
                            nstep_ok (fst (fst lr)) (snd (fst lr)) (nrow_at (snd lr) i)
                                     (nrow_at (snd lr) i') src tgt) all_Instr
                   end
                 else true
             end) (seq 0 (length lvs)))
        (sassign P (tl_reg lf) (snd lr))
  end.

Definition nlive_ok (tmw : TM) (nw : ncert) : bool :=
  let w := nc_tc nw in
  let fired := map (leaf_fired tmw) (tc_leaves w) in
  (0 <? tc_P w)
  && forallb (fun ilr => nlive_node_ok tmw nw fired (fst ilr) (snd ilr))
             (combine (seq 0 (length (tc_S w))) (tc_S w)).

Definition tri_nu_check (tm : TM) (nw : ncert) : bool :=
  let w := nc_tc nw in
  let tmw := tm_wrap_trs tm (tc_pins w) in
  fams_ok tmw (tc_fams w) (tc_leaves w) && boot_ok tmw w && nlive_ok tmw nw.

(** ** Soundness *)

Section Live.

Variable tm : TM.
Variable nw : ncert.

Let w := nc_tc nw.
Let tmw := tm_wrap_trs tm (tc_pins w).
Let fams := tc_fams w.
Let lvs := tc_leaves w.
Let P := tc_P w.

Hypothesis Hfams : fams_ok tmw fams lvs = true.
Hypothesis Hlive : nlive_ok tmw nw = true.

Lemma nHP : 0 < P.
Proof.
  unfold nlive_ok in Hlive. apply andb_prop in Hlive as [H _]. apply Nat.ltb_lt, H.
Qed.

Lemma nlive_node : forall i lr, nth_error (tc_S w) i = Some lr ->
  nlive_node_ok tmw nw (map (leaf_fired tmw) lvs) i lr = true.
Proof.
  intros i lr H. unfold nlive_ok in Hlive. apply andb_prop in Hlive as [_ Hl].
  rewrite forallb_forall in Hl. apply (Hl (i, lr)).
  assert (Hlt : i < length (tc_S w)) by (apply nth_error_Some; rewrite H; discriminate).
  assert (Hc : forall s, nth_error (combine (seq s (length (tc_S w))) (tc_S w)) i
                         = Some (s + i, lr)).
  { clear Hl. revert i H Hlt. induction (tc_S w) as [|x xs IH]; intros [|i] H Hlt s;
      cbn in *; try discriminate; try lia.
    - injection H as ->. rewrite Nat.add_0_r. reflexivity.
    - rewrite <- Nat.add_succ_comm. apply IH; [exact H | lia]. }
  specialize (Hc 0). apply nth_error_In in Hc. exact Hc.
Qed.

Definition nGoodS (a : nat * list nat) : Prop := Good fams a /\ nodeidx w a <> None.

Definition nleafof (a : nat * list nat) : option tleaf :=
  match nth_error fams (fst a) with
  | Some F => match fwalk F (snd a) with
              | Some (l, _, _) => nth_error lvs l
              | None => None
              end
  | None => None
  end.

Definition nfires_at (a : nat * list nat) (t : Instr) : bool :=
  match nleafof a with Some lf => tr_inb t (leaf_fired tmw lf) | None => false end.

Definition nmeas (t : Instr) (a : nat * list nat) : list nat :=
  let lr := nrank_of (nc_live nw) t in
  match nodeidx w a with
  | Some i => nmeas_row (fst (fst lr)) (snd (fst lr)) (nrow_at (snd lr) i) (snd a)
  | None => repeat 0 (S (S (snd (fst lr))))
  end.

Lemma nmodl_rsub : forall R z, length z = length R ->
  modl P (map (aeval z) (rsub R))
  = map (fun Mz => (fst (fst Mz) * snd Mz + snd (fst Mz)) mod P) (combine R z).
Proof.
  intros R z Hl. apply nth_ext with (d := 0) (d' := 0).
  - unfold modl. rewrite !map_length, rsub_length, combine_length. lia.
  - intros k Hk. unfold modl in Hk |- *. rewrite !map_length, rsub_length in Hk.
    rewrite (nth_map_lt _ _ _ 0 0) by (rewrite map_length, rsub_length; exact Hk).
    rewrite rsub_nth by exact Hk.
    rewrite (nth_map_lt _ _ _ ((0, 0), 0) 0) by (rewrite combine_length; lia).
    rewrite combine_nth by lia. reflexivity.
Qed.

Lemma nnext_ok : forall a, nGoodS a ->
  nGoodS (tnxt fams lvs a)
  /\ forall t, ~ In t (tc_pins w) -> nfires_at a t = false ->
       nfires_at (tnxt fams lvs a) t = false ->
       lexlt (nmeas t (tnxt fams lvs a)) (nmeas t a).
Proof.
  intros a [Ha Hn].
  destruct (walk_leaf tmw fams lvs Hfams a Ha)
    as (F & lf & l & R & z & HF & Hw & Hlf & _ & HR & Hok & Hv & HzR).
  unfold nodeidx in Hn. fold w fams in Hn. rewrite HF, Hw in Hn.
  destruct (nidx (tc_S w) l (modl (tc_P w) (snd a))) as [i|] eqn:Ei; [|contradiction].
  pose proof (nidx_ok _ _ _ _ Ei) as HSi.
  pose proof (nlive_node _ _ HSi) as Hln.
  unfold nlive_node_ok in Hln. fold w in Hln. cbn [fst snd] in Hln. fold lvs in Hln.
  rewrite Hlf in Hln.
  rewrite forallb_forall in Hln.
  set (s := modl P z).
  assert (Hs : In s (sassign (tc_P w) (tl_reg lf) (modl (tc_P w) (snd a)))).
  { fold P. rewrite HR, Hv, nmodl_rsub by exact HzR. apply sassign_in; [exact nHP | exact HzR]. }
  specialize (Hln s Hs). cbv zeta in Hln. apply andb_prop in Hln as [Hdiv Hln].
  rewrite forallb_forall in Hln.
  destruct (step_ok tmw fams lvs Hfams a Ha) as (_ & Ha').
  assert (Hnx : tnxt fams lvs a = (tl_g lf, map (aeval z) (tl_tgt lf))).
  { unfold tnxt. rewrite HF, Hw, Hlf. reflexivity. }
  destruct (walk_leaf tmw fams lvs Hfams _ Ha')
    as (G & lf' & l' & R' & z2 & HG & Hw' & Hlf' & Hfl' & HR' & Hok' & Hv' & HzR').
  rewrite Hnx in HG, Hw', Hfl', Hv'. cbn [fst snd] in HG, Hw', Hfl', Hv'.
  set (z' := map (fun x => x / P) z).
  set (tgt := map (asubst (zsub (tc_P w) s)) (tl_tgt lf)) in *.
  set (src := map (asubst (zsub (tc_P w) s)) (rsub (tl_reg lf))) in *.
  assert (Hzs : forall e, aeval z' (asubst (zsub (tc_P w) s) e) = aeval z e).
  { intros e. subst z' s. apply aeval_zsub. exact nHP. }
  assert (Htgt : map (aeval z') tgt = map (aeval z) (tl_tgt lf)).
  { subst tgt. rewrite map_map. apply map_ext. exact Hzs. }
  assert (Hsrc : map (aeval z') src = snd a).
  { subst src. rewrite map_map, Hv, <- HR. apply map_ext. exact Hzs. }
  assert (Hl' : In l' (seq 0 (length (tc_leaves w)))).
  { apply in_seq. split; [lia|]. apply nth_error_Some. fold lvs. rewrite Hlf'. discriminate. }
  specialize (Hln l' Hl'). fold lvs in Hln. rewrite Hlf' in Hln.
  destruct (leaf_ok_inv _ _ _ _ Hok) as (g & _ & _ & _ & Hg & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & _ & _ & Htl & _).
  destruct (leaf_ok_inv _ _ _ _ Hok') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & _ & _ & _ & HrG).
  fold fams in Hg. rewrite HG in Hg. injection Hg as <-.
  assert (Hcomp : compat (tc_P w) (tl_reg lf') tgt = true).
  { apply (compat_ok (tc_P w) z' (tl_reg lf') tgt z2 Hdiv).
    - subst tgt. rewrite map_length, Htl, HrG. reflexivity.
    - intros k Hk. rewrite HR' in Hk |- *.
      assert (Hk2 : k < length tgt) by (subst tgt; rewrite map_length, Htl, <- HrG, HR'; exact Hk).
      rewrite <- (nth_map_lt (aeval z') tgt k (aconst 0) 0 Hk2), Htgt, Hv'.
      apply rsub_nth. exact Hk. }
  rewrite Hfl', Nat.eqb_refl, Hcomp in Hln. cbn [andb] in Hln.
  assert (Hrho : map (fun e => a_c e mod tc_P w) tgt = modl (tc_P w) (map (aeval z) (tl_tgt lf))).
  { rewrite <- Htgt. unfold modl. rewrite map_map. apply map_ext_in. intros e He.
    rewrite forallb_forall in Hdiv. symmetry. apply pdiv_mod. exact (Hdiv e He). }
  rewrite Hrho in Hln.
  destruct (nidx (tc_S w) l' (modl (tc_P w) (map (aeval z) (tl_tgt lf)))) as [i'|] eqn:Ei';
    [|discriminate].
  assert (Hn' : nodeidx w (tnxt fams lvs a) = Some i').
  { unfold nodeidx. rewrite Hnx. cbn [fst snd]. fold fams. rewrite HG, Hw'. exact Ei'. }
  split.
  - split; [exact Ha' | rewrite Hn'; discriminate].
  - intros t Hpin Hf Hf'.
    unfold nfires_at, nleafof in Hf, Hf'.
    rewrite HF, Hw, Hlf in Hf. rewrite Hnx in Hf'. cbn [fst snd] in Hf'.
    rewrite HG, Hw', Hlf' in Hf'.
    rewrite forallb_forall in Hln. specialize (Hln t (all_Instr_complete t)).
    assert (Hpin' : tr_inb t (tc_pins w) = false).
    { destruct (tr_inb t (tc_pins w)) eqn:E; [|reflexivity].
      exfalso. apply Hpin. apply tr_inb_spec. exact E. }
    assert (Hfl : nth l (map (leaf_fired tmw) lvs) [] = leaf_fired tmw lf).
    { apply nth_error_nth. apply map_nth_error. exact Hlf. }
    assert (Hfl2 : nth l' (map (leaf_fired tmw) lvs) [] = leaf_fired tmw lf').
    { apply nth_error_nth. apply map_nth_error. exact Hlf'. }
    rewrite Hpin', Hfl, Hfl2, Hf, Hf' in Hln. cbn [orb] in Hln.
    pose proof (nstep_sound _ _ _ _ _ _ z' Hln) as Hlex.
    rewrite Htgt, Hsrc in Hlex.
    unfold nmeas. rewrite Hn'. unfold nodeidx. fold fams. rewrite HF, Hw, Ei.
    rewrite Hnx. cbn [snd]. exact Hlex.
Qed.

Definition nFiresFrom (c : cconf) (t : Instr) : Prop :=
  exists k e, stepn tmw k (lift c) = Some e /\ instr_of e = t.

Lemma nfires_lex : forall t, ~ In t (tc_pins w) ->
  forall a, nGoodS a -> nFiresFrom (tanc fams a) t.
Proof.
  intros t Hpin a0.
  set (K := snd (fst (nrank_of (nc_live nw) t))).
  assert (Hlen : forall a, length (nmeas t a) = S (S K)).
  { intros a. unfold nmeas. destruct (nodeidx w a); [apply nmeas_row_length|].
    apply repeat_length. }
  refine (lex_ind (S (S K)) (fun b => forall a, nmeas t a = b -> nGoodS a ->
                                     nFiresFrom (tanc fams a) t) _ (nmeas t a0) (Hlen a0)
                  a0 eq_refl).
  intros b _ IH a <- Ha.
  assert (Hfire : forall b, nGoodS b -> nfires_at b t = true -> nFiresFrom (tanc fams b) t).
  { intros b [Hb _] Ef.
    destruct (walk_leaf tmw fams lvs Hfams b Hb)
      as (F & lf & l & R & z & HF & Hw & Hlf & _ & HR & Hok & Hv & _).
    unfold nfires_at, nleafof in Ef. rewrite HF, Hw, Hlf in Ef.
    apply tr_inb_spec in Ef.
    destruct (leaf_fires _ _ _ _ _ Hok Ef z) as (k & c & Hk & Hc).
    exists k, (lift c). split.
    - unfold tanc. rewrite HF, Hv, <- HR. apply csteps_lift. exact Hk.
    - rewrite cinstr_lift. exact Hc. }
  destruct (nfires_at a t) eqn:Ef; [exact (Hfire a Ha Ef)|].
  destruct (step_ok tmw fams lvs Hfams a (proj1 Ha)) as ((m & c' & Hm & Hl & _) & _).
  destruct (nnext_ok a Ha) as (Ha' & Hrk).
  assert (Hback : forall t', nFiresFrom (tanc fams (tnxt fams lvs a)) t' ->
                             nFiresFrom (tanc fams a) t')
    by (intros t' (k & e & Hk & He); exists (m + k), e;
        split; [rewrite stepn_add, (csteps_lift _ _ _ _ Hm), Hl; exact Hk | exact He]).
  apply Hback.
  destruct (nfires_at (tnxt fams lvs a) t) eqn:Ef'; [exact (Hfire _ Ha' Ef')|].
  exact (IH _ (Hlen _) (Hrk t Hpin Ef Ef') _ eq_refl Ha').
Qed.

Definition ntriCf (a0 : nat * list nat) (p : positive) : cconf :=
  tanc fams (Nat.iter (Nat.pred (Pos.to_nat p)) (tnxt fams lvs) a0).

Lemma ntriCf_succ : forall a0 p, ntriCf a0 (Pos.succ p) =
  tanc fams (tnxt fams lvs (Nat.iter (Nat.pred (Pos.to_nat p)) (tnxt fams lvs) a0)).
Proof.
  intros a0 p. unfold ntriCf. rewrite Pos2Nat.inj_succ.
  destruct (Pos2Nat.is_succ p) as (m & Hm). rewrite Hm. reflexivity.
Qed.

Lemma niter_good : forall a0, nGoodS a0 -> forall m, nGoodS (Nat.iter m (tnxt fams lvs) a0).
Proof.
  intros a0 H0 m. induction m as [|m IH]; [exact H0|].
  cbn [Nat.iter nat_rect]. exact (proj1 (nnext_ok _ IH)).
Qed.

Theorem tri_nu_glue : forall a0, nGoodS a0 ->
  (exists t0, stepn tmw t0 InitES = Some (lift (tanc fams a0))) ->
  NeverQuasiHaltsTr tm.
Proof.
  intros a0 H0 Hboot.
  apply (glue_neverqhtr tm (tc_pins w) (ntriCf a0) xH).
  - exact Hboot.
  - intros p _. rewrite ntriCf_succ. unfold ntriCf.
    exact (proj1 (step_ok tmw fams lvs Hfams _ (proj1 (niter_good a0 H0 _)))).
  - intros t Hnin p _. apply fire_csteps_of_lift. unfold ntriCf.
    exact (nfires_lex t Hnin _ (niter_good a0 H0 _)).
Qed.

Theorem tri_nu_glue_qh : forall a0 t0, nGoodS a0 ->
  stepn tm t0 InitES = Some (lift (tanc fams a0)) ->
  existsb (fun tg => cfires tm c0 t0 tg) (tc_pins w) = true ->
  (t0 <=? 32779478) = true ->
  NonHalt tm /\ QHBoundTr 32779478 tm /\ QuasiHaltsTr tm.
Proof.
  intros a0 t0 H0 Hboot Hwit Hcap.
  apply (lap_qh_stage tm (tc_pins w) (ntriCf a0) xH t0 32779478).
  - exact Hboot.
  - intros p _. rewrite ntriCf_succ. unfold ntriCf.
    exact (proj1 (step_ok tmw fams lvs Hfams _ (proj1 (niter_good a0 H0 _)))).
  - intros t Hnin p _. apply fire_csteps_of_lift. unfold ntriCf.
    exact (nfires_lex t Hnin _ (niter_good a0 H0 _)).
  - exact Hwit.
  - exact Hcap.
Qed.

End Live.

Theorem tri_nu_sound : forall tm nw, tri_nu_check tm nw = true -> NeverQuasiHaltsTr tm.
Proof.
  intros tm nw H. unfold tri_nu_check in H.
  apply andb_prop in H as [H Hl]. apply andb_prop in H as [Hf Hb].
  destruct nw as [w lv]. cbn [nc_tc] in *.
  apply (tri_nu_glue tm (mkNC w lv) Hf Hl (tc_f0 w, tc_v0 w)); unfold nGoodS; cbn [nc_tc].
  - unfold boot_ok in Hb.
    destruct (nth_error (tc_fams w) (tc_f0 w)) as [F|] eqn:EF; [|discriminate].
    destruct (csteps (tm_wrap_trs tm (tc_pins w)) (tc_t0 w) c0) as [c|]; [|discriminate].
    apply andb_prop in Hb as [Hb Hn]. apply andb_prop in Hb as [_ Hlen].
    apply Nat.eqb_eq in Hlen.
    split; [exists F; split; assumption|].
    destruct (nodeidx w (tc_f0 w, tc_v0 w)); [discriminate | discriminate].
  - unfold boot_ok in Hb.
    destruct (nth_error (tc_fams w) (tc_f0 w)) as [F|] eqn:EF; [|discriminate].
    destruct (csteps (tm_wrap_trs tm (tc_pins w)) (tc_t0 w) c0) as [c|] eqn:E; [|discriminate].
    apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hc _].
    exists (tc_t0 w). rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
    unfold tanc. cbn [fst snd]. rewrite EF. f_equal. exact (ceqb_lift _ _ Hc).
Qed.

Theorem tri_nu_sound_mirror : forall tm nw, tri_nu_check (mirror_tm tm) nw = true ->
  NeverQuasiHaltsTr tm.
Proof.
  intros tm nw H. apply neverqhtr_mirror. exact (tri_nu_sound _ nw H).
Qed.

(** ** Quasihalting rows *)

Definition tri_nu_check_qh (tm : TM) (nw : ncert) : bool :=
  let w := nc_tc nw in
  let tmw := tm_wrap_trs tm (tc_pins w) in
  fams_ok tmw (tc_fams w) (tc_leaves w) && boot_qh_ok tm w && nlive_ok tmw nw
  && existsb (fun tg => cfires tm c0 (tc_t0 w) tg) (tc_pins w)
  && (tc_t0 w <=? sw_boot_cap).

Theorem tri_nu_sound_qh : forall tm nw, tri_nu_check_qh tm nw = true ->
  NonHalt tm /\ QHBoundTr 32779478 tm /\ QuasiHaltsTr tm.
Proof.
  intros tm nw H. unfold tri_nu_check_qh in H.
  apply andb_prop in H as [H Hcap]. apply andb_prop in H as [H Hwit].
  apply andb_prop in H as [H Hl]. apply andb_prop in H as [Hf Hb].
  destruct nw as [w lv]. cbn [nc_tc] in *.
  unfold boot_qh_ok in Hb.
  destruct (nth_error (tc_fams w) (tc_f0 w)) as [F|] eqn:EF; [|discriminate].
  destruct (csteps tm (tc_t0 w) c0) as [c|] eqn:E; [|discriminate].
  apply andb_prop in Hb as [Hb Hn]. apply andb_prop in Hb as [Hc Hlen].
  apply Nat.eqb_eq in Hlen.
  apply (tri_nu_glue_qh tm (mkNC w lv) Hf Hl (tc_f0 w, tc_v0 w) (tc_t0 w)); unfold nGoodS;
    cbn [nc_tc].
  - split; [exists F; split; assumption|].
    destruct (nodeidx w (tc_f0 w, tc_v0 w)); [discriminate | discriminate].
  - rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
    unfold tanc. cbn [fst snd]. rewrite EF. f_equal. exact (ceqb_lift _ _ Hc).
  - exact Hwit.
  - exact (sw_cap_le _ Hcap).
Qed.

Theorem tri_nu_sound_qh_mirror : forall tm nw, tri_nu_check_qh (mirror_tm tm) nw = true ->
  NonHalt tm /\ QHBoundTr 32779478 tm /\ QuasiHaltsTr tm.
Proof.
  intros tm nw H.
  destruct (tri_nu_sound_qh (mirror_tm tm) nw H) as (Hnh & Hb & (t & (n & Hn) & N & HN)).
  split; [exact (mirror_nonhalt tm Hnh) |].
  split; [exact (qhboundtr_mirror 32779478 tm Hb) |].
  exists t. split.
  - exists n. apply mirror_fires. exact Hn.
  - exists N. intros m Hm Hf. apply (HN m Hm). apply mirror_fires. exact Hf.
Qed.
