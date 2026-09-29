(** * CensusTr/RepWLMBTr: multi-block RepWL at TRANSITION level.

    RepWL ([Checkers/RepWL.v], [CensusTr/RepWLTr.v]) cuts every
    departed buffer into blocks of ONE length L.  A bouncer whose tape
    is [(001)^a (0110)^b [head] (01)^c] then needs L = 12, and RepWL
    keeps up to 3L = 36 cells verbatim around the head: the closure
    explodes there first (SCOPING_INSTR 7.3f, 7.4.BR).

    Here the node is the SAME [rconf] (item words were never required
    to share a length: [items_den], [push_side_den], [pop_den] and the
    five measures of [rw_meas_exact] hold for any non-empty words).
    Only the FOLD changes: [mb_fold] cuts the far end of the departed
    buffer at whichever word of a per-side list matches ([mb_cut]),
    so each tape region keeps its own block length.  The policy is
    untrusted in the strongest sense -- [mb_fold_den] holds for ANY
    cut, since the pushed block is literally [skipn c buf] -- so the
    parameters (the word lists, the thresholds) are plain data, and
    the certificate syntax, the measures, the engine and the search
    are RepWL's.

    [mb_tier_tr] is parameter-closed like [rw_tier_tr]: the closure
    and the certificate search run inside the kernel at the finder's
    parameters (tools/censustr/mb_cert_find.py, SCOPING_INSTR 7.4.MB). *)

From Coq Require Import Arith Lia Bool List ZArith PArith.
From Coq Require Import FSets.FMapPositive MSets.MSetPositive.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape PosEnc
  Closure ClosureTr.
From BBB4.Checkers Require Import RepWL WrapTr.
From BBB4.Census Require Import RepWLSearch.
From BBB4.CensusTr Require Import TNF_QHTr RepWLTr.
Import ListNotations.
Open Scope nat_scope.

Set Default Goal Selector "!".

(** ** The parameters

    [mb_DL] / [mb_DR]: the word lists, nearest-first (a left word is
    stored mirrored, as RepWL stores it); [mb_K]: cells a word fold
    must leave in the buffer; [mb_Y]: the buffer length at which word
    folds start; [mb_X]: past it, with no word matching, the farthest
    single cell is folded (unmerged, [push_raw]); [mb_B]: the length of a popped blank block;
    [mb_T]: the run-length saturation threshold. *)

Record mbpar : Type := MbPar {
  mb_DL : list (list Sym);
  mb_DR : list (list Sym);
  mb_K : nat;
  mb_Y : nat;
  mb_X : nat;
  mb_B : nat;
  mb_T : nat
}.

(** ** The fold *)

Definition in_words (w : list Sym) (D : list (list Sym)) : bool :=
  existsb (syms_eqb w) D.

(** A forced fold's block is pushed as an exact one-copy item and
    never merged: a bounded junk run folded cell by cell would
    otherwise become an unbounded [x^T+] item.  A blank block against
    an empty list is absorbed by the blank infinity, as in
    [push_item]. *)
Definition push_raw (w : list Sym) (items : list ritem) : list ritem :=
  match items with
  | [] => if word_blank w then [] else [mkItem w 1 false]
  | _ => mkItem w 1 false :: items
  end.

Lemma push_raw_den : forall b blk items f,
  side_den (b ++ blk) items f ->
  side_den b (push_raw blk items) f.
Proof.
  intros b blk items f (ext & Hden & Hf).
  unfold push_raw.
  assert (Hone : side_den b (mkItem blk 1 false :: items) f).
  { exists (wrep blk 1 ++ ext). split.
    - apply (items_den_cons blk 1 false 1 items ext); [reflexivity | exact Hden].
    - intro i. rewrite Hf. unfold wrep; simpl. rewrite app_nil_r.
      rewrite <- app_assoc. reflexivity. }
  destruct items as [|it rest]; [| exact Hone].
  destruct (word_blank blk) eqn:Eb; [| exact Hone].
  inversion Hden; subst ext.
  exists []. split; [constructor|].
  intro i. rewrite Hf. rewrite !app_nil_r.
  destruct (le_lt_dec (length b) i) as [Hge | Hlt].
  - rewrite nthb_app_r by assumption.
    rewrite (word_blank_nthb blk Eb).
    unfold nthb. rewrite nth_overflow by assumption. reflexivity.
  - rewrite nthb_app_l by assumption. reflexivity.
Qed.

Lemma push_raw_wf : forall w items,
  w <> [] -> Forall item_wf items -> Forall item_wf (push_raw w items).
Proof.
  intros w items Hw Hwf.
  assert (Hit : item_wf (mkItem w 1 false)).
  { split; [simpl; lia|]. split; [discriminate | exact Hw]. }
  unfold push_raw.
  destruct items as [|it rest].
  - destruct (word_blank w); constructor; [exact Hit | constructor].
  - constructor; [exact Hit | exact Hwf].
Qed.

(** Where to cut a departed buffer [buf] (nearest-first): keep
    [firstn c buf], fold [skipn c buf], merging ([true]) for a listed
    word, unmerged ([false]) for a forced single cell.  Word folds
    start at [Y] cells and leave at least [K]; the word is the nearest
    item's when it is listed and matches (a run keeps its phase), else
    a listed word the far end holds TWICE (a rotation of a long word
    does not cut into a short-period run), else any listed word. *)
Definition far_is (K n : nat) (buf w : list Sym) (k : nat) : bool :=
  (1 <=? length w) && (K + k * length w <=? n)
  && syms_eqb (skipn (n - k * length w) buf) (wrep w k).

Definition mb_cut (D : list (list Sym)) (K Y X : nat)
    (buf : list Sym) (items : list ritem) : option (nat * bool) :=
  let n := length buf in
  let pref := match items with
              | mkItem w0 _ _ :: _ => if in_words w0 D then [w0] else []
              | [] => []
              end in
  let single := if X <? n then Some (n - 1, false) else None in
  if Y <=? n then
    match find (fun w => far_is K n buf w 1) pref with
    | Some w => Some (n - length w, true)
    | None =>
        match find (fun w => far_is K n buf w 2) D with
        | Some w => Some (n - length w, true)
        | None =>
            match find (fun w => far_is K n buf w 1) D with
            | Some w => Some (n - length w, true)
            | None => single
            end
        end
    end
  else single.

Definition mb_push (T : nat) (mg : bool) (w : list Sym)
    (items : list ritem) : list ritem :=
  if mg then push_item T w items else push_raw w items.

Fixpoint mb_fold_go (fuel : nat) (D : list (list Sym)) (K Y X T : nat)
    (buf : list Sym) (items : list ritem) : list Sym * list ritem :=
  match fuel with
  | 0 => (buf, items)
  | S f =>
      match mb_cut D K Y X buf items with
      | Some (c, mg) =>
          if c <? length buf
          then mb_fold_go f D K Y X T (firstn c buf)
                 (mb_push T mg (skipn c buf) items)
          else (buf, items)
      | None => (buf, items)
      end
  end.

Definition mb_fold (D : list (list Sym)) (K Y X T : nat)
    (buf : list Sym) (items : list ritem) : list Sym * list ritem :=
  mb_fold_go (length buf) D K Y X T buf items.

Lemma mb_fold_go_den : forall fuel D K Y X T buf items f b' it',
  mb_fold_go fuel D K Y X T buf items = (b', it') ->
  side_den buf items f ->
  side_den b' it' f.
Proof.
  induction fuel as [|fu IH]; intros D K Y X T buf items f b' it' E Hd;
    cbn [mb_fold_go] in E.
  - injection E as <- <-. exact Hd.
  - destruct (mb_cut D K Y X buf items) as [[c mg]|];
      [| injection E as <- <-; exact Hd].
    destruct (c <? length buf); [| injection E as <- <-; exact Hd].
    apply (IH _ _ _ _ _ _ _ _ _ _ E).
    rewrite <- (firstn_skipn c buf) in Hd.
    destruct mg; [apply push_side_den | apply push_raw_den]; exact Hd.
Qed.

Lemma mb_fold_den : forall D K Y X T buf items f b' it',
  mb_fold D K Y X T buf items = (b', it') ->
  side_den buf items f ->
  side_den b' it' f.
Proof.
  intros D K Y X T buf items f b' it' E Hd.
  exact (mb_fold_go_den _ _ _ _ _ _ _ _ _ _ _ E Hd).
Qed.

Lemma mb_fold_go_wf : forall fuel D K Y X T buf items b' it',
  2 <= T ->
  mb_fold_go fuel D K Y X T buf items = (b', it') ->
  Forall item_wf items ->
  Forall item_wf it'.
Proof.
  induction fuel as [|fu IH]; intros D K Y X T buf items b' it' HT E Hw;
    cbn [mb_fold_go] in E.
  - injection E as <- <-. exact Hw.
  - destruct (mb_cut D K Y X buf items) as [[c mg]|];
      [| injection E as <- <-; exact Hw].
    destruct (c <? length buf) eqn:Ec; [| injection E as <- <-; exact Hw].
    apply (IH _ _ _ _ _ _ _ _ _ HT E).
    assert (Hne : skipn c buf <> []).
    { apply Nat.ltb_lt in Ec.
      intro Hn. pose proof (f_equal (@length Sym) Hn) as Hl.
      rewrite skipn_length in Hl. simpl in Hl. lia. }
    destruct mg; cbn [mb_push];
      [apply push_item_wf | apply push_raw_wf]; assumption.
Qed.

Lemma mb_fold_wf : forall D K Y X T buf items b' it',
  2 <= T ->
  mb_fold D K Y X T buf items = (b', it') ->
  Forall item_wf items ->
  Forall item_wf it'.
Proof.
  intros D K Y X T buf items b' it' HT E Hw.
  exact (mb_fold_go_wf _ _ _ _ _ _ _ _ _ _ HT E Hw).
Qed.

Definition mb_fold_l (P : mbpar) (buf : list Sym) (items : list ritem)
    : list Sym * list ritem :=
  mb_fold (mb_DL P) (mb_K P) (mb_Y P) (mb_X P) (mb_T P) buf items.

Definition mb_fold_r (P : mbpar) (buf : list Sym) (items : list ritem)
    : list Sym * list ritem :=
  mb_fold (mb_DR P) (mb_K P) (mb_Y P) (mb_X P) (mb_T P) buf items.

(** ** The step: [rw_succs] with the fold replaced *)

Definition mb_succs (tm : TM) (P : mbpar) (a : rconf)
    : option (list rconf) :=
  let '(q, (li, lb, h, rb, ri)) := a in
  match tm q h with
  | None => None
  | Some tr =>
      let w := t_write tr in
      let q2 := t_next tr in
      match t_dir tr with
      | DR =>
          match rb with
          | x :: rb' => Some [(q2, (li, w :: lb, x, rb', ri))]
          | [] =>
              let '(lb2, li2) := mb_fold_l P (w :: lb) li in
              match pop_item (mb_B P) ri with
              | None => None
              | Some ps =>
                  Some (map (fun p =>
                          (q2, (li2, lb2, hd S0 (fst p), tl (fst p),
                                snd p))) ps)
              end
          end
      | DL =>
          match lb with
          | x :: lb' => Some [(q2, (li, lb', x, w :: rb, ri))]
          | [] =>
              let '(rb2, ri2) := mb_fold_r P (w :: rb) ri in
              match pop_item (mb_B P) li with
              | None => None
              | Some ps =>
                  Some (map (fun p =>
                          (q2, (snd p, tl (fst p), hd S0 (fst p), rb2,
                                ri2))) ps)
              end
          end
      end
  end.

Lemma mb_succs_sound : forall tm P a c,
  1 <= mb_B P ->
  rw_covers a c ->
  match mb_succs tm P a, step tm c with
  | Some l, Some c' => exists a', In a' l /\ rw_covers a' c'
  | Some _, None => False
  | None, _ => True
  end.
Proof.
  intros tm P [q [[[[li lb] h] rb] ri]] [qc tp] HB (Hq & Hh & Hl & Hr).
  simpl in Hq, Hh, Hl, Hr. subst qc.
  unfold mb_succs.
  destruct (tm q h) as [tr|] eqn:Etr; [| exact I].
  assert (Hstep : step tm (q, tp)
                  = Some (t_next tr, tape_move (t_dir tr) (t_write tr) tp)).
  { unfold step. rewrite Hh, Etr. reflexivity. }
  rewrite Hstep.
  destruct (t_dir tr) eqn:Ed; cbn [tape_move].
  - (* DL: left is the arrival side, right the departed one *)
    pose proof (side_den_push (t_write tr) rb ri (t_right tp) Hr) as Hr1.
    destruct lb as [|x lb'].
    + destruct Hl as (ext & Hden & Hf). cbn [app] in Hf.
      destruct (mb_fold_r P (t_write tr :: rb) ri) as [rb2 ri2] eqn:Ef.
      destruct (pop_item (mb_B P) li) as [ps|] eqn:Ep; [| exact I].
      destruct (pop_den (mb_B P) li ps ext HB Ep Hden)
        as (wd & li' & ext' & HIn & Hne & Hden' & Hpt).
      destruct wd as [|y wd']; [congruence|].
      eexists. split.
      { apply in_map_iff. exists (y :: wd', li').
        split; [reflexivity | exact HIn]. }
      repeat split; cbn [t_left t_right t_head snd fst hd tl].
      * rewrite Hf, (Hpt 0). reflexivity.
      * exists ext'. split; [exact Hden'|].
        intro i. unfold tail_side. rewrite Hf, (Hpt (S i)). reflexivity.
      * exact (mb_fold_den _ _ _ _ _ _ _ _ _ _ Ef Hr1).
    + destruct Hl as (ext & Hden & Hf).
      eexists. split; [left; reflexivity|].
      repeat split; cbn [t_left t_right t_head snd fst].
      * rewrite Hf. reflexivity.
      * exists ext. split; [exact Hden|].
        intro i. unfold tail_side. rewrite Hf. reflexivity.
      * exact Hr1.
  - (* DR: mirror image *)
    pose proof (side_den_push (t_write tr) lb li (t_left tp) Hl) as Hl1.
    destruct rb as [|x rb'].
    + destruct Hr as (ext & Hden & Hf). cbn [app] in Hf.
      destruct (mb_fold_l P (t_write tr :: lb) li) as [lb2 li2] eqn:Ef.
      destruct (pop_item (mb_B P) ri) as [ps|] eqn:Ep; [| exact I].
      destruct (pop_den (mb_B P) ri ps ext HB Ep Hden)
        as (wd & ri' & ext' & HIn & Hne & Hden' & Hpt).
      destruct wd as [|y wd']; [congruence|].
      eexists. split.
      { apply in_map_iff. exists (y :: wd', ri').
        split; [reflexivity | exact HIn]. }
      repeat split; cbn [t_left t_right t_head snd fst hd tl].
      * rewrite Hf, (Hpt 0). reflexivity.
      * exact (mb_fold_den _ _ _ _ _ _ _ _ _ _ Ef Hl1).
      * exists ext'. split; [exact Hden'|].
        intro i. unfold tail_side. rewrite Hf, (Hpt (S i)). reflexivity.
    + destruct Hr as (ext & Hden & Hf).
      eexists. split; [left; reflexivity|].
      repeat split; cbn [t_left t_right t_head snd fst].
      * rewrite Hf. reflexivity.
      * exact Hl1.
      * exists ext. split; [exact Hden|].
        intro i. unfold tail_side. rewrite Hf. reflexivity.
Qed.

Lemma mb_succs_wf : forall tm P a sl a',
  2 <= mb_T P ->
  rw_wf a ->
  mb_succs tm P a = Some sl ->
  In a' sl ->
  rw_wf a'.
Proof.
  intros tm P [q [[[[li lb] h] rb] ri]] sl a' HT [Hli Hri] Hs HIn.
  unfold mb_succs in Hs.
  destruct (tm q h) as [tr|]; [|discriminate].
  destruct (t_dir tr).
  - destruct lb as [|x lb'].
    + destruct (mb_fold_r P (t_write tr :: rb) ri) as [rb2 ri2] eqn:Ef.
      destruct (pop_item (mb_B P) li) as [ps|] eqn:Ep; [|discriminate].
      injection Hs as <-.
      apply in_map_iff in HIn as ((wd & li2) & E & HInp).
      subst a'. simpl.
      split.
      * exact (pop_item_wf (mb_B P) li ps Ep Hli wd li2 HInp).
      * exact (mb_fold_wf _ _ _ _ _ _ _ _ _ HT Ef Hri).
    + injection Hs as <-.
      destruct HIn as [E | []]. subst a'. simpl.
      split; [exact Hli | exact Hri].
  - destruct rb as [|x rb'].
    + destruct (mb_fold_l P (t_write tr :: lb) li) as [lb2 li2] eqn:Ef.
      destruct (pop_item (mb_B P) ri) as [ps|] eqn:Ep; [|discriminate].
      injection Hs as <-.
      apply in_map_iff in HIn as ((wd & ri2) & E & HInp).
      subst a'. simpl.
      split.
      * exact (mb_fold_wf _ _ _ _ _ _ _ _ _ HT Ef Hli).
      * exact (pop_item_wf (mb_B P) ri ps Ep Hri wd ri2 HInp).
    + injection Hs as <-.
      destruct HIn as [E | []]. subst a'. simpl.
      split; [exact Hli | exact Hri].
Qed.

Lemma mb_succs_sound' : forall tm P a c,
  1 <= mb_B P -> 2 <= mb_T P ->
  rw_covers' a c ->
  match mb_succs tm P a, step tm c with
  | Some l, Some c' => exists a', In a' l /\ rw_covers' a' c'
  | Some _, None => False
  | None, _ => True
  end.
Proof.
  intros tm P a c HB HT [Hcov Hwf].
  pose proof (mb_succs_sound tm P a c HB Hcov) as H.
  destruct (mb_succs tm P a) as [sl|] eqn:Hs; [| exact I].
  destruct (step tm c) as [c'|]; [| exact H].
  destruct H as (a' & HIn & Hcov').
  exists a'. split; [exact HIn|].
  split; [exact Hcov' | exact (mb_succs_wf tm P a sl a' HT Hwf Hs HIn)].
Qed.

(** the node-size cut, failing closed as in [RepWLTr] *)
Definition mb_succs_cut (M : nat) (tm : TM) (P : mbpar) (a : rconf)
  : option (list rconf) :=
  if M <? rw_asz a then None else mb_succs tm P a.

Lemma mb_succs_cut_sound' : forall M tm P a c,
  1 <= mb_B P -> 2 <= mb_T P ->
  rw_covers' a c ->
  match mb_succs_cut M tm P a, step tm c with
  | Some l, Some c' => exists a', In a' l /\ rw_covers' a' c'
  | Some _, None => False
  | None, _ => True
  end.
Proof.
  intros M tm P a c HB HT Hcov.
  unfold mb_succs_cut.
  destruct (M <? rw_asz a).
  - destruct (step tm c); exact I.
  - apply mb_succs_sound'; assumption.
Qed.

(** ** The seed: each concrete side is the buffer, then folded *)

Definition mb_seed (P : mbpar) (cc : cconf) : rconf :=
  let '(q, (l, h, r)) := cc in
  let '(lb, li) := mb_fold_l P l [] in
  let '(rb, ri) := mb_fold_r P r [] in
  (q, (li, lb, h, rb, ri)).

Lemma side_den_list : forall l, side_den l [] (lift_side l).
Proof.
  intro l. exists []. split; [constructor|].
  intro i. rewrite app_nil_r. reflexivity.
Qed.

Lemma mb_seed_covers' : forall P cc,
  2 <= mb_T P -> rw_covers' (mb_seed P cc) (lift cc).
Proof.
  intros P [q [[l h] r]] HT.
  unfold mb_seed.
  destruct (mb_fold_l P l []) as [lb li] eqn:El.
  destruct (mb_fold_r P r []) as [rb ri] eqn:Er.
  split.
  - cbn [rw_covers lift lift_tape fst snd t_left t_right t_head].
    repeat split.
    + exact (mb_fold_den _ _ _ _ _ _ _ _ _ _ El (side_den_list l)).
    + exact (mb_fold_den _ _ _ _ _ _ _ _ _ _ Er (side_den_list r)).
  - split.
    + exact (mb_fold_wf _ _ _ _ _ _ _ _ _ HT El (Forall_nil _)).
    + exact (mb_fold_wf _ _ _ _ _ _ _ _ _ HT Er (Forall_nil _)).
Qed.

(** ** The verified checker *)

Definition mb_check_neverqhtr (tm : TM) (P : mbpar) (t fuel M : nat)
    (cert : Instr -> list rwcomp) : bool :=
  (1 <=? mb_B P) && (2 <=? mb_T P) &&
  match csteps tm t c0 with
  | Some cc =>
      closure_check_neverqhtr_lex tm rconf rconf_enc rw_instr
        (mb_succs_cut M tm P) t fuel (mb_seed P cc)
        (fun tg => map (rw_comp_denote tm) (cert tg))
  | None => false
  end.

Theorem mb_check_neverqhtr_sound : forall tm P t fuel M cert,
  mb_check_neverqhtr tm P t fuel M cert = true ->
  NeverQuasiHaltsTr tm.
Proof.
  intros tm P t fuel M cert H.
  unfold mb_check_neverqhtr in H.
  apply andb_prop in H as [Hg H].
  apply andb_prop in Hg as [HB HT].
  apply Nat.leb_le in HB. apply Nat.leb_le in HT.
  destruct (csteps tm t c0) as [cc|] eqn:Et; [| discriminate].
  apply (closure_check_neverqhtr_lex_sound tm rconf rconf_enc rw_instr
           (mb_succs_cut M tm P) rw_covers') in H;
    [assumption | | | | |].
  - exact rconf_enc_inj.
  - intros a c Hc. exact (rw_covers'_instr a c Hc).
  - intros a c Hc. apply mb_succs_cut_sound'; assumption.
  - intros ct' Hct'. rewrite Et in Hct'. injection Hct' as <-.
    apply mb_seed_covers'. exact HT.
  - intros tg. apply Forall_forall. intros comp Hin.
    apply in_map_iff in Hin. destruct Hin as (c & <- & _).
    destruct c as [phi | m K phi gate]; simpl.
    + exact I.
    + intros a cc0 a' cc0' sl Hca Hca' Hstep Es HInl.
      exact (rw_meas_exact tm m a cc0 cc0' Hca Hstep).
Qed.

(** ** The untrusted search: [RepWLTr.rw_procedure_tr] on the
    multi-block successors *)

Definition irows_mb (tm : TM) (P : mbpar) (tg : Instr)
    (im : PositiveMap.tree positive) (nodes : list rconf) : IAdj :=
  snd (fold_left
    (fun '(i, g) a =>
       (Pos.succ i,
        PositiveMap.add i
          (fold_right (fun b acc =>
             if instr_eqb (rw_instr b) tg then acc
             else match PositiveMap.find (rkey b) im with
                  | Some j => j :: acc
                  | None => acc
                  end)
             []
             (match mb_succs tm P a with Some l => l | None => [] end))
          g))
    nodes (1%positive, PositiveMap.empty _)).

Definition mb_procedure_tr (tm : TM) (P : mbpar)
    (closure : list rconf) (tg : Instr) : list rwcomp :=
  let nodes := filter (fun a => negb (instr_eqb (rw_instr a) tg)) closure in
  let '(im, arr) := iintern nodes in
  let g := irows_mb tm P tg im nodes in
  let idxs := iidxs nodes in
  let Kc := S (S (length nodes)) in
  let rfuel := S (length nodes * 8 + 8) in
  match iproc_rounds 300 tm arr Kc rfuel idxs g [] with
  | Some comps => comps
  | None => []
  end.

(** ** The parameter-closed tier *)

Definition mb_tier_tr (tm : TM) (P : mbpar) (t fuel M : nat) : bool :=
  match csteps tm t c0 with
  | None => false
  | Some cc =>
      let a0 := mb_seed P cc in
      match close rconf rconf_enc (mb_succs_cut M tm P) fuel
                  [] PositiveSet.empty [a0] with
      | None => false
      | Some Sl =>
          mb_check_neverqhtr tm P t fuel M
            (fun tg =>
               if cfires tm c0 t tg
                  || existsb (fun a => instr_eqb (rw_instr a) tg) Sl
               then mb_procedure_tr tm P Sl tg
               else [])
      end
  end.

Theorem mb_tier_tr_sound : forall tm P t fuel M,
  mb_tier_tr tm P t fuel M = true -> NeverQuasiHaltsTr tm.
Proof.
  intros tm P t fuel M H.
  unfold mb_tier_tr in H.
  destruct (csteps tm t c0) as [cc|]; [|discriminate].
  destruct (close rconf rconf_enc (mb_succs_cut M tm P) fuel
                  [] PositiveSet.empty [mb_seed P cc]) as [Sl|];
    [|discriminate].
  exact (mb_check_neverqhtr_sound tm P t fuel M _ H).
Qed.

(** ** The wrapped tier: transition-quasihalting, as [rw_tier_qhbtr] *)

Definition mb_check_qhbtr (tm : TM) (tgs : list (Instr * nat))
    (P : mbpar) (t fuel M : nat) (cert : Instr -> list rwcomp) : bool :=
  (1 <=? mb_B P) && (2 <=? mb_T P) &&
  match csteps tm t c0 with
  | Some ct =>
      let tmw := tm_wrap_trs tm (map fst tgs) in
      wrap_check_qhboundtr_g tm tgs t rconf rconf_enc rw_instr
        (mb_succs_cut M tmw P) fuel (mb_seed P ct)
        (fun tg => map (rw_comp_denote tmw) (cert tg))
  | None => false
  end.

Theorem mb_check_qhbtr_sound : forall tm tgs P t fuel M cert,
  mb_check_qhbtr tm tgs P t fuel M cert = true ->
  NonHalt tm
  /\ (forall tg' s', QuietAfterTr tm tg' s' -> S s' <= S t)
  /\ QuasiHaltsTr tm.
Proof.
  intros tm tgs P t fuel M cert H.
  unfold mb_check_qhbtr in H.
  apply andb_prop in H as [Hg H].
  apply andb_prop in Hg as [HB HT].
  apply Nat.leb_le in HB. apply Nat.leb_le in HT.
  destruct (csteps tm t c0) as [ct|] eqn:Et; [|discriminate].
  apply (wrap_check_qhboundtr_g_sound tm tgs t rconf rconf_enc rw_instr
           (mb_succs_cut M (tm_wrap_trs tm (map fst tgs)) P) rw_covers')
    in H; [assumption | | | | |].
  - exact rconf_enc_inj.
  - intros a c Hc. exact (rw_covers'_instr a c Hc).
  - intros a c Hc. apply mb_succs_cut_sound'; assumption.
  - intros ct' Hct'. rewrite Et in Hct'. injection Hct' as <-.
    apply mb_seed_covers'. exact HT.
  - intros tg. apply Forall_forall. intros comp Hin.
    apply in_map_iff in Hin. destruct Hin as (c & <- & _).
    destruct c as [phi | m0 K phi gate]; simpl.
    + exact I.
    + intros a cc0 a' cc0' sl Hca Hca' Hstep Es HInl.
      exact (rw_meas_exact (tm_wrap_trs tm (map fst tgs))
               m0 a cc0 cc0' Hca Hstep).
Qed.

Definition mb_tier_qhbtr (tm : TM) (lf : list (Instr * nat))
    (P : mbpar) (t fuel M : nat) : bool :=
  match filter (fun p => snd p <? t) lf with
  | [] => false
  | pins =>
      match csteps tm t c0 with
      | None => false
      | Some ct =>
          let tmw := tm_wrap_trs tm (map fst pins) in
          let a0 := mb_seed P ct in
          match close rconf rconf_enc (mb_succs_cut M tmw P) fuel
                      [] PositiveSet.empty [a0] with
          | None => false
          | Some Sl =>
              mb_check_qhbtr tm pins P t fuel M
                (fun tg => mb_procedure_tr tmw P Sl tg)
          end
      end
  end.

Theorem mb_tier_qhbtr_sound : forall tm lf P t fuel M,
  mb_tier_qhbtr tm lf P t fuel M = true ->
  NonHalt tm
  /\ (forall tg' s', QuietAfterTr tm tg' s' -> S s' <= S t)
  /\ QuasiHaltsTr tm.
Proof.
  intros tm lf P t fuel M H.
  unfold mb_tier_qhbtr in H.
  destruct (filter (fun p => snd p <? t) lf) as [|p0 rest] eqn:Ef;
    [discriminate|].
  destruct (csteps tm t c0) as [ct|]; [|discriminate].
  destruct (close rconf rconf_enc _ fuel [] PositiveSet.empty _)
    as [Sl|]; [|discriminate].
  exact (mb_check_qhbtr_sound tm (p0 :: rest) P t fuel M _ H).
Qed.

(** the stage form a closeout row needs ([CloseoutKitTr.coversTr_qh3],
    with the literal bound): [QHConveyorTr.rwqh_stage] for this tier *)
Lemma mbqh_stage : forall tm lf P t fuel M B,
  mb_tier_qhbtr tm lf P t fuel M = true ->
  (S t <=? B) = true ->
  NonHalt tm /\ QHBoundTr B tm /\ QuasiHaltsTr tm.
Proof.
  intros tm lf P t fuel M B H Hle.
  destruct (mb_tier_qhbtr_sound tm lf P t fuel M H) as [Hnh [Hb Hq]].
  split; [exact Hnh|]. split; [| exact Hq].
  intros tg s Hs. apply Nat.leb_le in Hle.
  exact (Nat.le_trans _ _ _ (Hb tg s Hs) Hle).
Qed.
