(** Frozen-census closeout. A board contains proved partial-table families.
    Matching a completion excludes that machine from the residual predicate;
    the source census and its structural weights are left unchanged. *)
From Coq Require Import Arith Lia Bool List NArith.
From BBB24 Require Import Statement StatementTr CTape Spec Bounds Census.
Import ListNotations.

Definition closeout_symbols : list Sym := [S0; S1; S2; S3].
Lemma closeout_symbols_complete : forall s, In s closeout_symbols.
Proof. destruct s; simpl; auto. Qed.

Definition trans_eqb (a b : Trans) :=
  sym_eqb (t_write a) (t_write b) &&
  (match t_dir a, t_dir b with DL,DL | DR,DR => true | _,_ => false end) &&
  st_eqb (t_next a) (t_next b).
Lemma trans_eqb_spec : forall a b, trans_eqb a b = true <-> a = b.
Proof.
  intros [w d q] [w' d' q']; destruct w,d,q,w',d',q';
    cbn; split; congruence.
Qed.

Definition cell_leb (a b : option Trans) :=
  match a,b with None,_ => true | Some x,Some y => trans_eqb x y | _,_ => false end.
Lemma cell_leb_spec : forall a b,
  cell_leb a b = true <-> a = None \/ b = a.
Proof.
  intros [a|] [b|]; simpl; try rewrite trans_eqb_spec;
    split; intros H; try tauto; try discriminate; intuition congruence.
Qed.
Definition table_leb (a b : TM) := forallb (fun q =>
  forallb (fun s => cell_leb (a q s) (b q s)) closeout_symbols) all_St.
Lemma table_leb_spec : forall a b, table_leb a b = true <-> TM_le a b.
Proof.
  intros a b. unfold table_leb, TM_le. split.
  - intros H q s. apply cell_leb_spec.
    apply forallb_forall with (x:=q) in H; [|apply all_St_complete].
    apply forallb_forall with (x:=s) in H; [exact H|apply closeout_symbols_complete].
  - intros H. apply forallb_forall. intros q _.
    apply forallb_forall. intros s _. apply cell_leb_spec, H.
Qed.

Definition board_check (board : list TM) (tm : TM) :=
  existsb (fun family => table_leb family tm) board.
Definition BoardSound bs bi (board : list TM) :=
  forall family, In family board -> forall tm, TM_le family tm -> Bounds bs bi tm.
Lemma board_check_sound : forall bs bi board tm,
  BoardSound bs bi board -> board_check board tm = true -> Bounds bs bi tm.
Proof.
  intros bs bi board tm Hsound H. apply existsb_exists in H as (family & Hin & Hle).
  apply table_leb_spec in Hle. exact (Hsound family Hin tm Hle).
Qed.
Definition remaining (pending : TM -> Prop) (board : list TM) tm :=
  pending tm /\ board_check board tm = false.
Lemma board_sound_app : forall bs bi left right,
  BoardSound bs bi left -> BoardSound bs bi right -> BoardSound bs bi (left ++ right).
Proof.
  intros bs bi left right Hl Hr family Hin tm Hle.
  apply in_app_iff in Hin as [Hin|Hin]; [eapply Hl|eapply Hr]; eauto.
Qed.
Lemma remaining_app : forall pending left right tm,
  remaining pending (left ++ right) tm <-> remaining (remaining pending left) right tm.
Proof.
  intros. unfold remaining, board_check. rewrite existsb_app, orb_false_iff. tauto.
Qed.
Theorem closeout_coverage : forall bs bi pending board,
  (forall tm, Bounds bs bi tm \/ pending tm) -> BoardSound bs bi board ->
  forall tm, Bounds bs bi tm \/ remaining pending board tm.
Proof.
  intros bs bi pending board Hcover Hsound tm.
  destruct (board_check board tm) eqn:E.
  - left. eapply board_check_sound; eauto.
  - destruct (Hcover tm) as [H|H]; [left; exact H|right; split; assumption].
Qed.
Theorem closeout_upper_if_remaining : forall bs bi pending board,
  (forall tm, Bounds bs bi tm \/ pending tm) -> BoardSound bs bi board ->
  (forall tm, remaining pending board tm -> Bounds bs bi tm) ->
  forall tm, Bounds bs bi tm.
Proof.
  intros bs bi pending board Hcover Hsound Hrest tm.
  destruct (closeout_coverage _ _ _ _ Hcover Hsound tm); auto.
Qed.
Lemma bounds_weaken : forall bs bi bs' bi' tm,
  (bs <= bs')%N -> (bi <= bi')%N -> Bounds bs bi tm -> Bounds bs' bi' tm.
Proof.
  intros bs bi bs' bi' tm Hs Hi [Hs' Hi'].
  split; intros q s Hq.
  - specialize (Hs' q s Hq). lia.
  - specialize (Hi' q s Hq). lia.
Qed.

(** A bounded path check proves actual membership in the frozen pending set
    without evaluating its million-element list. Every successful path ends
    at Deferred and checks inclusion of the entire partial table. *)
Definition trans_code (tr : Trans) :=
  4 * sym_index (t_write tr) +
  (match t_dir tr with DL => 0 | DR => 2 end) + st_index (t_next tr).
Fixpoint pending_check depth partial cert complete : bool :=
  match depth with
  | 0 => false
  | S d => match cert with
    | Deferred => table_leb partial complete
    | Branch n cs => match csteps partial n c0 with
      | Some (q,(_,h,_)) => match complete q h with
        | Some tr => let v := trans_code tr in
          (v <? 16) && pending_check d (update partial q h (nat_trans v))
            (nth v cs Invalid) complete
        | None => false end
      | None => false end
    | _ => false end
  end.
Theorem pending_check_sound : forall depth partial cert complete,
  pending_check depth partial cert complete = true ->
  Pending (residue depth partial cert) complete.
Proof.
  induction depth as [|d IH]; intros partial cert complete H; [discriminate|].
  destruct cert as [| |n cs|m t p W]; cbn [pending_check residue] in *; try discriminate.
  - exists partial. split; [left; reflexivity|apply table_leb_spec; exact H].
  - destruct (csteps partial n c0) as [[q [[l h] r]]|] eqn:E; [|discriminate].
    destruct (complete q h) as [tr|] eqn:Et; [|discriminate].
    apply andb_prop in H as [Hv H]. apply Nat.ltb_lt in Hv.
    destruct (IH _ _ _ H) as (leaf & Hin & Hle). exists leaf. split; [|exact Hle].
    apply in_concat. eexists. split; [apply in_map_iff|exact Hin].
    exists (trans_code tr). split; [reflexivity|apply in_seq; lia].
Qed.

Print Assumptions closeout_coverage.
Print Assumptions pending_check_sound.
