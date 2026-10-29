(** Checked finite inventories of relabelings and one-blank-step shadows.
    Conditional shadow links alone do not prove their cores.  StrongBoard keeps
    the nonhalting evidence required to reuse partial-table completions. *)
From Coq Require Import List Bool Arith Lia NArith FunctionalExtensionality.
From BBB24 Require Import Statement StatementTr Spec Bounds Census Mirror
  CycleCensus Closeout Symmetry Shadow Pipeline Bootstrap.
Import ListNotations.

Definition StrongBoard bs bi (board : list TM) :=
  forall tm, In tm board -> NonHalt tm /\ Bounds bs bi tm.
Lemma strong_board_app : forall bs bi a b,
  StrongBoard bs bi a -> StrongBoard bs bi b -> StrongBoard bs bi (a++b).
Proof. intros bs bi a b Ha Hb tm H; apply in_app_iff in H as [H|H]; auto. Qed.
Lemma strong_board_completions : forall bs bi board,
  StrongBoard bs bi board -> BoardSound bs bi board.
Proof.
  intros bs bi board H family Hin tm Hle. destruct (H family Hin) as [Hnh Hb].
  eapply extend_bounds; eauto.
Qed.
Lemma completion_strong : forall bs bi tm complete,
  NonHalt tm /\ Bounds bs bi tm -> TM_le tm complete ->
  NonHalt complete /\ Bounds bs bi complete.
Proof.
  intros bs bi tm complete [Hnh Hb] Hle. split.
  - intros n E. rewrite (extend_run tm complete Hnh Hle n) in E. exact (Hnh n E).
  - eapply extend_bounds; eauto.
Qed.
Lemma mirror_tm_involutive : forall tm, mirror_tm (mirror_tm tm)=tm.
Proof.
  intro tm. apply functional_extensionality; intro q.
  apply functional_extensionality; intro s. unfold mirror_tm.
  destruct (tm q s) as [[w d q']|]; [destruct d|]; reflexivity.
Qed.
Lemma mirror_strong : forall bs bi tm,
  NonHalt tm /\ Bounds bs bi tm -> NonHalt (mirror_tm tm) /\ Bounds bs bi (mirror_tm tm).
Proof.
  intros bs bi tm [Hnh Hb]. split.
  - intros n E. rewrite mirror_stepn_init in E.
    specialize (Hnh n). destruct (stepn tm n InitES); congruence.
  - apply mirror_bounds. now rewrite mirror_tm_involutive.
Qed.
Definition image_tm p (mirrored : bool) tm :=
  if mirrored then mirror_tm (perm_tm p tm) else perm_tm p tm.
Lemma image_strong : forall bs bi p mirrored tm,
  NonHalt tm /\ Bounds bs bi tm ->
  NonHalt (image_tm p mirrored tm) /\ Bounds bs bi (image_tm p mirrored tm).
Proof.
  intros bs bi p mirrored tm [Hnh Hb].
  assert (H : NonHalt (perm_tm p tm) /\ Bounds bs bi (perm_tm p tm)).
  { split; [apply perm_nonhalt|apply perm_bounds]; assumption. }
  unfold image_tm. destruct mirrored; [apply mirror_strong|]; exact H.
Qed.

Record ImageRow := image_row {
  image_codes : list nat;
  image_source : nat;
  image_permutation : SymPerm;
  image_mirrored : bool
}.
Definition image_row_tm row := machine_of_codes (image_codes row).
Definition image_row_check board row :=
  (image_source row <? length board) &&
  table_leb (image_tm (image_permutation row) (image_mirrored row)
    (nth (image_source row) board empty)) (image_row_tm row).
Lemma image_row_sound : forall bs bi board row,
  StrongBoard bs bi board -> image_row_check board row=true ->
  NonHalt (image_row_tm row) /\ Bounds bs bi (image_row_tm row).
Proof.
  intros bs bi board row Hboard H. apply andb_prop in H as [Hi Hl].
  apply Nat.ltb_lt in Hi. apply table_leb_spec in Hl.
  eapply completion_strong; [apply image_strong, Hboard, nth_In; exact Hi|exact Hl].
Qed.
Theorem image_batch_sound : forall bs bi board rows,
  StrongBoard bs bi board -> forallb (image_row_check board) rows=true ->
  StrongBoard bs bi (map image_row_tm rows).
Proof.
  intros bs bi board rows Hboard H tm Hin.
  apply in_map_iff in Hin as (row & <- & Hin).
  apply forallb_forall with (x:=row) in H; [|exact Hin].
  eapply image_row_sound; eauto.
Qed.

Record ShadowLink := shadow_link {
  link_shadow_codes : list nat;
  link_core_codes : list nat;
  link_permutation : SymPerm;
  link_mirrored : bool
}.
Definition link_shadow row := machine_of_codes (link_shadow_codes row).
Definition link_core row := machine_of_codes (link_core_codes row).
Definition shadow_link_check row := shadow_check (link_shadow row) (link_core row)
  (link_permutation row) (link_mirrored row).
Theorem shadow_links_conditional : forall rows,
  forallb shadow_link_check rows=true -> forall row, In row rows ->
  forall bs bi, NonHalt (link_core row) -> Bounds bs bi (link_core row) ->
  forall complete, TM_le (link_shadow row) complete ->
  NonHalt complete /\ Bounds (N.succ bs) (N.succ bi) complete.
Proof.
  intros rows H row Hin bs bi Hnh Hb complete Hle.
  apply forallb_forall with (x:=row) in H; [|exact Hin].
  eapply shadow_check_sound; eauto.
Qed.

Record ReadyShadow := ready_shadow {
  ready_codes : list nat;
  ready_source : nat;
  ready_core_permutation : SymPerm;
  ready_core_mirrored : bool;
  ready_permutation : SymPerm;
  ready_mirrored : bool
}.
Definition ready_tm row := machine_of_codes (ready_codes row).
Definition ready_check board row :=
  (ready_source row <? length board) &&
  shadow_check (ready_tm row)
    (image_tm (ready_core_permutation row) (ready_core_mirrored row)
      (nth (ready_source row) board empty))
    (ready_permutation row) (ready_mirrored row).
Lemma ready_shadow_sound : forall bs bi board row,
  StrongBoard bs bi board -> ready_check board row=true ->
  NonHalt (ready_tm row) /\ Bounds (N.succ bs) (N.succ bi) (ready_tm row).
Proof.
  intros bs bi board row Hboard H. apply andb_prop in H as [Hi Hl].
  apply Nat.ltb_lt in Hi.
  pose proof (image_strong bs bi (ready_core_permutation row) (ready_core_mirrored row)
    (nth (ready_source row) board empty) (Hboard _ (nth_In _ empty Hi))) as [Hnh Hb].
  eapply shadow_check_sound; [exact Hl|exact Hnh|exact Hb|].
  intros q s; right; reflexivity.
Qed.
Theorem ready_shadows_sound : forall bs bi board rows,
  StrongBoard bs bi board -> forallb (ready_check board) rows=true ->
  StrongBoard (N.succ bs) (N.succ bi) (map ready_tm rows).
Proof.
  intros bs bi board rows Hboard H tm Hin.
  apply in_map_iff in Hin as (row & <- & Hin).
  apply forallb_forall with (x:=row) in H; [|exact Hin].
  eapply ready_shadow_sound; eauto.
Qed.
Lemma strong_board_weaken : forall bs bi bs' bi' board,
  (bs<=bs')%N -> (bi<=bi')%N -> StrongBoard bs bi board -> StrongBoard bs' bi' board.
Proof.
  intros bs bi bs' bi' board Hs Hi H tm Hin.
  destruct (H tm Hin) as [Hnh Hb]; split; [exact Hnh|]. eapply bounds_weaken; eauto.
Qed.

Print Assumptions shadow_links_conditional.
Print Assumptions image_batch_sound.
Print Assumptions ready_shadows_sound.
