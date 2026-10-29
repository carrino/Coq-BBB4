From Coq Require Import List Bool PArith.
From BBB24Burn43S071FAR Require Import Sparse FARForward DataSchema Checker.
Import ListNotations.
Set Implicit Arguments.

Lemma check_h2_sound d idx local q r w r0 :
  check_h2 d idx local = true ->
  mem (h2 d) (slot q r) = true -> pushfind d w r0 = Some r ->
  exists wn qn back,
    local w q true true (zflag r0) = Some (Out wn qn back) /\
    if back then exists rn, pushfind d wn r0 = Some rn /\
       edge (ret2 d) (slot q r) (slot qn rn) = true
    else exists c, cok d c = true /\ rw (getrow d c) = wn /\
       rq (getrow d c) = qn /\ rr (getrow d c) = r0 /\
       edge (pre32 d) c (slot q r) = true.
Proof.
  intros Hcheck Hmem Hpush.
  pose proof (forall_push_sound Hcheck Hpush) as Hboth.
  apply andb_true_iff in Hboth; destruct Hboth as [Hfalse Htrue].
  assert (Hone : check_h2_one d idx local q w r0 r = true).
  { destruct q; assumption. }
  unfold check_h2_one in Hone; rewrite Hmem in Hone.
  destruct (local w q true true (zflag r0)) as [[wn qn back]|] eqn:Hl;
    [|discriminate].
  exists wn, qn, back; split; [reflexivity|]. simpl in Hone.
  destruct back.
  - destruct (pushfind d wn r0) as [rn|] eqn:Hp; [|discriminate].
    exists rn; auto.
  - apply nodecheck_sound in Hone. exact Hone.
Qed.

Lemma check_h3_sound d idx local c q r :
  check_h3 d idx local = true -> cok d c = true ->
  edge (ret2 d) (slot (rq (getrow d c)) (rr (getrow d c))) (slot q r) = true ->
  exists wn qn back,
    local (rw (getrow d c)) q false (zflag r) (zflag (rr (getrow d c)))
      = Some (Out wn qn back) /\
    if back then exists c0, cok d c0 = true /\ rw (getrow d c0) = wn /\
      rq (getrow d c0) = qn /\ rr (getrow d c0) = r /\ edge (pre33 d) c0 c = true
    else exists rn, pushfind d wn r = Some rn /\
      edge (ret3 d) c (slot qn rn) = true.
Proof.
  intros Hcheck Hc Hret.
  pose proof (all_map_sound Hcheck (cok_getrow Hc)) as Hall.
  rewrite forallb_forall in Hall.
  pose proof (Hall (slot q r) (proj1 (edge_in _ _ _) Hret)) as Hone.
  unfold check_h3_one in Hone. rewrite unslot_slot in Hone.
  destruct (local (rw (getrow d c)) q false (zflag r)
     (zflag (rr (getrow d c)))) as [[wn qn back]|] eqn:Hl; [|discriminate].
  exists wn, qn, back; split; [reflexivity|]. simpl in Hone.
  destruct back.
  - now apply nodecheck_sound in Hone.
  - destruct (pushfind d wn r) as [rn|] eqn:Hp; [|discriminate].
    exists rn; auto.
Qed.

Lemma check_left_sound d idx local q r :
  check_left d idx local = true -> mem (retl d) (slot q r) = true ->
  exists wn qn back,
    local blankword q false (zflag r) true = Some (Out wn qn back) /\
    if back then exists c, cok d c = true /\ rw (getrow d c) = wn /\
      rq (getrow d c) = qn /\ rr (getrow d c) = r /\ mem (pre3l d) c = true
    else exists rn, pushfind d wn r = Some rn /\ mem (retl d) (slot qn rn) = true.
Proof.
  intros Hcheck Hret.
  pose proof (@all_set_sound (retl d) (check_left_one d idx local) Hcheck (slot q r) Hret) as Hone.
  unfold check_left_one in Hone. rewrite unslot_slot in Hone.
  destruct (local blankword q false (zflag r) true)
    as [[wn qn back]|] eqn:Hl; [|discriminate].
  exists wn, qn, back; split; [reflexivity|]. simpl in Hone.
  destruct back.
  - now apply nodecheck_sound in Hone.
  - destruct (pushfind d wn r) as [rn|] eqn:Hp; [|discriminate].
    exists rn; auto.
Qed.

Theorem check_closed d idx local : check d idx local = true -> Closed (model d local).
Proof.
  unfold check; repeat rewrite andb_true_iff.
  intros [[[[[[[[Hroot Hinitial] Hzero] Hblank] Htwo] Hthree] Hleft] Hreturn] Hwords].
  constructor.
  - intros c Hc. cbn in Hc |- *.
    exact (all_map_sound Hroot (cok_getrow Hc)).
  - unfold check_initial in Hinitial.
    apply andb_true_iff in Hinitial; destruct Hinitial as [Hinitial Hp].
    apply andb_true_iff in Hinitial; destruct Hinitial as [Hc He].
    apply roweqb_true in He.
    exists 1%positive. cbn. rewrite He. auto.
  - reflexivity.
  - intros r H; exact H.
  - intros r rn Hz Hp. cbn in Hz, Hp |- *.
    pose proof (forall_push_sound Hzero Hp) as H.
    change (negb (zflag r) || zflag rn = true) in H.
    change (zflag r = true) in Hz. rewrite Hz in H. exact H.
  - cbn. unfold check_blank in Hblank.
    destruct (pushfind d blankword startsummary) as [rn|] eqn:Hp; [|discriminate].
    apply Pos.eqb_eq in Hblank. now subst rn.
  - intros q r w r0 Hh Hp. cbn in Hh, Hp |- *.
    now apply (@check_h2_sound d idx local q r w r0 Htwo Hh Hp).
  - intros c q r Hc Hr. cbn in Hc, Hr |- *.
    now apply (@check_h3_sound d idx local c q r Hthree Hc Hr).
  - intros q r Hr. cbn in Hr |- *.
    now apply (@check_left_sound d idx local q r Hleft Hr).
  - intros c [q r] Hr Hp. cbn in Hr, Hp |- *.
    pose proof (@all_adj_sound (ret3 d) (check_return_one d) Hreturn c (slot q r) Hr) as H.
    unfold check_return_one in H. repeat rewrite andb_true_iff in H.
    destruct H as [[H _] _]. now rewrite Hp in H.
  - intros c [qa ra] [qb rb] Hr Hp. cbn in Hr, Hp |- *.
    pose proof (@all_adj_sound (ret3 d) (check_return_one d) Hreturn c (slot qb rb) Hr) as H.
    unfold check_return_one in H. repeat rewrite andb_true_iff in H.
    destruct H as [[_ H] _]. rewrite forallb_forall in H.
    apply H. now apply edge_in in Hp.
  - intros c c0 [q r] Hr Hp. cbn in Hr, Hp |- *.
    pose proof (@all_adj_sound (ret3 d) (check_return_one d) Hreturn c (slot q r) Hr) as H.
    unfold check_return_one in H. repeat rewrite andb_true_iff in H.
    destruct H as [[_ _] H]. rewrite forallb_forall in H.
    apply H. now apply edge_in in Hp.
Qed.

Print Assumptions check_closed.
