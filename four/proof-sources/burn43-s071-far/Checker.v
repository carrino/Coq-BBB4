From Coq Require Import List Bool PArith.
From BBB24Burn43S071FAR Require Import Sparse FARForward DataSchema.
Import ListNotations.
Set Implicit Arguments.

Definition model (d : rawcert) (runlocal : localfun) : FARData :=
 {| W := positive; Q := bool; R := positive; C := positive;
    blank := blankword; start := startsummary; initial := false;
    cw := fun c => rw (getrow d c);
    cq := fun c => rq (getrow d c);
    cr := fun c => rr (getrow d c);
    Cok := fun c => cok d c = true;
    Push := fun w r rn => pushfind d w r = Some rn;
    Zero := fun r => zflag r = true;
    H2ok := fun a => mem (h2 d) (slot (fst a) (snd a)) = true;
    Pre32 := fun c a => edge (pre32 d) c (slot (fst a) (snd a)) = true;
    Pre33 := fun c c0 => edge (pre33 d) c c0 = true;
    Pre3l := fun c => mem (pre3l d) c = true;
    Ret2 := fun a b => edge (ret2 d) (slot (fst a) (snd a))
                             (slot (fst b) (snd b)) = true;
    Ret3 := fun c b => edge (ret3 d) c (slot (fst b) (snd b)) = true;
    Retl := fun b => mem (retl d) (slot (fst b) (snd b)) = true;
    Local := fun w q f bz fz wn qn back =>
      runlocal w q f bz fz = Some (Out wn qn back);
    FARForward.zflag := zflag |}.

Definition forall_push (d : rawcert)
    (f : positive -> positive -> positive -> bool) : bool :=
  all_map (fun w rs => all_map (f w) rs) (push d).

Lemma forall_push_sound d f : forall_push d f = true ->
  forall w r rn, pushfind d w r = Some rn -> f w r rn = true.
Proof.
  intros H w r rn P. unfold pushfind in P.
  destruct (PM.find w (push d)) as [rs|] eqn:F; [|discriminate].
  unfold forall_push in H.
  exact (all_map_sound (all_map_sound H F) P).
Qed.
Arguments forall_push_sound {d f} _ {w r rn} _.

Lemma cok_getrow d c : cok d c = true ->
  PM.find c (h3 d) = Some (getrow d c).
Proof.
  unfold cok, getrow; destruct (PM.find c (h3 d)); congruence.
Qed.
Arguments cok_getrow {d c} _.

Definition nodeindex := PM.t (PM.t positive).
Definition nodefind (idx : nodeindex) w q r :=
  match PM.find w idx with Some m => PM.find (slot q r) m | None => None end.
Definition nodecheck (d : rawcert) (idx : nodeindex) w q r
    (f : positive -> bool) : bool :=
  match nodefind idx w q r with
  | Some c => cok d c && roweqb (getrow d c) (Row w q r) && f c
  | None => false
  end.

Lemma nodecheck_sound d idx w q r f : nodecheck d idx w q r f = true ->
  exists c, cok d c = true /\ rw (getrow d c) = w /\
       rq (getrow d c) = q /\ rr (getrow d c) = r /\ f c = true.
Proof.
  unfold nodecheck; destruct (nodefind idx w q r) as [c|]; [|discriminate].
  repeat rewrite andb_true_iff. intros [[Hc He] Hf].
  apply roweqb_true in He. exists c; split; [exact Hc|].
  now rewrite He.
Qed.

Definition check_root (d : rawcert) : bool :=
  all_map (fun c row => mem (h2 d) (slot (rq row) (rr row))) (h3 d).

Definition check_initial (d : rawcert) : bool :=
  cok d 1 && roweqb (getrow d 1) (Row blankword false startsummary) &&
    mem (pre3l d) 1.

Definition check_zero (d : rawcert) : bool :=
  forall_push d (fun w r rn =>
    negb (Pos.eqb w blankword && zflag r) || zflag rn).

Definition check_blank (d : rawcert) : bool :=
  match pushfind d blankword startsummary with
  | Some rn => Pos.eqb rn startsummary | None => false end.

Definition check_h2_one (d : rawcert) (idx : nodeindex) (runlocal : localfun)
    (q : bool) (w r0 r : positive) : bool :=
  if mem (h2 d) (slot q r) then
    match runlocal w q true true (zflag r0) with
    | None => false
    | Some out =>
      if ob out then
        match pushfind d (ow out) r0 with
        | Some rn => edge (ret2 d) (slot q r) (slot (oq out) rn)
        | None => false end
      else nodecheck d idx (ow out) (oq out) r0
          (fun c => edge (pre32 d) c (slot q r))
    end
  else true.

Definition check_h2 (d : rawcert) (idx : nodeindex) (runlocal : localfun) : bool :=
  forall_push d (fun w r0 r =>
    check_h2_one d idx runlocal false w r0 r &&
    check_h2_one d idx runlocal true w r0 r).

Definition check_h3_one (d : rawcert) (idx : nodeindex) (runlocal : localfun)
    (c : positive) (row : h3row) (b : positive) : bool :=
  let '(q,r) := unslot b in
  match runlocal (rw row) q false (zflag r) (zflag (rr row)) with
  | None => false
  | Some out =>
    if ob out then nodecheck d idx (ow out) (oq out) r
        (fun c0 => edge (pre33 d) c0 c)
    else match pushfind d (ow out) r with
         | Some rn => edge (ret3 d) c (slot (oq out) rn)
         | None => false end
  end.

Definition check_h3 (d : rawcert) (idx : nodeindex) (runlocal : localfun) : bool :=
  all_map (fun c row => forallb (check_h3_one d idx runlocal c row)
    (get (ret2 d) (slot (rq row) (rr row)))) (h3 d).

Definition check_left_one (d : rawcert) (idx : nodeindex) (runlocal : localfun)
    (b : positive) : bool :=
  let '(q,r) := unslot b in
  match runlocal blankword q false (zflag r) true with
  | None => false
  | Some out =>
    if ob out then nodecheck d idx (ow out) (oq out) r
        (fun c => mem (pre3l d) c)
    else match pushfind d (ow out) r with
         | Some rn => mem (retl d) (slot (oq out) rn)
         | None => false end
  end.

Definition check_left (d : rawcert) (idx : nodeindex) (runlocal : localfun) : bool :=
  all_map (fun b _ => check_left_one d idx runlocal b) (retl d).

Definition check_return_one (d : rawcert) (c b : positive) : bool :=
  (negb (mem (pre3l d) c) || mem (retl d) b) &&
  forallb (fun a => edge (ret2 d) a b) (get (pre32 d) c) &&
  forallb (fun c0 => edge (ret3 d) c0 b) (get (pre33 d) c).

Definition check_return (d : rawcert) : bool :=
  all_adj (check_return_one d) (ret3 d).

Definition valid_word (w : positive) : bool := Pos.leb w 14.
Definition check_words (d : rawcert) : bool :=
  forall_push d (fun w _ _ => valid_word w) &&
  all_map (fun _ row => valid_word (rw row)) (h3 d).

Definition check (d : rawcert) (idx : nodeindex) (runlocal : localfun) : bool :=
  check_root d && check_initial d && check_zero d && check_blank d &&
  check_h2 d idx runlocal && check_h3 d idx runlocal &&
  check_left d idx runlocal && check_return d && check_words d.

Lemma check_push_words d idx local : check d idx local = true ->
  forall w r rn, pushfind d w r = Some rn -> valid_word w = true.
Proof.
  unfold check; repeat rewrite andb_true_iff.
  intros [[[[[[[[Hr Hi] Hz] Hb] H2] H3] Hl] Ht] Hw].
  unfold check_words in Hw; apply andb_true_iff in Hw; destruct Hw as [Hw _].
  intros w r rn Hpush; exact (forall_push_sound Hw Hpush).
Qed.

Lemma check_h3_words d idx local : check d idx local = true ->
  forall c, cok d c = true -> valid_word (rw (getrow d c)) = true.
Proof.
  unfold check; repeat rewrite andb_true_iff.
  intros [[[[[[[[Hr Hi] Hz] Hb] H2] H3] Hl] Ht] Hw] c Hc.
  unfold check_words in Hw; apply andb_true_iff in Hw; destruct Hw as [_ Hw].
  exact (all_map_sound Hw (cok_getrow Hc)).
Qed.
