(** A small, fully checked language of costed accelerated operations. *)
From Coq Require Import Arith Lia List NArith Bool.
From BBB24 Require Import Statement Spec CTape Gap Macros RLE.
Import ListNotations.

Definition chain (tm:TM) (k:N) c : option rconf :=
  match rd c with
  | DL => match rl c with
    | (s,n)::l => match tm (rq c) s with
      | Some (mkTrans w DL p) =>
        if (k<=?n)%N && st_eqb p (rq c)
        then Some (RC (rq c) DL ((s,(n-k)%N)::l) (push w k (rr c))) else None
      | _=>None end
    | _=>None end
  | DR => match rr c with
    | (s,n)::r => match tm (rq c) s with
      | Some (mkTrans w DR p) =>
        if (k<=?n)%N && st_eqb p (rq c)
        then Some (RC (rq c) DR (push w k (rl c)) ((s,(n-k)%N)::r)) else None
      | _=>None end
    | _=>None end
  end.
Lemma chain_sound : forall tm k c c', chain tm k c = Some c' ->
  Runs tm (N.to_nat k) (decode c) (decode c').
Proof.
  intros tm k [q d l r] c' H; destruct d; cbn [chain rq rd rl rr] in H.
  - destruct l as [|[s n] l]; [discriminate|].
    destruct (tm q s) as [[w d p]|] eqn:Et; [|discriminate].
    destruct d; [|discriminate].
    destruct ((k<=?n)%N && st_eqb p q) eqn:E; [|discriminate].
    apply Bool.andb_true_iff in E as [E Ep]. apply N.leb_le in E.
    apply st_eqb_spec in Ep; subst p. injection H as <-.
    rewrite push_gap_right. unfold decode; cbn [rq rd rl rr gap].
    rewrite (expand_take s n k l E). apply chain_left; exact Et.
  - destruct r as [|[s n] r]; [discriminate|].
    destruct (tm q s) as [[w d p]|] eqn:Et; [|discriminate].
    destruct d; [discriminate|].
    destruct ((k<=?n)%N && st_eqb p q) eqn:E; [|discriminate].
    apply Bool.andb_true_iff in E as [E Ep]. apply N.leb_le in E.
    apply st_eqb_spec in Ep; subst p. injection H as <-.
    rewrite push_gap_left. unfold decode; cbn [rq rd rl rr gap].
    rewrite (expand_take s n k r E). apply chain_right; exact Et.
Qed.

Definition pair3 (k:N) c : option rconf :=
  match c with RC q DL ((S3,n)::l) r =>
    if (2*k<=?n)%N
    then Some (RC q DL ((S3,(n-2*k)%N)::l) (push S1 (2*k) r)) else None
  | _=>None end.
Lemma pair3_sound : forall k c c', pair3 k c=Some c' ->
  Runs champion (N.to_nat (2*k)) (decode c) (decode c').
Proof.
  intros k [q d l r] c' H. destruct d; [|discriminate].
  destruct l as [|[s n] l]; [discriminate|]. destruct s; try discriminate.
  cbn [pair3] in H. destruct (2*k<=?n)%N eqn:E; [|discriminate].
  apply N.leb_le in E. injection H as <-.
  rewrite push_gap_right. unfold decode; cbn [rq rd rl rr gap].
  change (Runs champion (N.to_nat (2*k))
    (leftward q (expand ((S3,n)::l)) (expand r))
    (leftward q (expand ((S3,(n-2*k)%N)::l))
      (repeat S1 (N.to_nat (2*k)) ++ expand r))).
  rewrite (expand_take S3 n (2*k) l E).
  replace (N.to_nat (2*k)) with (2*N.to_nat k) by (rewrite N2Nat.inj_mul; reflexivity).
  apply pair3_many.
Qed.

Definition grow2 (k:N) c : option rconf :=
  match c with RC StA DL ((S2,n)::l) [(S2,m)] =>
    if (2*k<=?n)%N
    then Some (RC StA DL ((S2,(n-2*k)%N)::l) [(S2,(m+3*k)%N)]) else None
  | _=>None end.
Definition grow_cost k m := (6*k*k+(4*m+8)*k)%N.
Lemma grow2_sound : forall k q d l r c' m,
  r=[(S2,m)] -> grow2 k (RC q d l r)=Some c' ->
  Runs champion (N.to_nat (grow_cost k m)) (decode (RC q d l r)) (decode c').
Proof.
  intros k q d l r c' m -> H.
  destruct q,d; try discriminate.
  destruct l as [|[s n] l]; [discriminate|]. destruct s; try discriminate.
  cbn [grow2] in H. destruct (2*k<=?n)%N eqn:E; [|discriminate].
  apply N.leb_le in E. injection H as <-.
  unfold decode; cbn [rq rd rl rr gap]. rewrite (expand_take S2 n (2*k) l E).
  cbn [expand]. rewrite !app_nil_r.
  change (Runs champion (N.to_nat (grow_cost k m))
    (leftward StA (repeat S2 (N.to_nat (2*k)) ++ expand ((S2,(n-2*k)%N)::l))
      (repeat S2 (N.to_nat m)))
    (leftward StA (expand ((S2,(n-2*k)%N)::l))
      (repeat S2 (N.to_nat (m+3*k))))).
  unfold grow_cost. repeat first [rewrite N2Nat.inj_add | rewrite N2Nat.inj_mul].
  cbn [N.to_nat]. apply grow2_many.
Qed.

Definition consume1 (k:N) c : option rconf :=
  match c with RC StA DL ((S2,n)::l) ((S2,m)::(S1,j)::r) =>
    if (k<=?n)%N && (k<=?j)%N
    then Some (RC StA DL ((S2,(n-k)%N)::l) ((S2,(m+2*k)%N)::(S1,(j-k)%N)::r)) else None
  | _=>None end.
Definition consume_cost k m := (2*k*k+(2*m+1)*k)%N.
Lemma consume1_sound : forall k q d l r c' m j rs,
  r=(S2,m)::(S1,j)::rs -> consume1 k (RC q d l r)=Some c' ->
  Runs champion (N.to_nat (consume_cost k m)) (decode (RC q d l r)) (decode c').
Proof.
  intros k q d l r c' m j rs -> H. destruct q,d; try discriminate.
  destruct l as [|[s n] l]; [discriminate|]. destruct s; try discriminate.
  cbn [consume1] in H. destruct ((k<=?n)%N && (k<=?j)%N) eqn:E; [|discriminate].
  apply Bool.andb_true_iff in E as [En Ej]. apply N.leb_le in En,Ej.
  injection H as <-. unfold decode; cbn [rq rd rl rr gap].
  rewrite (expand_take S2 n k l En).
  change (Runs champion (N.to_nat (consume_cost k m))
    (leftward StA (repeat S2 (N.to_nat k) ++ expand ((S2,(n-k)%N)::l))
      (repeat S2 (N.to_nat m) ++ expand ((S1,j)::rs)))
    (leftward StA (expand ((S2,(n-k)%N)::l))
      (repeat S2 (N.to_nat (m+2*k)) ++ expand ((S1,(j-k)%N)::rs)))).
  rewrite (expand_take S1 j k rs Ej).
  unfold consume_cost. repeat first [rewrite N2Nat.inj_add | rewrite N2Nat.inj_mul].
  cbn [N.to_nat]. apply consume1_many.
Qed.

Inductive Op := Basic | Chain (k:N) | Pair3 (k:N) | Grow2 (k:N) | Consume1 (k:N).
Definition costed n (v:option rconf) : option (N*rconf) :=
  match v with Some c=>Some(n,c) | None=>None end.
Definition apply_op op c : option (N*rconf) :=
  match op with
  | Basic => costed 1 (basic champion c)
  | Chain k => costed k (chain champion k c)
  | Pair3 k => costed (2*k)%N (pair3 k c)
  | Grow2 k => match rr c with
    | [(S2,m)] => costed (grow_cost k m) (grow2 k c)
    | _=>None end
  | Consume1 k => match rr c with
    | (S2,m)::(S1,j)::rs => costed (consume_cost k m) (consume1 k c)
    | _=>None end
  end.
Lemma costed_some : forall n v t c, costed n v=Some(t,c) -> n=t /\ v=Some c.
Proof. intros n [x|] t c H; [injection H as <- <-; auto|discriminate]. Qed.
Lemma apply_op_sound : forall op c n c', apply_op op c=Some(n,c') ->
  Runs champion (N.to_nat n) (decode c) (decode c').
Proof.
  intros op c n c' H; destruct op; cbn [apply_op] in H.
  - apply costed_some in H as [<- H]; apply basic_sound,H.
  - apply costed_some in H as [<- H]; apply chain_sound,H.
  - apply costed_some in H as [<- H]; apply pair3_sound,H.
  - destruct c as [q d l r]. cbn [rr] in H.
    destruct r as [|[s m] rs]; [discriminate|]. destruct s; try discriminate.
    destruct rs; [|discriminate]. apply costed_some in H as [<- H].
    eapply grow2_sound; [reflexivity|exact H].
  - destruct c as [q d l r]. cbn [rr] in H.
    destruct r as [|[s m] rs]; [discriminate|]. destruct s; try discriminate.
    destruct rs as [|[s j] rs]; [discriminate|]. destruct s; try discriminate.
    apply costed_some in H as [<- H]. eapply consume1_sound; [reflexivity|exact H].
Qed.

Fixpoint replay (ops:list Op) c : option (N*rconf) :=
  match ops with
  | []=>Some(0%N,c)
  | op::ops=>match apply_op op c with
    | None=>None
    | Some(n,c')=>match replay ops (normalize c') with
      | None=>None | Some(m,c'')=>Some((n+m)%N,c'') end
    end
  end.
Theorem replay_sound : forall ops c n c', replay ops c=Some(n,c') ->
  Runs champion (N.to_nat n) (decode c) (decode c').
Proof.
  induction ops as [|op ops IH]; intros c n c' H; cbn [replay] in H.
  - injection H as <- <-. apply runs_zero.
  - destruct (apply_op op c) as [[t a]|] eqn:E; [|discriminate].
    destruct (replay ops (normalize a)) as [[u b]|] eqn:F; [|discriminate].
    injection H as <- <-. rewrite N2Nat.inj_add.
    apply apply_op_sound in E. specialize (IH _ _ _ F).
    rewrite normalize_sound in IH. eapply runs_add; eauto.
Qed.
