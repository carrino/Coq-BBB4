(** Binary run lengths. Expansion is used only in propositions; the checker
    never materializes a unary numeral or an expanded working tape. *)
From Coq Require Import Arith Lia List NArith FunctionalExtensionality.
From BBB24 Require Import Statement CTape Gap.
Import ListNotations.
Definition rside := list (Sym * N).
Fixpoint expand (xs:rside) : list Sym :=
  match xs with [] => [] | (s,n)::xs => repeat s (N.to_nat n) ++ expand xs end.
Definition push (s:Sym) (n:N) (xs:rside) : rside :=
  if N.eqb n 0 then xs else
  match xs with
  | [] => if sym_eqb s S0 then [] else [(s,n)]
  | (t,m)::xs' => if sym_eqb s t then (s,(n+m)%N)::xs' else (s,n)::xs
  end.
Fixpoint normal (xs:rside) : rside :=
  match xs with []=>[] | (s,n)::xs => push s n (normal xs) end.
Fixpoint view (xs:rside) : Sym * rside :=
  match xs with
  | [] => (S0,[])
  | (_,0%N)::xs => view xs
  | (s,Npos p)::xs => (s,(s,(Npos p-1)%N)::xs)
  end.

Lemma push_sound : forall s n xs,
  lift_side (expand (push s n xs)) =
  lift_side (repeat s (N.to_nat n) ++ expand xs).
Proof.
  intros s n xs. unfold push. destruct (N.eqb n 0) eqn:En.
  - apply N.eqb_eq in En; subst; reflexivity.
  - destruct xs as [|[t m] xs].
    + destruct (sym_eqb s S0) eqn:Es; [apply sym_eqb_spec in Es; subst|reflexivity].
      cbn [expand]. rewrite app_nil_r,lift_repeat_blank,lift_side_nil. reflexivity.
    + destruct (sym_eqb s t) eqn:Es; [apply sym_eqb_spec in Es; subst|reflexivity].
      cbn [expand]. rewrite N2Nat.inj_add,repeat_app,app_assoc. reflexivity.
Qed.
Lemma normal_sound : forall xs, lift_side (expand (normal xs)) = lift_side (expand xs).
Proof.
  induction xs as [|[s n] xs IH]; [reflexivity|]. cbn [normal expand].
  rewrite push_sound. apply lift_side_app_ext,IH.
Qed.
Lemma view_sound : forall xs s ys, view xs=(s,ys) ->
  lift_side (expand xs) = lift_side (s::expand ys).
Proof.
  induction xs as [|[a [|p]] xs IH]; intros s ys H.
  - injection H as <- <-. cbn [expand]. rewrite lift_side_cons,!lift_side_nil.
    apply functional_extensionality; intros [|n]; reflexivity.
  - exact (IH s ys H).
  - injection H as <- <-. cbn [expand].
    assert (E: N.to_nat (Npos p) = S (N.to_nat (Npos p-1))).
    { rewrite N2Nat.inj_sub. pose proof (Pnat.Pos2Nat.is_pos p). cbn [N.to_nat]. lia. }
    rewrite E. reflexivity.
Qed.
Lemma expand_take : forall s n k xs, (k<=n)%N ->
  expand ((s,n)::xs) = repeat s (N.to_nat k) ++ expand ((s,(n-k)%N)::xs).
Proof.
  intros. cbn [expand]. rewrite N2Nat.inj_sub.
  assert (N.to_nat k <= N.to_nat n) by lia.
  rewrite app_assoc, <- repeat_app. f_equal. f_equal. lia.
Qed.

Record rconf := RC { rq:St; rd:Dir; rl:rside; rr:rside }.
Definition decode c := gap (rq c) (rd c) (expand (rl c)) (expand (rr c)).
Definition normalize c := RC (rq c) (rd c) (normal (rl c)) (normal (rr c)).
Lemma normalize_sound : forall c, decode (normalize c) = decode c.
Proof. intros []; apply gap_sides; apply normal_sound. Qed.

Definition basic (tm:TM) c : option rconf :=
  match rd c with
  | DL => let '(s,l) := view (rl c) in
    match tm (rq c) s with
    | None=>None
    | Some tr=>Some
      (match t_dir tr with
       | DL=>RC (t_next tr) DL l (push (t_write tr) 1 (rr c))
       | DR=>RC (t_next tr) DR (push (t_write tr) 1 l) (rr c) end)
    end
  | DR => let '(s,r) := view (rr c) in
    match tm (rq c) s with
    | None=>None
    | Some tr=>Some
      (match t_dir tr with
       | DL=>RC (t_next tr) DL (rl c) (push (t_write tr) 1 r)
       | DR=>RC (t_next tr) DR (push (t_write tr) 1 (rl c)) r end)
    end
  end.
Lemma push_gap_left : forall q d s n l r,
  decode (RC q d (push s n l) r) =
  gap q d (repeat s (N.to_nat n) ++ expand l) (expand r).
Proof. intros; apply gap_sides; [apply push_sound|reflexivity]. Qed.
Lemma push_gap_right : forall q d s n l r,
  decode (RC q d l (push s n r)) =
  gap q d (expand l) (repeat s (N.to_nat n) ++ expand r).
Proof. intros; apply gap_sides; [reflexivity|apply push_sound]. Qed.
Lemma basic_sound : forall tm c c', basic tm c = Some c' ->
  Runs tm 1 (decode c) (decode c').
Proof.
  intros tm [q d l r] c' H. destruct d; cbn [basic rq rd rl rr] in H.
  - destruct (view l) as [s l'] eqn:E.
    destruct (tm q s) as [[w d p]|] eqn:Et; [|discriminate].
    pose proof (view_sound l s l' E) as V.
    assert (D: decode (RC q DL l r) = leftward q (s::expand l') (expand r)).
    { exact (gap_sides q DL (expand l) (s::expand l') (expand r) (expand r) V eq_refl). }
    rewrite D. destruct d; injection H as <-.
    + rewrite push_gap_right. apply left_step with (d:=DL); exact Et.
    + rewrite push_gap_left. apply left_step with (d:=DR); exact Et.
  - destruct (view r) as [s r'] eqn:E.
    destruct (tm q s) as [[w d p]|] eqn:Et; [|discriminate].
    pose proof (view_sound r s r' E) as V.
    assert (D: decode (RC q DR l r) = rightward q (expand l) (s::expand r')).
    { exact (gap_sides q DR (expand l) (expand l) (expand r) (s::expand r') eq_refl V). }
    rewrite D. destruct d; injection H as <-.
    + rewrite push_gap_right. apply right_step with (d:=DL); exact Et.
    + rewrite push_gap_left. apply right_step with (d:=DR); exact Et.
Qed.
