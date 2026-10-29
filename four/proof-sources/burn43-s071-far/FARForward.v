From Coq Require Import List Bool.
Import ListNotations.
Set Implicit Arguments.

(* A finite certificate need not describe every right stack. Push only records
   the partial summary edges which occur in its checked forward closure. *)
Record FARData := {
  W : Type; Q : Type; R : Type; C : Type;
  blank : W; start : R; initial : Q;
  cw : C -> W; cq : C -> Q; cr : C -> R;
  Cok : C -> Prop;
  Push : W -> R -> R -> Prop;
  Zero : R -> Prop;
  H2ok : (Q * R) -> Prop;
  Pre32 : C -> (Q * R) -> Prop;
  Pre33 : C -> C -> Prop;
  Pre3l : C -> Prop;
  Ret2 : (Q * R) -> (Q * R) -> Prop;
  Ret3 : C -> (Q * R) -> Prop;
  Retl : (Q * R) -> Prop;
  (* entry-forward, behind-zero, ahead-zero, output word/state, exit-back *)
  Local : W -> Q -> bool -> bool -> bool -> W -> Q -> bool -> Prop;
  zflag : R -> bool
}.

Section Forward.
Context (d : FARData).
Let Word := W d.
Let State := Q d.
Let Summary := R d.
Let Node := C d.
Let H2 := (State * Summary)%type.
Definition root (c : Node) : H2 := (cq d c, cr d c).

Inductive Gen2 : H2 -> list Word -> Prop :=
| gen2 : forall c L, Cok d c -> Gen3 c L ->
    Gen2 (root c) (cw d c :: L)
with Gen3 : Node -> list Word -> Prop :=
| gen3_left : forall c, Cok d c -> Pre3l d c -> Gen3 c []
| gen3_two : forall c a L, Cok d c -> Pre32 d c a -> Gen2 a L -> Gen3 c L
| gen3_three : forall c c0 L, Cok d c -> Pre33 d c c0 -> Gen3 c0 L -> Gen3 c L.

Definition BackInv (b : H2) (L : list Word) : Prop :=
  (L = [] /\ Retl d b) \/ exists a, Gen2 a L /\ Ret2 d a b.

Record Closed := {
  root_ok : forall c, Cok d c -> H2ok d (root c);
  initial_node : exists c, Cok d c /\ cw d c = blank d /\
      cq d c = initial d /\ cr d c = start d /\ Pre3l d c;
  zero_start : Zero d (start d);
  zero_flag : forall r, Zero d r -> zflag d r = true;
  zero_push : forall r rn, Zero d r -> Push d (blank d) r rn -> Zero d rn;
  blank_push : Push d (blank d) (start d) (start d);
  h2_rule : forall q r w r0, H2ok d (q,r) -> Push d w r0 r ->
    exists wn qn back,
      Local d w q true true (zflag d r0) wn qn back /\
      if back then exists rn, Push d wn r0 rn /\ Ret2 d (q,r) (qn,rn)
      else exists c, Cok d c /\ cw d c = wn /\ cq d c = qn /\
            cr d c = r0 /\ Pre32 d c (q,r);
  h3_rule : forall c q r, Cok d c -> Ret2 d (root c) (q,r) ->
    exists wn qn back,
      Local d (cw d c) q false (zflag d r) (zflag d (cr d c)) wn qn back /\
      if back then exists c0, Cok d c0 /\ cw d c0 = wn /\
         cq d c0 = qn /\ cr d c0 = r /\ Pre33 d c0 c
      else exists rn, Push d wn r rn /\ Ret3 d c (qn,rn);
  left_rule : forall q r, Retl d (q,r) ->
    exists wn qn back,
      Local d (blank d) q false (zflag d r) true wn qn back /\
      if back then exists c, Cok d c /\ cw d c = wn /\
         cq d c = qn /\ cr d c = r /\ Pre3l d c
      else exists rn, Push d wn r rn /\ Retl d (qn,rn);
  ret_three_left : forall c b, Ret3 d c b -> Pre3l d c -> Retl d b;
  ret_three_two : forall c a b, Ret3 d c b -> Pre32 d c a -> Ret2 d a b;
  ret_three_three : forall c c0 b, Ret3 d c b -> Pre33 d c c0 -> Ret3 d c0 b
}.

Inductive Summ : list Word -> Summary -> Prop :=
| sum_nil : Summ [] (start d)
| sum_cons : forall w L r rn, Summ L r -> Push d w r rn -> Summ (w::L) rn.

Inductive View : list Word -> Word -> list Word -> Prop :=
| view_cons : forall w L, View (w::L) w L
| view_nil : View [] (blank d) [].

Definition Inv (forward : bool) (q : State) (L T : list Word) : Prop :=
  exists r, Summ T r /\ if forward then Gen2 (q,r) L else BackInv (q,r) L.

Context (closed : Closed).

Lemma gen2_h2ok : forall a L, Gen2 a L -> H2ok d a.
Proof. intros a L H; inversion H; subst; eapply root_ok; eauto. Qed.

Scheme Gen2_mut := Induction for Gen2 Sort Prop
with Gen3_mut := Induction for Gen3 Sort Prop.
Combined Scheme Gen_mut from Gen2_mut, Gen3_mut.

Lemma ret3_gen3_back : forall c L, Gen3 c L ->
  forall b, Ret3 d c b -> BackInv b L.
Proof.
  apply (Gen3_mut (fun a L (_ : Gen2 a L) => True)
    (fun c L (_ : Gen3 c L) => forall b, Ret3 d c b -> BackInv b L)).
  - intros; exact I.
  - intros c Hc Hp b Hr. left; split; [reflexivity|].
    eapply ret_three_left; eauto.
  - intros c a L Hc Hp Hg _ b Hr. right. exists a; split; [exact Hg|].
    eapply ret_three_two; eauto.
  - intros c c0 L Hc Hp Hg IH b Hr. apply IH.
    eapply ret_three_three; eauto.
Qed.

Lemma summ_blank : forall L r, Summ L r ->
  Forall (fun w => w = blank d) L -> Zero d r.
Proof.
  intros L r H; induction H; intro Hb.
  - apply zero_start; exact closed.
  - inversion Hb; subst. eapply zero_push; eauto.
Qed.

Lemma summ_view : forall T r, Summ T r ->
  exists w T0 r0, View T w T0 /\ Summ T0 r0 /\ Push d w r0 r.
Proof.
  intros T r H; inversion H; subst.
  - exists (blank d), [], (start d). repeat split.
    + apply view_nil.
    + apply sum_nil.
    + apply blank_push; exact closed.
  - eexists; eexists; eexists. repeat split; eauto using View.
Qed.

Inductive BlockStep : bool -> State -> list Word -> list Word ->
    bool -> State -> list Word -> list Word -> Prop :=
| bs_forward : forall q L T w T0 r0 wn qn back,
    View T w T0 -> Summ T0 r0 ->
    Local d w q true true (zflag d r0) wn qn back ->
    BlockStep true q L T (negb back) qn
      (if back then L else wn::L) (if back then wn::T0 else T0)
| bs_backward : forall q L T w L0 r fz wn qn back,
    View L w L0 -> Summ T r ->
    Local d w q false (zflag d r) fz wn qn back ->
    BlockStep false q L T back qn
      (if back then wn::L0 else L0) (if back then T else wn::T).

Lemma initial_inv : Inv true (initial d) [blank d] [].
Proof.
  destruct (initial_node closed) as [c [Hc [Hw [Hq [Hr Hp]]]]].
  exists (start d); split; [constructor|].
  unfold root. rewrite <- Hw, <- Hq, <- Hr.
  apply gen2; auto. apply gen3_left; auto.
Qed.

Theorem invariant_progress : forall f q L T, Inv f q L T ->
  exists f' q' L' T', BlockStep f q L T f' q' L' T' /\ Inv f' q' L' T'.
Proof.
  intros f q L T [r [Hs Hi]]. destruct f.
  - destruct (summ_view Hs) as [w [T0 [r0 [Hv [Hs0 Hp]]]]].
    destruct (h2_rule closed q r w r0 (gen2_h2ok Hi) Hp)
      as [wn [qn [back [Hl Ho]]]].
    destruct back.
    + destruct Ho as [rn [Hpn Hret]].
      exists false, qn, L, (wn::T0); split.
      * eapply bs_forward with (back:=true); eauto.
      * exists rn; split; [econstructor; eauto|].
        right. exists (q,r); auto.
    + destruct Ho as [c [Hc [Hw [Hq [Hr Hpre]]]]].
      exists true, qn, (wn::L), T0; split.
      * eapply bs_forward with (back:=false); eauto.
      * exists r0; split; [exact Hs0|].
        rewrite <- Hw, <- Hq, <- Hr. change (Gen2 (root c) (cw d c :: L)).
        apply gen2; auto. eapply gen3_two; eauto.
  - destruct Hi as [[He Hret] | [a [Hg Hret]]].
    + subst L.
      destruct (left_rule closed q r Hret) as [wn [qn [back [Hl Ho]]]].
      destruct back.
      * destruct Ho as [c [Hc [Hw [Hq [Hr Hpre]]]]].
        exists true, qn, [wn], T; split.
        -- eapply bs_backward with (back:=true); eauto using View.
        -- exists r; split; [exact Hs|].
           rewrite <- Hw, <- Hq, <- Hr. change (Gen2 (root c) [cw d c]).
           apply gen2; auto. apply gen3_left; auto.
      * destruct Ho as [rn [Hpn Hr]].
        exists false, qn, [], (wn::T); split.
        -- eapply bs_backward with (back:=false); eauto using View.
        -- exists rn; split; [econstructor; eauto|]. left; auto.
    + inversion Hg as [c L0 Hc Hg3]; subst a L.
      destruct (h3_rule closed c q r Hc Hret)
        as [wn [qn [back [Hl Ho]]]].
      destruct back.
      * destruct Ho as [c0 [Hc0 [Hw [Hq [Hr Hpre]]]]].
        exists true, qn, (wn::L0), T; split.
        -- eapply bs_backward with (back:=true); eauto using View.
        -- exists r; split; [exact Hs|].
           rewrite <- Hw, <- Hq, <- Hr. change (Gen2 (root c0) (cw d c0::L0)).
           apply gen2; auto. eapply gen3_three; eauto.
      * destruct Ho as [rn [Hpn Hret3]].
        exists false, qn, L0, (wn::T); split.
        -- eapply bs_backward with (back:=false); eauto using View.
        -- exists rn; split; [econstructor; eauto|].
           eapply ret3_gen3_back; eauto.
Qed.

Print Assumptions invariant_progress.
End Forward.
