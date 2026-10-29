(** A checked finite FAR forward invariant covers the concrete S071 run.
    The finite Closed certificate is an explicit premise in this file. *)
From Coq Require Import List Arith Lia Bool PArith.
From BBB24 Require Import Statement CTape.
From BBB24Burn43S071FAR Require Import Programs.
From BBB24Burn43S071FAR Require Import FARForward DataSchema Checker SafeCover ZeroBridge.
From BBB24Burn43S071FAR Require Import BlockMicro LocalTable.
Import ListNotations.
Set Implicit Arguments.

Section Concrete.
Context (cert:rawcert).
Let d:=model cert c52_localfun.
Context (closed:Closed d).
Definition c54_flat(xs:list positive):list Sym:=flat_map c52_cells xs.
Definition c54_decode(f q:bool)(L T:list positive):cconf:=
 if f then s71_front(c52_state q)(c54_flat L)(c54_flat T)
 else s71_back(c52_state q)(c54_flat L)(c54_flat T).

Lemma c54_right_ok:forall T r,Summ d T r ->
 c52_right_ok(zflag r)(c54_flat T).
Proof.
 intros T r HS HB.
 eapply(@c53_summ_flat_right_ok d c52_cells);eauto.
 intros w r0 rn HP Hw;now apply c52_cells_blank in Hw.
Qed.

Lemma c54_view_front:forall q L T w T0,View d T w T0 ->
 lift(c54_decode true q L T)=
 lift(c52_local_entry w q true(c54_flat L)(c54_flat T0)).
Proof.
 intros q L T w T0 HV;destruct HV.
 - reflexivity.
 - apply c53_front_empty_pad.
Qed.

Lemma c54_view_back:forall q L T w L0,View d L w L0 ->
 lift(c54_decode false q L T)=
 lift(c52_local_entry w q false(c54_flat L0)(c54_flat T)).
Proof.
 intros q L T w L0 HV;destruct HV.
 - reflexivity.
 - apply c53_back_empty_pad.
Qed.

Lemma c54_forward_out:forall wn qn back L T0,
 c52_local_exit true wn qn back(c54_flat L)(c54_flat T0)=
 c54_decode(negb back)qn(if back then L else wn::L)
   (if back then wn::T0 else T0).
Proof. intros;destruct back;reflexivity. Qed.

Lemma c54_backward_out:forall wn qn back L0 T,
 c52_local_exit false wn qn back(c54_flat L0)(c54_flat T)=
 c54_decode back qn(if back then wn::L0 else L0)
   (if back then T else wn::T).
Proof. intros;destruct back;reflexivity. Qed.

Theorem c54_block_sound:forall f q L T f' q' L' T',
 BlockStep d f q L T f' q' L' T' ->
 exists k ci ce,0<k /\ lift ci=lift(c54_decode f q L T) /\
 csteps s71_tm k ci=Some ce /\
 lift ce=lift(c54_decode f' q' L' T') /\ c52_safe_before k ci.
Proof.
 intros f q L T f' q' L' T' H.
 destruct H as[q L T w T0 r0 wn qn back HV HS HL|
  q L T w L0 r fz wn qn back HV HS HL].
 - pose proof(c54_right_ok HS)as HR.
   destruct(c52_localfun_micro w q true true(zflag r0)wn qn back HL
     (c54_flat L)(c54_flat T0)HR)as[k[Hk[Hrun Hsafe]]].
   exists k,(c52_local_entry w q true(c54_flat L)(c54_flat T0)),
    (c52_local_exit true wn qn back(c54_flat L)(c54_flat T0)).
   split;[exact Hk|]. split.
   + symmetry;now apply c54_view_front.
   + split;[exact Hrun|]. split;[now rewrite c54_forward_out|exact Hsafe].
 - pose proof(c54_right_ok HS)as HR.
   destruct(c52_localfun_micro w q false(zflag r)fz wn qn back HL
     (c54_flat L0)(c54_flat T)HR)as[k[Hk[Hrun Hsafe]]].
   exists k,(c52_local_entry w q false(c54_flat L0)(c54_flat T)),
    (c52_local_exit false wn qn back(c54_flat L0)(c54_flat T)).
   split;[exact Hk|]. split.
   + symmetry;now apply c54_view_back.
   + split;[exact Hrun|]. split;[now rewrite c54_backward_out|exact Hsafe].
Qed.

Definition c54_good(c:cconf):Prop:=exists f q L T,
 c=c54_decode f q L T /\ Inv d f q L T.

Theorem c54_progress:c53_progress s71_tm c54_good.
Proof.
 intros c[f[q[L[T[-> HI]]]]].
 destruct(invariant_progress closed HI)as[f'[q'[L'[T'[HS HI']]]]].
 destruct(c54_block_sound HS)as[k[ci[ce[Hk[Hci[Hrun[Hce Hsafe]]]]]]].
 exists k,ci,ce,(c54_decode f' q' L' T').
 split;[exact Hk|]. split;[exact Hci|]. split;[exact Hrun|].
 split;[exact Hce|]. split;[|exact Hsafe].
 exists f',q',L',T';auto.
Qed.

Theorem c54_no_spinout:forall n l,
 csteps s71_tm n c0<>Some(StB,(l,S0,[])).
Proof.
 apply(c53_blank_no_spinout s71_tm c54_good
   (c54_decode true false [blankword] [])).
 - exact c54_progress.
 - exists true,false,[blankword],[];split;[reflexivity|].
   exact(initial_inv closed).
 - apply c53_initial_padded.
Qed.
End Concrete.

Print Assumptions c54_block_sound.
Print Assumptions c54_progress.
Print Assumptions c54_no_spinout.
