(** Uniform guarded sweeps for the periodic block-list core C orbit. *)
From Coq Require Import Arith Lia List FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr GuardedSweepTr BlockCoreCOrbitDefsTr.
Import ListNotations.
Definition bco_A:list Sym:=[S0;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1].
Definition bco_Qr:list Sym:=[S1;S1;S0;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1].
Definition bco_Wr:list Sym:=[S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1].
Definition bco_G:list Sym:=[S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0].
Definition bco_Ql:list Sym:=[S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1;S1].
Definition bco_Wl:list Sym:=[S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0].
Definition bco_X:list Sym:=[S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1;S1].
Definition bco_T(second:bool):list Sym:=if second then [S1;S1;S0;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1] else [S1;S1;S0;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1].
Definition bco_S(second:bool):list Sym:=if second then [S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0] else [S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0].
Section Machine.
Variable tm:TM.
Hypothesis Htm:forall q h,tm q h=bco_tm q h.
Lemma bco_tm_equal:tm=bco_tm.
Proof. apply functional_extensionality;intro q;apply functional_extensionality;intro h;apply Htm. Qed.
Local Ltac run:=rewrite bco_tm_equal;vm_compute;reflexivity.
Lemma bco_unitR:forall L R,
 Reach0 tm(cR StB(bco_A++L)(bco_Qr++R))
          (cR StB(bco_A++bco_Wr++L)R).
Proof.
 intros. eapply(r0_run _ 330).
 - unfold cR,bco_A,bco_Qr,bco_Wr;cbn[app];run.
 - apply reach0_refl.
Qed.
Lemma bco_unitL:forall L R,
 Reach0 tm(cL StC(bco_Ql++L)(bco_G++R))
          (cL StC L(bco_G++bco_Wl++R)).
Proof.
 intros. eapply(r0_run _ 190).
 - unfold cL,bco_G,bco_Ql,bco_Wl;cbn[app];run.
 - apply reach0_refl.
Qed.
Lemma bco_sweepR:forall n L R,
 Reach0 tm(cR StB(bco_A++L)(rep bco_Qr n++R))
          (cR StB(bco_A++rep bco_Wr n++L)R).
Proof. apply guarded_sweepR;apply bco_unitR. Qed.
Lemma bco_sweepL:forall n L R,
 Reach0 tm(cL StC(rep bco_Ql n++L)(bco_G++R))
          (cL StC L(bco_G++rep bco_Wl n++R)).
Proof. apply guarded_sweepL;apply bco_unitL. Qed.
Lemma bco_X_repeat:forall n,
 rep bco_Wr n++bco_X=bco_X++rep bco_Ql n.
Proof.
 intro n. change(rep(bco_X++[S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1])n++bco_X=
 bco_X++rep([S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1]++bco_X)n).
 symmetry;apply rep_rotate_prefix.
Qed.
Theorem bco_roundtrip_hyp:forall T S,
 (forall U,Reach0 tm(cR StB(bco_A++bco_X++U)T)
                    (cL StC U(bco_G++S)))->
 forall n U,
 Reach0 tm(cR StB(bco_A++bco_X++U)(rep bco_Qr n++T))
          (cL StC U(bco_G++rep bco_Wl n++S)).
Proof.
 intros T S HB n U.
 eapply reach0_trans;[apply bco_sweepR|].
 rewrite (app_assoc(rep bco_Wr n)bco_X U),bco_X_repeat.
 repeat rewrite <-app_assoc.
 eapply reach0_trans;[apply HB|].
 apply bco_sweepL.
Qed.

Lemma bco_bridge:forall second U,
 Reach0 tm(cR StB(bco_A++bco_X++U)(bco_T second))
          (cL StC U(bco_G++bco_S second)).
Proof.
 intros [] U.
 - eapply(r0_run _ 830).
   + unfold cR,cL,bco_A,bco_X,bco_T,bco_G,bco_S;cbn[app];run.
   + apply reach0_refl.
 - eapply(r0_run _ 726).
   + unfold cR,cL,bco_A,bco_X,bco_T,bco_G,bco_S;cbn[app];run.
   + apply reach0_refl.
Qed.
Lemma bco_bridge_pad:forall second U,
 Reach0 tm(cR StB(bco_A++bco_X++U)(bco_T second++[S0]))
          (cL StC U(bco_G++bco_S second)).
Proof.
 intros [] U.
 - eapply(r0_run _ 830).
   + unfold cR,cL,bco_A,bco_X,bco_T,bco_G,bco_S;cbn[app];run.
   + apply reach0_refl.
 - eapply(r0_run _ 726).
   + unfold cR,cL,bco_A,bco_X,bco_T,bco_G,bco_S;cbn[app];run.
   + apply reach0_refl.
Qed.
Theorem bco_roundtrip:forall second n U,
 Reach0 tm(cR StB((bco_A++bco_X)++U)(rep bco_Qr n++bco_T second))
          (cL StC U(bco_G++rep bco_Wl n++bco_S second)).
Proof. intros;rewrite <-app_assoc;apply bco_roundtrip_hyp;apply bco_bridge. Qed.
Theorem bco_roundtrip_pad:forall second n U,
 Reach0 tm(cR StB((bco_A++bco_X)++U)(rep bco_Qr n++bco_T second++[S0]))
          (cL StC U(bco_G++rep bco_Wl n++bco_S second)).
Proof. intros;rewrite <-app_assoc;apply bco_roundtrip_hyp;apply bco_bridge_pad. Qed.
End Machine.
