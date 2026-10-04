(** * Marked returns for the paired block-list core.

    The right normal form has fixed 1s in alternate cells.  A D pass
    returns through a left 1 and preserves this language, with its phase
    shifted.  Strong induction on the finite pair word handles the two
    continuing cases: runs of one and five 1s.  Longer odd runs normalize
    through the 1110 / 1011 blocks produced by the paired sweeps.

    A C pass then consumes a finite stack of left pairs 01 / 11.  The
    rightward D scan builds exactly such a stack.  Two protected left
    bases give positive returns to A0 for either A0=0RB or A0=1LD.
    No numerical relation between adjacent block lengths is required. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Inductive bca_tail : list Sym -> Prop :=
| bca_tail_nil : bca_tail []
| bca_tail_one : bca_tail [S1]
| bca_tail_pair : forall b R,bca_tail R->bca_tail(S1::b::R).
Fixpoint bca_enc(w:list bool):list Sym := match w with
| []=>[]|b::w=>S1::(if b then S1 else S0)::bca_enc w end.
Fixpoint bca_pre(k:nat)(w:list bool):list bool := match k with
|0=>w|S k=>true::true::bca_pre k w end.
Lemma bca_enc_tail:forall w,bca_tail(bca_enc w).
Proof. induction w;cbn;constructor;assumption. Qed.
Lemma bca_enc_pre:forall k w,bca_enc(bca_pre k w)=rep[S1;S1;S1;S1]k++bca_enc w.
Proof. induction k;intro w;cbn;now rewrite ?IHk. Qed.
Lemma bca_pre_len:forall k w,length(bca_pre k w)=2*k+length w.
Proof. induction k;intro w;cbn;rewrite ?IHk;lia. Qed.
Lemma bca_decomp:forall w,exists k t,w=bca_pre k t /\
 (t=[] \/t=[true]\/ (exists r,t=false::r)\/(exists r,t=true::false::r)).
Proof.
 fix IH 1. intros[|[]w].
 - exists 0,[];cbn;auto.
 - destruct w as[|[]w].
   + exists 0,[true];cbn;auto.
   + destruct(IH w)as(k&t&E&H). exists(S k),t;split;[cbn;now rewrite E|exact H].
   + exists 0,(true::false::w);split;[reflexivity|right;right;right;exists w;reflexivity].
 - exists 0,(false::w);split;[reflexivity|right;right;left;exists w;reflexivity].
Qed.
Lemma bca_tail_even_ones:forall n R,bca_tail R->bca_tail(rep[S1](2*n)++R).
Proof. induction n;intros;cbn;[assumption|].
 replace(n+S(n+0))with(S(2*n))by lia;cbn;constructor;apply IHn;assumption.
Qed.
Lemma bca_tail_ones:forall n,bca_tail(rep[S1]n).
Proof. fix IH 1. intros[|[|n]];cbn;constructor;apply IH. Qed.
Lemma bca_tail_1110:forall k R,bca_tail R->bca_tail(rep[S1;S1;S1;S0]k++R).
Proof. induction k;intros;cbn;[assumption|constructor;constructor;apply IHk;assumption]. Qed.
Lemma bca_tail_1011:forall k R,bca_tail R->bca_tail(rep[S1;S0;S1;S1]k++R).
Proof. induction k;intros;cbn;[assumption|constructor;constructor;apply IHk;assumption]. Qed.
Fixpoint bca_left(w:list bool):list Sym:=match w with
|[]=>[]|b::w=>(if b then S1 else S0)::S1::bca_left w end.
Inductive bca_even_tail:list Sym->Prop:=
|bca_even_nil:bca_even_tail[]
|bca_even_last:forall b,bca_even_tail[b]
|bca_even_pair:forall b R,bca_even_tail R->bca_even_tail(b::S1::R).
Lemma bca_shift:forall R,bca_tail R->forall b,bca_even_tail(b::R).
Proof. intros R H;induction H;intro a;constructor;auto. constructor. Qed.
Lemma bca_tail_complete:forall R,bca_tail R->exists w,
 R=bca_enc w \/ R++[S0]=bca_enc w.
Proof.
 intros R H;induction H.
 - exists[];left;reflexivity.
 - exists[false];right;reflexivity.
 - destruct IHbca_tail as(w&[E|E]);destruct b.
   + exists(false::w);left;cbn;now rewrite E.
   + exists(true::w);left;cbn;now rewrite E.
   + exists(false::w);right;cbn;now rewrite E.
   + exists(true::w);right;cbn;now rewrite E.
Qed.
Section Core.
Variable tm:TM.
Hypotheses
 (HA1:tm StA S1=Some(mkTrans S0 DL StB))
 (HB0:tm StB S0=Some(mkTrans S1 DL StC))
 (HB1:tm StB S1=Some(mkTrans S1 DR StD))
 (HC0:tm StC S0=Some(mkTrans S1 DL StA))
 (HC1:tm StC S1=Some(mkTrans S0 DR StD))
 (HD0:tm StD S0=Some(mkTrans S1 DR StB))
 (HD1:tm StD S1=Some(mkTrans S1 DR StC)).
Local Ltac run :=
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep];
 repeat(first[rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep]);reflexivity.
Local Ltac go n := first
 [eapply(r1_run _ n);[lia|run|]
 |eapply(r0_run _ n);[run|]].
Definition bca_hit(c:cconf):Prop := Fires tm c(StA,S0).
Lemma bca_Azero : forall L R,bca_hit(StA,(L,S0,R)).
Proof. intros;apply fires_here;reflexivity. Qed.
Lemma bca_Cboundary : forall R,bca_hit(StC,([],S0,R)).
Proof. intros;eapply fire_back;[go 1;r0|apply bca_Azero]. Qed.
Lemma bca_Bboundary : forall R,bca_hit(StB,([],S0,R)).
Proof. intros;eapply fire_back;[go 1;r0|apply bca_Cboundary]. Qed.
(** Every instruction which can cross the left boundary either already
    is A0 or reaches it through the blank B0/C0 chain. *)
Theorem bca_left_boundary : forall q h tr R,
 tm q h=Some tr -> t_dir tr=DL -> bca_hit(q,([],h,R)).
Proof.
 intros q h tr R E D. destruct q,h.
 - apply bca_Azero.
 - rewrite HA1 in E;injection E as <-.
   eapply fire_back;[go 1;r0|apply bca_Bboundary].
 - rewrite HB0 in E;injection E as <-. apply bca_Bboundary.
 - rewrite HB1 in E;injection E as <-;discriminate.
 - rewrite HC0 in E;injection E as <-. apply bca_Cboundary.
 - rewrite HC1 in E;injection E as <-;discriminate.
 - rewrite HD0 in E;injection E as <-;discriminate.
 - rewrite HD1 in E;injection E as <-;discriminate.
Qed.
(** A right 10 marker turns each encountered C1 into a left step. *)
Lemma bca_marked_one : forall L R,
 Reach0 tm(cL StC(S1::L)(S1::S0::R))
          (cL StC L(S1::S0::S1::R)).
Proof. intros;go 5;r0. Qed.
(** Two alternating left pairs are rewritten into the 1110 list unit. *)
Lemma bca_pair_drain : forall k L R,
 Reach0 tm(cL StC(rep[S0;S1;S0;S1]k++L)(S1::S0::R))
          (cL StC L(S1::S0::(rep[S1;S1;S1;S0]k++R))).
Proof.
 induction k as[|k IH];intros L R.
 - cbn[rep app];r0.
 - cbn[rep app]. go 8.
   change(Reach0 tm(cL StC(rep[S0;S1;S0;S1]k++L)(S1::S0::(S1::S1::S1::S0::R)))
     (cL StC L(S1::S0::S1::S1::S1::S0::(rep[S1;S1;S1;S0]k++R)))).
   pose proof(IH L(S1::S1::S1::S0::R))as H.
   replace(S1::S1::S1::S0::(rep[S1;S1;S1;S0]k++R))
     with(rep[S1;S1;S1;S0]k++S1::S1::S1::S0::R).
   + exact H.
   + symmetry. change([S1;S1;S1;S0]++rep[S1;S1;S1;S0]k++R=
            rep[S1;S1;S1;S0]k++[S1;S1;S1;S0]++R).
     rewrite !app_assoc. f_equal. change(rep[S1;S1;S1;S0](S k)=
       rep[S1;S1;S1;S0]k++[S1;S1;S1;S0]). apply rep_S_r.
Qed.
(** The block introduced by the pair drain turns D back to its left tail. *)
Lemma bca_unit_return : forall L R,
 Reach0 tm(cR StD L(S1::S1::S1::S0::R))
          (cL StC L(S1::S0::S1::S1::R)).
Proof. intros;go 11;r0. Qed.
(** A four-cell right sweep creates exactly the left unit drained above. *)
Lemma bca_quad_scan : forall k L R,
 Reach0 tm(cR StD L(rep[S1;S1;S1;S1]k++R))
          (cR StD(rep[S0;S1;S0;S1]k++L)R).
Proof. apply sweepR. intros;go 4;r0. Qed.
Lemma bca_ones_drain : forall k L R,
 Reach0 tm(cL StC(rep[S1]k++L)(S1::S0::R))
          (cL StC L(S1::S0::(rep[S1]k++R))).
Proof.
 induction k as[|k IH];intros L R.
 - cbn[rep app];r0.
 - cbn[rep app]. rt bca_marked_one.
   pose proof(IH L(S1::R))as H.
   replace(S1::(rep[S1]k++R))with(rep[S1]k++S1::R).
   + exact H.
   + symmetry. change([S1]++rep[S1]k++R=rep[S1]k++[S1]++R).
     rewrite !app_assoc. f_equal. change(rep[S1](S k)=rep[S1]k++[S1]).
     apply rep_S_r.
Qed.
(** Every run whose length is three modulo four returns to the left;
    the run becomes a finite sequence of 1110 list units. *)
Theorem bca_odd_run : forall k L R,
 Reach0 tm(cR StD L(rep[S1;S1;S1;S1]k++S1::S1::S1::S0::R))
          (cL StC L(S1::S0::(rep[S1;S1;S1;S0]k++S1::S1::R))).
Proof. intros;rt bca_quad_scan;rt bca_unit_return;apply bca_pair_drain. Qed.
(** The complementary B return crosses the same left pairs. *)
Lemma bca_Bpair_drain : forall k L R,
 Reach0 tm(cL StB(rep[S0;S1;S0;S1]k++L)(S0::S1::R))
          (cL StB L(S0::S1::(rep[S1;S0;S1;S1]k++R))).
Proof.
 induction k as[|k IH];intros L R.
 - cbn[rep app];r0.
 - cbn[rep app]. go 8.
   change(Reach0 tm(cL StB(rep[S0;S1;S0;S1]k++L)(S0::S1::(S1::S0::S1::S1::R)))
     (cL StB L(S0::S1::S1::S0::S1::S1::(rep[S1;S0;S1;S1]k++R)))).
   pose proof(IH L(S1::S0::S1::S1::R))as H.
   replace(S1::S0::S1::S1::(rep[S1;S0;S1;S1]k++R))
     with(rep[S1;S0;S1;S1]k++S1::S0::S1::S1::R).
   + exact H.
   + symmetry. change([S1;S0;S1;S1]++rep[S1;S0;S1;S1]k++R=
            rep[S1;S0;S1;S1]k++[S1;S0;S1;S1]++R).
     rewrite !app_assoc. f_equal. change(rep[S1;S0;S1;S1](S k)=
       rep[S1;S0;S1;S1]k++[S1;S0;S1;S1]). apply rep_S_r.
Qed.
Theorem bca_odd_run_B : forall k L R,
 Reach0 tm(cR StD L(rep[S1;S1;S1;S1]k++S1::S0::R))
          (cL StB L(S0::S1::(rep[S1;S0;S1;S1]k++R))).
Proof. intros;rt bca_quad_scan;go 3;apply bca_Bpair_drain. Qed.
(** With a left 1, two generated 1011 units force the C return. *)
Theorem bca_long_odd_return : forall k L R,
 Reach0 tm(cR StD(S1::L)(rep[S1;S1;S1;S1](S(S k))++S1::S0::R))
   (cL StC L(S1::S0::(rep[S1]9++rep[S1;S0;S1;S1]k++R))).
Proof.
 intros;rt bca_odd_run_B. cbn[rep app]. go 3. go 6.
 change(Reach0 tm(cR StD(S1::S1::S1::S1::S1::L)
   (S1::S1::S1::S0::S1::S1::(rep[S1;S0;S1;S1]k++R)))
   (cL StC L(S1::S0::(rep[S1]9++rep[S1;S0;S1;S1]k++R)))).
 rt bca_unit_return.
 change(Reach0 tm(cL StC(rep[S1]5++L)
   (S1::S0::(S1::S1::S1::S1::(rep[S1;S0;S1;S1]k++R))))
   (cL StC L(S1::S0::(rep[S1]5++S1::S1::S1::S1::(rep[S1;S0;S1;S1]k++R))))).
 apply bca_ones_drain.
Qed.
Lemma bca_short_one : forall L R,
 Reach0 tm(cR StD(S1::L)(S1::S0::R))(cR StD(S1::S1::S1::L)R).
Proof. intros;go 6;r0. Qed.
Lemma bca_short_five : forall L R,
 Reach0 tm(cR StD(S1::L)(S1::S1::S1::S1::S1::S0::R))
          (cR StD(S1::S1::S1::S1::S1::L)(S1::S1::R)).
Proof. intros;go 24;r0. Qed.
Lemma bca_blank_return : forall L,
 Reach0 tm(cR StD L[])(cL StC L[S1;S0;S1]).
Proof. intros;go 7;r0. Qed.
Lemma bca_two_blank : forall L,
 Reach0 tm(cR StD L[S1;S1])(cL StB L[S0;S1;S1;S0;S1]).
Proof. intros;go 11;r0. Qed.
Lemma bca_tail_phase_add : forall k R,bca_tail(S1::R)->
 bca_tail(S1::(rep[S1](2*k)++R)).
Proof.
 intros k R H. replace(S1::(rep[S1](2*k)++R))with(rep[S1](2*k)++S1::R).
 - now apply bca_tail_even_ones.
 - induction(2*k);cbn;now rewrite ?IHn.
Qed.
Lemma bca_quad_terminal : forall k L,exists R,
 bca_tail(S1::R) /\
 Reach0 tm(cR StD(S1::L)(rep[S1;S1;S1;S1]k))
          (cL StC L(S1::S0::R)).
Proof.
 intros. exists(S1::(rep[S1;S1;S1;S0]k++[S1]));split.
 - constructor;apply bca_tail_1110;constructor.
 - rewrite <-app_nil_r with(l:=rep[S1;S1;S1;S1]k).
   rt bca_quad_scan;rt bca_blank_return;rt bca_pair_drain;apply bca_marked_one.
Qed.
Lemma bca_quad_two_terminal : forall k L,exists R,
 bca_tail(S1::R) /\
 Reach0 tm(cR StD(S1::L)(rep[S1;S1;S1;S1]k++[S1;S1]))
          (cL StC L(S1::S0::R)).
Proof.
 intros k L.
 assert(H:Reach0 tm(cR StD(S1::L)(rep[S1;S1;S1;S1]k++[S1;S1]))
  (cR StD(S1::S1::S1::L)(rep[S1;S0;S1;S1]k++[S1;S0;S1]))).
 { rt bca_quad_scan;rt bca_two_blank;rt bca_Bpair_drain;go 3;r0. }
 destruct k as[|[|k]].
 - exists(rep[S1]8);split;[change(bca_tail(rep[S1]9));apply bca_tail_ones|].
   rt H. cbn[rep app]. go 12. rt bca_blank_return.
   change(Reach0 tm(cL StC(rep[S1]7++L)(S1::S0::[S1]))
     (cL StC L(S1::S0::(rep[S1]7++[S1])))). apply bca_ones_drain.
 - exists(rep[S1]8);split;[change(bca_tail(rep[S1]9));apply bca_tail_ones|].
   rt H. cbn[rep app]. go 6. rt bca_unit_return.
   change(Reach0 tm(cL StC(rep[S1]5++L)(S1::S0::[S1;S1;S1]))
     (cL StC L(S1::S0::(rep[S1]5++[S1;S1;S1])))). apply bca_ones_drain.
 - exists(rep[S1]9++rep[S1;S0;S1;S1]k++[S1;S0;S1]);split.
   + change(bca_tail(rep[S1](2*5)++rep[S1;S0;S1;S1]k++[S1;S0;S1])).
     apply bca_tail_even_ones,bca_tail_1011;constructor;constructor.
   + rt H. cbn[rep app]. go 6. rt bca_unit_return.
     change(Reach0 tm(cL StC(rep[S1]5++L)(S1::S0::(rep[S1]4++rep[S1;S0;S1;S1]k++[S1;S0;S1])))
      (cL StC L(S1::S0::(rep[S1]5++rep[S1]4++rep[S1;S0;S1;S1]k++[S1;S0;S1])))).
     apply bca_ones_drain.
Qed.
(** A leading left 1 is enough.  The extra 1 in the output language
    records the phase shift caused by consuming that protected cell. *)
Theorem bca_paired_right : forall w L,exists R,
 bca_tail(S1::R) /\
 Reach0 tm(cR StD(S1::L)(bca_enc w))(cL StC L(S1::S0::R)).
Proof.
 assert(H:forall N w L,length w<=N->exists R,bca_tail(S1::R) /\
  Reach0 tm(cR StD(S1::L)(bca_enc w))(cL StC L(S1::S0::R))).
 { intro N;induction N using lt_wf_ind. intros w L Hlen.
   destruct(bca_decomp w)as(k&t&E&[Et|[Et|[(r&Et)|(r&Et)]]]);subst w t;
     rewrite bca_pre_len in Hlen;rewrite bca_enc_pre;cbn[bca_enc].
   - rewrite app_nil_r;apply bca_quad_terminal.
   - apply bca_quad_two_terminal.
   - destruct k as[|[|k]].
     + destruct(H(length r) ltac:(cbn in Hlen;lia) r(S1::S1::L) ltac:(lia))as(R&HT&HR).
       exists(S1::S1::R);split;[constructor;exact HT|].
       cbn[rep app]. rt bca_short_one;rt HR.
       exact(bca_ones_drain 2 L R).
     + destruct(H(length(true::r)) ltac:(cbn in Hlen|-*;lia) (true::r)
         (S1::S1::S1::S1::L) ltac:(lia))as(R&HT&HR).
       exists(S1::S1::S1::S1::R);split;[constructor;constructor;exact HT|].
       cbn[rep app]. rt bca_short_five;rt HR.
       exact(bca_ones_drain 4 L R).
     + exists(rep[S1]9++rep[S1;S0;S1;S1]k++bca_enc r);split.
       * change(bca_tail(rep[S1](2*5)++rep[S1;S0;S1;S1]k++bca_enc r)).
         apply bca_tail_even_ones,bca_tail_1011,bca_enc_tail.
       * apply bca_long_odd_return.
   - exists(S1::(rep[S1;S1;S1;S0]k++S1::S1::bca_enc r));split.
     + constructor;apply bca_tail_1110;constructor;apply bca_enc_tail.
     + rt bca_odd_run;apply bca_marked_one. }
 intros w L;apply(H(length w));lia.
Qed.
Lemma bca_cR_pad:forall q L R,
 lift(cR q L(R++[S0]))=lift(cR q L R).
Proof.
 intros q L[|h R];[reflexivity|]. unfold cR;cbn[chd ctl app].
 exact(lift_padR 1 q L h R).
Qed.
Theorem bca_paired_tail:forall T,bca_tail T->forall L,exists R,
 bca_tail(S1::R) /\ Reach0 tm(cR StD(S1::L)T)(cL StC L(S1::S0::R)).
Proof.
 intros T HT L;destruct(bca_tail_complete T HT)as(w&[E|E]).
 - rewrite E;apply bca_paired_right.
 - destruct(bca_paired_right w L)as(R&HR&HE);exists R;split;[exact HR|].
   eapply reach0_lift_l;[|exact HE]. rewrite <-E; symmetry;apply bca_cR_pad.
Qed.
Definition bca_returns (c:cconf)(A:list Sym->cconf):Prop:=
 exists T,bca_tail T /\ Reach0 tm c(A T).
Lemma bca_returns_back:forall c d A,Reach0 tm c d->bca_returns d A->bca_returns c A.
Proof. intros c d A E(T&HT&H);exists T;split;[exact HT|eapply reach0_trans;eauto]. Qed.
(** The left stack is read from its near end.  Its two difficult pairs
    01,11 invoke the paired right-word normalization above. *)
Lemma bca_Cwalk:forall L0 A,
 (forall R,bca_tail R->bca_returns(cL StC L0(S1::S0::R))A)->
 (forall R,bca_tail R->bca_returns(cL StC(S0::S1::L0)(S1::S0::R))A)->
 forall w R,bca_tail R->bca_returns(cL StC(bca_left w++L0)(S1::S0::R))A.
Proof.
 intros L0 A Hbase Hodd. fix IH 1. intros[|[]w]R HR.
 - apply Hbase,HR.
 - eapply bca_returns_back;[|apply(IH w(S1::S1::R));constructor;exact HR].
   cbn[bca_left app]. exact(bca_ones_drain 2(bca_left w++L0)R).
 - destruct w as[|[]w].
   + apply Hodd,HR.
   + destruct(bca_paired_tail R HR(S1::S1::S1::S1::S1::(bca_left w++L0)))as(T&HT&HE).
     eapply bca_returns_back;[|apply(IH w(rep[S1]5++T))].
     * cbn[bca_left app]. go 11;rt HE;apply(bca_ones_drain 5).
     * change(bca_tail(S1::(rep[S1](2*2)++T)));apply bca_tail_phase_add;exact HT.
   + eapply bca_returns_back;[|apply(IH w(S1::S1::S1::S0::R));constructor;constructor;exact HR].
     cbn[bca_left app]. exact(bca_pair_drain 1(bca_left w++L0)R).
Qed.
Lemma bca_Bwalk:forall L0 A,
 (forall R,bca_tail R->bca_returns(cL StC L0(S1::S0::R))A)->
 (forall R,bca_tail R->bca_returns(cL StC(S0::S1::L0)(S1::S0::R))A)->
 forall w R,bca_tail R->bca_returns(cL StB L0(S0::S1::R))A->
 bca_returns(cL StB(bca_left w++L0)(S0::S1::R))A.
Proof.
 intros L0 A HC HO[|[]w]R HR HB;[exact HB| |].
 - destruct(bca_paired_tail R HR(S1::S1::S1::(bca_left w++L0)))as(T&HT&HE).
   eapply bca_returns_back;[|apply(bca_Cwalk L0 A HC HO w(rep[S1]3++T))].
   + cbn[bca_left app]. go 3;rt HE;apply(bca_ones_drain 3).
   + change(bca_tail(S1::(rep[S1](2*1)++T)));apply bca_tail_phase_add;exact HT.
 - eapply bca_returns_back;[|apply(bca_Cwalk L0 A HC HO w(S1::S1::R));constructor;exact HR].
   cbn[bca_left app]. go 6;r0.
Qed.
(** Pairs 01 / 11 on the right become respectively 11 / 01 on the left.
    The terminal blank or final 1 then starts the verified stack return. *)
Lemma bca_Dwalk:forall L0 A,
 (forall R,bca_tail R->bca_returns(cL StC L0(S1::S0::R))A)->
 (forall R,bca_tail R->bca_returns(cL StC(S0::S1::L0)(S1::S0::R))A)->
 bca_returns(cL StB L0[S0;S1])A->
 forall T,bca_even_tail T->forall w,
 bca_returns(cR StD(bca_left w++L0)T)A.
Proof.
 intros L0 A HC HO HB T HT;induction HT;intro w.
 - eapply bca_returns_back;[apply bca_blank_return|].
   apply(bca_Cwalk L0 A HC HO w[S1]);constructor.
 - destruct b.
   + change(bca_returns(cR StD(bca_left w++L0)[])A).
     eapply bca_returns_back;[apply bca_blank_return|].
     apply(bca_Cwalk L0 A HC HO w[S1]);constructor.
   + eapply bca_returns_back;[go 3;r0|].
     apply(bca_Bwalk L0 A HC HO w[]);[constructor|exact HB].
 - destruct b.
   + eapply bca_returns_back;[go 2;r0|]. apply(IHHT(true::w)).
   + eapply bca_returns_back;[go 2;r0|]. apply(IHHT(false::w)).
Qed.
Definition bca_anchor_left(T:list Sym):cconf:=(StA,([],S0,S1::S1::S0::T)).
Definition bca_anchor_right(T:list Sym):cconf:=(StA,([],S0,S1::S1::S0::S1::T)).
Lemma bca_left_Cbase:forall R,bca_tail R->
 bca_returns(cL StC[S1;S1](S1::S0::R))bca_anchor_left.
Proof.
 intros;exists(S1::S1::R);split;[constructor;assumption|].
 unfold bca_anchor_left;go 11;r0.
Qed.
Lemma bca_left_Codd:forall R,bca_tail R->
 bca_returns(cL StC[S0;S1;S1;S1](S1::S0::R))bca_anchor_left.
Proof.
 intros R HR;destruct(bca_paired_tail R HR[S1;S1;S1;S1;S1])as(T&HT&HE).
 exists(S1::S1::S1::S1::S1::T);split;[constructor;constructor;exact HT|].
 go 11;rt HE.
 eapply reach0_trans;[exact(bca_ones_drain 5[]T)|].
 unfold bca_anchor_left;go 1;r0.
Qed.
Lemma bca_left_Bbase:bca_returns(cL StB[S1;S1][S0;S1])bca_anchor_left.
Proof.
 destruct(bca_paired_tail [] bca_tail_nil[S1;S1;S1])as(T&HT&HE).
 exists(S1::S1::S1::T);split;[constructor;exact HT|].
 go 3;rt HE.
 eapply reach0_trans;[exact(bca_ones_drain 3[]T)|].
 unfold bca_anchor_left;go 1;r0.
Qed.
Lemma bca_right_Cbase:forall R,bca_tail R->
 bca_returns(cL StC[S1;S0](S1::S0::R))bca_anchor_right.
Proof. intros;exists R;split;[assumption|unfold bca_anchor_right;go 6;r0]. Qed.
Lemma bca_right_Codd:forall R,bca_tail R->
 bca_returns(cL StC[S0;S1;S1;S0](S1::S0::R))bca_anchor_right.
Proof.
 intros R HR;destruct(bca_paired_tail R HR[S1;S1;S1;S1;S0])as(T&HT&HE).
 exists(S1::S1::S1::T);split;[constructor;exact HT|].
 go 11;rt HE.
 eapply reach0_trans;[exact(bca_ones_drain 4[S0]T)|].
 unfold bca_anchor_right;go 1;r0.
Qed.
Lemma bca_right_Bbase:bca_returns(cL StB[S1;S0][S0;S1])bca_anchor_right.
Proof.
 destruct(bca_paired_tail [] bca_tail_nil[S1;S1;S0])as(T&HT&HE).
 exists(S1::T);split;[exact HT|].
 go 3;rt HE.
 eapply reach0_trans;[exact(bca_ones_drain 2[S0]T)|].
 unfold bca_anchor_right;go 1;r0.
Qed.
Theorem bca_zero_return(HA0:tm StA S0=Some(mkTrans S0 DR StB)):
 forall R,bca_tail R->exists T,bca_tail T /\
 Reach1 tm(bca_anchor_right R)(bca_anchor_right T).
Proof.
 intros R HR.
 destruct(bca_Dwalk[S1;S0]bca_anchor_right bca_right_Cbase bca_right_Codd bca_right_Bbase
   (S1::R)(bca_shift R HR S1)[true])as(T&HT&HE).
 exists T;split;[exact HT|]. unfold bca_anchor_right at 1.
 eapply(r1_run _ 8);[lia| |exact HE].
 cbn[csteps cstep];rewrite HA0;run.
Qed.
Theorem bca_oneleft_return(HA0:tm StA S0=Some(mkTrans S1 DL StD)):
 forall R,bca_tail R->exists T,bca_tail T /\
 Reach1 tm(bca_anchor_left R)(bca_anchor_left T).
Proof.
 intros R HR.
 assert(HT:bca_even_tail(S1::S1::S0::R))by(constructor;apply bca_shift;exact HR).
 destruct(bca_Dwalk[S1;S1]bca_anchor_left bca_left_Cbase bca_left_Codd bca_left_Bbase
   _ HT[])as(T&HU&HE).
 exists T;split;[exact HU|]. unfold bca_anchor_left at 1.
 eapply(r1_run _ 3);[lia| |exact HE].
 cbn[csteps cstep];rewrite HA0;run.
Qed.
End Core.
