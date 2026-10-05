(** * Counters.BlockCoreKVariantTr: nested finite token descents

    The left word consists of B=10111 and Z=011. A left sweep converts
    these to right-facing codes. Scanning Z merely transfers it; scanning
    B invokes a carry on strictly fewer B tokens. Three boundary markers
    discharge the remaining passes in order. Strong induction on the B
    count and ordinary induction on each finite code word prove a
    positive B0 return. The next anchor supplies a C1 witness even when
    the initial word is empty; every anchor reaches all eight instructions. *)
From Coq Require Import Arith Lia List Bool.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Definition kv_block(b:bool):list Sym:=if b then[S1;S0;S1;S1;S1]else[S0;S1;S1].
Definition kv_cblock(b:bool):list Sym:=if b then[S1;S1;S0;S1;S1]else[S1;S0;S1].
Fixpoint kv_enc(w:list bool):list Sym:=match w with[]=>[]|b::w=>kv_block b++kv_enc w end.
Fixpoint kv_code(w:list bool):list Sym:=match w with[]=>[]|b::w=>kv_cblock b++kv_code w end.
Fixpoint kv_count(w:list bool):nat:=match w with[]=>0|b::w=>(if b then 1 else 0)+kv_count w end.
Definition kv_M1:list Sym:=[S1;S0;S1;S0;S0;S1;S1].
Definition kv_M2:list Sym:=[S1;S1;S1;S0;S1;S0].
Definition kv_M3:list Sym:=[S0;S1;S0;S1;S0].
Lemma kv_code_app:forall u v,kv_code(u++v)=kv_code u++kv_code v.
Proof. induction u;intro v;cbn[kv_code app];[reflexivity|rewrite IHu,app_assoc;reflexivity]. Qed.
Lemma kv_count_app:forall u v,kv_count(u++v)=kv_count u+kv_count v.
Proof. induction u;intro v;cbn[kv_count app];[reflexivity|rewrite IHu;lia]. Qed.
Lemma kv_count_rev:forall w,kv_count(rev w)=kv_count w.
Proof. induction w;cbn[rev kv_count];[reflexivity|rewrite kv_count_app;cbn[kv_count];rewrite IHw;lia]. Qed.
Definition kv_anchor(w:list bool):cconf:=(StB,(kv_enc w,S0,[])).
Section Core.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S1 DR StB))
 (HA1:tm StA S1=Some(mkTrans S0 DL StC))
 (HB0:tm StB S0=Some(mkTrans S1 DR StC))
 (HB1:tm StB S1=Some(mkTrans S1 DR StD))
 (HC0:tm StC S0=Some(mkTrans S1 DL StA))
 (HC1:tm StC S1=Some(mkTrans S1 DL StC))
 (HD0:tm StD S0=Some(mkTrans S1 DR StD))
 (HD1:tm StD S1=Some(mkTrans S0 DR StA)).
Local Ltac run:=
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR kv_enc kv_code kv_block kv_cblock kv_M1 kv_M2 kv_M3 kv_anchor];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR kv_enc kv_code kv_block kv_cblock kv_M1 kv_M2 kv_M3 kv_anchor]);reflexivity.
Local Ltac go n:=first[eapply(r1_run _ n);[lia|run|]|eapply(r0_run _ n);[run|]].
Lemma kv_C_scan:forall w R,
 Reach0 tm(cL StC(kv_enc w)R)(cR StD[S1;S1](kv_code(rev w)++R)).
Proof.
 induction w as[|b w IH];intro R.
 - cbn[kv_enc kv_code rev app];go 3;r0.
 - cbn[kv_enc rev];rewrite kv_code_app;cbn[kv_code];rewrite app_nil_r,<-app_assoc.
   destruct b;cbn[kv_block kv_cblock app].
   + go 5;apply IH.
   + go 3;apply IH.
Qed.
Lemma kv_D_B:forall u R,
 Reach0 tm(cR StD(S1::S1::kv_enc u)(kv_cblock true++R))
 (cL StC(kv_enc u)(kv_M1++R)).
Proof. intros;go 5;r0. Qed.
Lemma kv_D_M1:forall u R,
 Reach0 tm(cR StD(S1::S1::kv_enc u)(kv_M1++R))
 (cL StC(kv_enc u)(kv_cblock false++kv_M2++R)).
Proof. intros;go 15;r0. Qed.
Lemma kv_D_M2:forall u R,
 Reach0 tm(cR StD(S1::S1::kv_enc u)(kv_M2++R))
 (cL StC(kv_enc u)(kv_cblock false++kv_M3++R)).
Proof. intros;go 5;r0. Qed.
Lemma kv_D_M3:forall u R,
 Reach0 tm(cR StD(S1::S1::kv_enc u)(kv_M3++R))
 (cR StD(S1::S1::kv_enc(true::u))R).
Proof. intros;go 5;r0. Qed.
Definition kv_result(n:nat)(c:cconf)(R:list Sym):Prop:=
 exists w,kv_count w=S n/\Reach0 tm c(cR StD(S1::S1::kv_enc w)R).
Lemma kv_back:forall n c d R,Reach0 tm c d->kv_result n d R->kv_result n c R.
Proof. intros n c d R H(w&HN&HR);exists w;split;[exact HN|eapply reach0_trans;eauto]. Qed.
(** Every B code calls a carry on strictly fewer B tokens. Z codes merely
    move to the left, so induction on the finite right word suffices. *)
Lemma kv_D_scan:forall n,
 (forall u,kv_count u<n->forall R,kv_result(kv_count u)(cL StC(kv_enc u)(kv_M1++R))R)->
 forall v u R,kv_count u+kv_count v=n->
 exists w,kv_count w=n/\
 Reach0 tm(cR StD(S1::S1::kv_enc u)(kv_code v++R))
          (cR StD(S1::S1::kv_enc w)R).
Proof.
 intros n HS v;induction v as[|b v IH];intros u R HN.
 - exists u;split;[cbn[kv_count]in HN;lia|r0].
 - destruct b.
   + assert(Hlt:kv_count u<n)by(cbn[kv_count]in HN;lia).
     destruct(HS u Hlt(kv_code v++R))as(w&HW&HR).
     destruct(IH w R ltac:(cbn[kv_count]in HN;lia))as(z&HZ&HE).
     exists z;split;[exact HZ|]. cbn[kv_code];rewrite<-app_assoc.
     rt kv_D_B;rt HR;exact HE.
   + destruct(IH(false::u)R ltac:(cbn[kv_count]in*;lia))as(z&HZ&HE).
     exists z;split;[exact HZ|]. cbn[kv_code kv_cblock app];go 3;exact HE.
Qed.
Lemma kv_C_to_scan:forall u v R,
 Reach0 tm(cL StC(kv_enc u)(kv_code v++R))
 (cR StD[S1;S1](kv_code(rev u++v)++R)).
Proof. intros;rewrite kv_code_app,<-app_assoc;apply kv_C_scan. Qed.
Theorem kv_carry:forall n u,kv_count u=n->forall R,
 kv_result n(cL StC(kv_enc u)(kv_M1++R))R.
Proof.
 intro n;induction n using lt_wf_ind.
 assert(HS:forall u,kv_count u<n->forall R,
   kv_result(kv_count u)(cL StC(kv_enc u)(kv_M1++R))R).
 { intros u Hlt R;apply(H _ Hlt u eq_refl). }
 assert(H3:forall u v R,kv_count u+kv_count v=n->
   kv_result n(cL StC(kv_enc u)(kv_code v++kv_M3++R))R).
 {
  intros u v R HN.
  destruct(kv_D_scan n HS(rev u++v)[](kv_M3++R)
    ltac:(cbn[kv_count];rewrite kv_count_app,kv_count_rev;exact HN))as(w&HW&HR).
  exists(true::w);split;[cbn[kv_count];lia|].
  rt kv_C_to_scan;rt HR;apply kv_D_M3.
 }
 assert(H2:forall u v R,kv_count u+kv_count v=n->
   kv_result n(cL StC(kv_enc u)(kv_code v++kv_M2++R))R).
 {
  intros u v R HN.
  destruct(kv_D_scan n HS(rev u++v)[](kv_M2++R)
    ltac:(cbn[kv_count];rewrite kv_count_app,kv_count_rev;exact HN))as(w&HW&HR).
  eapply kv_back;[apply kv_C_to_scan|]. eapply kv_back;[exact HR|].
  eapply kv_back;[apply kv_D_M2|].
  change(kv_result n(cL StC(kv_enc w)(kv_code[false]++kv_M3++R))R).
  apply H3;cbn[kv_count];lia.
 }
 intros u HU R.
 destruct(kv_D_scan n HS(rev u)[](kv_M1++R)
    ltac:(cbn[kv_count];rewrite kv_count_rev;exact HU))as(w&HW&HR).
 eapply kv_back;[apply kv_C_scan|]. eapply kv_back;[exact HR|].
 eapply kv_back;[apply kv_D_M1|].
 change(kv_result n(cL StC(kv_enc w)(kv_code[false]++kv_M2++R))R).
 apply H2;cbn[kv_count];lia.
Qed.
Lemma kv_D_all:forall v u R,exists w,
 Reach0 tm(cR StD(S1::S1::kv_enc u)(kv_code v++R))
          (cR StD(S1::S1::kv_enc w)R).
Proof.
 intros v u R;destruct(kv_D_scan(kv_count u+kv_count v)
   ltac:(intros z _;apply kv_carry;reflexivity)v u R eq_refl)as(w&HW&HR).
 exists w;exact HR.
Qed.
Lemma kv_anchor_boundary:forall w,exists u,
 Reach0 tm(kv_anchor w)(cR StD(S1::S1::kv_enc u)[S0;S1]).
Proof.
 intro w;destruct(kv_D_all(rev w)[][S0;S1])as(u&HU).
 exists u;go 3;rt kv_C_scan;exact HU.
Qed.
Theorem kv_return:forall w,exists u,Reach1 tm(kv_anchor w)(kv_anchor(true::u)).
Proof.
 intro w;destruct(kv_D_all(rev w)[][S0;S1])as(u&HU).
 exists u;go 3;rt kv_C_scan;rt HU;go 3;r0.
Qed.
Lemma kv_C_B1:forall w R,Fires tm(cL StC(kv_enc w)R)(StB,S1).
Proof.
 induction w as[|b w IH];intro R.
 - exists 2;eexists;split;[run|reflexivity].
 - destruct b;cbn[kv_enc kv_block app].
   + eapply fire_back;[go 5;r0|apply IH].
   + eapply fire_back;[go 3;r0|apply IH].
Qed.
Theorem kv_anchor_fires:forall w q,Fires tm(kv_anchor w)q.
Proof.
 intros w[q h];destruct q,h.
 - destruct(kv_anchor_boundary w)as(u&HU);eapply fire_back;[exact HU|].
   exists 2;eexists;split;[run|reflexivity].
 - exists 2;eexists;split;[run|reflexivity].
 - apply fires_here;reflexivity.
 - eapply fire_back;[go 3;r0|apply kv_C_B1].
 - exists 1;eexists;split;[run|reflexivity].
 - destruct(kv_return w)as(u&HU);eapply fire_back;[apply reach1_0;exact HU|].
   exists 3;eexists;split;[run|reflexivity].
 - destruct(kv_anchor_boundary w)as(u&HU);eapply fire_back;[exact HU|].
   apply fires_here;reflexivity.
 - destruct(kv_anchor_boundary w)as(u&HU);eapply fire_back;[exact HU|].
   exists 1;eexists;split;[run|reflexivity].
Qed.
End Core.
