(** Exact S070 scanner, with arbitrary untouched right context. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census.
Import ListNotations.
Definition st_tm:TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DR StA
 |StA,S2=>mkTrans S1 DR StA |StA,S3=>mkTrans S0 DR StA
 |StB,S0=>mkTrans S2 DR StB |StB,S1=>mkTrans S1 DL StA
 |StB,S2=>mkTrans S3 DL StB |StB,S3=>mkTrans S2 DL StB end).
Definition st_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition st_back q l r:cconf := (q,(ctl l,chd l,r)).
Definition st_main w r:cconf := (StA,(w,S0,r)).
Definition st_write(h:Sym):Sym := match h with S1=>S2|S2=>S1|_=>S0 end.
Definition st_rev(w:list Sym):list Sym := rev(map st_write w).
Definition st_nz(w:list Sym):Prop := Forall(fun h=>h<>S0)w.
Definition st_steps(c d:cconf):Prop := exists n,csteps st_tm n c=Some d.
Lemma st_refl : forall c,st_steps c c.
Proof. intro c;exists 0;reflexivity. Qed.
Lemma st_trans : forall c d e,st_steps c d ->st_steps d e ->st_steps c e.
Proof. intros c d e[n H][m E];exists(n+m);rewrite csteps_add,H;exact E. Qed.
Lemma st_one : forall c d,cstep st_tm c=Some d ->st_steps c d.
Proof. intros c d E;exists 1;cbn[csteps];rewrite E;reflexivity. Qed.
Lemma st_rev_cons : forall h w,st_rev(h::w)=st_rev w++[st_write h].
Proof. reflexivity. Qed.
Lemma st_A_right : forall w l r,st_nz w ->
 csteps st_tm(length w)(st_front StA l(w++r))=Some(st_front StA(st_rev w++l)r).
Proof.
 induction w as[|h w IH];intros l r H;[reflexivity|].
 inversion H as[|h' w' Hh Hw];subst.
 assert(E:cstep st_tm(st_front StA l((h::w)++r))=
 Some(st_front StA(st_write h::l)(w++r))).
 {destruct h;[contradiction|reflexivity|reflexivity|reflexivity]. }
 cbn[length csteps];rewrite E,IH by exact Hw.
 rewrite st_rev_cons,<-app_assoc;reflexivity.
Qed.
Inductive st_mode := st_B3 |st_A |st_B1 |st_Copy.
Definition st_emit(p:list Sym)(o:option(list Sym)):option(list Sym) :=
 match o with Some w=>Some(p++w)|None=>None end.
Fixpoint st_scan(m:st_mode)(w:list Sym):option(list Sym) :=
 match m with st_Copy=>Some w|_=>
 match w with
 |[]=>match m with st_B3=>None|st_A=>Some[S2;S1]|st_B1=>Some[S1]|st_Copy=>Some[]end
 |h::u=>match m,h with
  |st_B3,S0=>st_emit[S1](st_scan st_B3 u)
  |st_B3,S1=>st_emit[S0;S2](st_scan st_A u)
  |st_B3,S2=>st_emit[S0](st_scan st_B3 u)
  |st_A,S0=>st_emit[S2](st_scan st_B1 u)
  |st_A,S1=>Some(S2::u)|st_A,S2=>Some(S1::u)
  |st_B1,S0=>Some(S1::u)
  |st_B1,S1=>st_emit[S2](st_scan st_A u)
  |st_B1,S2=>st_scan st_B3 u
  |_,_=>None end
 end end.
Definition st_G w := st_emit[S0](st_scan st_B3 w).
Definition st_T w := st_emit[S2](st_scan st_B1 w).
Definition st_cfg m w R r :=
 match m with
 |st_B3=>st_back StB w(S3::R++r)
 |st_A=>st_back StA w(S1::R++r)
 |st_B1=>st_back StB w(S1::R++r)
 |st_Copy=>st_front StA(st_rev R++w)r end.
Definition st_acc m R :=
 match m with st_B3=>st_rev R|st_A|st_B1=>st_rev R++[S2]|st_Copy=>st_rev R end.
Lemma st_emit_some : forall p x y,st_emit p x=Some y ->exists z,x=Some z /\ y=p++z.
Proof. intros p[x|]y H;[injection H as <-;eauto|discriminate]. Qed.
Lemma st_finish_A : forall h w R r,h<>S0 ->st_nz R ->
 st_steps(st_back StA(h::w)(S1::R++r))
 (st_front StA((st_rev R++[S2])++st_write h::w)r).
Proof.
 intros h w R r Hh HR.
 assert(E:st_nz(h::S1::R))by(constructor;[exact Hh|constructor;[discriminate|exact HR]]).
 pose proof(st_A_right(h::S1::R)w r E)as H.
 unfold st_rev in H;cbn[map rev st_write]in H.
 rewrite <-!app_assoc in H;exists(length(h::S1::R));unfold st_rev;rewrite <-app_assoc;exact H.
Qed.
Lemma st_finish_B1 : forall w R r,st_nz R ->
 st_steps(st_back StB(S0::w)(S1::R++r))
 (st_front StA((st_rev R++[S2])++S1::w)r).
Proof.
 intros w R r HR.
 eapply st_trans with(d:=st_back StA(S2::w)(S1::R++r)).
 - exists 2;reflexivity.
 - exact(st_finish_A S2 w R r ltac:(discriminate)HR).
Qed.
Lemma st_empty_B1 : forall R r,st_nz R ->
 st_steps(st_back StB[](S1::R++r))
 (st_front StA((st_rev R++[S2])++[S1])r).
Proof.
 intros R r HR.
 eapply st_trans with(d:=st_back StA[S2](S1::R++r)).
 - exists 2;reflexivity.
 - exact(st_finish_A S2[]R r ltac:(discriminate)HR).
Qed.
Ltac st_clean E := cbn[st_acc]in E;
 repeat rewrite st_rev_cons in E;cbn[st_write]in E;
 repeat rewrite <-app_assoc in E;cbn[app]in E.
Theorem st_scan_sound : forall w m out R r,st_nz R ->st_scan m w=Some out ->
 st_steps(st_cfg m w R r)(st_front StA(st_acc m R++out)r).
Proof.
 induction w as[|h w IH];intros m out R r HR H;destruct m.
 - discriminate.
 - injection H as <-;cbn[st_cfg st_acc].
   pose proof(st_empty_B1(S1::R)r ltac:(constructor;[discriminate|exact HR]))as E;st_clean E.
   eapply st_trans;[exists 1;reflexivity|].
   rewrite <-app_assoc;cbn[app];exact E.
 - injection H as <-;exact(st_empty_B1 R r HR).
 - injection H as <-;apply st_refl.
 - destruct h;cbn[st_scan]in H.
   + destruct(st_emit_some _ _ _ H)as(z&Hz&->).
     pose proof(IH st_B3 z(S2::R)r ltac:(constructor;[discriminate|exact HR])Hz)as E;st_clean E.
     cbn[st_cfg st_acc];eapply st_trans;[exists 3;reflexivity|exact E].
   + destruct(st_emit_some _ _ _ H)as(z&Hz&->).
     pose proof(IH st_A z(S3::R)r ltac:(constructor;[discriminate|exact HR])Hz)as E;st_clean E.
     cbn[st_cfg st_acc];eapply st_trans;[exists 1;reflexivity|exact E].
   + destruct(st_emit_some _ _ _ H)as(z&Hz&->).
     pose proof(IH st_B3 z(S3::R)r ltac:(constructor;[discriminate|exact HR])Hz)as E;st_clean E.
     cbn[st_cfg st_acc];eapply st_trans;[exists 1;reflexivity|exact E].
   + discriminate.
 - destruct h;cbn[st_scan]in H.
   + destruct(st_emit_some _ _ _ H)as(z&Hz&->).
     pose proof(IH st_B1 z(S1::R)r ltac:(constructor;[discriminate|exact HR])Hz)as E;st_clean E.
     cbn[st_cfg st_acc];rewrite <-app_assoc;cbn[app].
     eapply st_trans;[exists 1;reflexivity|exact E].
   + injection H as <-;exact(st_finish_A S1 w R r ltac:(discriminate)HR).
   + injection H as <-;exact(st_finish_A S2 w R r ltac:(discriminate)HR).
   + discriminate.
 - destruct h;cbn[st_scan]in H.
   + injection H as <-;exact(st_finish_B1 w R r HR).
   + destruct(st_emit_some _ _ _ H)as(z&Hz&->).
     pose proof(IH st_A z(S1::R)r ltac:(constructor;[discriminate|exact HR])Hz)as E;st_clean E.
     cbn[st_cfg st_acc];rewrite <-app_assoc;cbn[app].
     eapply st_trans;[exists 1;reflexivity|exact E].
   + pose proof(IH st_B3 out(S1::R)r ltac:(constructor;[discriminate|exact HR])H)as E;st_clean E.
     cbn[st_cfg st_acc];rewrite <-app_assoc;cbn[app].
     eapply st_trans;[exists 1;reflexivity|exact E].
   + discriminate.
 - injection H as <-;apply st_refl.
Qed.
Theorem st_T_sound : forall w out r,st_T w=Some out ->
 exists t,0<t /\ csteps st_tm t(st_main w r)=Some(st_front StA out r).
Proof.
 intros w out r H;destruct(st_emit_some _ _ _ H)as(z&Hz&->).
 destruct(st_scan_sound w st_B1 z[]r ltac:(constructor)Hz)as(t&E).
 exists(1+t);split;[lia|rewrite csteps_add;exact E].
Qed.
Definition st_odd:list Sym := [S2;S1;S0;S0;S0;S2;S2].
Definition st_even:list Sym := [S2;S0;S2;S2;S1;S0;S2;S2].
Lemma st_odd_even : forall w,st_T(st_odd++w)=Some(st_even++w).
Proof. reflexivity. Qed.
Lemma st_even_odd : forall w out,st_G w=Some out ->
 st_T(st_even++w)=Some(st_odd++out).
Proof.
 intros w out H;destruct(st_emit_some _ _ _ H)as(z&Hz&->).
 unfold st_T;cbn[st_even app st_scan];rewrite Hz;reflexivity.
Qed.
Theorem st_G_sound : forall w out,st_G w=Some out ->
 exists t,0<t /\ csteps st_tm t(st_main(st_odd++w)[])=Some(st_main(st_odd++out)[]).
Proof.
 intros w out H.
 destruct(st_T_sound _ _ [](st_odd_even w))as(n&Hn&En).
 destruct(st_T_sound _ _ [](st_even_odd w out H))as(m&Hm&Em).
 exists(n+m);split;[lia|rewrite csteps_add,En;exact Em].
Qed.
Lemma st_entry : csteps st_tm 35 c0=Some(st_main(st_odd++[S1])[]).
Proof. reflexivity. Qed.
Print Assumptions st_scan_sound.
Print Assumptions st_G_sound.
