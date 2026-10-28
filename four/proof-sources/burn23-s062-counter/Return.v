(** A finite protected cut system. Dead boundary cuts also allow the
    permanent five-step left march, so rightmost returns are not assumed. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census.
From BBB24Burn23S062Counter Require Import S062Core.
Import ListNotations.
Definition s62_go cc := exists n cc',0<n /\s62_safe cc' /\
 csteps s62_tm n cc=Some cc'.
Lemma s62_go_cut : forall n cc cc',0<n->s62_safe cc'->
 csteps s62_tm n cc=Some cc'->s62_go cc.
Proof. intros;exists n,cc';auto. Qed.
Lemma s62_go_prefix : forall n cc cc',csteps s62_tm n cc=Some cc'->
 s62_go cc'->s62_go cc.
Proof.
 intros n cc cc' E(k&c&HK&HS&E');exists(n+k),c;repeat split;try lia;auto.
 rewrite csteps_add,E;exact E'.
Qed.
Lemma s62_dead_tail : forall l,Forall s62_03 l->Forall s62_03(ctl l).
Proof. intros[|h l]H;[constructor|inversion H;assumption]. Qed.
Lemma s62_dead_head : forall l,Forall s62_03 l->s62_03(chd l).
Proof. intros[|h l]H;[left;reflexivity|inversion H;assumption]. Qed.
Lemma s62_safe_main : forall a u v,Forall s62_13 u->Forall s62_03 v->
 s62_safe(s62_main a u v).
Proof. intros;left;exists a,u,v;auto. Qed.
Lemma s62_safe_dead : forall l r,Forall s62_03 l->s62_guarded r->
 s62_safe(s62_dead l r).
Proof. intros;right;exists l,r;auto. Qed.
Lemma s62_guarded_three : forall r,s62_guarded r->s62_guarded(S3::r).
Proof.
 intros r[(n&->)|(w&a&->&Hw)].
 - left;exists(S n);reflexivity.
 - right;exists(S3::w),a;split;[reflexivity|constructor;[right;reflexivity|exact Hw]].
Qed.
Lemma s62_B_three_cross : forall l r,Forall s62_03 l->
 exists n l',Forall s62_03 l' /\
 csteps s62_tm n(s62_front StB l(S3::r))=Some(s62_front StB l' r).
Proof.
 induction l as[|x l IH];intros r H.
 - exists 3,[S0;S3];split;[constructor;[left;reflexivity|constructor;[right;reflexivity|constructor]]|reflexivity].
 - inversion H as[|? ? Hx Hl];subst;destruct Hx as[Hx|Hx];subst x.
   + exists 3,(S0::S3::l);split;[constructor;[left;reflexivity|constructor;[right;reflexivity|exact Hl]]|reflexivity].
   + destruct(IH(S2::r)Hl)as(n&l'&Hl'&E).
     exists(1+(n+1)),(S0::l');split;[constructor;[left;reflexivity|exact Hl']|].
     rewrite csteps_add.
     change(csteps s62_tm(n+1)(s62_front StB l(S3::S2::r))=Some(s62_front StB(S0::l')r)).
     rewrite csteps_add,E;reflexivity.
Qed.
Lemma s62_B_dead_cell : forall l h r,Forall s62_03 l->h=S0 \/h=S2 \/h=S3->
 exists n l',Forall s62_03 l' /\
 csteps s62_tm n(s62_front StB l(h::r))=Some(s62_front StB l' r).
Proof.
 intros l h r Hl[Hh|[Hh|Hh]];subst h.
 - exists 1,(S3::l);split;[constructor;[right;reflexivity|exact Hl]|reflexivity].
 - exists 1,(S0::l);split;[constructor;[left;reflexivity|exact Hl]|reflexivity].
 - apply s62_B_three_cross;exact Hl.
Qed.
Lemma s62_B_dead_finish : forall w l r,Forall s62_23 w->Forall s62_03 l->
 exists n l',0<n /\Forall s62_03 l' /\
 csteps s62_tm n(s62_front StB l(w++S1::r))=Some(s62_back StA l'(S3::r)).
Proof.
 induction w as[|x w IH];intros l r Hw Hl.
 - exists 1,l;repeat split;try lia;auto;reflexivity.
 - inversion Hw as[|? ? Hx Htail];subst.
   destruct(s62_B_dead_cell l x(w++S1::r)Hl)as(n&l'&Hl'&E).
   {destruct Hx as[Hx|Hx];subst x;auto. }
   destruct(IH l' r Htail Hl')as(k&l''&Hk&Hl''&E').
   exists(n+k),l'';repeat split;try lia;auto;rewrite csteps_add;cbn[app];rewrite E;exact E'.
Qed.
Lemma s62_B_dead_back : forall l w r,Forall s62_03 l->Forall s62_23 w->
 exists n l',0<n /\Forall s62_03 l' /\
 csteps s62_tm n(s62_back StB l(w++S1::r))=Some(s62_back StA l'(S3::r)).
Proof.
 intros l w r Hl Hw;pose proof(s62_dead_head l Hl)as Hh.
 destruct(s62_B_dead_cell(ctl l)(chd l)(w++S1::r)(s62_dead_tail l Hl))as(n&l'&Hl'&E).
 {destruct Hh as[Hh|Hh];subst;auto. }
 destruct(s62_B_dead_finish w l' r Hw Hl')as(k&l''&Hk&Hl''&E').
 exists(n+k),l'';repeat split;try lia;auto.
 rewrite csteps_add;change(s62_front StB(ctl l)(chd l::w++S1::r))with(s62_back StB l(w++S1::r))in E.
 rewrite E;exact E'.
Qed.

Definition s62_land cc := s62_safe cc \/s62_go cc.
Lemma s62_go_land : forall n cc cc',0<n->csteps s62_tm n cc=Some cc'->
 s62_land cc'->s62_go cc.
Proof.
 intros n cc cc' Hn E[H|H].
 - eapply s62_go_cut;eauto.
 - eapply s62_go_prefix;eauto.
Qed.
Lemma s62_dead_landing : forall l r,Forall s62_03 l->s62_guarded r->
 s62_land(s62_back StA l(S3::r)).
Proof.
 intros[|x l]r Hl Hr.
 - left;apply s62_safe_dead;[constructor|apply s62_guarded_three;exact Hr].
 - inversion Hl as[|? ? Hx Htail];subst;destruct Hx as[Hx|Hx];subst x.
   + left;apply s62_safe_dead;[exact Htail|apply s62_guarded_three;exact Hr].
   + right;destruct Hr as[(n&->)|(w&a&->&Hw)].
     * eapply(s62_go_cut(2+n)_ (s62_main 0(repeat S1 n)l));[lia| |apply s62_A_plain_launch].
       apply s62_safe_main;[apply s62_forall_repeat;left;reflexivity|exact Htail].
     * eapply(s62_go_cut(length w+3*a+9)_ (s62_main(a+1)(s62_decode w++[S1;S1])l));[lia| |exact(s62_A_guard_launch a w [] l Hw)].
       apply s62_safe_main;[|exact Htail].
       apply Forall_app;split;[apply s62_decode_13;exact Hw|].
       constructor;[left;reflexivity|constructor;[left;reflexivity|constructor]].
Qed.
Lemma s62_dead_next : forall l r,Forall s62_03 l->s62_guarded r->s62_go(s62_dead l r).
Proof.
 intros l r Hl Hr;destruct(s62_B_dead_back l [] r Hl(Forall_nil _))as(n&l'&Hn&Hl'&E).
 eapply(s62_go_land(1+n)_ (s62_back StA l'(S3::r)));[lia| |].
 - rewrite csteps_add;exact E.
 - apply s62_dead_landing;assumption.
Qed.
Lemma s62_B_dead_go : forall l w a,Forall s62_03 l->Forall s62_23 w->
 s62_go(s62_back StB l(s62_guard w a)).
Proof.
 intros l w a Hl Hw.
 destruct(s62_B_dead_back l(w++[S2;S3]++repeat S2 a)[] Hl(s62_guard_prefix w a Hw))
 as(n&l'&Hn&Hl'&E).
 eapply(s62_go_land n _ (s62_back StA l'[S3]));[exact Hn| |].
 - replace(s62_guard w a)with((w++[S2;S3]++repeat S2 a)++[S1])
   by(unfold s62_guard;rewrite !app_assoc;reflexivity);exact E.
 - apply(s62_dead_landing l' [] Hl');left;exists 0;reflexivity.
Qed.
Lemma s62_double_go : forall a w u v,Forall s62_23 w->Forall s62_13 u->Forall s62_03 v->
 s62_go(s62_back StB(S1::S3::(u++v))(s62_guard w a)).
Proof.
 intros a w u v Hw Hu Hv;eapply(s62_go_cut(length w+3*a+10)_ (s62_main(a+1)(s62_decode w++S1::S1::u)v));[lia| |exact(s62_double_launch a w u v Hw)].
 apply s62_safe_main;[|exact Hv];apply Forall_app;split;[apply s62_decode_13;exact Hw|].
 constructor;[left;reflexivity|constructor;[left;reflexivity|exact Hu]].
Qed.
Lemma s62_single_blank : forall l w a,Forall s62_03 l->Forall s62_23 w->
 s62_go(s62_back StB(S1::S0::l)(s62_guard w a)).
Proof.
 intros;eapply(s62_go_cut 1 _ (s62_dead l(S3::s62_guard w a)));[lia| |reflexivity].
 apply s62_safe_dead;[assumption|apply s62_guarded_three;right;exists w,a;auto].
Qed.
Lemma s62_single_end : forall w a,Forall s62_23 w->s62_go(s62_back StB[S1](s62_guard w a)).
Proof.
 intros;eapply(s62_go_cut 1 _ (s62_dead[](S3::s62_guard w a)));[lia| |reflexivity].
 apply s62_safe_dead;[constructor|apply s62_guarded_three;right;exists w,a;auto].
Qed.
Lemma s62_parse_bound : forall n u v w a,length u<=n->Forall s62_13 u->
 Forall s62_03 v->Forall s62_23 w->s62_go(s62_back StB(u++v)(s62_guard w a)).
Proof.
 induction n as[|n IH];intros u v w a Hlen Hu Hv Hw;destruct u as[|x u].
 - apply s62_B_dead_go;assumption.
 - cbn[length]in Hlen;lia.
 - apply s62_B_dead_go;assumption.
 - inversion Hu as[|? ? Hx Htail];subst;destruct Hx as[Hx|Hx];subst x.
   + destruct u as[|x u].
     * destruct v as[|x v].
       -- apply s62_single_end;exact Hw.
       -- inversion Hv as[|? ? Hx Hv'];subst;destruct Hx as[Hx|Hx];subst x.
          ++ apply s62_single_blank;assumption.
          ++ apply(s62_double_go a w [] v);[exact Hw|constructor|exact Hv'].
     * inversion Htail as[|? ? Hx Hu'];subst;destruct Hx as[Hx|Hx];subst x.
       -- eapply(s62_go_prefix 2 _ (s62_back StB(u++v)(s62_guard(S2::S3::w)a))).
          ++ apply s62_pair.
          ++ apply IH;[cbn[length]in Hlen;lia|exact Hu'|exact Hv|].
             constructor;[left;reflexivity|constructor;[right;reflexivity|exact Hw]].
       -- apply s62_double_go;assumption.
   + eapply(s62_go_prefix 1 _ (s62_back StB(u++v)(s62_guard(S2::w)a))).
     * reflexivity.
     * apply IH;[cbn[length]in Hlen;lia|exact Htail|exact Hv|].
       constructor;[left;reflexivity|exact Hw].
Qed.
Lemma s62_main_next : forall a u v,Forall s62_13 u->Forall s62_03 v->s62_go(s62_main a u v).
Proof.
 intros a u v Hu Hv;eapply s62_go_prefix;[apply s62_main_start|].
 apply(s62_parse_bound(length u));auto;constructor.
Qed.
Theorem s62_safe_next : forall cc,s62_safe cc->s62_go cc.
Proof.
 intros cc[(a&u&v&Hu&Hv&->)|(l&r&Hl&Hr&->)].
 - apply s62_main_next;assumption.
 - apply s62_dead_next;assumption.
Qed.
Lemma s62_entry : csteps s62_tm 5 c0=Some(s62_main 0 [] []).
Proof. reflexivity. Qed.
Lemma s62_cut_form : forall cc,s62_safe cc->exists l r,cc=(StA,(l,S0,r)).
Proof.
 intros cc[(a&u&v&Hu&Hv&->)|(l&r&Hl&Hr&->)].
 - exists(repeat S3 a++S1::S1::(u++v)),[];reflexivity.
 - exists l,r;reflexivity.
Qed.
Lemma s62_returns : forall N,exists t cc,N<=t /\s62_safe cc /\csteps s62_tm t c0=Some cc.
Proof.
 intro N;induction N as[|N IH].
 - exists 5,(s62_main 0 [] []);split;[lia|split;[apply s62_safe_main;constructor|exact s62_entry]].
 - destruct IH as(t&cc&Ht&Hsafe&E);destruct(s62_safe_next cc Hsafe)as(k&cc'&Hk&HS&E').
   exists(t+k),cc';repeat split;try lia;auto;rewrite csteps_add,E;exact E'.
Qed.
Theorem s62_A_recurrent : forall N,exists t,N<=t /\VisitsAt s62_tm StA t.
Proof.
 intro N;destruct(s62_returns N)as(t&cc&Ht&HS&E).
 destruct(s62_cut_form cc HS)as(l&r&->);exists t;split;[exact Ht|].
 exists(lift(StA,(l,S0,r)));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem s62_B_recurrent : forall N,exists t,N<=t /\VisitsAt s62_tm StB t.
Proof.
 intro N;destruct(s62_returns N)as(t&cc&Ht&HS&E).
 destruct(s62_cut_form cc HS)as(l&r&->);exists(t+1);split;[lia|].
 exists(lift(s62_back StB l(S1::r)));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem s62_nonhalt : NonHalt s62_tm.
Proof.
 intros n Hnone;destruct(s62_returns n)as(t&cc&Ht&HS&E).
 pose proof(csteps_lift s62_tm t c0 cc E)as Er;rewrite lift_c0 in Er.
 destruct(stepn_prefix s62_tm n t InitES(lift cc)Ht Er)as(c&Ec&_);congruence.
Qed.
Theorem s62_state_zero : QHBound 0 s62_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(s62_A_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(s62_B_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem s62_sound : NonHalt s62_tm /\QHBound 0 s62_tm.
Proof. split;[exact s62_nonhalt|exact s62_state_zero]. Qed.
Print Assumptions s62_sound.
