(** * A finite right suffix forces repeated visits to D1.

    An anchor has arbitrary finite left side and right side [X ++ 111110].
    Every A configuration with this suffix reaches another D1 anchor.
    The proof is strong induction on the length of [X]. A1 consumes one
    prefix cell. A0 followed by 1 consumes two, apart from a finite
    boundary case. A0 followed by 0 either reaches D1 during the left
    scan, or turns around and returns to A0 one cell farther right.
    Three exact boundary computations close the induction.

    A finite C scan reduces to A0 or D1. The outgoing D1 instruction
    therefore has a positive return to the same anchor language. No
    arithmetic interpretation or invariant for the left word is needed. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
Import ListNotations.
Definition fo_tail:list Sym := [S1;S1;S1;S1;S1;S0].
Definition fo_anchor L X:cconf :=(StD,(L,S1,X++fo_tail)).
Lemma fo_repeat_tail:forall(x:Sym)k R,repeat x k++x::R=x::repeat x k++R.
Proof. intros x k;induction k;intro R;cbn[repeat app];[reflexivity|now rewrite IHk]. Qed.
Lemma fo_ones_split:forall L:list Sym,exists k t,L=repeat S1 k++t /\(t=[]\/exists X,t=S0::X).
Proof.
 induction L as[|[] L IH].
 - exists 0,[]. split;[reflexivity|now left].
 - exists 0,(S0::L). split;[reflexivity|right;eexists;reflexivity].
 - destruct IH as(k&t&E&H). exists(S k),t. split;[cbn[repeat app];now rewrite E|exact H].
Qed.
Section FiveOnes.
Variable tm:TM.
Hypothesis HA0:tm StA S0=Some(mkTrans S1 DR StB).
Hypothesis HA1:tm StA S1=Some(mkTrans S0 DR StA).
Hypothesis HB0:tm StB S0=Some(mkTrans S0 DL StC).
Hypothesis HB1:tm StB S1=Some(mkTrans S1 DR StA).
Hypothesis HC0:tm StC S0=Some(mkTrans S0 DL StD).
Hypothesis HC1:tm StC S1=Some(mkTrans S1 DL StC).
Hypothesis HD0:tm StD S0=Some(mkTrans S1 DL StA).
Hypothesis HD1:tm StD S1=Some(mkTrans S0 DL StB).
Local Ltac fo_compute:=
 cbn[Nat.add csteps cstep ctape_move chd ctl t_next t_dir t_write];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[Nat.add csteps cstep ctape_move chd ctl t_next t_dir t_write]);reflexivity.
Lemma fo_ascan:forall k L R,
 csteps tm k(StA,(L,chd(repeat S1 k++R),ctl(repeat S1 k++R)))=
 Some(StA,(repeat S0 k++L,chd R,ctl R)).
Proof.
 induction k as[|k IH];intros L R;[reflexivity|].
 cbn[repeat app chd ctl csteps].
 assert(H:cstep tm(StA,(L,S1,repeat S1 k++R))=
 Some(StA,(S0::L,chd(repeat S1 k++R),ctl(repeat S1 k++R))))by fo_compute.
 rewrite H,IH,fo_repeat_tail. reflexivity.
Qed.
Lemma fo_across:forall k L R,
 csteps tm (k+2)(StA,(L,S0,repeat S1(S k)++S0::R))=
 Some(StA,(repeat S0 k++S1::S1::L,S0,R)).
Proof.
 intros. replace(k+2)with(2+k)by lia. rewrite csteps_add.
 assert(H:csteps tm 2(StA,(L,S0,repeat S1(S k)++S0::R))=
 Some(StA,(S1::S1::L,chd(repeat S1 k++S0::R),ctl(repeat S1 k++S0::R))))by(cbn[repeat app];fo_compute).
 rewrite H,fo_ascan. reflexivity.
Qed.
Lemma fo_cscan:forall k L R,
 csteps tm k(StC,(ctl(repeat S1 k++L),chd(repeat S1 k++L),R))=
 Some(StC,(ctl L,chd L,repeat S1 k++R)).
Proof.
 induction k as[|k IH];intros L R;[reflexivity|].
 cbn[repeat app chd ctl csteps].
 assert(H:cstep tm(StC,(repeat S1 k++L,S1,R))=
 Some(StC,(ctl(repeat S1 k++L),chd(repeat S1 k++L),S1::R)))by fo_compute.
 rewrite H,IH,fo_repeat_tail. reflexivity.
Qed.
Lemma fo_turn:forall L R,exists L',
 csteps tm 4(StC,(S0::L,S0,R))=Some(StA,(L',S0,R)).
Proof.
 intros [|[] L] R.
 - exists[S1;S1]. fo_compute.
 - exists(S1::S1::L). fo_compute.
 - exists(S0::S0::L). fo_compute.
Qed.
Lemma fo_turn_blank:forall R,
 csteps tm 4(StC,([],S0,R))=Some(StA,([S1;S1],S0,R)).
Proof. intro R;fo_compute. Qed.
Lemma fo_zero_progress:forall L R,
 (exists k L',csteps tm k(StA,(L,S0,S0::R))=Some(StA,(L',S0,R)))\/
 (exists k L' X,csteps tm k(StA,(L,S0,S0::R))=Some(StD,(L',S1,X++R))).
Proof.
 intros L R. destruct(fo_ones_split L)as(k&t&E&[Et|(Y&Et)]);subst t;rewrite E.
 - left. exists(2+(S k+(4+(k+2)))),(repeat S0 k++[S1;S1;S1;S1]).
   rewrite csteps_add.
   assert(H:csteps tm 2(StA,(repeat S1 k++[],S0,S0::R))=
    Some(StC,(ctl(repeat S1(S k)++[]),chd(repeat S1(S k)++[]),S0::R)))by(cbn[repeat app chd ctl];fo_compute).
   rewrite H,csteps_add,fo_cscan. cbn[ctl chd]. rewrite csteps_add,fo_turn_blank.
   apply fo_across.
 - destruct Y as[|d Y].
   + left. exists(2+(S k+(4+(k+2)))),(repeat S0 k++[S1;S1;S1;S1]).
     rewrite csteps_add.
     assert(H:csteps tm 2(StA,(repeat S1 k++[S0],S0,S0::R))=
      Some(StC,(ctl(repeat S1(S k)++[S0]),chd(repeat S1(S k)++[S0]),S0::R)))by(cbn[repeat app chd ctl];fo_compute).
     rewrite H,csteps_add,fo_cscan. cbn[ctl chd]. rewrite csteps_add,fo_turn_blank. apply fo_across.
   + destruct d.
     * destruct(fo_turn Y(repeat S1(S k)++S0::R))as(L'&HT).
       left. exists(2+(S k+(4+(k+2)))),(repeat S0 k++S1::S1::L').
       rewrite csteps_add.
       assert(H:csteps tm 2(StA,(repeat S1 k++S0::S0::Y,S0,S0::R))=
        Some(StC,(ctl(repeat S1(S k)++S0::S0::Y),chd(repeat S1(S k)++S0::S0::Y),S0::R)))by(cbn[repeat app chd ctl];fo_compute).
       rewrite H,csteps_add,fo_cscan. cbn[ctl chd]. rewrite csteps_add,HT. apply fo_across.
     * right. exists(2+(S k+1)),Y,(S0::repeat S1(S k)++[S0]).
       rewrite csteps_add.
       assert(H:csteps tm 2(StA,(repeat S1 k++S0::S1::Y,S0,S0::R))=
        Some(StC,(ctl(repeat S1(S k)++S0::S1::Y),chd(repeat S1(S k)++S0::S1::Y),S0::R)))by(cbn[repeat app chd ctl];fo_compute).
       rewrite H,csteps_add,fo_cscan. cbn[ctl chd].
       change((S0::repeat S1(S k)++[S0])++R)with(S0::(repeat S1(S k)++[S0])++R).
       rewrite <-app_assoc. cbn[app]. fo_compute.
Qed.
Lemma fo_base0:forall L,
 csteps tm 23(StA,(L,S0,fo_tail))=Some(fo_anchor(S1::L)[S0]).
Proof. intro L;unfold fo_anchor,fo_tail;cbn[app];fo_compute. Qed.
Lemma fo_base1:forall L,
 csteps tm 49(StA,(L,S1,fo_tail))=Some(fo_anchor(S1::S1::S1::L)[S0]).
Proof. intro L;unfold fo_anchor,fo_tail;cbn[app];fo_compute. Qed.
Lemma fo_base01:forall L,
 csteps tm 50(StA,(L,S0,S1::fo_tail))=Some(fo_anchor(S1::S0::S0::S1::L)[S0]).
Proof. intro L;unfold fo_anchor,fo_tail;cbn[app];fo_compute. Qed.
Lemma fo_A_return:forall X L h,exists k L' Y,
 csteps tm k(StA,(L,h,X++fo_tail))=Some(fo_anchor L' Y).
Proof.
 intro X. remember(length X)as n eqn:En. revert X En.
 induction n using lt_wf_ind;intros X En L h. destruct X as[|d X].
 - destruct h.
   + exists 23,(S1::L),[S0]. apply fo_base0.
   + exists 49,(S1::S1::S1::L),[S0]. apply fo_base1.
 - destruct h.
   + destruct d.
     * destruct(fo_zero_progress L(X++fo_tail))as[(k&L'&Ek)|(k&L'&Y&Ek)].
       -- destruct(H(length X)ltac:(cbn in En;lia)X eq_refl L' S0)as(j&L''&Z&Ej).
          exists(k+j),L'',Z. cbn[app]. rewrite csteps_add,Ek. exact Ej.
       -- exists k,L',(Y++X). unfold fo_anchor. rewrite <-app_assoc. exact Ek.
     * destruct X as[|e X].
       -- exists 50,(S1::S0::S0::S1::L),[S0]. apply fo_base01.
       -- destruct(H(length X)ltac:(cbn in En;lia)X eq_refl(S1::S1::L)e)as(k&L'&Y&Ek).
          exists(2+k),L',Y. rewrite csteps_add.
          assert(E:csteps tm 2(StA,(L,S0,(S1::e::X)++fo_tail))=
           Some(StA,(S1::S1::L,e,X++fo_tail)))by(cbn[app];fo_compute).
          rewrite E. exact Ek.
   + destruct(H(length X)ltac:(cbn in En;lia)X eq_refl(S0::L)d)as(k&L'&Y&Ek).
     exists(1+k),L',Y. rewrite csteps_add.
     assert(E:csteps tm 1(StA,(L,S1,(d::X)++fo_tail))=
      Some(StA,(S0::L,d,X++fo_tail)))by(cbn[app];fo_compute).
     rewrite E. exact Ek.
Qed.
Lemma fo_C_return:forall L h X,exists k L' Y,
 csteps tm k(StC,(L,h,X++fo_tail))=Some(fo_anchor L' Y).
Proof.
 intros L h X. destruct(fo_ones_split(h::L))as(k&t&E&[Et|(V&Et)]);subst t.
 - change(StC,(L,h,X++fo_tail))with(StC,(ctl(h::L),chd(h::L),X++fo_tail)).
   rewrite E. destruct(fo_A_return (repeat S1 k++X)[S1;S1]S0)as(j&L'&Y&Ej).
   exists(k+(4+j)),L',Y. rewrite csteps_add,fo_cscan. cbn[ctl chd]. rewrite csteps_add,fo_turn_blank.
   rewrite app_assoc. exact Ej.
 - change(StC,(L,h,X++fo_tail))with(StC,(ctl(h::L),chd(h::L),X++fo_tail)).
   rewrite E. destruct V as[|[] V].
   + destruct(fo_A_return (repeat S1 k++X)[S1;S1]S0)as(j&L'&Y&Ej).
     exists(k+(4+j)),L',Y. rewrite csteps_add,fo_cscan. cbn[ctl chd]. rewrite csteps_add,fo_turn_blank.
     rewrite app_assoc. exact Ej.
   + destruct(fo_turn V(repeat S1 k++X++fo_tail))as(U&EU).
     destruct(fo_A_return (repeat S1 k++X)U S0)as(j&L'&Y&Ej).
     exists(k+(4+j)),L',Y. rewrite csteps_add,fo_cscan. cbn[ctl chd]. rewrite csteps_add,EU.
     rewrite app_assoc. exact Ej.
   + exists(k+1),V,(S0::repeat S1 k++X). rewrite csteps_add,fo_cscan. cbn[ctl chd].
     unfold fo_anchor. cbn[app]. rewrite <-app_assoc. fo_compute.
Qed.
Lemma fo_positive_return:forall L X,exists k L' Y,0<k /\
 csteps tm k(fo_anchor L X)=Some(fo_anchor L' Y).
Proof.
 intros L X. destruct L as[|[] L].
 - destruct(fo_C_return [] S0(S0::S0::X))as(k&L'&Y&Ek).
   exists(2+k),L',Y. split;[lia|]. rewrite csteps_add.
   assert(H:csteps tm 2(fo_anchor[]X)=Some(StC,([],S0,(S0::S0::X)++fo_tail)))by(unfold fo_anchor;cbn[app];fo_compute).
   rewrite H. exact Ek.
 - destruct(fo_C_return (ctl L)(chd L)(S0::S0::X))as(k&L'&Y&Ek).
   exists(2+k),L',Y. split;[lia|]. rewrite csteps_add.
   assert(H:csteps tm 2(fo_anchor(S0::L)X)=Some(StC,(ctl L,chd L,(S0::S0::X)++fo_tail)))by(unfold fo_anchor;cbn[app];fo_compute).
   rewrite H. exact Ek.
 - destruct(fo_A_return X(S1::L)S0)as(k&L'&Y&Ek).
   exists(2+k),L',Y. split;[lia|]. rewrite csteps_add.
   assert(H:csteps tm 2(fo_anchor(S1::L)X)=Some(StA,(S1::L,S0,X++fo_tail)))by(unfold fo_anchor;fo_compute).
   rewrite H. exact Ek.
Qed.
Theorem five_ones_D1_recurrent:
 (exists t L X,stepn tm t InitES=Some(lift(fo_anchor L X))) ->
 forall N,exists j e,N<=j /\stepn tm j InitES=Some e /\instr_of e=(StD,S1).
Proof.
 intro Boot. assert(Reach:forall N,exists t L X,N<=t /\stepn tm t InitES=Some(lift(fo_anchor L X))).
 { induction N as[|N IH].
   - destruct Boot as(t&L&X&Et). exists t,L,X. split;[lia|exact Et].
   - destruct IH as(t&L&X&Ht&Et). destruct(fo_positive_return L X)as(k&L'&Y&Hk&Ek).
     exists(t+k),L',Y. split;[lia|]. rewrite stepn_add,Et. apply csteps_lift;exact Ek. }
 intro N. destruct(Reach N)as(t&L&X&Ht&Et).
 exists t,(lift(fo_anchor L X)). repeat split;assumption||reflexivity.
Qed.
End FiveOnes.
