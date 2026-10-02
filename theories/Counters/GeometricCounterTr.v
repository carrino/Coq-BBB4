(** * A finite binary counter between visits to an outer blank.

    The outer anchors have empty left side, head 0 in the fourth state,
    and right side [(110)^(n+1) ++ 1^(m+1)], optionally preceded by 1.
    A periodic sweep initializes a finite counter whose digits are 110
    and 100. The two phases use terminators 1010 and 10.

    A carry consumes leading 100 digits. An interior sweep changes the
    next 110 digit to 100, restores the carried digits to 110, and adds
    two ones to the unary right tail. The complement binary value of
    the digit word decreases by one, so a finite sequence of increments
    reaches overflow. The terminator then yields another outer anchor,
    with a strictly longer unary tail and the other phase.

    This proof only needs a decreasing counter rank. It does not assume
    a closed formula for the exponentially long outer laps. Every
    instruction has a witness in the initial periodic sweep; positive
    outer returns make those witnesses recur at unbounded times.
    State names are parameters to support renamed and mirrored instances. *)
From Coq Require Import Arith Lia List Bool.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Definition gc_term(b:bool):list Sym:=if b then[S1;S0]else[S1;S0;S1;S0].
Fixpoint gc_word b(w:list Sym):list Sym:=match w with
 | []=>gc_term b | S0::w=>S1::S1::S0::gc_word b w
 | S1::w=>S1::S0::S0::gc_word b w end.
Fixpoint gc_rank(w:list Sym):nat:=match w with
 | []=>0|S0::w=>S(2*gc_rank w)|S1::w=>2*gc_rank w end.
Definition gc_anchor(q:St)(b:bool)n m:cconf:=
 (q,([],S0,(if b then[S1]else[])++rep[S1;S1;S0](S n)++repeat S1(S m))).
Lemma gc_repeat_tail:forall(x:Sym)k R,repeat x k++x::R=x::repeat x k++R.
Proof. intros x k;induction k;intro R;cbn[repeat app];[reflexivity|now rewrite IHk]. Qed.
Lemma gc_block_tail:forall u k R,rep u k++u++R=u++rep u k++R.
Proof. intros u k;induction k;intro R;cbn[rep app];[reflexivity|rewrite <-app_assoc,IHk;repeat rewrite <-app_assoc;reflexivity]. Qed.
Lemma gc_rot0:forall k R,rep[S0;S1;S1]k++S0::R=S0::rep[S1;S1;S0]k++R.
Proof. induction k;intro R;cbn[rep app];[reflexivity|now rewrite IHk]. Qed.
Lemma gc_rot1:forall k R,S1::rep[S1;S0;S1]k++R=rep[S1;S1;S0]k++S1::R.
Proof. induction k;intro R;cbn[rep app];[reflexivity|now rewrite IHk]. Qed.
Lemma gc_word_ones:forall k w b,gc_word b(repeat S1 k++w)=rep[S1;S0;S0]k++gc_word b w.
Proof. induction k;intros;cbn[repeat app rep gc_word];[reflexivity|now rewrite IHk]. Qed.
Lemma gc_word_zeros:forall k w b,gc_word b(repeat S0 k++w)=rep[S1;S1;S0]k++gc_word b w.
Proof. induction k;intros;cbn[repeat app rep gc_word];[reflexivity|now rewrite IHk]. Qed.
Lemma gc_rank_succ:forall k w,
 gc_rank(repeat S1 k++S0::w)=S(gc_rank(repeat S0 k++S1::w)).
Proof. induction k;intro w;cbn[repeat app gc_rank];[lia|rewrite IHk;lia]. Qed.
Lemma gc_ones_split:forall w:list Sym,exists k t,w=repeat S1 k++t /\(t=[]\/exists v,t=S0::v).
Proof.
 induction w as[|[] w IH].
 - exists 0,[]. split;[reflexivity|now left].
 - exists 0,(S0::w). split;[reflexivity|right;eexists;reflexivity].
 - destruct IH as(k&t&E&H). exists(S k),t. split;[cbn[repeat app];now rewrite E|exact H].
Qed.
Section GeometricCounter.
Variable tm:TM.
Variable qa qb qc qd:St.
Hypothesis HA0:tm qa S0=Some(mkTrans S1 DR qb).
Hypothesis HA1:tm qa S1=Some(mkTrans S1 DR qa).
Hypothesis HB0:tm qb S0=Some(mkTrans S1 DL qc).
Hypothesis HB1:tm qb S1=Some(mkTrans S0 DR qa).
Hypothesis HC0:tm qc S0=Some(mkTrans S1 DL qd).
Hypothesis HC1:tm qc S1=Some(mkTrans S1 DL qc).
Hypothesis HD0:tm qd S0=Some(mkTrans S1 DR qd).
Hypothesis HD1:tm qd S1=Some(mkTrans S0 DL qb).
Local Ltac gc_compute:=
 cbn[Nat.add csteps cstep ctape_move chd ctl t_next t_dir t_write];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[Nat.add csteps cstep ctape_move chd ctl t_next t_dir t_write]);reflexivity.
Lemma gc_aones:forall m L R,
 csteps tm m(qa,(L,chd(repeat S1 m++R),ctl(repeat S1 m++R)))=
 Some(qa,(repeat S1 m++L,chd R,ctl R)).
Proof.
 induction m as[|m IH];intros L R;[reflexivity|].
 cbn[repeat app chd ctl csteps].
 assert(E:cstep tm(qa,(L,S1,repeat S1 m++R))=
 Some(qa,(S1::L,chd(repeat S1 m++R),ctl(repeat S1 m++R))))by gc_compute.
 rewrite E,IH,gc_repeat_tail. reflexivity.
Qed.
Lemma gc_cones:forall m L R,
 csteps tm m(qc,(ctl(repeat S1 m++L),chd(repeat S1 m++L),R))=
 Some(qc,(ctl L,chd L,repeat S1 m++R)).
Proof.
 induction m as[|m IH];intros L R;[reflexivity|].
 cbn[repeat app chd ctl csteps].
 assert(E:cstep tm(qc,(repeat S1 m++L,S1,R))=
 Some(qc,(ctl(repeat S1 m++L),chd(repeat S1 m++L),S1::R)))by gc_compute.
 rewrite E,IH,gc_repeat_tail. reflexivity.
Qed.
Lemma gc_blocks101:forall n L R,
 csteps tm(3*n)(qa,(L,chd(rep[S1;S0;S1]n++R),ctl(rep[S1;S0;S1]n++R)))=
 Some(qa,(rep[S0;S1;S1]n++L,chd R,ctl R)).
Proof.
 induction n as[|n IH];intros L R;[reflexivity|].
 replace(3*S n)with(3+3*n)by lia. rewrite csteps_add.
 assert(E:csteps tm 3(qa,(L,chd(rep[S1;S0;S1](S n)++R),ctl(rep[S1;S0;S1](S n)++R)))=
 Some(qa,(S0::S1::S1::L,chd(rep[S1;S0;S1]n++R),ctl(rep[S1;S0;S1]n++R))))by(cbn[rep app chd ctl];gc_compute).
 rewrite E,IH. change(rep[S0;S1;S1]n++S0::S1::S1::L)with(rep[S0;S1;S1]n++[S0;S1;S1]++L).
 rewrite gc_block_tail. reflexivity.
Qed.
Lemma gc_blocks011:forall n L R,
 csteps tm(3*n)(qa,(L,S0,rep[S1;S1;S0]n++R))=
 Some(qa,(rep[S1;S0;S1]n++L,S0,R)).
Proof.
 induction n as[|n IH];intros L R;[reflexivity|].
 replace(3*S n)with(3+3*n)by lia. rewrite csteps_add.
 assert(E:csteps tm 3(qa,(L,S0,rep[S1;S1;S0](S n)++R))=
 Some(qa,(S1::S0::S1::L,S0,rep[S1;S1;S0]n++R)))by(cbn[rep app];gc_compute).
 rewrite E,IH. change(rep[S1;S0;S1]n++S1::S0::S1::L)with(rep[S1;S0;S1]n++[S1;S0;S1]++L).
 rewrite gc_block_tail. reflexivity.
Qed.
Lemma gc_carry:forall n L R,
 csteps tm(3*n)(qc,(rep[S1;S0;S0]n++L,S0,R))=
 Some(qc,(L,S0,rep[S1;S0;S1]n++R)).
Proof.
 induction n as[|n IH];intros L R;[reflexivity|].
 replace(3*S n)with(3+3*n)by lia. rewrite csteps_add.
 assert(E:csteps tm 3(qc,(rep[S1;S0;S0](S n)++L,S0,R))=
 Some(qc,(rep[S1;S0;S0]n++L,S0,S1::S0::S1::R)))by(cbn[rep app];gc_compute).
 rewrite E,IH. change(rep[S1;S0;S1]n++S1::S0::S1::R)with(rep[S1;S0;S1]n++[S1;S0;S1]++R).
 rewrite gc_block_tail. reflexivity.
Qed.
Lemma gc_finish:forall m L,
 csteps tm(2+S m)(qa,(repeat S1 m++L,S0,[]))=
 Some(qc,(ctl L,chd L,repeat S1(m+2))).
Proof.
 intros. rewrite csteps_add.
 assert(E:csteps tm 2(qa,(repeat S1 m++L,S0,[]))=
 Some(qc,(ctl(repeat S1(S m)++L),chd(repeat S1(S m)++L),[S1])))by(cbn[repeat app chd ctl];gc_compute).
 rewrite E,gc_cones. replace(m+2)with(S m+1)by lia. rewrite repeat_app. reflexivity.
Qed.
Lemma gc_interior:forall n m L,
 csteps tm(3*n+2*m+8)(qc,(S1::S1::S0::L,S0,rep[S1;S0;S1]n++repeat S1 m))=
 Some(qc,(rep[S1;S1;S0]n++S1::S0::S0::L,S0,repeat S1(m+2))).
Proof.
 intros. replace(3*n+2*m+8)with(5+(3*n+(m+(2+S m))))by lia. rewrite csteps_add.
 assert(E:csteps tm 5(qc,(S1::S1::S0::L,S0,rep[S1;S0;S1]n++repeat S1 m))=
 Some(qa,(S0::S1::S0::S0::L,chd(rep[S1;S0;S1]n++repeat S1 m),ctl(rep[S1;S0;S1]n++repeat S1 m))))by gc_compute.
 rewrite E,csteps_add,gc_blocks101,csteps_add.
 rewrite <-(app_nil_r(repeat S1 m))at 1 2. rewrite gc_aones.
 cbn[chd ctl]. rewrite gc_finish,gc_rot0. reflexivity.
Qed.
Lemma gc_overflow:forall (b:bool) n m,
 csteps tm(if b then 4 else 5)(qc,(gc_term b,S0,rep[S1;S0;S1]n++repeat S1 m))=
 Some(gc_anchor qd(negb b)n m).
Proof.
 intros [] n m;unfold gc_term,gc_anchor;cbn[negb app rep repeat];
 rewrite <-gc_rot1;gc_compute.
Qed.
Lemma gc_counter:forall w b m,exists k m',m<=m' /\0<k /\
 csteps tm k(qc,(gc_word b w,S0,repeat S1 m))=
 Some(gc_anchor qd(negb b)(length w)m').
Proof.
 intro w. remember(gc_rank w)as r eqn:Er. revert w Er.
 induction r using lt_wf_ind;intros w Er b m.
 destruct(gc_ones_split w)as(n&t&E&[Et|(v&Et)]);subst t;subst w.
 - exists(3*n+(if b then 4 else 5)),m. split;[lia|]. split;[destruct b;lia|].
   rewrite gc_word_ones. cbn[gc_word]. rewrite csteps_add,gc_carry,gc_overflow.
   rewrite app_length,repeat_length;cbn[length];replace(n+0)with n by lia;reflexivity.
 - assert(Hrank:gc_rank(repeat S0 n++S1::v)<r)by(rewrite gc_rank_succ in Er;lia).
   destruct(H _ Hrank _ eq_refl b(m+2))as(k&m'&Hm&Hk&Ek).
   exists(3*n+((3*n+2*m+8)+k)),m'. split;[lia|]. split;[lia|].
   rewrite gc_word_ones. cbn[gc_word]. rewrite csteps_add,gc_carry,csteps_add,gc_interior.
   rewrite gc_word_zeros in Ek. cbn[gc_word]in Ek.
   rewrite Ek. repeat rewrite app_length. repeat rewrite repeat_length. reflexivity.
Qed.
Lemma gc_prepare:forall n m L,
 csteps tm(3*n+2*m+5)(qa,(L,S0,rep[S1;S1;S0]n++repeat S1(S m)))=
 Some(qc,(rep[S1;S1;S0]n++S1::L,S0,repeat S1(m+2))).
Proof.
 intros. replace(3*n+2*m+5)with(3*n+(2+(m+(2+S m))))by lia.
 rewrite csteps_add,gc_blocks011,csteps_add.
 assert(E:csteps tm 2(qa,(rep[S1;S0;S1]n++L,S0,repeat S1(S m)))=
 Some(qa,(S0::S1::rep[S1;S0;S1]n++L,chd(repeat S1 m),ctl(repeat S1 m))))by(cbn[repeat];gc_compute).
 rewrite E,csteps_add. rewrite <-(app_nil_r(repeat S1 m))at 1 2. rewrite gc_aones.
 cbn[chd ctl]. rewrite gc_finish. cbn[chd ctl]. rewrite gc_rot1. reflexivity.
Qed.
Lemma gc_positive_return:forall b n m,exists k b' n' m',m<m' /\0<k /\
 csteps tm k(gc_anchor qd b n m)=Some(gc_anchor qd b' n' m').
Proof.
 intros [] n m.
 - destruct(gc_counter(repeat S0(S n))true(m+2))as(k&m'&Hm&Hk&Ek).
   exists(3+((3*S n+2*m+5)+k)),false,(S n),m'. split;[lia|]. split;[lia|].
   unfold gc_anchor at 1;cbn[app]. rewrite csteps_add.
   assert(E:csteps tm 3(qd,([],S0,S1::rep[S1;S1;S0](S n)++repeat S1(S m)))=
    Some(qa,([S0],S0,rep[S1;S1;S0](S n)++repeat S1(S m))))by gc_compute.
   rewrite E,csteps_add,gc_prepare.
   rewrite <-(app_nil_r(repeat S0(S n)))in Ek. rewrite gc_word_zeros in Ek. cbn[gc_word gc_term negb]in Ek.
   rewrite app_length,repeat_length in Ek;cbn[length]in Ek;replace(S n+0)with(S n)in Ek by lia. exact Ek.
 - destruct(gc_counter(repeat S0 n)false(m+2))as(k&m'&Hm&Hk&Ek).
   exists(5+((3*n+2*m+5)+k)),true,n,m'. split;[lia|]. split;[lia|].
   unfold gc_anchor at 1;cbn[app]. rewrite csteps_add.
   assert(E:csteps tm 5(qd,([],S0,rep[S1;S1;S0](S n)++repeat S1(S m)))=
    Some(qa,([S0;S1;S0],S0,rep[S1;S1;S0]n++repeat S1(S m))))by(cbn[rep app];gc_compute).
   rewrite E,csteps_add,gc_prepare.
   rewrite <-(app_nil_r(repeat S0 n))in Ek. rewrite gc_word_zeros in Ek. cbn[gc_word gc_term negb]in Ek.
   rewrite app_length,repeat_length in Ek;cbn[length]in Ek;replace(n+0)with n in Ek by lia. exact Ek.
Qed.
Lemma gc_prepare_mid:forall n m L,
 csteps tm(3*n+2+m)(qa,(L,S0,rep[S1;S1;S0]n++repeat S1(S m)))=
 Some(qa,(repeat S1 m++S0::S1::rep[S1;S0;S1]n++L,S0,[])).
Proof.
 intros. replace(3*n+2+m)with(3*n+(2+m))by lia.
 rewrite csteps_add,gc_blocks011,csteps_add.
 assert(E:csteps tm 2(qa,(rep[S1;S0;S1]n++L,S0,repeat S1(S m)))=
 Some(qa,(S0::S1::rep[S1;S0;S1]n++L,chd(repeat S1 m),ctl(repeat S1 m))))by(cbn[repeat];gc_compute).
 rewrite E. rewrite <-(app_nil_r(repeat S1 m))at 1 2. rewrite gc_aones. reflexivity.
Qed.
Lemma gc_entry:forall b n m,exists k j L,
 csteps tm k(gc_anchor qd b n m)=Some(qa,(L,S0,rep[S1;S1;S0]j++repeat S1(S m))).
Proof.
 intros [] n m.
 - exists 3,(S n),[S0]. unfold gc_anchor;cbn[app];gc_compute.
 - exists 5,n,[S0;S1;S0]. unfold gc_anchor;cbn[rep app];gc_compute.
Qed.
Lemma gc_start_fires:forall n m L,0<m ->forall q h,
 q=qa\/q=qb\/q=qc ->exists k c,
 csteps tm k(qa,(L,S0,rep[S1;S1;S0]n++repeat S1(S m)))=Some c /\cinstr c=(q,h).
Proof.
 intros n m L Hm q h [Eq|[Eq|Eq]];subst q;destruct h.
 - exists 0,(qa,(L,S0,rep[S1;S1;S0]n++repeat S1(S m))). split;reflexivity.
 - destruct m as[|m];[lia|]. destruct n as[|n];exists 2;eexists;split;
   [cbn[rep repeat app];gc_compute|reflexivity|cbn[rep repeat app];gc_compute|reflexivity].
 - exists(3*n+2+m+1),(qb,(S1::(repeat S1 m++S0::S1::rep[S1;S0;S1]n++L),S0,[])).
   split;[|reflexivity]. rewrite csteps_add,gc_prepare_mid. gc_compute.
 - destruct n as[|n];exists 1;eexists;split;
   [cbn[rep repeat app];gc_compute|reflexivity|cbn[rep repeat app];gc_compute|reflexivity].
 - exists(3*n+2*m+5),(qc,(rep[S1;S1;S0]n++S1::L,S0,repeat S1(m+2))).
   split;[apply gc_prepare|reflexivity].
 - exists(3*n+2+m+2),(qc,(repeat S1 m++S0::S1::rep[S1;S0;S1]n++L,S1,[S1])).
   split;[|reflexivity]. rewrite csteps_add,gc_prepare_mid. gc_compute.
Qed.
Hypothesis Hstates:forall q,q=qa\/q=qb\/q=qc\/q=qd.
Lemma gc_all_fires:forall b n m,0<m ->forall t,exists k c,
 csteps tm k(gc_anchor qd b n m)=Some c /\cinstr c=t.
Proof.
 intros b n m Hm [q h]. destruct(Hstates q)as[E|[E|[E|E]]].
 - destruct(gc_entry b n m)as(k&j&L&Ek).
   destruct(gc_start_fires j m L Hm q h(or_introl E))as(s&c&Es&Ec).
   exists(k+s),c. split;[rewrite csteps_add,Ek;exact Es|exact Ec].
 - destruct(gc_entry b n m)as(k&j&L&Ek).
   destruct(gc_start_fires j m L Hm q h(or_intror(or_introl E)))as(s&c&Es&Ec).
   exists(k+s),c. split;[rewrite csteps_add,Ek;exact Es|exact Ec].
 - destruct(gc_entry b n m)as(k&j&L&Ek).
   destruct(gc_start_fires j m L Hm q h(or_intror(or_intror E)))as(s&c&Es&Ec).
   exists(k+s),c. split;[rewrite csteps_add,Ek;exact Es|exact Ec].
 - subst q. destruct h.
   + exists 0,(gc_anchor qd b n m). split;reflexivity.
   + destruct b;exists 1;eexists;split;
     [unfold gc_anchor;cbn[rep app];gc_compute|reflexivity|
      unfold gc_anchor;cbn[rep app];gc_compute|reflexivity].
Qed.
Theorem geometric_counter_neverqhtr:
 (exists t b n m,0<m /\stepn tm t InitES=Some(lift(gc_anchor qd b n m))) ->
 NeverQuasiHaltsTr tm.
Proof.
 intro Boot. assert(Reach:forall N,exists t b n m,N<=t /\0<m /\stepn tm t InitES=Some(lift(gc_anchor qd b n m))).
 { induction N as[|N IH].
   - destruct Boot as(t&b&n&m&Hm&Et). exists t,b,n,m. repeat split;[lia|exact Hm|exact Et].
   - destruct IH as(t&b&n&m&Ht&Hm&Et). destruct(gc_positive_return b n m)as(k&b'&n'&m'&Hinc&Hk&Ek).
     exists(t+k),b',n',m'. repeat split;[lia|lia|]. rewrite stepn_add,Et. apply csteps_lift;exact Ek. }
 intros target _ N. destruct(Reach N)as(t&b&n&m&Ht&Hm&Et).
 destruct(gc_all_fires b n m Hm target)as(k&c&Ek&Ec).
 exists(t+k). split;[lia|]. exists(lift c). split.
 - rewrite stepn_add,Et. apply csteps_lift;exact Ek.
 - rewrite cinstr_lift. exact Ec.
Qed.
Theorem geometric_counter_recurrent:
 (exists t b n m,stepn tm t InitES=Some(lift(gc_anchor qd b n m))) ->
 forall N,exists j e,N<=j /\stepn tm j InitES=Some e /\instr_of e=(qd,S0).
Proof.
 intro Boot. assert(Reach:forall N,exists t b n m,N<=t /\stepn tm t InitES=Some(lift(gc_anchor qd b n m))).
 { induction N as[|N IH].
   - destruct Boot as(t&b&n&m&Et). exists t,b,n,m. split;[lia|exact Et].
   - destruct IH as(t&b&n&m&Ht&Et). destruct(gc_positive_return b n m)as(k&b'&n'&m'&Hm&Hk&Ek).
     exists(t+k),b',n',m'. split;[lia|]. rewrite stepn_add,Et. apply csteps_lift;exact Ek. }
 intro N. destruct(Reach N)as(t&b&n&m&Ht&Et).
 exists t,(lift(gc_anchor qd b n m)). repeat split;assumption||reflexivity.
Qed.
End GeometricCounter.
