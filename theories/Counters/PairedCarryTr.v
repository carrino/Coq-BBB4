(** * Recurrence through a paired word and a periodic right tail.

    The first state has a returning 1-anchor with left side [00 ++ E w]
    and right side [1^m ++ (01)^n]. [E] uses pairs 10 and 11, terminated
    by 11. The four state names are parameters, so state-renamed machines
    can reuse the same proof directly.

    Two leading right ones give a four-step return. A leading 01 pair
    gives a twelve-step return. The two remaining boundary cases reduce
    by periodic sweeps to a left carry. That carry stops at the first
    zero or at the finite word's blank end; both outcomes preserve the
    anchor language. Positive return times give recurrent visits to the
    first state's 1-instruction without choosing a canonical numeral. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape.
Import ListNotations.
Fixpoint pcw_word (w:list Sym) : list Sym :=
 match w with []=>[S1;S1] | d::w=>S1::d::pcw_word w end.
Definition pcw_anchor (qa:St) w m n : cconf :=
 (qa,(S0::S0::pcw_word w,S1,repeat S1 m++rep [S0;S1] n)).
Lemma pcw_repeat_tail : forall (x:Sym) m L,
 repeat x m++x::L=x::repeat x m++L.
Proof. intros x m;induction m;intro L;cbn[repeat app];[reflexivity|now rewrite IHm]. Qed.
Lemma pcw_rep_tail : forall n L,
 rep [S0;S1] n++S0::S1::L=S0::S1::rep [S0;S1] n++L.
Proof. induction n;intro L;cbn[rep app];[reflexivity|now rewrite IHn]. Qed.
Lemma pcw_word_split : forall w, exists m t,
 S1::pcw_word w=repeat S1 (S(S m))++t /\
 (t=[] \/ exists v,t=S0::pcw_word v).
Proof.
 induction w as[|d w IH].
 - exists 1,[]. split;[reflexivity|now left].
 - destruct d.
   + exists 0,(S0::pcw_word w). split;[reflexivity|right;eexists;reflexivity].
   + destruct IH as(m&t&H&Ht). exists(S(S m)),t. split;[|exact Ht].
     cbn[pcw_word repeat app]. now rewrite H.
Qed.
Section PairedCarry.
Variable tm:TM.
Variable qa qb qc qd:St.
Hypothesis HA0:tm qa S0=Some(mkTrans S1 DR qb).
Hypothesis HA1:tm qa S1=Some(mkTrans S1 DL qd).
Hypothesis HB0:tm qb S0=Some(mkTrans S1 DL qc).
Hypothesis HB1:tm qb S1=Some(mkTrans S0 DR qa).
Hypothesis HC0:tm qc S0=Some(mkTrans S0 DL qd).
Hypothesis HC1:tm qc S1=Some(mkTrans S0 DL qb).
Hypothesis HD0:tm qd S0=Some(mkTrans S1 DR qd).
Hypothesis HD1:tm qd S1=Some(mkTrans S0 DR qb).
Local Ltac pcw_compute :=
 cbn[Nat.add csteps cstep ctape_move chd ctl t_next t_dir t_write];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[Nat.add csteps cstep ctape_move chd ctl t_next t_dir t_write]);reflexivity.
Lemma pcw_right : forall n L,
 csteps tm (2*n) (qa,(L,chd(rep[S0;S1]n),ctl(rep[S0;S1]n)))=
 Some(qa,(rep[S0;S1]n++L,S0,[])).
Proof.
 induction n as[|n IH];intro L;[reflexivity|].
 replace(2*S n)with(2+2*n)by lia. rewrite csteps_add.
 assert(H:csteps tm 2(qa,(L,chd(rep[S0;S1](S n)),ctl(rep[S0;S1](S n))))=
 Some(qa,(S0::S1::L,chd(rep[S0;S1]n),ctl(rep[S0;S1]n))))by(cbn[rep app chd ctl];pcw_compute).
 rewrite H,IH,pcw_rep_tail. reflexivity.
Qed.
Lemma pcw_left : forall n L R,
 csteps tm (2*n) (qb,(ctl(rep[S0;S1]n++L),chd(rep[S0;S1]n++L),R))=
 Some(qb,(ctl L,chd L,rep[S0;S1]n++R)).
Proof.
 induction n as[|n IH];intros L R;[reflexivity|].
 replace(2*S n)with(2+2*n)by lia. rewrite csteps_add.
 assert(H:csteps tm 2(qb,(ctl(rep[S0;S1](S n)++L),chd(rep[S0;S1](S n)++L),R))=
 Some(qb,(ctl(rep[S0;S1]n++L),chd(rep[S0;S1]n++L),S0::S1::R)))by(cbn[rep app chd ctl];pcw_compute).
 rewrite H,IH,pcw_rep_tail. reflexivity.
Qed.
Lemma pcw_back : forall n X,
 csteps tm (2*n+5)(qa,(rep[S0;S1]n++S0::S0::S1::X,S0,[]))=
 Some(qd,(X,S1,rep[S0;S1](n+2))).
Proof.
 intros. replace(2*n+5)with(3+(2*n+2))by lia. rewrite csteps_add.
 assert(H:csteps tm 3(qa,(rep[S0;S1]n++S0::S0::S1::X,S0,[]))=
 Some(qb,(ctl(rep[S0;S1]n++S0::S0::S1::X),chd(rep[S0;S1]n++S0::S0::S1::X),[S0;S1])))by pcw_compute.
 rewrite H,csteps_add,pcw_left.
 replace(rep[S0;S1](n+2))with(S0::S1::rep[S0;S1]n++[S0;S1]).
 2:{rewrite rep_add;cbn[rep app];repeat rewrite pcw_rep_tail;reflexivity. }
 pcw_compute.
Qed.
Lemma pcw_zero : forall n X,
 csteps tm (4*n+12)(qd,(S0::X,S1,rep[S0;S1](S n)))=
 Some(qd,(S1::X,S1,rep[S0;S1](n+2))).
Proof.
 intros. replace(4*n+12)with(7+(2*n+(2*n+5)))by lia.
 rewrite csteps_add.
 assert(H:csteps tm 7(qd,(S0::X,S1,rep[S0;S1](S n)))=
 Some(qa,(S0::S0::S1::S1::X,chd(rep[S0;S1]n),ctl(rep[S0;S1]n))))by(cbn[rep app];pcw_compute).
 rewrite H,csteps_add,pcw_right. apply pcw_back.
Qed.
Lemma pcw_normal : forall n X,
 csteps tm (8*n+25)(qa,(S0::S0::X,S1,S1::rep[S0;S1]n))=
 Some(qd,(S1::X,S1,rep[S0;S1](n+3))).
Proof.
 intros. replace(8*n+25)with(4+(2*n+((2*n+5)+(4*(n+1)+12))))by lia.
 rewrite csteps_add.
 assert(H:csteps tm 4(qa,(S0::S0::X,S1,S1::rep[S0;S1]n))=
 Some(qa,(S0::S0::S1::S0::X,chd(rep[S0;S1]n),ctl(rep[S0;S1]n))))by pcw_compute.
 rewrite H,csteps_add,pcw_right,csteps_add,pcw_back.
 replace(n+2)with(S(n+1))by lia.
 rewrite pcw_zero. replace(n+1+2)with(n+3)by lia. reflexivity.
Qed.
Lemma pcw_empty : forall X,
 csteps tm 17(qa,(S0::S0::X,S1,[]))=
 Some(qd,(S1::X,S1,rep[S0;S1]2)).
Proof. intro X;pcw_compute. Qed.
Lemma pcw_carry_scan : forall k L R,
 csteps tm (3*S k)(qd,(repeat S1 k++L,S1,S0::R))=
 Some(qd,(ctl L,chd L,S0::repeat S1(S k)++R)).
Proof.
 induction k as[|k IH];intros L R;[cbn[Nat.mul repeat app];pcw_compute|].
 replace(3*S(S k))with(3+3*S k)by lia. rewrite csteps_add.
 assert(H:csteps tm 3(qd,(repeat S1(S k)++L,S1,S0::R))=
 Some(qd,(repeat S1 k++L,S1,S0::S1::R)))by(cbn[repeat app];pcw_compute).
 rewrite H,IH,pcw_repeat_tail. reflexivity.
Qed.
Lemma pcw_carry : forall m L R,
 chd L=S0 ->
 csteps tm (3*(m+3)+4)(qd,(repeat S1(S(S m))++L,S1,S0::R))=
 Some(qa,(S0::S0::S1::S1::ctl L,S1,repeat S1 m++R)).
Proof.
 intros m L R E. replace(3*(m+3)+4)with(3*S(S(S m))+4)by lia.
 rewrite csteps_add,pcw_carry_scan,E. cbn[repeat app]. pcw_compute.
Qed.
Lemma pcw_close : forall w n,exists k w' m,0<k /\
 csteps tm k(qd,(S1::pcw_word w,S1,rep[S0;S1](S n)))=
 Some(pcw_anchor qa w' m n).
Proof.
 intros w n. destruct(pcw_word_split w)as(m&t&E&[Et|(v&Et)]);subst t.
 - exists(3*(m+3)+4),[],(S m). split;[lia|].
   rewrite E. cbn[rep app]. rewrite pcw_carry by reflexivity.
   unfold pcw_anchor;cbn[pcw_word ctl]. rewrite pcw_repeat_tail. reflexivity.
 - exists(3*(m+3)+4),(S1::v),(S m). split;[lia|].
   rewrite E. cbn[rep app]. rewrite pcw_carry by reflexivity.
   unfold pcw_anchor;cbn[pcw_word ctl]. rewrite pcw_repeat_tail. reflexivity.
Qed.
Lemma pcw_return : forall w m n,exists k w' m' n',0<k /\
 csteps tm k(pcw_anchor qa w m n)=Some(pcw_anchor qa w' m' n').
Proof.
 intros w [|[|m]] n.
 - destruct n as[|n].
   + destruct(pcw_close w 1)as(k&w'&m'&Hk&Ek).
     exists(17+k),w',m',1. split;[lia|].
     unfold pcw_anchor at 1;cbn[repeat rep app]. rewrite csteps_add,pcw_empty. exact Ek.
   + exists 12,(S1::w),0,n. split;[lia|]. unfold pcw_anchor;cbn[repeat rep app pcw_word]. pcw_compute.
 - destruct(pcw_close w (n+2))as(k&w'&m'&Hk&Ek).
   exists(8*n+25+k),w',m',(n+2). split;[lia|].
   unfold pcw_anchor at 1;cbn[repeat app]. rewrite csteps_add,pcw_normal.
   replace(n+3)with(S(n+2))by lia. exact Ek.
 - exists 4,(S0::w),m,n. split;[lia|]. unfold pcw_anchor;cbn[repeat app pcw_word]. pcw_compute.
Qed.
Theorem paired_carry_A1_recurrent :
 (exists t w m n,stepn tm t InitES=Some(lift(pcw_anchor qa w m n))) ->
 forall N,exists j e,N<=j /\ stepn tm j InitES=Some e /\ instr_of e=(qa,S1).
Proof.
 intro Boot. assert(Reach:forall N,exists t w m n,N<=t /\stepn tm t InitES=Some(lift(pcw_anchor qa w m n))).
 { induction N as[|N IH].
   - destruct Boot as(t&w&m&n&Et). exists t,w,m,n. split;[lia|exact Et].
   - destruct IH as(t&w&m&n&Ht&Et).
     destruct(pcw_return w m n)as(k&w'&m'&n'&Hk&Ek).
     exists(t+k),w',m',n'. split;[lia|]. rewrite stepn_add,Et. apply csteps_lift;exact Ek. }
 intro N. destruct(Reach N)as(t&w&m&n&Ht&Et).
 exists t,(lift(pcw_anchor qa w m n)). repeat split;assumption||reflexivity.
Qed.
End PairedCarry.
