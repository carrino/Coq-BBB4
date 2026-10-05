(** * Counters.BlockCoreNWordTr: a regular transducer invariant

    The abstract map satisfies F[]=101, F(0x)=11x,
    F(11x)=01F(x), and F(101x)=101F(x).  The finite family of eight
    base phases and five prefix constructors below is closed under F.
    The four P-prefix phases rotate, then prepend P0 and Q to F of
    their tail; the two base families feed one another at larger
    repetition counts.

    Machine realization additionally requires the regular language
    [(1|01)*].  That condition excludes adjacent zeros and noncanonical
    far-zero padding.  It is preserved by the abstract map, and in
    particular forces the tail in its zero clause to start in 1.
    Every theorem in this file is closed under the global context. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
Import ListNotations.
Definition bn_Q:list Sym:=[S1;S0;S1].
Definition bn_P0:list Sym:=[S0;S1;S1;S0].
Definition bn_P1:list Sym:=[S1;S1;S1;S1;S0].
Definition bn_P2:list Sym:=[S0;S1;S0;S1;S1;S1].
Definition bn_P3:list Sym:=[S1;S1;S1;S0;S1;S1;S1].
Inductive bn_map:list Sym->list Sym->Prop:=
| bn_map_nil:bn_map[]bn_Q
| bn_map_zero:forall x,bn_map(S0::x)(S1::S1::x)
| bn_map_pair:forall x y,bn_map x y->bn_map(S1::S1::x)(S0::S1::y)
| bn_map_Q:forall x y,bn_map x y->bn_map(S1::S0::S1::x)(S1::S0::S1::y).
Lemma bn_map_q:forall x y,bn_map x y->bn_map(bn_Q++x)(bn_Q++y).
Proof. intros;apply bn_map_Q;assumption. Qed.
Lemma bn_map_qrep:forall n x y,bn_map x y->bn_map(rep bn_Q n++x)(rep bn_Q n++y).
Proof. induction n;intros;cbn[rep];[assumption|rewrite<-!app_assoc;apply bn_map_q,IHn;assumption]. Qed.
Lemma bn_map_qonly:forall n,bn_map(rep bn_Q n)(rep bn_Q(S n)).
Proof.
 intro n;pose proof(bn_map_qrep n [] bn_Q bn_map_nil)as H.
 rewrite app_nil_r in H. rewrite<-rep_S_r in H. exact H.
Qed.
Lemma bn_map_P0:forall w,bn_map(bn_P0++w)(bn_P1++w).
Proof. intros;apply bn_map_zero. Qed.
Lemma bn_map_P1:forall w,bn_map(bn_P1++w)(bn_P2++w).
Proof. intros;apply bn_map_pair,bn_map_pair,bn_map_zero. Qed.
Lemma bn_map_P2:forall w,bn_map(bn_P2++w)(bn_P3++w).
Proof. intros;apply bn_map_zero. Qed.
Lemma bn_map_P3:forall x y,bn_map x y->bn_map(bn_P3++x)(bn_P0++bn_Q++y).
Proof. intros;apply bn_map_pair,bn_map_Q,bn_map_pair;assumption. Qed.
Definition bn_A0 n:=S1::rep bn_Q(S n).
Definition bn_A1 n:=[S0;S1;S1;S1;S1]++rep bn_Q n.
Definition bn_A2 n:=[S1;S1;S1;S1;S1;S1]++rep bn_Q n.
Definition bn_A3 n:=[S0;S1;S0;S1;S0;S1]++rep bn_Q(S n).
Definition bn_A4 n:=[S1;S1;S1;S0;S1;S0;S1]++rep bn_Q(S n).
Definition bn_B0 n:=[S1;S1;S1;S1]++rep bn_Q n.
Definition bn_B1 n:=[S0;S1;S0;S1]++rep bn_Q(S n).
Definition bn_B2 n:=[S1;S1;S1;S0;S1]++rep bn_Q(S n).
Inductive bn_good:list Sym->Prop:=
| bn_good_A0:forall n,bn_good(bn_A0 n)
| bn_good_A1:forall n,bn_good(bn_A1 n)
| bn_good_A2:forall n,bn_good(bn_A2 n)
| bn_good_A3:forall n,bn_good(bn_A3 n)
| bn_good_A4:forall n,bn_good(bn_A4 n)
| bn_good_B0:forall n,bn_good(bn_B0 n)
| bn_good_B1:forall n,bn_good(bn_B1 n)
| bn_good_B2:forall n,bn_good(bn_B2 n)
| bn_good_Q:forall w,bn_good w->bn_good(bn_Q++w)
| bn_good_P0:forall w,bn_good w->bn_good(bn_P0++w)
| bn_good_P1:forall w,bn_good w->bn_good(bn_P1++w)
| bn_good_P2:forall w,bn_good w->bn_good(bn_P2++w)
| bn_good_P3:forall w,bn_good w->bn_good(bn_P3++w).
Lemma bn_A01:forall n,bn_map(bn_A0 n)(bn_A1 n).
Proof. intros;apply bn_map_pair,bn_map_zero. Qed.
Lemma bn_A12:forall n,bn_map(bn_A1 n)(bn_A2 n).
Proof. intros;apply bn_map_zero. Qed.
Lemma bn_A23:forall n,bn_map(bn_A2 n)(bn_A3 n).
Proof. intros;apply bn_map_pair,bn_map_pair,bn_map_pair,bn_map_qonly. Qed.
Lemma bn_A34:forall n,bn_map(bn_A3 n)(bn_A4 n).
Proof. intros;apply bn_map_zero. Qed.
Lemma bn_A40:forall n,bn_map(bn_A4 n)(bn_P0++bn_B0(S n)).
Proof. intros;apply bn_map_pair,bn_map_Q,bn_map_zero. Qed.
Lemma bn_B01:forall n,bn_map(bn_B0 n)(bn_B1 n).
Proof. intros;apply bn_map_pair,bn_map_pair,bn_map_qonly. Qed.
Lemma bn_B12:forall n,bn_map(bn_B1 n)(bn_B2 n).
Proof. intros;apply bn_map_zero. Qed.
Lemma bn_B20:forall n,bn_map(bn_B2 n)(bn_P0++bn_A0(S n)).
Proof. intros;apply bn_map_pair,bn_map_Q,bn_map_q. apply bn_map_qonly. Qed.
Theorem bn_good_map:forall x,bn_good x->exists y,bn_map x y/\bn_good y.
Proof.
 intros x H;induction H.
 - exists(bn_A1 n);split;[apply bn_A01|constructor].
 - exists(bn_A2 n);split;[apply bn_A12|constructor].
 - exists(bn_A3 n);split;[apply bn_A23|constructor].
 - exists(bn_A4 n);split;[apply bn_A34|constructor].
 - exists(bn_P0++bn_B0(S n));split;[apply bn_A40|apply bn_good_P0;constructor].
 - exists(bn_B1 n);split;[apply bn_B01|constructor].
 - exists(bn_B2 n);split;[apply bn_B12|constructor].
 - exists(bn_P0++bn_A0(S n));split;[apply bn_B20|apply bn_good_P0;constructor].
 - destruct IHbn_good as(y&HM&HY);exists(bn_Q++y);split;[apply bn_map_q|apply bn_good_Q];assumption.
 - exists(bn_P1++w);split;[apply bn_map_P0|apply bn_good_P1;assumption].
 - exists(bn_P2++w);split;[apply bn_map_P1|apply bn_good_P2;assumption].
 - exists(bn_P3++w);split;[apply bn_map_P2|apply bn_good_P3;assumption].
 - destruct IHbn_good as(y&HM&HY);exists(bn_P0++bn_Q++y);split.
   + apply bn_map_P3;assumption.
   + apply bn_good_P0,bn_good_Q;assumption.
Qed.

Inductive bn_word:list Sym->Prop:=
| bn_nil:bn_word[]
| bn_one:forall w,bn_word w->bn_word(S1::w)
| bn_pair:forall w,bn_word w->bn_word(S0::S1::w).
Lemma bn_word_tail1:forall w,bn_word(S1::w)->bn_word w.
Proof. intros w H;inversion H;assumption. Qed.
Lemma bn_word_tail0:forall w,bn_word(S0::w)->exists u,w=S1::u/\bn_word u.
Proof. intros w H;inversion H;subst;eauto. Qed.
Lemma bn_word_q:forall w,bn_word w->bn_word(bn_Q++w).
Proof. intros;apply bn_one,bn_pair;assumption. Qed.
Lemma bn_map_word:forall x y,bn_map x y->bn_word x->bn_word y.
Proof.
 intros x y HM;induction HM;intro HW.
 - apply bn_one,bn_pair,bn_nil.
 - destruct(bn_word_tail0 _ HW)as(u&->&HU);apply bn_one,bn_one,bn_one;assumption.
 - apply bn_pair,IHHM,bn_word_tail1,bn_word_tail1;assumption.
 - apply bn_word_q,IHHM. apply bn_word_tail1 in HW.
   destruct(bn_word_tail0 _ HW)as(u&E&HU);injection E as <-;assumption.
Qed.
