(** * FuelB0ReturnTr: positive B0 returns on every finite tape.

    The leftward C routine consumes either two or three cells before
    recurring, and otherwise reaches A0. A separate marker lemma bounds
    the right tape remaining after an A1 carry. This yields A0-to-B0
    reachability by induction on the right tape length. Composing both
    routines gives a positive B0 return without any tape-language
    assumption. The final recurrence theorem can be combined with
    checked certificates for the other seven instructions. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
Import ListNotations.
Section Machine.
Variable tm : TM.
Hypothesis HA0 : tm StA S0 = Some (mkTrans S1 DR StB).
Hypothesis HA1 : tm StA S1 = Some (mkTrans S1 DR StC).
Hypothesis HB0 : tm StB S0 = Some (mkTrans S0 DL StC).
Hypothesis HB1 : tm StB S1 = Some (mkTrans S0 DR StA).
Hypothesis HC0 : tm StC S0 = Some (mkTrans S1 DR StA).
Hypothesis HC1 : tm StC S1 = Some (mkTrans S1 DL StD).
Hypothesis HD0 : tm StD S0 = Some (mkTrans S1 DL StA).
Hypothesis HD1 : tm StD S1 = Some (mkTrans S0 DL StC).
Local Ltac bf_compute :=
 cbn [Nat.add csteps cstep ctape_move chd ctl t_next t_dir t_write];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[Nat.add csteps cstep ctape_move chd ctl t_next t_dir t_write]);reflexivity.
Definition bf_hit (q:St) (s:Sym) (c:cconf) : Prop :=
 exists k L R, csteps tm k c = Some(q,(L,s,R)).
Lemma bf_hit_back : forall q s k c d,
 csteps tm k c=Some d -> bf_hit q s d -> bf_hit q s c.
Proof. intros q s k c d H(j&L&R&Hj). exists(k+j),L,R. now rewrite csteps_add,H. Qed.
(** The right-hand zero is preserved by each leftward recursive branch. *)
Lemma bf_C_zero_A0 : forall U R,
 bf_hit StA S0 (StC,(ctl U,chd U,S0::R)).
Proof.
 fix IH 1. intros U R. destruct U as[|[] U].
 - exists 1,[S1],R. bf_compute.
 - exists 1,(S1::U),R. bf_compute.
 - destruct U as[|[] U].
   + exists 2,[],(S1::S1::S0::R). bf_compute.
   + destruct U as[|[] U].
     * exists 2,[],(S1::S1::S0::R). bf_compute.
     * exists 2,U,(S1::S1::S0::R). bf_compute.
     * eapply bf_hit_back with(k:=5)(d:=(StC,(ctl U,chd U,S0::S1::S1::S0::R))).
       -- bf_compute.
       -- apply IH.
   + eapply bf_hit_back with(k:=2)(d:=(StC,(ctl U,chd U,S0::S1::S0::R))).
     * bf_compute.
     * apply IH.
Qed.
Fixpoint bf_pairs (k:nat) : list Sym :=
 match k with 0=>[] | S k=>S1::S1::bf_pairs k end.
Fixpoint bf_zpairs (k:nat) : list Sym :=
 match k with 0=>[] | S k=>S0::S1::bf_zpairs k end.
Lemma bf_zpair_push : forall k L,
 bf_zpairs k++S0::S1::L = bf_zpairs(S k)++L.
Proof. induction k;intro L;cbn[bf_zpairs app];[reflexivity|now rewrite IHk]. Qed.
Lemma bf_zpairs_length : forall k, length(bf_zpairs k)=2*k.
Proof. induction k;cbn[bf_zpairs length];lia. Qed.
Lemma bf_C_pairs : forall k L R,
 csteps tm (2*k) (StC,(ctl(bf_pairs k++S0::L),chd(bf_pairs k++S0::L),R)) =
 Some(StC,(L,S0,bf_zpairs k++R)).
Proof.
 induction k as[|k IH];intros L R;cbn[bf_pairs app chd ctl].
 - reflexivity.
 - replace(2*S k)with(2+2*k)by lia. rewrite csteps_add.
   assert(E:csteps tm 2(StC,(S1::bf_pairs k++S0::L,S1,R))=
     Some(StC,(ctl(bf_pairs k++S0::L),chd(bf_pairs k++S0::L),S0::S1::R)))by bf_compute.
   rewrite E,IH,bf_zpair_push. reflexivity.
Qed.
Lemma bf_A1_carry : forall k L R,
 csteps tm (3+(2*k+1)) (StA,(bf_pairs k++S0::L,S1,S1::R)) =
 Some(StA,(S1::L,S0,S1::bf_zpairs k++R)).
Proof.
 intros. rewrite csteps_add.
 assert(E:csteps tm 3(StA,(bf_pairs k++S0::L,S1,S1::R))=
   Some(StC,(ctl(bf_pairs k++S0::L),chd(bf_pairs k++S0::L),S0::S1::R)))by bf_compute.
 rewrite E,csteps_add,bf_C_pairs,bf_zpair_push.
 cbn[bf_zpairs app]. bf_compute.
Qed.
(** A paired-one prefix ends at a zero marker. Carrying across it cannot
    increase the remaining right tape beyond its consumed prefix bound. *)
Lemma bf_A1_marker : forall R k L,
 exists t L' R', length R' <= 2*k+length R /\
 csteps tm t (StA,(bf_pairs k++S0::L,S1,R))=Some(StA,(L',S0,R')).
Proof.
 fix IH 1. intros R k L. destruct R as[|[] R].
 - exists 2,(S1::S1::bf_pairs k++S0::L),[]. split;[cbn[length];lia|bf_compute].
 - destruct R as[|[] R].
   + exists 2,(S1::S1::bf_pairs k++S0::L),[]. split;[cbn[length];lia|bf_compute].
   + exists 2,(S1::S1::bf_pairs k++S0::L),R. split;[cbn[length];lia|bf_compute].
   + destruct(IH R(S k)L)as(t&L'&R'&Hlen&Et).
     exists(2+t),L',R'. split;[cbn[length]in*;lia|].
     rewrite csteps_add.
     assert(E:csteps tm 2(StA,(bf_pairs k++S0::L,S1,S0::S1::R))=
       Some(StA,(bf_pairs(S k)++S0::L,S1,R)))by bf_compute.
     now rewrite E.
 - exists(3+(2*k+1)),(S1::L),(S1::bf_zpairs k++R).
   split;[cbn[length];rewrite app_length,bf_zpairs_length;cbn[length];lia|].
   apply bf_A1_carry.
Qed.
(** The marker produced by A0 makes the next A0 right tape shorter. *)
Lemma bf_A0_B0 : forall L R, bf_hit StB S0 (StA,(L,S0,R)).
Proof.
 assert(H:forall N R L,length R=N -> bf_hit StB S0(StA,(L,S0,R))).
 { intro N. induction N as[N IH]using(well_founded_induction lt_wf).
   intros R L Hlen. destruct R as[|[] R].
   - exists 1,(S1::L),[]. bf_compute.
   - exists 1,(S1::L),R. bf_compute.
   - destruct R as[|[] R].
     + eapply bf_hit_back with(k:=2)(d:=(StA,(S0::S1::L,S0,[]))).
       * bf_compute.
       * apply(IH 0);[cbn[length]in Hlen;lia|reflexivity].
     + eapply bf_hit_back with(k:=2)(d:=(StA,(S0::S1::L,S0,R))).
       * bf_compute.
       * apply(IH(length R));[cbn[length]in Hlen;lia|reflexivity].
     + destruct(bf_A1_marker R 0(S1::L))as(t&L'&R'&Hbound&Et).
       eapply bf_hit_back with(k:=2+t)(d:=(StA,(L',S0,R'))).
       * rewrite csteps_add.
         assert(E:csteps tm 2(StA,(L,S0,S1::S1::R))=
           Some(StA,(S0::S1::L,S1,R)))by bf_compute.
         rewrite E. exact Et.
       * apply(IH(length R'));[cbn[length]in Hlen;cbn[Nat.mul Nat.add]in Hbound;lia|reflexivity].
 }
 intros L R. apply(H(length R)R L eq_refl).
Qed.
Lemma bf_B0_return : forall L R,
 exists k L' R', 0<k /\ csteps tm k(StB,(L,S0,R))=Some(StB,(L',S0,R')).
Proof.
 intros L R.
 destruct(bf_C_zero_A0 L R)as(k&U&V&Ek).
 destruct(bf_A0_B0 U V)as(j&U'&V'&Ej).
 exists(1+(k+j)),U',V'. split;[lia|].
 rewrite csteps_add.
 assert(E:csteps tm 1(StB,(L,S0,R))=Some(StC,(ctl L,chd L,S0::R)))by bf_compute.
 now rewrite E,csteps_add,Ek.
Qed.
Theorem bf_B0_recurrent : forall N,
 exists j, N<=j /\ FiresAt tm (StB,S0) j.
Proof.
 assert(Reach:forall N,exists t L R,N<=t /\ csteps tm t c0=Some(StB,(L,S0,R))).
 { induction N as[|N IH].
   - exists 1,[S1],[]. split;[lia|]. unfold c0. bf_compute.
   - destruct IH as(t&L&R&Ht&Et).
     destruct(bf_B0_return L R)as(k&U&V&Hk&Ek).
     exists(t+k),U,V. split;[lia|]. now rewrite csteps_add,Et.
 }
 intro N. destruct(Reach N)as(t&L&R&Ht&Et).
 exists t. split;[exact Ht|]. exists(lift(StB,(L,S0,R))).
 split;[rewrite <-lift_c0;apply csteps_lift;exact Et|reflexivity].
Qed.
End Machine.
