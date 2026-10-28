(** Compact binary-count certificate: each edge instantiates a universal
    cut lemma; all arithmetic remains in N until transported to nat. *)
From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement Spec CTape Census.
From BBB24Burn21S032Finite Require Import CutMacros BinaryBridge.
Import ListNotations.
Opaque sf_count.
#[local] Hint Rewrite sf_r0 sf_r1 sf_r2 : sf_repeat.
Ltac sf_words := unfold sf_word in *;autorewrite with sf_repeat in *;cbn[app]in *.
Lemma sf_edge_01 : csteps sc_tm(sf_count 22%N)(sc_cut(sf_count 0%N)(sf_word 0%N None 0%N))=Some(sc_cut(sf_count 2%N)(sf_word 2%N (Some S1) 0%N)).
Proof. pose proof(sf_N_blank 0%N)as H;sf_words;exact H. Qed.
Lemma sf_prefix_01 : csteps sc_tm(sf_count 22%N)c0=Some(sc_cut(sf_count 2%N)(sf_word 2%N (Some S1) 0%N)).
Proof. pose proof sf_edge_01 as H;sf_words;rewrite sf_small0 in H;exact H. Qed.
Lemma sf_edge_02 : csteps sc_tm(sf_count 25%N)(sc_cut(sf_count 2%N)(sf_word 2%N (Some S1) 0%N))=Some(sc_cut(sf_count 7%N)(sf_word 0%N (Some S1) 0%N)).
Proof. unfold sf_word. change(csteps sc_tm(sf_count 25%N)
 (sc_cut(sf_count 2%N)(repeat S3(sf_count(2*1+0)%N)++(S1::repeat S3(sf_count 0%N))))=
 Some(sc_cut(sf_count 7%N)(repeat S3(sf_count 0%N)++(S1::repeat S3(sf_count 0%N))))).
 rewrite sf_radd,<-app_assoc. exact(sf_N_bulk 1%N 2%N (repeat S3(sf_count 0%N)++(S1::repeat S3(sf_count 0%N)))). Qed.
Lemma sf_prefix_02 : csteps sc_tm(sf_count 47%N)c0=Some(sc_cut(sf_count 7%N)(sf_word 0%N (Some S1) 0%N)).
Proof. exact(sf_comp 22%N 25%N c0 (sc_cut(sf_count 2%N)(sf_word 2%N (Some S1) 0%N)) (sc_cut(sf_count 7%N)(sf_word 0%N (Some S1) 0%N)) sf_prefix_01 sf_edge_02). Qed.
Lemma sf_edge_03 : csteps sc_tm(sf_count 31%N)(sc_cut(sf_count 7%N)(sf_word 0%N (Some S1) 0%N))=Some(sc_cut(sf_count 11%N)(sf_word 0%N None 0%N)).
Proof. pose proof(sf_N_one 7%N (repeat S3(sf_count 0%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_03 : csteps sc_tm(sf_count 78%N)c0=Some(sc_cut(sf_count 11%N)(sf_word 0%N None 0%N)).
Proof. exact(sf_comp 47%N 31%N c0 (sc_cut(sf_count 7%N)(sf_word 0%N (Some S1) 0%N)) (sc_cut(sf_count 11%N)(sf_word 0%N None 0%N)) sf_prefix_02 sf_edge_03). Qed.
Lemma sf_edge_04 : csteps sc_tm(sf_count 44%N)(sc_cut(sf_count 11%N)(sf_word 0%N None 0%N))=Some(sc_cut(sf_count 2%N)(sf_word 13%N (Some S1) 0%N)).
Proof. pose proof(sf_N_blank 11%N)as H;sf_words;exact H. Qed.
Lemma sf_prefix_04 : csteps sc_tm(sf_count 122%N)c0=Some(sc_cut(sf_count 2%N)(sf_word 13%N (Some S1) 0%N)).
Proof. exact(sf_comp 78%N 44%N c0 (sc_cut(sf_count 11%N)(sf_word 0%N None 0%N)) (sc_cut(sf_count 2%N)(sf_word 13%N (Some S1) 0%N)) sf_prefix_03 sf_edge_04). Qed.
Lemma sf_edge_05 : csteps sc_tm(sf_count 300%N)(sc_cut(sf_count 2%N)(sf_word 13%N (Some S1) 0%N))=Some(sc_cut(sf_count 32%N)(sf_word 1%N (Some S1) 0%N)).
Proof. unfold sf_word. change(csteps sc_tm(sf_count 300%N)
 (sc_cut(sf_count 2%N)(repeat S3(sf_count(2*6+1)%N)++(S1::repeat S3(sf_count 0%N))))=
 Some(sc_cut(sf_count 32%N)(repeat S3(sf_count 1%N)++(S1::repeat S3(sf_count 0%N))))).
 rewrite sf_radd,<-app_assoc. exact(sf_N_bulk 6%N 2%N (repeat S3(sf_count 1%N)++(S1::repeat S3(sf_count 0%N)))). Qed.
Lemma sf_prefix_05 : csteps sc_tm(sf_count 422%N)c0=Some(sc_cut(sf_count 32%N)(sf_word 1%N (Some S1) 0%N)).
Proof. exact(sf_comp 122%N 300%N c0 (sc_cut(sf_count 2%N)(sf_word 13%N (Some S1) 0%N)) (sc_cut(sf_count 32%N)(sf_word 1%N (Some S1) 0%N)) sf_prefix_04 sf_edge_05). Qed.
Lemma sf_edge_06 : csteps sc_tm(sf_count 88%N)(sc_cut(sf_count 32%N)(sf_word 1%N (Some S1) 0%N))=Some(sc_cut(sf_count 2%N)(sf_word 34%N (Some S0) 1%N)).
Proof. pose proof(sf_N_three_one 32%N (repeat S3(sf_count 0%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_06 : csteps sc_tm(sf_count 510%N)c0=Some(sc_cut(sf_count 2%N)(sf_word 34%N (Some S0) 1%N)).
Proof. exact(sf_comp 422%N 88%N c0 (sc_cut(sf_count 32%N)(sf_word 1%N (Some S1) 0%N)) (sc_cut(sf_count 2%N)(sf_word 34%N (Some S0) 1%N)) sf_prefix_05 sf_edge_06). Qed.
Lemma sf_edge_07 : csteps sc_tm(sf_count 1785%N)(sc_cut(sf_count 2%N)(sf_word 34%N (Some S0) 1%N))=Some(sc_cut(sf_count 87%N)(sf_word 0%N (Some S0) 1%N)).
Proof. unfold sf_word. change(csteps sc_tm(sf_count 1785%N)
 (sc_cut(sf_count 2%N)(repeat S3(sf_count(2*17+0)%N)++(S0::repeat S3(sf_count 1%N))))=
 Some(sc_cut(sf_count 87%N)(repeat S3(sf_count 0%N)++(S0::repeat S3(sf_count 1%N))))).
 rewrite sf_radd,<-app_assoc. exact(sf_N_bulk 17%N 2%N (repeat S3(sf_count 0%N)++(S0::repeat S3(sf_count 1%N)))). Qed.
Lemma sf_prefix_07 : csteps sc_tm(sf_count 2295%N)c0=Some(sc_cut(sf_count 87%N)(sf_word 0%N (Some S0) 1%N)).
Proof. exact(sf_comp 510%N 1785%N c0 (sc_cut(sf_count 2%N)(sf_word 34%N (Some S0) 1%N)) (sc_cut(sf_count 87%N)(sf_word 0%N (Some S0) 1%N)) sf_prefix_06 sf_edge_07). Qed.
Lemma sf_edge_08 : csteps sc_tm(sf_count 196%N)(sc_cut(sf_count 87%N)(sf_word 0%N (Some S0) 1%N))=Some(sc_cut(sf_count 2%N)(sf_word 89%N (Some S1) 1%N)).
Proof. pose proof(sf_N_zero 87%N (repeat S3(sf_count 1%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_08 : csteps sc_tm(sf_count 2491%N)c0=Some(sc_cut(sf_count 2%N)(sf_word 89%N (Some S1) 1%N)).
Proof. exact(sf_comp 2295%N 196%N c0 (sc_cut(sf_count 87%N)(sf_word 0%N (Some S0) 1%N)) (sc_cut(sf_count 2%N)(sf_word 89%N (Some S1) 1%N)) sf_prefix_07 sf_edge_08). Qed.
Lemma sf_edge_09 : csteps sc_tm(sf_count 10560%N)(sc_cut(sf_count 2%N)(sf_word 89%N (Some S1) 1%N))=Some(sc_cut(sf_count 222%N)(sf_word 1%N (Some S1) 1%N)).
Proof. unfold sf_word. change(csteps sc_tm(sf_count 10560%N)
 (sc_cut(sf_count 2%N)(repeat S3(sf_count(2*44+1)%N)++(S1::repeat S3(sf_count 1%N))))=
 Some(sc_cut(sf_count 222%N)(repeat S3(sf_count 1%N)++(S1::repeat S3(sf_count 1%N))))).
 rewrite sf_radd,<-app_assoc. exact(sf_N_bulk 44%N 2%N (repeat S3(sf_count 1%N)++(S1::repeat S3(sf_count 1%N)))). Qed.
Lemma sf_prefix_09 : csteps sc_tm(sf_count 13051%N)c0=Some(sc_cut(sf_count 222%N)(sf_word 1%N (Some S1) 1%N)).
Proof. exact(sf_comp 2491%N 10560%N c0 (sc_cut(sf_count 2%N)(sf_word 89%N (Some S1) 1%N)) (sc_cut(sf_count 222%N)(sf_word 1%N (Some S1) 1%N)) sf_prefix_08 sf_edge_09). Qed.
Lemma sf_edge_10 : csteps sc_tm(sf_count 468%N)(sc_cut(sf_count 222%N)(sf_word 1%N (Some S1) 1%N))=Some(sc_cut(sf_count 2%N)(sf_word 224%N (Some S0) 2%N)).
Proof. pose proof(sf_N_three_one 222%N (repeat S3(sf_count 1%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_10 : csteps sc_tm(sf_count 13519%N)c0=Some(sc_cut(sf_count 2%N)(sf_word 224%N (Some S0) 2%N)).
Proof. exact(sf_comp 13051%N 468%N c0 (sc_cut(sf_count 222%N)(sf_word 1%N (Some S1) 1%N)) (sc_cut(sf_count 2%N)(sf_word 224%N (Some S0) 2%N)) sf_prefix_09 sf_edge_10). Qed.
Lemma sf_edge_11 : csteps sc_tm(sf_count 64960%N)(sc_cut(sf_count 2%N)(sf_word 224%N (Some S0) 2%N))=Some(sc_cut(sf_count 562%N)(sf_word 0%N (Some S0) 2%N)).
Proof. unfold sf_word. change(csteps sc_tm(sf_count 64960%N)
 (sc_cut(sf_count 2%N)(repeat S3(sf_count(2*112+0)%N)++(S0::repeat S3(sf_count 2%N))))=
 Some(sc_cut(sf_count 562%N)(repeat S3(sf_count 0%N)++(S0::repeat S3(sf_count 2%N))))).
 rewrite sf_radd,<-app_assoc. exact(sf_N_bulk 112%N 2%N (repeat S3(sf_count 0%N)++(S0::repeat S3(sf_count 2%N)))). Qed.
Lemma sf_prefix_11 : csteps sc_tm(sf_count 78479%N)c0=Some(sc_cut(sf_count 562%N)(sf_word 0%N (Some S0) 2%N)).
Proof. exact(sf_comp 13519%N 64960%N c0 (sc_cut(sf_count 2%N)(sf_word 224%N (Some S0) 2%N)) (sc_cut(sf_count 562%N)(sf_word 0%N (Some S0) 2%N)) sf_prefix_10 sf_edge_11). Qed.
Lemma sf_edge_12 : csteps sc_tm(sf_count 1146%N)(sc_cut(sf_count 562%N)(sf_word 0%N (Some S0) 2%N))=Some(sc_cut(sf_count 2%N)(sf_word 564%N (Some S1) 2%N)).
Proof. pose proof(sf_N_zero 562%N (repeat S3(sf_count 2%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_12 : csteps sc_tm(sf_count 79625%N)c0=Some(sc_cut(sf_count 2%N)(sf_word 564%N (Some S1) 2%N)).
Proof. exact(sf_comp 78479%N 1146%N c0 (sc_cut(sf_count 562%N)(sf_word 0%N (Some S0) 2%N)) (sc_cut(sf_count 2%N)(sf_word 564%N (Some S1) 2%N)) sf_prefix_11 sf_edge_12). Qed.
Lemma sf_edge_13 : csteps sc_tm(sf_count 403260%N)(sc_cut(sf_count 2%N)(sf_word 564%N (Some S1) 2%N))=Some(sc_cut(sf_count 1412%N)(sf_word 0%N (Some S1) 2%N)).
Proof. unfold sf_word. change(csteps sc_tm(sf_count 403260%N)
 (sc_cut(sf_count 2%N)(repeat S3(sf_count(2*282+0)%N)++(S1::repeat S3(sf_count 2%N))))=
 Some(sc_cut(sf_count 1412%N)(repeat S3(sf_count 0%N)++(S1::repeat S3(sf_count 2%N))))).
 rewrite sf_radd,<-app_assoc. exact(sf_N_bulk 282%N 2%N (repeat S3(sf_count 0%N)++(S1::repeat S3(sf_count 2%N)))). Qed.
Lemma sf_prefix_13 : csteps sc_tm(sf_count 482885%N)c0=Some(sc_cut(sf_count 1412%N)(sf_word 0%N (Some S1) 2%N)).
Proof. exact(sf_comp 79625%N 403260%N c0 (sc_cut(sf_count 2%N)(sf_word 564%N (Some S1) 2%N)) (sc_cut(sf_count 1412%N)(sf_word 0%N (Some S1) 2%N)) sf_prefix_12 sf_edge_13). Qed.
Lemma sf_edge_14 : csteps sc_tm(sf_count 2841%N)(sc_cut(sf_count 1412%N)(sf_word 0%N (Some S1) 2%N))=Some(sc_cut(sf_count 1416%N)(sf_word 2%N None 0%N)).
Proof. pose proof(sf_N_one 1412%N (repeat S3(sf_count 2%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_14 : csteps sc_tm(sf_count 485726%N)c0=Some(sc_cut(sf_count 1416%N)(sf_word 2%N None 0%N)).
Proof. exact(sf_comp 482885%N 2841%N c0 (sc_cut(sf_count 1412%N)(sf_word 0%N (Some S1) 2%N)) (sc_cut(sf_count 1416%N)(sf_word 2%N None 0%N)) sf_prefix_13 sf_edge_14). Qed.
Lemma sf_edge_15 : csteps sc_tm(sf_count 2853%N)(sc_cut(sf_count 1416%N)(sf_word 2%N None 0%N))=Some(sc_cut(sf_count 1421%N)(sf_word 0%N None 0%N)).
Proof. unfold sf_word. change(csteps sc_tm(sf_count 2853%N)
 (sc_cut(sf_count 1416%N)(repeat S3(sf_count(2*1+0)%N)++([])))=
 Some(sc_cut(sf_count 1421%N)(repeat S3(sf_count 0%N)++([])))).
 rewrite sf_radd,<-app_assoc. exact(sf_N_bulk 1%N 1416%N (repeat S3(sf_count 0%N)++([]))). Qed.
Lemma sf_prefix_15 : csteps sc_tm(sf_count 488579%N)c0=Some(sc_cut(sf_count 1421%N)(sf_word 0%N None 0%N)).
Proof. exact(sf_comp 485726%N 2853%N c0 (sc_cut(sf_count 1416%N)(sf_word 2%N None 0%N)) (sc_cut(sf_count 1421%N)(sf_word 0%N None 0%N)) sf_prefix_14 sf_edge_15). Qed.
Lemma sf_edge_16 : csteps sc_tm(sf_count 2864%N)(sc_cut(sf_count 1421%N)(sf_word 0%N None 0%N))=Some(sc_cut(sf_count 2%N)(sf_word 1423%N (Some S1) 0%N)).
Proof. pose proof(sf_N_blank 1421%N)as H;sf_words;exact H. Qed.
Lemma sf_prefix_16 : csteps sc_tm(sf_count 491443%N)c0=Some(sc_cut(sf_count 2%N)(sf_word 1423%N (Some S1) 0%N)).
Proof. exact(sf_comp 488579%N 2864%N c0 (sc_cut(sf_count 1421%N)(sf_word 0%N None 0%N)) (sc_cut(sf_count 2%N)(sf_word 1423%N (Some S1) 0%N)) sf_prefix_15 sf_edge_16). Qed.
Lemma sf_edge_17 : csteps sc_tm(sf_count 2541825%N)(sc_cut(sf_count 2%N)(sf_word 1423%N (Some S1) 0%N))=Some(sc_cut(sf_count 3557%N)(sf_word 1%N (Some S1) 0%N)).
Proof. unfold sf_word. change(csteps sc_tm(sf_count 2541825%N)
 (sc_cut(sf_count 2%N)(repeat S3(sf_count(2*711+1)%N)++(S1::repeat S3(sf_count 0%N))))=
 Some(sc_cut(sf_count 3557%N)(repeat S3(sf_count 1%N)++(S1::repeat S3(sf_count 0%N))))).
 rewrite sf_radd,<-app_assoc. exact(sf_N_bulk 711%N 2%N (repeat S3(sf_count 1%N)++(S1::repeat S3(sf_count 0%N)))). Qed.
Lemma sf_prefix_17 : csteps sc_tm(sf_count 3033268%N)c0=Some(sc_cut(sf_count 3557%N)(sf_word 1%N (Some S1) 0%N)).
Proof. exact(sf_comp 491443%N 2541825%N c0 (sc_cut(sf_count 2%N)(sf_word 1423%N (Some S1) 0%N)) (sc_cut(sf_count 3557%N)(sf_word 1%N (Some S1) 0%N)) sf_prefix_16 sf_edge_17). Qed.
Lemma sf_edge_18 : csteps sc_tm(sf_count 7138%N)(sc_cut(sf_count 3557%N)(sf_word 1%N (Some S1) 0%N))=Some(sc_cut(sf_count 2%N)(sf_word 3559%N (Some S0) 1%N)).
Proof. pose proof(sf_N_three_one 3557%N (repeat S3(sf_count 0%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_18 : csteps sc_tm(sf_count 3040406%N)c0=Some(sc_cut(sf_count 2%N)(sf_word 3559%N (Some S0) 1%N)).
Proof. exact(sf_comp 3033268%N 7138%N c0 (sc_cut(sf_count 3557%N)(sf_word 1%N (Some S1) 0%N)) (sc_cut(sf_count 2%N)(sf_word 3559%N (Some S0) 1%N)) sf_prefix_17 sf_edge_18). Qed.
Lemma sf_edge_19 : csteps sc_tm(sf_count 15859785%N)(sc_cut(sf_count 2%N)(sf_word 3559%N (Some S0) 1%N))=Some(sc_cut(sf_count 8897%N)(sf_word 1%N (Some S0) 1%N)).
Proof. unfold sf_word. change(csteps sc_tm(sf_count 15859785%N)
 (sc_cut(sf_count 2%N)(repeat S3(sf_count(2*1779+1)%N)++(S0::repeat S3(sf_count 1%N))))=
 Some(sc_cut(sf_count 8897%N)(repeat S3(sf_count 1%N)++(S0::repeat S3(sf_count 1%N))))).
 rewrite sf_radd,<-app_assoc. exact(sf_N_bulk 1779%N 2%N (repeat S3(sf_count 1%N)++(S0::repeat S3(sf_count 1%N)))). Qed.
Lemma sf_prefix_19 : csteps sc_tm(sf_count 18900191%N)c0=Some(sc_cut(sf_count 8897%N)(sf_word 1%N (Some S0) 1%N)).
Proof. exact(sf_comp 3040406%N 15859785%N c0 (sc_cut(sf_count 2%N)(sf_word 3559%N (Some S0) 1%N)) (sc_cut(sf_count 8897%N)(sf_word 1%N (Some S0) 1%N)) sf_prefix_18 sf_edge_19). Qed.
Lemma sf_edge_20 : csteps sc_tm(sf_count 8919%N)(sc_cut(sf_count 8897%N)(sf_word 1%N (Some S0) 1%N))=Some(sc_Q(sf_count 8903%N)(sf_word 0%N None 0%N)).
Proof. pose proof(sf_N_bridge 8897%N [])as H;sf_words;exact H. Qed.
Lemma sf_prefix_20 : csteps sc_tm(sf_count 18909110%N)c0=Some(sc_Q(sf_count 8903%N)(sf_word 0%N None 0%N)).
Proof. exact(sf_comp 18900191%N 8919%N c0 (sc_cut(sf_count 8897%N)(sf_word 1%N (Some S0) 1%N)) (sc_Q(sf_count 8903%N)(sf_word 0%N None 0%N)) sf_prefix_19 sf_edge_20). Qed.
Lemma sf_edge_21 : csteps sc_tm(sf_count 8909%N)(sc_Q(sf_count 8903%N)(sf_word 0%N None 0%N))=Some(sc_cut(sf_count 2%N)(sf_word 8902%N (Some S1) 0%N)).
Proof. pose proof(sf_N_Qblank 8902%N)as H;sf_words;exact H. Qed.
Lemma sf_prefix_21 : csteps sc_tm(sf_count 18918019%N)c0=Some(sc_cut(sf_count 2%N)(sf_word 8902%N (Some S1) 0%N)).
Proof. exact(sf_comp 18909110%N 8909%N c0 (sc_Q(sf_count 8903%N)(sf_word 0%N None 0%N)) (sc_cut(sf_count 2%N)(sf_word 8902%N (Some S1) 0%N)) sf_prefix_20 sf_edge_21). Qed.
Lemma sf_edge_22 : csteps sc_tm(sf_count 99146025%N)(sc_cut(sf_count 2%N)(sf_word 8902%N (Some S1) 0%N))=Some(sc_cut(sf_count 22257%N)(sf_word 0%N (Some S1) 0%N)).
Proof. unfold sf_word. change(csteps sc_tm(sf_count 99146025%N)
 (sc_cut(sf_count 2%N)(repeat S3(sf_count(2*4451+0)%N)++(S1::repeat S3(sf_count 0%N))))=
 Some(sc_cut(sf_count 22257%N)(repeat S3(sf_count 0%N)++(S1::repeat S3(sf_count 0%N))))).
 rewrite sf_radd,<-app_assoc. exact(sf_N_bulk 4451%N 2%N (repeat S3(sf_count 0%N)++(S1::repeat S3(sf_count 0%N)))). Qed.
Lemma sf_prefix_22 : csteps sc_tm(sf_count 118064044%N)c0=Some(sc_cut(sf_count 22257%N)(sf_word 0%N (Some S1) 0%N)).
Proof. exact(sf_comp 18918019%N 99146025%N c0 (sc_cut(sf_count 2%N)(sf_word 8902%N (Some S1) 0%N)) (sc_cut(sf_count 22257%N)(sf_word 0%N (Some S1) 0%N)) sf_prefix_21 sf_edge_22). Qed.
Lemma sf_edge_23 : csteps sc_tm(sf_count 44531%N)(sc_cut(sf_count 22257%N)(sf_word 0%N (Some S1) 0%N))=Some(sc_cut(sf_count 22261%N)(sf_word 0%N None 0%N)).
Proof. pose proof(sf_N_one 22257%N (repeat S3(sf_count 0%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_23 : csteps sc_tm(sf_count 118108575%N)c0=Some(sc_cut(sf_count 22261%N)(sf_word 0%N None 0%N)).
Proof. exact(sf_comp 118064044%N 44531%N c0 (sc_cut(sf_count 22257%N)(sf_word 0%N (Some S1) 0%N)) (sc_cut(sf_count 22261%N)(sf_word 0%N None 0%N)) sf_prefix_22 sf_edge_23). Qed.
Lemma sf_edge_24 : csteps sc_tm(sf_count 44544%N)(sc_cut(sf_count 22261%N)(sf_word 0%N None 0%N))=Some(sc_cut(sf_count 2%N)(sf_word 22263%N (Some S1) 0%N)).
Proof. pose proof(sf_N_blank 22261%N)as H;sf_words;exact H. Qed.
Lemma sf_prefix_24 : csteps sc_tm(sf_count 118153119%N)c0=Some(sc_cut(sf_count 2%N)(sf_word 22263%N (Some S1) 0%N)).
Proof. exact(sf_comp 118108575%N 44544%N c0 (sc_cut(sf_count 22261%N)(sf_word 0%N None 0%N)) (sc_cut(sf_count 2%N)(sf_word 22263%N (Some S1) 0%N)) sf_prefix_23 sf_edge_24). Qed.
Lemma sf_edge_25 : csteps sc_tm(sf_count 619718425%N)(sc_cut(sf_count 2%N)(sf_word 22263%N (Some S1) 0%N))=Some(sc_cut(sf_count 55657%N)(sf_word 1%N (Some S1) 0%N)).
Proof. unfold sf_word. change(csteps sc_tm(sf_count 619718425%N)
 (sc_cut(sf_count 2%N)(repeat S3(sf_count(2*11131+1)%N)++(S1::repeat S3(sf_count 0%N))))=
 Some(sc_cut(sf_count 55657%N)(repeat S3(sf_count 1%N)++(S1::repeat S3(sf_count 0%N))))).
 rewrite sf_radd,<-app_assoc. exact(sf_N_bulk 11131%N 2%N (repeat S3(sf_count 1%N)++(S1::repeat S3(sf_count 0%N)))). Qed.
Lemma sf_prefix_25 : csteps sc_tm(sf_count 737871544%N)c0=Some(sc_cut(sf_count 55657%N)(sf_word 1%N (Some S1) 0%N)).
Proof. exact(sf_comp 118153119%N 619718425%N c0 (sc_cut(sf_count 2%N)(sf_word 22263%N (Some S1) 0%N)) (sc_cut(sf_count 55657%N)(sf_word 1%N (Some S1) 0%N)) sf_prefix_24 sf_edge_25). Qed.
Lemma sf_edge_26 : csteps sc_tm(sf_count 111338%N)(sc_cut(sf_count 55657%N)(sf_word 1%N (Some S1) 0%N))=Some(sc_cut(sf_count 2%N)(sf_word 55659%N (Some S0) 1%N)).
Proof. pose proof(sf_N_three_one 55657%N (repeat S3(sf_count 0%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_26 : csteps sc_tm(sf_count 737982882%N)c0=Some(sc_cut(sf_count 2%N)(sf_word 55659%N (Some S0) 1%N)).
Proof. exact(sf_comp 737871544%N 111338%N c0 (sc_cut(sf_count 55657%N)(sf_word 1%N (Some S1) 0%N)) (sc_cut(sf_count 2%N)(sf_word 55659%N (Some S0) 1%N)) sf_prefix_25 sf_edge_26). Qed.
Lemma sf_edge_27 : csteps sc_tm(sf_count 3872822785%N)(sc_cut(sf_count 2%N)(sf_word 55659%N (Some S0) 1%N))=Some(sc_cut(sf_count 139147%N)(sf_word 1%N (Some S0) 1%N)).
Proof. unfold sf_word. change(csteps sc_tm(sf_count 3872822785%N)
 (sc_cut(sf_count 2%N)(repeat S3(sf_count(2*27829+1)%N)++(S0::repeat S3(sf_count 1%N))))=
 Some(sc_cut(sf_count 139147%N)(repeat S3(sf_count 1%N)++(S0::repeat S3(sf_count 1%N))))).
 rewrite sf_radd,<-app_assoc. exact(sf_N_bulk 27829%N 2%N (repeat S3(sf_count 1%N)++(S0::repeat S3(sf_count 1%N)))). Qed.
Lemma sf_prefix_27 : csteps sc_tm(sf_count 4610805667%N)c0=Some(sc_cut(sf_count 139147%N)(sf_word 1%N (Some S0) 1%N)).
Proof. exact(sf_comp 737982882%N 3872822785%N c0 (sc_cut(sf_count 2%N)(sf_word 55659%N (Some S0) 1%N)) (sc_cut(sf_count 139147%N)(sf_word 1%N (Some S0) 1%N)) sf_prefix_26 sf_edge_27). Qed.
Lemma sf_edge_28 : csteps sc_tm(sf_count 139169%N)(sc_cut(sf_count 139147%N)(sf_word 1%N (Some S0) 1%N))=Some(sc_Q(sf_count 139153%N)(sf_word 0%N None 0%N)).
Proof. pose proof(sf_N_bridge 139147%N [])as H;sf_words;exact H. Qed.
Lemma sf_prefix_28 : csteps sc_tm(sf_count 4610944836%N)c0=Some(sc_Q(sf_count 139153%N)(sf_word 0%N None 0%N)).
Proof. exact(sf_comp 4610805667%N 139169%N c0 (sc_cut(sf_count 139147%N)(sf_word 1%N (Some S0) 1%N)) (sc_Q(sf_count 139153%N)(sf_word 0%N None 0%N)) sf_prefix_27 sf_edge_28). Qed.
Lemma sf_edge_29 : csteps sc_tm(sf_count 139159%N)(sc_Q(sf_count 139153%N)(sf_word 0%N None 0%N))=Some(sc_cut(sf_count 2%N)(sf_word 139152%N (Some S1) 0%N)).
Proof. pose proof(sf_N_Qblank 139152%N)as H;sf_words;exact H. Qed.
Lemma sf_prefix_29 : csteps sc_tm(sf_count 4611083995%N)c0=Some(sc_cut(sf_count 2%N)(sf_word 139152%N (Some S1) 0%N)).
Proof. exact(sf_comp 4610944836%N 139159%N c0 (sc_Q(sf_count 139153%N)(sf_word 0%N None 0%N)) (sc_cut(sf_count 2%N)(sf_word 139152%N (Some S1) 0%N)) sf_prefix_28 sf_edge_29). Qed.
Lemma sf_edge_30 : csteps sc_tm(sf_count 24205490400%N)(sc_cut(sf_count 2%N)(sf_word 139152%N (Some S1) 0%N))=Some(sc_cut(sf_count 347882%N)(sf_word 0%N (Some S1) 0%N)).
Proof. unfold sf_word. change(csteps sc_tm(sf_count 24205490400%N)
 (sc_cut(sf_count 2%N)(repeat S3(sf_count(2*69576+0)%N)++(S1::repeat S3(sf_count 0%N))))=
 Some(sc_cut(sf_count 347882%N)(repeat S3(sf_count 0%N)++(S1::repeat S3(sf_count 0%N))))).
 rewrite sf_radd,<-app_assoc. exact(sf_N_bulk 69576%N 2%N (repeat S3(sf_count 0%N)++(S1::repeat S3(sf_count 0%N)))). Qed.
Lemma sf_prefix_30 : csteps sc_tm(sf_count 28816574395%N)c0=Some(sc_cut(sf_count 347882%N)(sf_word 0%N (Some S1) 0%N)).
Proof. exact(sf_comp 4611083995%N 24205490400%N c0 (sc_cut(sf_count 2%N)(sf_word 139152%N (Some S1) 0%N)) (sc_cut(sf_count 347882%N)(sf_word 0%N (Some S1) 0%N)) sf_prefix_29 sf_edge_30). Qed.
Lemma sf_edge_31 : csteps sc_tm(sf_count 695781%N)(sc_cut(sf_count 347882%N)(sf_word 0%N (Some S1) 0%N))=Some(sc_cut(sf_count 347886%N)(sf_word 0%N None 0%N)).
Proof. pose proof(sf_N_one 347882%N (repeat S3(sf_count 0%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_31 : csteps sc_tm(sf_count 28817270176%N)c0=Some(sc_cut(sf_count 347886%N)(sf_word 0%N None 0%N)).
Proof. exact(sf_comp 28816574395%N 695781%N c0 (sc_cut(sf_count 347882%N)(sf_word 0%N (Some S1) 0%N)) (sc_cut(sf_count 347886%N)(sf_word 0%N None 0%N)) sf_prefix_30 sf_edge_31). Qed.
Lemma sf_edge_32 : csteps sc_tm(sf_count 695794%N)(sc_cut(sf_count 347886%N)(sf_word 0%N None 0%N))=Some(sc_cut(sf_count 2%N)(sf_word 347888%N (Some S1) 0%N)).
Proof. pose proof(sf_N_blank 347886%N)as H;sf_words;exact H. Qed.
Lemma sf_prefix_32 : csteps sc_tm(sf_count 28817965970%N)c0=Some(sc_cut(sf_count 2%N)(sf_word 347888%N (Some S1) 0%N)).
Proof. exact(sf_comp 28817270176%N 695794%N c0 (sc_cut(sf_count 347886%N)(sf_word 0%N None 0%N)) (sc_cut(sf_count 2%N)(sf_word 347888%N (Some S1) 0%N)) sf_prefix_31 sf_edge_32). Qed.
Lemma sf_edge_33 : csteps sc_tm(sf_count 151286054560%N)(sc_cut(sf_count 2%N)(sf_word 347888%N (Some S1) 0%N))=Some(sc_cut(sf_count 869722%N)(sf_word 0%N (Some S1) 0%N)).
Proof. unfold sf_word. change(csteps sc_tm(sf_count 151286054560%N)
 (sc_cut(sf_count 2%N)(repeat S3(sf_count(2*173944+0)%N)++(S1::repeat S3(sf_count 0%N))))=
 Some(sc_cut(sf_count 869722%N)(repeat S3(sf_count 0%N)++(S1::repeat S3(sf_count 0%N))))).
 rewrite sf_radd,<-app_assoc. exact(sf_N_bulk 173944%N 2%N (repeat S3(sf_count 0%N)++(S1::repeat S3(sf_count 0%N)))). Qed.
Lemma sf_prefix_33 : csteps sc_tm(sf_count 180104020530%N)c0=Some(sc_cut(sf_count 869722%N)(sf_word 0%N (Some S1) 0%N)).
Proof. exact(sf_comp 28817965970%N 151286054560%N c0 (sc_cut(sf_count 2%N)(sf_word 347888%N (Some S1) 0%N)) (sc_cut(sf_count 869722%N)(sf_word 0%N (Some S1) 0%N)) sf_prefix_32 sf_edge_33). Qed.
Lemma sf_edge_34 : csteps sc_tm(sf_count 1739461%N)(sc_cut(sf_count 869722%N)(sf_word 0%N (Some S1) 0%N))=Some(sc_cut(sf_count 869726%N)(sf_word 0%N None 0%N)).
Proof. pose proof(sf_N_one 869722%N (repeat S3(sf_count 0%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_34 : csteps sc_tm(sf_count 180105759991%N)c0=Some(sc_cut(sf_count 869726%N)(sf_word 0%N None 0%N)).
Proof. exact(sf_comp 180104020530%N 1739461%N c0 (sc_cut(sf_count 869722%N)(sf_word 0%N (Some S1) 0%N)) (sc_cut(sf_count 869726%N)(sf_word 0%N None 0%N)) sf_prefix_33 sf_edge_34). Qed.
Lemma sf_edge_35 : csteps sc_tm(sf_count 1739474%N)(sc_cut(sf_count 869726%N)(sf_word 0%N None 0%N))=Some(sc_cut(sf_count 2%N)(sf_word 869728%N (Some S1) 0%N)).
Proof. pose proof(sf_N_blank 869726%N)as H;sf_words;exact H. Qed.
Lemma sf_prefix_35 : csteps sc_tm(sf_count 180107499465%N)c0=Some(sc_cut(sf_count 2%N)(sf_word 869728%N (Some S1) 0%N)).
Proof. exact(sf_comp 180105759991%N 1739474%N c0 (sc_cut(sf_count 869726%N)(sf_word 0%N None 0%N)) (sc_cut(sf_count 2%N)(sf_word 869728%N (Some S1) 0%N)) sf_prefix_34 sf_edge_35). Qed.
Lemma sf_edge_36 : csteps sc_tm(sf_count 945542189760%N)(sc_cut(sf_count 2%N)(sf_word 869728%N (Some S1) 0%N))=Some(sc_cut(sf_count 2174322%N)(sf_word 0%N (Some S1) 0%N)).
Proof. unfold sf_word. change(csteps sc_tm(sf_count 945542189760%N)
 (sc_cut(sf_count 2%N)(repeat S3(sf_count(2*434864+0)%N)++(S1::repeat S3(sf_count 0%N))))=
 Some(sc_cut(sf_count 2174322%N)(repeat S3(sf_count 0%N)++(S1::repeat S3(sf_count 0%N))))).
 rewrite sf_radd,<-app_assoc. exact(sf_N_bulk 434864%N 2%N (repeat S3(sf_count 0%N)++(S1::repeat S3(sf_count 0%N)))). Qed.
Lemma sf_prefix_36 : csteps sc_tm(sf_count 1125649689225%N)c0=Some(sc_cut(sf_count 2174322%N)(sf_word 0%N (Some S1) 0%N)).
Proof. exact(sf_comp 180107499465%N 945542189760%N c0 (sc_cut(sf_count 2%N)(sf_word 869728%N (Some S1) 0%N)) (sc_cut(sf_count 2174322%N)(sf_word 0%N (Some S1) 0%N)) sf_prefix_35 sf_edge_36). Qed.
Lemma sf_edge_37 : csteps sc_tm(sf_count 4348661%N)(sc_cut(sf_count 2174322%N)(sf_word 0%N (Some S1) 0%N))=Some(sc_cut(sf_count 2174326%N)(sf_word 0%N None 0%N)).
Proof. pose proof(sf_N_one 2174322%N (repeat S3(sf_count 0%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_37 : csteps sc_tm(sf_count 1125654037886%N)c0=Some(sc_cut(sf_count 2174326%N)(sf_word 0%N None 0%N)).
Proof. exact(sf_comp 1125649689225%N 4348661%N c0 (sc_cut(sf_count 2174322%N)(sf_word 0%N (Some S1) 0%N)) (sc_cut(sf_count 2174326%N)(sf_word 0%N None 0%N)) sf_prefix_36 sf_edge_37). Qed.
Lemma sf_edge_38 : csteps sc_tm(sf_count 4348674%N)(sc_cut(sf_count 2174326%N)(sf_word 0%N None 0%N))=Some(sc_cut(sf_count 2%N)(sf_word 2174328%N (Some S1) 0%N)).
Proof. pose proof(sf_N_blank 2174326%N)as H;sf_words;exact H. Qed.
Lemma sf_prefix_38 : csteps sc_tm(sf_count 1125658386560%N)c0=Some(sc_cut(sf_count 2%N)(sf_word 2174328%N (Some S1) 0%N)).
Proof. exact(sf_comp 1125654037886%N 4348674%N c0 (sc_cut(sf_count 2174326%N)(sf_word 0%N None 0%N)) (sc_cut(sf_count 2%N)(sf_word 2174328%N (Some S1) 0%N)) sf_prefix_37 sf_edge_38). Qed.
Lemma sf_edge_39 : csteps sc_tm(sf_count 5909649557760%N)(sc_cut(sf_count 2%N)(sf_word 2174328%N (Some S1) 0%N))=Some(sc_cut(sf_count 5435822%N)(sf_word 0%N (Some S1) 0%N)).
Proof. unfold sf_word. change(csteps sc_tm(sf_count 5909649557760%N)
 (sc_cut(sf_count 2%N)(repeat S3(sf_count(2*1087164+0)%N)++(S1::repeat S3(sf_count 0%N))))=
 Some(sc_cut(sf_count 5435822%N)(repeat S3(sf_count 0%N)++(S1::repeat S3(sf_count 0%N))))).
 rewrite sf_radd,<-app_assoc. exact(sf_N_bulk 1087164%N 2%N (repeat S3(sf_count 0%N)++(S1::repeat S3(sf_count 0%N)))). Qed.
Lemma sf_prefix_39 : csteps sc_tm(sf_count 7035307944320%N)c0=Some(sc_cut(sf_count 5435822%N)(sf_word 0%N (Some S1) 0%N)).
Proof. exact(sf_comp 1125658386560%N 5909649557760%N c0 (sc_cut(sf_count 2%N)(sf_word 2174328%N (Some S1) 0%N)) (sc_cut(sf_count 5435822%N)(sf_word 0%N (Some S1) 0%N)) sf_prefix_38 sf_edge_39). Qed.
Lemma sf_edge_40 : csteps sc_tm(sf_count 10871661%N)(sc_cut(sf_count 5435822%N)(sf_word 0%N (Some S1) 0%N))=Some(sc_cut(sf_count 5435826%N)(sf_word 0%N None 0%N)).
Proof. pose proof(sf_N_one 5435822%N (repeat S3(sf_count 0%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_40 : csteps sc_tm(sf_count 7035318815981%N)c0=Some(sc_cut(sf_count 5435826%N)(sf_word 0%N None 0%N)).
Proof. exact(sf_comp 7035307944320%N 10871661%N c0 (sc_cut(sf_count 5435822%N)(sf_word 0%N (Some S1) 0%N)) (sc_cut(sf_count 5435826%N)(sf_word 0%N None 0%N)) sf_prefix_39 sf_edge_40). Qed.
Lemma sf_edge_41 : csteps sc_tm(sf_count 10871674%N)(sc_cut(sf_count 5435826%N)(sf_word 0%N None 0%N))=Some(sc_cut(sf_count 2%N)(sf_word 5435828%N (Some S1) 0%N)).
Proof. pose proof(sf_N_blank 5435826%N)as H;sf_words;exact H. Qed.
Lemma sf_prefix_41 : csteps sc_tm(sf_count 7035329687655%N)c0=Some(sc_cut(sf_count 2%N)(sf_word 5435828%N (Some S1) 0%N)).
Proof. exact(sf_comp 7035318815981%N 10871674%N c0 (sc_cut(sf_count 5435826%N)(sf_word 0%N None 0%N)) (sc_cut(sf_count 2%N)(sf_word 5435828%N (Some S1) 0%N)) sf_prefix_40 sf_edge_41). Qed.
Lemma sf_edge_42 : csteps sc_tm(sf_count 36935336915260%N)(sc_cut(sf_count 2%N)(sf_word 5435828%N (Some S1) 0%N))=Some(sc_cut(sf_count 13589572%N)(sf_word 0%N (Some S1) 0%N)).
Proof. unfold sf_word. change(csteps sc_tm(sf_count 36935336915260%N)
 (sc_cut(sf_count 2%N)(repeat S3(sf_count(2*2717914+0)%N)++(S1::repeat S3(sf_count 0%N))))=
 Some(sc_cut(sf_count 13589572%N)(repeat S3(sf_count 0%N)++(S1::repeat S3(sf_count 0%N))))).
 rewrite sf_radd,<-app_assoc. exact(sf_N_bulk 2717914%N 2%N (repeat S3(sf_count 0%N)++(S1::repeat S3(sf_count 0%N)))). Qed.
Lemma sf_prefix_42 : csteps sc_tm(sf_count 43970666602915%N)c0=Some(sc_cut(sf_count 13589572%N)(sf_word 0%N (Some S1) 0%N)).
Proof. exact(sf_comp 7035329687655%N 36935336915260%N c0 (sc_cut(sf_count 2%N)(sf_word 5435828%N (Some S1) 0%N)) (sc_cut(sf_count 13589572%N)(sf_word 0%N (Some S1) 0%N)) sf_prefix_41 sf_edge_42). Qed.
Lemma sf_edge_43 : csteps sc_tm(sf_count 27179161%N)(sc_cut(sf_count 13589572%N)(sf_word 0%N (Some S1) 0%N))=Some(sc_cut(sf_count 13589576%N)(sf_word 0%N None 0%N)).
Proof. pose proof(sf_N_one 13589572%N (repeat S3(sf_count 0%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_43 : csteps sc_tm(sf_count 43970693782076%N)c0=Some(sc_cut(sf_count 13589576%N)(sf_word 0%N None 0%N)).
Proof. exact(sf_comp 43970666602915%N 27179161%N c0 (sc_cut(sf_count 13589572%N)(sf_word 0%N (Some S1) 0%N)) (sc_cut(sf_count 13589576%N)(sf_word 0%N None 0%N)) sf_prefix_42 sf_edge_43). Qed.
Lemma sf_edge_44 : csteps sc_tm(sf_count 27179174%N)(sc_cut(sf_count 13589576%N)(sf_word 0%N None 0%N))=Some(sc_cut(sf_count 2%N)(sf_word 13589578%N (Some S1) 0%N)).
Proof. pose proof(sf_N_blank 13589576%N)as H;sf_words;exact H. Qed.
Lemma sf_prefix_44 : csteps sc_tm(sf_count 43970720961250%N)c0=Some(sc_cut(sf_count 2%N)(sf_word 13589578%N (Some S1) 0%N)).
Proof. exact(sf_comp 43970693782076%N 27179174%N c0 (sc_cut(sf_count 13589576%N)(sf_word 0%N None 0%N)) (sc_cut(sf_count 2%N)(sf_word 13589578%N (Some S1) 0%N)) sf_prefix_43 sf_edge_44). Qed.
Lemma sf_edge_45 : csteps sc_tm(sf_count 230845923668385%N)(sc_cut(sf_count 2%N)(sf_word 13589578%N (Some S1) 0%N))=Some(sc_cut(sf_count 33973947%N)(sf_word 0%N (Some S1) 0%N)).
Proof. unfold sf_word. change(csteps sc_tm(sf_count 230845923668385%N)
 (sc_cut(sf_count 2%N)(repeat S3(sf_count(2*6794789+0)%N)++(S1::repeat S3(sf_count 0%N))))=
 Some(sc_cut(sf_count 33973947%N)(repeat S3(sf_count 0%N)++(S1::repeat S3(sf_count 0%N))))).
 rewrite sf_radd,<-app_assoc. exact(sf_N_bulk 6794789%N 2%N (repeat S3(sf_count 0%N)++(S1::repeat S3(sf_count 0%N)))). Qed.
Lemma sf_prefix_45 : csteps sc_tm(sf_count 274816644629635%N)c0=Some(sc_cut(sf_count 33973947%N)(sf_word 0%N (Some S1) 0%N)).
Proof. exact(sf_comp 43970720961250%N 230845923668385%N c0 (sc_cut(sf_count 2%N)(sf_word 13589578%N (Some S1) 0%N)) (sc_cut(sf_count 33973947%N)(sf_word 0%N (Some S1) 0%N)) sf_prefix_44 sf_edge_45). Qed.
Lemma sf_edge_46 : csteps sc_tm(sf_count 67947911%N)(sc_cut(sf_count 33973947%N)(sf_word 0%N (Some S1) 0%N))=Some(sc_cut(sf_count 33973951%N)(sf_word 0%N None 0%N)).
Proof. pose proof(sf_N_one 33973947%N (repeat S3(sf_count 0%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_46 : csteps sc_tm(sf_count 274816712577546%N)c0=Some(sc_cut(sf_count 33973951%N)(sf_word 0%N None 0%N)).
Proof. exact(sf_comp 274816644629635%N 67947911%N c0 (sc_cut(sf_count 33973947%N)(sf_word 0%N (Some S1) 0%N)) (sc_cut(sf_count 33973951%N)(sf_word 0%N None 0%N)) sf_prefix_45 sf_edge_46). Qed.
Lemma sf_edge_47 : csteps sc_tm(sf_count 67947924%N)(sc_cut(sf_count 33973951%N)(sf_word 0%N None 0%N))=Some(sc_cut(sf_count 2%N)(sf_word 33973953%N (Some S1) 0%N)).
Proof. pose proof(sf_N_blank 33973951%N)as H;sf_words;exact H. Qed.
Lemma sf_prefix_47 : csteps sc_tm(sf_count 274816780525470%N)c0=Some(sc_cut(sf_count 2%N)(sf_word 33973953%N (Some S1) 0%N)).
Proof. exact(sf_comp 274816712577546%N 67947924%N c0 (sc_cut(sf_count 33973951%N)(sf_word 0%N None 0%N)) (sc_cut(sf_count 2%N)(sf_word 33973953%N (Some S1) 0%N)) sf_prefix_46 sf_edge_47). Qed.
Lemma sf_edge_48 : csteps sc_tm(sf_count 1442787107862400%N)(sc_cut(sf_count 2%N)(sf_word 33973953%N (Some S1) 0%N))=Some(sc_cut(sf_count 84934882%N)(sf_word 1%N (Some S1) 0%N)).
Proof. unfold sf_word. change(csteps sc_tm(sf_count 1442787107862400%N)
 (sc_cut(sf_count 2%N)(repeat S3(sf_count(2*16986976+1)%N)++(S1::repeat S3(sf_count 0%N))))=
 Some(sc_cut(sf_count 84934882%N)(repeat S3(sf_count 1%N)++(S1::repeat S3(sf_count 0%N))))).
 rewrite sf_radd,<-app_assoc. exact(sf_N_bulk 16986976%N 2%N (repeat S3(sf_count 1%N)++(S1::repeat S3(sf_count 0%N)))). Qed.
Lemma sf_prefix_48 : csteps sc_tm(sf_count 1717603888387870%N)c0=Some(sc_cut(sf_count 84934882%N)(sf_word 1%N (Some S1) 0%N)).
Proof. exact(sf_comp 274816780525470%N 1442787107862400%N c0 (sc_cut(sf_count 2%N)(sf_word 33973953%N (Some S1) 0%N)) (sc_cut(sf_count 84934882%N)(sf_word 1%N (Some S1) 0%N)) sf_prefix_47 sf_edge_48). Qed.
Lemma sf_edge_49 : csteps sc_tm(sf_count 169869788%N)(sc_cut(sf_count 84934882%N)(sf_word 1%N (Some S1) 0%N))=Some(sc_cut(sf_count 2%N)(sf_word 84934884%N (Some S0) 1%N)).
Proof. pose proof(sf_N_three_one 84934882%N (repeat S3(sf_count 0%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_49 : csteps sc_tm(sf_count 1717604058257658%N)c0=Some(sc_cut(sf_count 2%N)(sf_word 84934884%N (Some S0) 1%N)).
Proof. exact(sf_comp 1717603888387870%N 169869788%N c0 (sc_cut(sf_count 84934882%N)(sf_word 1%N (Some S1) 0%N)) (sc_cut(sf_count 2%N)(sf_word 84934884%N (Some S0) 1%N)) sf_prefix_48 sf_edge_49). Qed.
Lemma sf_edge_50 : csteps sc_tm(sf_count 9017418999465660%N)(sc_cut(sf_count 2%N)(sf_word 84934884%N (Some S0) 1%N))=Some(sc_cut(sf_count 212337212%N)(sf_word 0%N (Some S0) 1%N)).
Proof. unfold sf_word. change(csteps sc_tm(sf_count 9017418999465660%N)
 (sc_cut(sf_count 2%N)(repeat S3(sf_count(2*42467442+0)%N)++(S0::repeat S3(sf_count 1%N))))=
 Some(sc_cut(sf_count 212337212%N)(repeat S3(sf_count 0%N)++(S0::repeat S3(sf_count 1%N))))).
 rewrite sf_radd,<-app_assoc. exact(sf_N_bulk 42467442%N 2%N (repeat S3(sf_count 0%N)++(S0::repeat S3(sf_count 1%N)))). Qed.
Lemma sf_prefix_50 : csteps sc_tm(sf_count 10735023057723318%N)c0=Some(sc_cut(sf_count 212337212%N)(sf_word 0%N (Some S0) 1%N)).
Proof. exact(sf_comp 1717604058257658%N 9017418999465660%N c0 (sc_cut(sf_count 2%N)(sf_word 84934884%N (Some S0) 1%N)) (sc_cut(sf_count 212337212%N)(sf_word 0%N (Some S0) 1%N)) sf_prefix_49 sf_edge_50). Qed.
Lemma sf_edge_51 : csteps sc_tm(sf_count 424674446%N)(sc_cut(sf_count 212337212%N)(sf_word 0%N (Some S0) 1%N))=Some(sc_cut(sf_count 2%N)(sf_word 212337214%N (Some S1) 1%N)).
Proof. pose proof(sf_N_zero 212337212%N (repeat S3(sf_count 1%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_51 : csteps sc_tm(sf_count 10735023482397764%N)c0=Some(sc_cut(sf_count 2%N)(sf_word 212337214%N (Some S1) 1%N)).
Proof. exact(sf_comp 10735023057723318%N 424674446%N c0 (sc_cut(sf_count 212337212%N)(sf_word 0%N (Some S0) 1%N)) (sc_cut(sf_count 2%N)(sf_word 212337214%N (Some S1) 1%N)) sf_prefix_50 sf_edge_51). Qed.
Lemma sf_edge_52 : csteps sc_tm(sf_count 56358867684974385%N)(sc_cut(sf_count 2%N)(sf_word 212337214%N (Some S1) 1%N))=Some(sc_cut(sf_count 530843037%N)(sf_word 0%N (Some S1) 1%N)).
Proof. unfold sf_word. change(csteps sc_tm(sf_count 56358867684974385%N)
 (sc_cut(sf_count 2%N)(repeat S3(sf_count(2*106168607+0)%N)++(S1::repeat S3(sf_count 1%N))))=
 Some(sc_cut(sf_count 530843037%N)(repeat S3(sf_count 0%N)++(S1::repeat S3(sf_count 1%N))))).
 rewrite sf_radd,<-app_assoc. exact(sf_N_bulk 106168607%N 2%N (repeat S3(sf_count 0%N)++(S1::repeat S3(sf_count 1%N)))). Qed.
Lemma sf_prefix_52 : csteps sc_tm(sf_count 67093891167372149%N)c0=Some(sc_cut(sf_count 530843037%N)(sf_word 0%N (Some S1) 1%N)).
Proof. exact(sf_comp 10735023482397764%N 56358867684974385%N c0 (sc_cut(sf_count 2%N)(sf_word 212337214%N (Some S1) 1%N)) (sc_cut(sf_count 530843037%N)(sf_word 0%N (Some S1) 1%N)) sf_prefix_51 sf_edge_52). Qed.
Lemma sf_edge_53 : csteps sc_tm(sf_count 1061686091%N)(sc_cut(sf_count 530843037%N)(sf_word 0%N (Some S1) 1%N))=Some(sc_cut(sf_count 530843041%N)(sf_word 1%N None 0%N)).
Proof. pose proof(sf_N_one 530843037%N (repeat S3(sf_count 1%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_53 : csteps sc_tm(sf_count 67093892229058240%N)c0=Some(sc_cut(sf_count 530843041%N)(sf_word 1%N None 0%N)).
Proof. exact(sf_comp 67093891167372149%N 1061686091%N c0 (sc_cut(sf_count 530843037%N)(sf_word 0%N (Some S1) 1%N)) (sc_cut(sf_count 530843041%N)(sf_word 1%N None 0%N)) sf_prefix_52 sf_edge_53). Qed.
Lemma sf_final_cut : csteps sc_tm(sf_count 67093892229058240%N)c0=Some(sc_cut(sf_count 530843041%N)[S3]).
Proof. pose proof sf_prefix_53 as H;unfold sf_word in H;rewrite sf_r1 in H;cbn[app]in H;exact H. Qed.
Theorem sf_escape : csteps sc_tm(sf_count 67093892759901295%N)c0=
 Some(StB,(S2::repeat S1(sf_count 530843044%N),S0,[])).
Proof. exact(sf_comp 67093892229058240%N 530843055%N c0 (sc_cut(sf_count 530843041%N)[S3])
 (StB,(S2::repeat S1(sf_count 530843044%N),S0,[])) sf_final_cut (sf_N_unprotected 530843041%N)). Qed.
Theorem sf_before_escape : csteps sc_tm(sf_count 67093892759901294%N)c0=Some(sc_Q(sf_count 530843044%N)[S3]).
Proof. exact(sf_comp 67093892229058240%N 530843054%N c0 (sc_cut(sf_count 530843041%N)[S3])
 (sc_Q(sf_count 530843044%N)[S3]) sf_final_cut (sf_N_before_unprotected 530843041%N)). Qed.
Print Assumptions sf_escape.
