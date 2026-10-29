(** 34 finite binary-count macro edges, preserving the full right word. *)
From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn25S030Finite Require Import Counter BinaryBridge.
Import ListNotations.
Opaque sf_count.
#[local] Hint Rewrite sf_r0 sf_r1 sf_r2 sf_r3 sf_r4 sf_r5 sf_r6 sf_r7 : sf_repeat.
Ltac sf_words := unfold sf_word in *;autorewrite with sf_repeat in *;cbn[app]in *.
Lemma sf_prefix_00 : csteps s30_tm(sf_count 3%N)c0=Some(s30_Q(sf_count 1%N)(sf_word 0%N false 0%N)).
Proof. sf_words;rewrite sf_small1,sf_small3;exact s30_entry. Qed.
Lemma sf_edge_01 : csteps s30_tm(sf_count 6%N)(s30_Q(sf_count 1%N)(sf_word 0%N false 0%N))=Some(s30_Q(sf_count 1%N)(sf_word 1%N true 1%N)).
Proof. pose proof(sf_N_blank 1%N)as H;sf_words;exact H. Qed.
Lemma sf_prefix_01 : csteps s30_tm(sf_count 9%N)c0=Some(s30_Q(sf_count 1%N)(sf_word 1%N true 1%N)).
Proof. exact(sf_comp 3%N 6%N c0 (s30_Q(sf_count 1%N)(sf_word 0%N false 0%N)) (s30_Q(sf_count 1%N)(sf_word 1%N true 1%N)) sf_prefix_00 sf_edge_01). Qed.
Lemma sf_edge_02 : csteps s30_tm(sf_count 25%N)(s30_Q(sf_count 1%N)(sf_word 1%N true 1%N))=Some(s30_Q(sf_count 7%N)(sf_word 0%N false 0%N)).
Proof. pose proof(sf_N_101 1%N (repeat S1(sf_count 0%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_02 : csteps s30_tm(sf_count 34%N)c0=Some(s30_Q(sf_count 7%N)(sf_word 0%N false 0%N)).
Proof. exact(sf_comp 9%N 25%N c0 (s30_Q(sf_count 1%N)(sf_word 1%N true 1%N)) (s30_Q(sf_count 7%N)(sf_word 0%N false 0%N)) sf_prefix_01 sf_edge_02). Qed.
Lemma sf_edge_03 : csteps s30_tm(sf_count 12%N)(s30_Q(sf_count 7%N)(sf_word 0%N false 0%N))=Some(s30_Q(sf_count 1%N)(sf_word 7%N true 1%N)).
Proof. pose proof(sf_N_blank 7%N)as H;sf_words;exact H. Qed.
Lemma sf_prefix_03 : csteps s30_tm(sf_count 46%N)c0=Some(s30_Q(sf_count 1%N)(sf_word 7%N true 1%N)).
Proof. exact(sf_comp 34%N 12%N c0 (s30_Q(sf_count 7%N)(sf_word 0%N false 0%N)) (s30_Q(sf_count 1%N)(sf_word 7%N true 1%N)) sf_prefix_02 sf_edge_03). Qed.
Lemma sf_edge_04 : csteps s30_tm(sf_count 162%N)(s30_Q(sf_count 1%N)(sf_word 7%N true 1%N))=Some(s30_Q(sf_count 16%N)(sf_word 1%N true 1%N)).
Proof. unfold sf_word. change(csteps s30_tm(sf_count 162%N)
 (s30_Q(sf_count 1%N)(repeat S1(sf_count(2*3+1)%N)++(S0::repeat S1(sf_count 1%N))))=
 Some(s30_Q(sf_count 16%N)(repeat S1(sf_count 1%N)++(S0::repeat S1(sf_count 1%N))))).
 rewrite sf_radd,<-app_assoc;exact(sf_N_bulk 3%N 1%N (repeat S1(sf_count 1%N)++(S0::repeat S1(sf_count 1%N)))). Qed.
Lemma sf_prefix_04 : csteps s30_tm(sf_count 208%N)c0=Some(s30_Q(sf_count 16%N)(sf_word 1%N true 1%N)).
Proof. exact(sf_comp 46%N 162%N c0 (s30_Q(sf_count 1%N)(sf_word 7%N true 1%N)) (s30_Q(sf_count 16%N)(sf_word 1%N true 1%N)) sf_prefix_03 sf_edge_04). Qed.
Lemma sf_edge_05 : csteps s30_tm(sf_count 115%N)(s30_Q(sf_count 16%N)(sf_word 1%N true 1%N))=Some(s30_Q(sf_count 22%N)(sf_word 0%N false 0%N)).
Proof. pose proof(sf_N_101 16%N (repeat S1(sf_count 0%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_05 : csteps s30_tm(sf_count 323%N)c0=Some(s30_Q(sf_count 22%N)(sf_word 0%N false 0%N)).
Proof. exact(sf_comp 208%N 115%N c0 (s30_Q(sf_count 16%N)(sf_word 1%N true 1%N)) (s30_Q(sf_count 22%N)(sf_word 0%N false 0%N)) sf_prefix_04 sf_edge_05). Qed.
Lemma sf_edge_06 : csteps s30_tm(sf_count 27%N)(s30_Q(sf_count 22%N)(sf_word 0%N false 0%N))=Some(s30_Q(sf_count 1%N)(sf_word 22%N true 1%N)).
Proof. pose proof(sf_N_blank 22%N)as H;sf_words;exact H. Qed.
Lemma sf_prefix_06 : csteps s30_tm(sf_count 350%N)c0=Some(s30_Q(sf_count 1%N)(sf_word 22%N true 1%N)).
Proof. exact(sf_comp 323%N 27%N c0 (s30_Q(sf_count 22%N)(sf_word 0%N false 0%N)) (s30_Q(sf_count 1%N)(sf_word 22%N true 1%N)) sf_prefix_05 sf_edge_06). Qed.
Lemma sf_edge_07 : csteps s30_tm(sf_count 1914%N)(s30_Q(sf_count 1%N)(sf_word 22%N true 1%N))=Some(s30_Q(sf_count 56%N)(sf_word 0%N true 1%N)).
Proof. unfold sf_word. change(csteps s30_tm(sf_count 1914%N)
 (s30_Q(sf_count 1%N)(repeat S1(sf_count(2*11+0)%N)++(S0::repeat S1(sf_count 1%N))))=
 Some(s30_Q(sf_count 56%N)(repeat S1(sf_count 0%N)++(S0::repeat S1(sf_count 1%N))))).
 rewrite sf_radd,<-app_assoc;exact(sf_N_bulk 11%N 1%N (repeat S1(sf_count 0%N)++(S0::repeat S1(sf_count 1%N)))). Qed.
Lemma sf_prefix_07 : csteps s30_tm(sf_count 2264%N)c0=Some(s30_Q(sf_count 56%N)(sf_word 0%N true 1%N)).
Proof. exact(sf_comp 350%N 1914%N c0 (s30_Q(sf_count 1%N)(sf_word 22%N true 1%N)) (s30_Q(sf_count 56%N)(sf_word 0%N true 1%N)) sf_prefix_06 sf_edge_07). Qed.
Lemma sf_edge_08 : csteps s30_tm(sf_count 61%N)(s30_Q(sf_count 56%N)(sf_word 0%N true 1%N))=Some(s30_Q(sf_count 1%N)(sf_word 56%N true 2%N)).
Proof. pose proof(sf_N_zero 56%N (repeat S1(sf_count 1%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_08 : csteps s30_tm(sf_count 2325%N)c0=Some(s30_Q(sf_count 1%N)(sf_word 56%N true 2%N)).
Proof. exact(sf_comp 2264%N 61%N c0 (s30_Q(sf_count 56%N)(sf_word 0%N true 1%N)) (s30_Q(sf_count 1%N)(sf_word 56%N true 2%N)) sf_prefix_07 sf_edge_08). Qed.
Lemma sf_edge_09 : csteps s30_tm(sf_count 12012%N)(s30_Q(sf_count 1%N)(sf_word 56%N true 2%N))=Some(s30_Q(sf_count 141%N)(sf_word 0%N true 2%N)).
Proof. unfold sf_word. change(csteps s30_tm(sf_count 12012%N)
 (s30_Q(sf_count 1%N)(repeat S1(sf_count(2*28+0)%N)++(S0::repeat S1(sf_count 2%N))))=
 Some(s30_Q(sf_count 141%N)(repeat S1(sf_count 0%N)++(S0::repeat S1(sf_count 2%N))))).
 rewrite sf_radd,<-app_assoc;exact(sf_N_bulk 28%N 1%N (repeat S1(sf_count 0%N)++(S0::repeat S1(sf_count 2%N)))). Qed.
Lemma sf_prefix_09 : csteps s30_tm(sf_count 14337%N)c0=Some(s30_Q(sf_count 141%N)(sf_word 0%N true 2%N)).
Proof. exact(sf_comp 2325%N 12012%N c0 (s30_Q(sf_count 1%N)(sf_word 56%N true 2%N)) (s30_Q(sf_count 141%N)(sf_word 0%N true 2%N)) sf_prefix_08 sf_edge_09). Qed.
Lemma sf_edge_10 : csteps s30_tm(sf_count 146%N)(s30_Q(sf_count 141%N)(sf_word 0%N true 2%N))=Some(s30_Q(sf_count 1%N)(sf_word 141%N true 3%N)).
Proof. pose proof(sf_N_zero 141%N (repeat S1(sf_count 2%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_10 : csteps s30_tm(sf_count 14483%N)c0=Some(s30_Q(sf_count 1%N)(sf_word 141%N true 3%N)).
Proof. exact(sf_comp 14337%N 146%N c0 (s30_Q(sf_count 141%N)(sf_word 0%N true 2%N)) (s30_Q(sf_count 1%N)(sf_word 141%N true 3%N)) sf_prefix_09 sf_edge_10). Qed.
Lemma sf_edge_11 : csteps s30_tm(sf_count 74130%N)(s30_Q(sf_count 1%N)(sf_word 141%N true 3%N))=Some(s30_Q(sf_count 351%N)(sf_word 1%N true 3%N)).
Proof. unfold sf_word. change(csteps s30_tm(sf_count 74130%N)
 (s30_Q(sf_count 1%N)(repeat S1(sf_count(2*70+1)%N)++(S0::repeat S1(sf_count 3%N))))=
 Some(s30_Q(sf_count 351%N)(repeat S1(sf_count 1%N)++(S0::repeat S1(sf_count 3%N))))).
 rewrite sf_radd,<-app_assoc;exact(sf_N_bulk 70%N 1%N (repeat S1(sf_count 1%N)++(S0::repeat S1(sf_count 3%N)))). Qed.
Lemma sf_prefix_11 : csteps s30_tm(sf_count 88613%N)c0=Some(s30_Q(sf_count 351%N)(sf_word 1%N true 3%N)).
Proof. exact(sf_comp 14483%N 74130%N c0 (s30_Q(sf_count 1%N)(sf_word 141%N true 3%N)) (s30_Q(sf_count 351%N)(sf_word 1%N true 3%N)) sf_prefix_10 sf_edge_11). Qed.
Lemma sf_edge_12 : csteps s30_tm(sf_count 2125%N)(s30_Q(sf_count 351%N)(sf_word 1%N true 3%N))=Some(s30_Q(sf_count 357%N)(sf_word 2%N false 0%N)).
Proof. pose proof(sf_N_101 351%N (repeat S1(sf_count 2%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_12 : csteps s30_tm(sf_count 90738%N)c0=Some(s30_Q(sf_count 357%N)(sf_word 2%N false 0%N)).
Proof. exact(sf_comp 88613%N 2125%N c0 (s30_Q(sf_count 351%N)(sf_word 1%N true 3%N)) (s30_Q(sf_count 357%N)(sf_word 2%N false 0%N)) sf_prefix_11 sf_edge_12). Qed.
Lemma sf_edge_13 : csteps s30_tm(sf_count 2160%N)(s30_Q(sf_count 357%N)(sf_word 2%N false 0%N))=Some(s30_Q(sf_count 362%N)(sf_word 0%N false 0%N)).
Proof. unfold sf_word. change(csteps s30_tm(sf_count 2160%N)
 (s30_Q(sf_count 357%N)(repeat S1(sf_count(2*1+0)%N)++([])))=
 Some(s30_Q(sf_count 362%N)(repeat S1(sf_count 0%N)++([])))).
 rewrite sf_radd,<-app_assoc;exact(sf_N_bulk 1%N 357%N (repeat S1(sf_count 0%N)++([]))). Qed.
Lemma sf_prefix_13 : csteps s30_tm(sf_count 92898%N)c0=Some(s30_Q(sf_count 362%N)(sf_word 0%N false 0%N)).
Proof. exact(sf_comp 90738%N 2160%N c0 (s30_Q(sf_count 357%N)(sf_word 2%N false 0%N)) (s30_Q(sf_count 362%N)(sf_word 0%N false 0%N)) sf_prefix_12 sf_edge_13). Qed.
Lemma sf_edge_14 : csteps s30_tm(sf_count 367%N)(s30_Q(sf_count 362%N)(sf_word 0%N false 0%N))=Some(s30_Q(sf_count 1%N)(sf_word 362%N true 1%N)).
Proof. pose proof(sf_N_blank 362%N)as H;sf_words;exact H. Qed.
Lemma sf_prefix_14 : csteps s30_tm(sf_count 93265%N)c0=Some(s30_Q(sf_count 1%N)(sf_word 362%N true 1%N)).
Proof. exact(sf_comp 92898%N 367%N c0 (s30_Q(sf_count 362%N)(sf_word 0%N false 0%N)) (s30_Q(sf_count 1%N)(sf_word 362%N true 1%N)) sf_prefix_13 sf_edge_14). Qed.
Lemma sf_edge_15 : csteps s30_tm(sf_count 493044%N)(s30_Q(sf_count 1%N)(sf_word 362%N true 1%N))=Some(s30_Q(sf_count 906%N)(sf_word 0%N true 1%N)).
Proof. unfold sf_word. change(csteps s30_tm(sf_count 493044%N)
 (s30_Q(sf_count 1%N)(repeat S1(sf_count(2*181+0)%N)++(S0::repeat S1(sf_count 1%N))))=
 Some(s30_Q(sf_count 906%N)(repeat S1(sf_count 0%N)++(S0::repeat S1(sf_count 1%N))))).
 rewrite sf_radd,<-app_assoc;exact(sf_N_bulk 181%N 1%N (repeat S1(sf_count 0%N)++(S0::repeat S1(sf_count 1%N)))). Qed.
Lemma sf_prefix_15 : csteps s30_tm(sf_count 586309%N)c0=Some(s30_Q(sf_count 906%N)(sf_word 0%N true 1%N)).
Proof. exact(sf_comp 93265%N 493044%N c0 (s30_Q(sf_count 1%N)(sf_word 362%N true 1%N)) (s30_Q(sf_count 906%N)(sf_word 0%N true 1%N)) sf_prefix_14 sf_edge_15). Qed.
Lemma sf_edge_16 : csteps s30_tm(sf_count 911%N)(s30_Q(sf_count 906%N)(sf_word 0%N true 1%N))=Some(s30_Q(sf_count 1%N)(sf_word 906%N true 2%N)).
Proof. pose proof(sf_N_zero 906%N (repeat S1(sf_count 1%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_16 : csteps s30_tm(sf_count 587220%N)c0=Some(s30_Q(sf_count 1%N)(sf_word 906%N true 2%N)).
Proof. exact(sf_comp 586309%N 911%N c0 (s30_Q(sf_count 906%N)(sf_word 0%N true 1%N)) (s30_Q(sf_count 1%N)(sf_word 906%N true 2%N)) sf_prefix_15 sf_edge_16). Qed.
Lemma sf_edge_17 : csteps s30_tm(sf_count 3082212%N)(s30_Q(sf_count 1%N)(sf_word 906%N true 2%N))=Some(s30_Q(sf_count 2266%N)(sf_word 0%N true 2%N)).
Proof. unfold sf_word. change(csteps s30_tm(sf_count 3082212%N)
 (s30_Q(sf_count 1%N)(repeat S1(sf_count(2*453+0)%N)++(S0::repeat S1(sf_count 2%N))))=
 Some(s30_Q(sf_count 2266%N)(repeat S1(sf_count 0%N)++(S0::repeat S1(sf_count 2%N))))).
 rewrite sf_radd,<-app_assoc;exact(sf_N_bulk 453%N 1%N (repeat S1(sf_count 0%N)++(S0::repeat S1(sf_count 2%N)))). Qed.
Lemma sf_prefix_17 : csteps s30_tm(sf_count 3669432%N)c0=Some(s30_Q(sf_count 2266%N)(sf_word 0%N true 2%N)).
Proof. exact(sf_comp 587220%N 3082212%N c0 (s30_Q(sf_count 1%N)(sf_word 906%N true 2%N)) (s30_Q(sf_count 2266%N)(sf_word 0%N true 2%N)) sf_prefix_16 sf_edge_17). Qed.
Lemma sf_edge_18 : csteps s30_tm(sf_count 2271%N)(s30_Q(sf_count 2266%N)(sf_word 0%N true 2%N))=Some(s30_Q(sf_count 1%N)(sf_word 2266%N true 3%N)).
Proof. pose proof(sf_N_zero 2266%N (repeat S1(sf_count 2%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_18 : csteps s30_tm(sf_count 3671703%N)c0=Some(s30_Q(sf_count 1%N)(sf_word 2266%N true 3%N)).
Proof. exact(sf_comp 3669432%N 2271%N c0 (s30_Q(sf_count 2266%N)(sf_word 0%N true 2%N)) (s30_Q(sf_count 1%N)(sf_word 2266%N true 3%N)) sf_prefix_17 sf_edge_18). Qed.
Lemma sf_edge_19 : csteps s30_tm(sf_count 19265532%N)(s30_Q(sf_count 1%N)(sf_word 2266%N true 3%N))=Some(s30_Q(sf_count 5666%N)(sf_word 0%N true 3%N)).
Proof. unfold sf_word. change(csteps s30_tm(sf_count 19265532%N)
 (s30_Q(sf_count 1%N)(repeat S1(sf_count(2*1133+0)%N)++(S0::repeat S1(sf_count 3%N))))=
 Some(s30_Q(sf_count 5666%N)(repeat S1(sf_count 0%N)++(S0::repeat S1(sf_count 3%N))))).
 rewrite sf_radd,<-app_assoc;exact(sf_N_bulk 1133%N 1%N (repeat S1(sf_count 0%N)++(S0::repeat S1(sf_count 3%N)))). Qed.
Lemma sf_prefix_19 : csteps s30_tm(sf_count 22937235%N)c0=Some(s30_Q(sf_count 5666%N)(sf_word 0%N true 3%N)).
Proof. exact(sf_comp 3671703%N 19265532%N c0 (s30_Q(sf_count 1%N)(sf_word 2266%N true 3%N)) (s30_Q(sf_count 5666%N)(sf_word 0%N true 3%N)) sf_prefix_18 sf_edge_19). Qed.
Lemma sf_edge_20 : csteps s30_tm(sf_count 5671%N)(s30_Q(sf_count 5666%N)(sf_word 0%N true 3%N))=Some(s30_Q(sf_count 1%N)(sf_word 5666%N true 4%N)).
Proof. pose proof(sf_N_zero 5666%N (repeat S1(sf_count 3%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_20 : csteps s30_tm(sf_count 22942906%N)c0=Some(s30_Q(sf_count 1%N)(sf_word 5666%N true 4%N)).
Proof. exact(sf_comp 22937235%N 5671%N c0 (s30_Q(sf_count 5666%N)(sf_word 0%N true 3%N)) (s30_Q(sf_count 1%N)(sf_word 5666%N true 4%N)) sf_prefix_19 sf_edge_20). Qed.
Lemma sf_edge_21 : csteps s30_tm(sf_count 120413832%N)(s30_Q(sf_count 1%N)(sf_word 5666%N true 4%N))=Some(s30_Q(sf_count 14166%N)(sf_word 0%N true 4%N)).
Proof. unfold sf_word. change(csteps s30_tm(sf_count 120413832%N)
 (s30_Q(sf_count 1%N)(repeat S1(sf_count(2*2833+0)%N)++(S0::repeat S1(sf_count 4%N))))=
 Some(s30_Q(sf_count 14166%N)(repeat S1(sf_count 0%N)++(S0::repeat S1(sf_count 4%N))))).
 rewrite sf_radd,<-app_assoc;exact(sf_N_bulk 2833%N 1%N (repeat S1(sf_count 0%N)++(S0::repeat S1(sf_count 4%N)))). Qed.
Lemma sf_prefix_21 : csteps s30_tm(sf_count 143356738%N)c0=Some(s30_Q(sf_count 14166%N)(sf_word 0%N true 4%N)).
Proof. exact(sf_comp 22942906%N 120413832%N c0 (s30_Q(sf_count 1%N)(sf_word 5666%N true 4%N)) (s30_Q(sf_count 14166%N)(sf_word 0%N true 4%N)) sf_prefix_20 sf_edge_21). Qed.
Lemma sf_edge_22 : csteps s30_tm(sf_count 14171%N)(s30_Q(sf_count 14166%N)(sf_word 0%N true 4%N))=Some(s30_Q(sf_count 1%N)(sf_word 14166%N true 5%N)).
Proof. pose proof(sf_N_zero 14166%N (repeat S1(sf_count 4%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_22 : csteps s30_tm(sf_count 143370909%N)c0=Some(s30_Q(sf_count 1%N)(sf_word 14166%N true 5%N)).
Proof. exact(sf_comp 143356738%N 14171%N c0 (s30_Q(sf_count 14166%N)(sf_word 0%N true 4%N)) (s30_Q(sf_count 1%N)(sf_word 14166%N true 5%N)) sf_prefix_21 sf_edge_22). Qed.
Lemma sf_edge_23 : csteps s30_tm(sf_count 752597082%N)(s30_Q(sf_count 1%N)(sf_word 14166%N true 5%N))=Some(s30_Q(sf_count 35416%N)(sf_word 0%N true 5%N)).
Proof. unfold sf_word. change(csteps s30_tm(sf_count 752597082%N)
 (s30_Q(sf_count 1%N)(repeat S1(sf_count(2*7083+0)%N)++(S0::repeat S1(sf_count 5%N))))=
 Some(s30_Q(sf_count 35416%N)(repeat S1(sf_count 0%N)++(S0::repeat S1(sf_count 5%N))))).
 rewrite sf_radd,<-app_assoc;exact(sf_N_bulk 7083%N 1%N (repeat S1(sf_count 0%N)++(S0::repeat S1(sf_count 5%N)))). Qed.
Lemma sf_prefix_23 : csteps s30_tm(sf_count 895967991%N)c0=Some(s30_Q(sf_count 35416%N)(sf_word 0%N true 5%N)).
Proof. exact(sf_comp 143370909%N 752597082%N c0 (s30_Q(sf_count 1%N)(sf_word 14166%N true 5%N)) (s30_Q(sf_count 35416%N)(sf_word 0%N true 5%N)) sf_prefix_22 sf_edge_23). Qed.
Lemma sf_edge_24 : csteps s30_tm(sf_count 35421%N)(s30_Q(sf_count 35416%N)(sf_word 0%N true 5%N))=Some(s30_Q(sf_count 1%N)(sf_word 35416%N true 6%N)).
Proof. pose proof(sf_N_zero 35416%N (repeat S1(sf_count 5%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_24 : csteps s30_tm(sf_count 896003412%N)c0=Some(s30_Q(sf_count 1%N)(sf_word 35416%N true 6%N)).
Proof. exact(sf_comp 895967991%N 35421%N c0 (s30_Q(sf_count 35416%N)(sf_word 0%N true 5%N)) (s30_Q(sf_count 1%N)(sf_word 35416%N true 6%N)) sf_prefix_23 sf_edge_24). Qed.
Lemma sf_edge_25 : csteps s30_tm(sf_count 4703758332%N)(s30_Q(sf_count 1%N)(sf_word 35416%N true 6%N))=Some(s30_Q(sf_count 88541%N)(sf_word 0%N true 6%N)).
Proof. unfold sf_word. change(csteps s30_tm(sf_count 4703758332%N)
 (s30_Q(sf_count 1%N)(repeat S1(sf_count(2*17708+0)%N)++(S0::repeat S1(sf_count 6%N))))=
 Some(s30_Q(sf_count 88541%N)(repeat S1(sf_count 0%N)++(S0::repeat S1(sf_count 6%N))))).
 rewrite sf_radd,<-app_assoc;exact(sf_N_bulk 17708%N 1%N (repeat S1(sf_count 0%N)++(S0::repeat S1(sf_count 6%N)))). Qed.
Lemma sf_prefix_25 : csteps s30_tm(sf_count 5599761744%N)c0=Some(s30_Q(sf_count 88541%N)(sf_word 0%N true 6%N)).
Proof. exact(sf_comp 896003412%N 4703758332%N c0 (s30_Q(sf_count 1%N)(sf_word 35416%N true 6%N)) (s30_Q(sf_count 88541%N)(sf_word 0%N true 6%N)) sf_prefix_24 sf_edge_25). Qed.
Lemma sf_edge_26 : csteps s30_tm(sf_count 88546%N)(s30_Q(sf_count 88541%N)(sf_word 0%N true 6%N))=Some(s30_Q(sf_count 1%N)(sf_word 88541%N true 7%N)).
Proof. pose proof(sf_N_zero 88541%N (repeat S1(sf_count 6%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_26 : csteps s30_tm(sf_count 5599850290%N)c0=Some(s30_Q(sf_count 1%N)(sf_word 88541%N true 7%N)).
Proof. exact(sf_comp 5599761744%N 88546%N c0 (s30_Q(sf_count 88541%N)(sf_word 0%N true 6%N)) (s30_Q(sf_count 1%N)(sf_word 88541%N true 7%N)) sf_prefix_25 sf_edge_26). Qed.
Lemma sf_edge_27 : csteps s30_tm(sf_count 29397891930%N)(s30_Q(sf_count 1%N)(sf_word 88541%N true 7%N))=Some(s30_Q(sf_count 221351%N)(sf_word 1%N true 7%N)).
Proof. unfold sf_word. change(csteps s30_tm(sf_count 29397891930%N)
 (s30_Q(sf_count 1%N)(repeat S1(sf_count(2*44270+1)%N)++(S0::repeat S1(sf_count 7%N))))=
 Some(s30_Q(sf_count 221351%N)(repeat S1(sf_count 1%N)++(S0::repeat S1(sf_count 7%N))))).
 rewrite sf_radd,<-app_assoc;exact(sf_N_bulk 44270%N 1%N (repeat S1(sf_count 1%N)++(S0::repeat S1(sf_count 7%N)))). Qed.
Lemma sf_prefix_27 : csteps s30_tm(sf_count 34997742220%N)c0=Some(s30_Q(sf_count 221351%N)(sf_word 1%N true 7%N)).
Proof. exact(sf_comp 5599850290%N 29397891930%N c0 (s30_Q(sf_count 1%N)(sf_word 88541%N true 7%N)) (s30_Q(sf_count 221351%N)(sf_word 1%N true 7%N)) sf_prefix_26 sf_edge_27). Qed.
Lemma sf_edge_28 : csteps s30_tm(sf_count 1328125%N)(s30_Q(sf_count 221351%N)(sf_word 1%N true 7%N))=Some(s30_Q(sf_count 221357%N)(sf_word 6%N false 0%N)).
Proof. pose proof(sf_N_101 221351%N (repeat S1(sf_count 6%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_28 : csteps s30_tm(sf_count 34999070345%N)c0=Some(s30_Q(sf_count 221357%N)(sf_word 6%N false 0%N)).
Proof. exact(sf_comp 34997742220%N 1328125%N c0 (s30_Q(sf_count 221351%N)(sf_word 1%N true 7%N)) (s30_Q(sf_count 221357%N)(sf_word 6%N false 0%N)) sf_prefix_27 sf_edge_28). Qed.
Lemma sf_edge_29 : csteps s30_tm(sf_count 3984570%N)(s30_Q(sf_count 221357%N)(sf_word 6%N false 0%N))=Some(s30_Q(sf_count 221372%N)(sf_word 0%N false 0%N)).
Proof. unfold sf_word. change(csteps s30_tm(sf_count 3984570%N)
 (s30_Q(sf_count 221357%N)(repeat S1(sf_count(2*3+0)%N)++([])))=
 Some(s30_Q(sf_count 221372%N)(repeat S1(sf_count 0%N)++([])))).
 rewrite sf_radd,<-app_assoc;exact(sf_N_bulk 3%N 221357%N (repeat S1(sf_count 0%N)++([]))). Qed.
Lemma sf_prefix_29 : csteps s30_tm(sf_count 35003054915%N)c0=Some(s30_Q(sf_count 221372%N)(sf_word 0%N false 0%N)).
Proof. exact(sf_comp 34999070345%N 3984570%N c0 (s30_Q(sf_count 221357%N)(sf_word 6%N false 0%N)) (s30_Q(sf_count 221372%N)(sf_word 0%N false 0%N)) sf_prefix_28 sf_edge_29). Qed.
Lemma sf_edge_30 : csteps s30_tm(sf_count 221377%N)(s30_Q(sf_count 221372%N)(sf_word 0%N false 0%N))=Some(s30_Q(sf_count 1%N)(sf_word 221372%N true 1%N)).
Proof. pose proof(sf_N_blank 221372%N)as H;sf_words;exact H. Qed.
Lemma sf_prefix_30 : csteps s30_tm(sf_count 35003276292%N)c0=Some(s30_Q(sf_count 1%N)(sf_word 221372%N true 1%N)).
Proof. exact(sf_comp 35003054915%N 221377%N c0 (s30_Q(sf_count 221372%N)(sf_word 0%N false 0%N)) (s30_Q(sf_count 1%N)(sf_word 221372%N true 1%N)) sf_prefix_29 sf_edge_30). Qed.
Lemma sf_edge_31 : csteps s30_tm(sf_count 183771855114%N)(s30_Q(sf_count 1%N)(sf_word 221372%N true 1%N))=Some(s30_Q(sf_count 553431%N)(sf_word 0%N true 1%N)).
Proof. unfold sf_word. change(csteps s30_tm(sf_count 183771855114%N)
 (s30_Q(sf_count 1%N)(repeat S1(sf_count(2*110686+0)%N)++(S0::repeat S1(sf_count 1%N))))=
 Some(s30_Q(sf_count 553431%N)(repeat S1(sf_count 0%N)++(S0::repeat S1(sf_count 1%N))))).
 rewrite sf_radd,<-app_assoc;exact(sf_N_bulk 110686%N 1%N (repeat S1(sf_count 0%N)++(S0::repeat S1(sf_count 1%N)))). Qed.
Lemma sf_prefix_31 : csteps s30_tm(sf_count 218775131406%N)c0=Some(s30_Q(sf_count 553431%N)(sf_word 0%N true 1%N)).
Proof. exact(sf_comp 35003276292%N 183771855114%N c0 (s30_Q(sf_count 1%N)(sf_word 221372%N true 1%N)) (s30_Q(sf_count 553431%N)(sf_word 0%N true 1%N)) sf_prefix_30 sf_edge_31). Qed.
Lemma sf_edge_32 : csteps s30_tm(sf_count 553436%N)(s30_Q(sf_count 553431%N)(sf_word 0%N true 1%N))=Some(s30_Q(sf_count 1%N)(sf_word 553431%N true 2%N)).
Proof. pose proof(sf_N_zero 553431%N (repeat S1(sf_count 1%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_32 : csteps s30_tm(sf_count 218775684842%N)c0=Some(s30_Q(sf_count 1%N)(sf_word 553431%N true 2%N)).
Proof. exact(sf_comp 218775131406%N 553436%N c0 (s30_Q(sf_count 553431%N)(sf_word 0%N true 1%N)) (s30_Q(sf_count 1%N)(sf_word 553431%N true 2%N)) sf_prefix_31 sf_edge_32). Qed.
Lemma sf_edge_33 : csteps s30_tm(sf_count 1148570358810%N)(s30_Q(sf_count 1%N)(sf_word 553431%N true 2%N))=Some(s30_Q(sf_count 1383576%N)(sf_word 1%N true 2%N)).
Proof. unfold sf_word. change(csteps s30_tm(sf_count 1148570358810%N)
 (s30_Q(sf_count 1%N)(repeat S1(sf_count(2*276715+1)%N)++(S0::repeat S1(sf_count 2%N))))=
 Some(s30_Q(sf_count 1383576%N)(repeat S1(sf_count 1%N)++(S0::repeat S1(sf_count 2%N))))).
 rewrite sf_radd,<-app_assoc;exact(sf_N_bulk 276715%N 1%N (repeat S1(sf_count 1%N)++(S0::repeat S1(sf_count 2%N)))). Qed.
Lemma sf_prefix_33 : csteps s30_tm(sf_count 1367346043652%N)c0=Some(s30_Q(sf_count 1383576%N)(sf_word 1%N true 2%N)).
Proof. exact(sf_comp 218775684842%N 1148570358810%N c0 (s30_Q(sf_count 1%N)(sf_word 553431%N true 2%N)) (s30_Q(sf_count 1383576%N)(sf_word 1%N true 2%N)) sf_prefix_32 sf_edge_33). Qed.
Lemma sf_edge_34 : csteps s30_tm(sf_count 8301475%N)(s30_Q(sf_count 1383576%N)(sf_word 1%N true 2%N))=Some(s30_Q(sf_count 1383582%N)(sf_word 1%N false 0%N)).
Proof. pose proof(sf_N_101 1383576%N (repeat S1(sf_count 1%N)))as H;sf_words;exact H. Qed.
Lemma sf_prefix_34 : csteps s30_tm(sf_count 1367354345127%N)c0=Some(s30_Q(sf_count 1383582%N)(sf_word 1%N false 0%N)).
Proof. exact(sf_comp 1367346043652%N 8301475%N c0 (s30_Q(sf_count 1383576%N)(sf_word 1%N true 2%N)) (s30_Q(sf_count 1383582%N)(sf_word 1%N false 0%N)) sf_prefix_33 sf_edge_34). Qed.
Theorem sf_exposed : csteps s30_tm(sf_count 1367354345127%N)c0=Some(s30_Q(sf_count 1383582%N)[S1]).
Proof. pose proof sf_prefix_34 as H;unfold sf_word in H;rewrite sf_r1 in H;cbn[app]in H;exact H. Qed.
Theorem sf_before : csteps s30_tm(sf_count 1367354345128%N)c0=
 Some(StA,(repeat S2(sf_count 1383582%N),S3,[S2])).
Proof. exact(sf_comp 1367354345127%N 1%N c0 (s30_Q(sf_count 1383582%N)[S1])
 (StA,(repeat S2(sf_count 1383582%N),S3,[S2])) sf_exposed (sf_N_before 1383582%N)). Qed.
Theorem sf_after : csteps s30_tm(sf_count 1367354345129%N)c0=
 Some(s30_back StB(repeat S2(sf_count 1383582%N))[S2;S2]).
Proof. exact(sf_comp 1367354345127%N 2%N c0 (s30_Q(sf_count 1383582%N)[S1])
 (s30_back StB(repeat S2(sf_count 1383582%N))[S2;S2]) sf_exposed (sf_N_after 1383582%N)). Qed.
Print Assumptions sf_after.
