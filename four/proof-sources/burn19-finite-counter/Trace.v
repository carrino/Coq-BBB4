(** A compressed binary-count transcript. It instantiates universal macros;
    no step count here is evaluated as a giant unary natural. *)
From Coq Require Import List Arith Lia Bool NArith.
From BBB24 Require Import Statement Spec CTape Census.
From BBB24Burn19FiniteCounter Require Import FiniteCounter.
Import ListNotations.
Lemma fc_small_0 : fc_count 0%N=0.
Proof. reflexivity. Qed.
Lemma fc_small_1 : fc_count 1%N=1.
Proof. reflexivity. Qed.
Lemma fc_small_2 : fc_count 2%N=2.
Proof. reflexivity. Qed.
Lemma fc_small_3 : fc_count 3%N=3.
Proof. reflexivity. Qed.
Lemma fc_small_4 : fc_count 4%N=4.
Proof. reflexivity. Qed.
Lemma fc_small_5 : fc_count 5%N=5.
Proof. reflexivity. Qed.
Lemma fc_small_6 : fc_count 6%N=6.
Proof. reflexivity. Qed.
Lemma fc_small_45 : fc_count 45%N=45.
Proof. reflexivity. Qed.
Lemma fc_score_count : score=fc_count scoreN.
Proof. unfold score,fc_count;reflexivity. Qed.
Definition fc_boundN:N := 4294967296%N.
Lemma fc_bound_count : fc_count fc_boundN=N.to_nat 4294967296%N.
Proof. unfold fc_count,fc_boundN;reflexivity. Qed.
Opaque fc_count.
Ltac fc_small := repeat first[rewrite fc_small_0 in *|rewrite fc_small_1 in *|rewrite fc_small_2 in *|rewrite fc_small_3 in *|rewrite fc_small_4 in *|rewrite fc_small_5 in *|rewrite fc_small_6 in *|rewrite fc_small_45 in *].
Lemma fc_prefix_00 : csteps fc_tm(fc_count 45%N)c0=Some(fc_X(fc_count 6%N)(fc_count 0%N)).
Proof. fc_small;reflexivity. Qed.
Lemma fc_edge_01 :
 csteps fc_tm(fc_count 159%N)(fc_X(fc_count 6%N)(fc_count 0%N))=Some(fc_L(fc_count 16%N)).
Proof. pose proof(fc_N_step0 6%N ltac:(easy))as H;fc_small;exact H. Qed.
Lemma fc_prefix_01 : csteps fc_tm(fc_count 204%N)c0=Some(fc_L(fc_count 16%N)).
Proof. exact(fc_compN 45%N 159%N _ _ _ fc_prefix_00 fc_edge_01). Qed.
Lemma fc_edge_02 :
 csteps fc_tm(fc_count 5%N)(fc_L(fc_count 16%N))=Some(fc_M(fc_count 1%N)(fc_count 16%N)).
Proof. pose proof(fc_L_step(fc_count 16%N))as H;fc_small;exact H. Qed.
Lemma fc_prefix_02 : csteps fc_tm(fc_count 209%N)c0=Some(fc_M(fc_count 1%N)(fc_count 16%N)).
Proof. exact(fc_compN 204%N 5%N _ _ _ fc_prefix_01 fc_edge_02). Qed.
Lemma fc_edge_03 :
 csteps fc_tm(fc_count 97%N)(fc_M(fc_count 1%N)(fc_count 16%N))=Some(fc_X(fc_count 6%N)(fc_count 15%N)).
Proof. pose proof(fc_N_M_one 16%N ltac:(easy))as H;fc_small;exact H. Qed.
Lemma fc_prefix_03 : csteps fc_tm(fc_count 306%N)c0=Some(fc_X(fc_count 6%N)(fc_count 15%N)).
Proof. exact(fc_compN 209%N 97%N _ _ _ fc_prefix_02 fc_edge_03). Qed.
Lemma fc_edge_04 :
 csteps fc_tm(fc_count 315%N)(fc_X(fc_count 6%N)(fc_count 15%N))=Some(fc_X(fc_count 21%N)(fc_count 3%N)).
Proof. pose proof(fc_N_bulk 3%N 6%N 3%N ltac:(easy))as H;fc_small;exact H. Qed.
Lemma fc_prefix_04 : csteps fc_tm(fc_count 621%N)c0=Some(fc_X(fc_count 21%N)(fc_count 3%N)).
Proof. exact(fc_compN 306%N 315%N _ _ _ fc_prefix_03 fc_edge_04). Qed.
Lemma fc_edge_05 :
 csteps fc_tm(fc_count 187%N)(fc_X(fc_count 21%N)(fc_count 3%N))=Some(fc_M(fc_count 25%N)(fc_count 1%N)).
Proof. pose proof(fc_N_step3 21%N ltac:(easy))as H;fc_small;exact H. Qed.
Lemma fc_prefix_05 : csteps fc_tm(fc_count 808%N)c0=Some(fc_M(fc_count 25%N)(fc_count 1%N)).
Proof. exact(fc_compN 621%N 187%N _ _ _ fc_prefix_04 fc_edge_05). Qed.
Lemma fc_edge_06 :
 csteps fc_tm(fc_count 1429%N)(fc_M(fc_count 25%N)(fc_count 1%N))=Some(fc_X(fc_count 6%N)(fc_count 48%N)).
Proof. pose proof(fc_N_M_step 25%N ltac:(easy))as H;fc_small;exact H. Qed.
Lemma fc_prefix_06 : csteps fc_tm(fc_count 2237%N)c0=Some(fc_X(fc_count 6%N)(fc_count 48%N)).
Proof. exact(fc_compN 808%N 1429%N _ _ _ fc_prefix_05 fc_edge_06). Qed.
Lemma fc_edge_07 :
 csteps fc_tm(fc_count 3420%N)(fc_X(fc_count 6%N)(fc_count 48%N))=Some(fc_X(fc_count 66%N)(fc_count 0%N)).
Proof. pose proof(fc_N_bulk 12%N 6%N 0%N ltac:(easy))as H;fc_small;exact H. Qed.
Lemma fc_prefix_07 : csteps fc_tm(fc_count 5657%N)c0=Some(fc_X(fc_count 66%N)(fc_count 0%N)).
Proof. exact(fc_compN 2237%N 3420%N _ _ _ fc_prefix_06 fc_edge_07). Qed.
Lemma fc_edge_08 :
 csteps fc_tm(fc_count 9519%N)(fc_X(fc_count 66%N)(fc_count 0%N))=Some(fc_L(fc_count 136%N)).
Proof. pose proof(fc_N_step0 66%N ltac:(easy))as H;fc_small;exact H. Qed.
Lemma fc_prefix_08 : csteps fc_tm(fc_count 15176%N)c0=Some(fc_L(fc_count 136%N)).
Proof. exact(fc_compN 5657%N 9519%N _ _ _ fc_prefix_07 fc_edge_08). Qed.
Lemma fc_edge_09 :
 csteps fc_tm(fc_count 5%N)(fc_L(fc_count 136%N))=Some(fc_M(fc_count 1%N)(fc_count 136%N)).
Proof. pose proof(fc_L_step(fc_count 136%N))as H;fc_small;exact H. Qed.
Lemma fc_prefix_09 : csteps fc_tm(fc_count 15181%N)c0=Some(fc_M(fc_count 1%N)(fc_count 136%N)).
Proof. exact(fc_compN 15176%N 5%N _ _ _ fc_prefix_08 fc_edge_09). Qed.
Lemma fc_edge_10 :
 csteps fc_tm(fc_count 577%N)(fc_M(fc_count 1%N)(fc_count 136%N))=Some(fc_X(fc_count 6%N)(fc_count 135%N)).
Proof. pose proof(fc_N_M_one 136%N ltac:(easy))as H;fc_small;exact H. Qed.
Lemma fc_prefix_10 : csteps fc_tm(fc_count 15758%N)c0=Some(fc_X(fc_count 6%N)(fc_count 135%N)).
Proof. exact(fc_compN 15181%N 577%N _ _ _ fc_prefix_09 fc_edge_10). Qed.
Lemma fc_edge_11 :
 csteps fc_tm(fc_count 23265%N)(fc_X(fc_count 6%N)(fc_count 135%N))=Some(fc_X(fc_count 171%N)(fc_count 3%N)).
Proof. pose proof(fc_N_bulk 33%N 6%N 3%N ltac:(easy))as H;fc_small;exact H. Qed.
Lemma fc_prefix_11 : csteps fc_tm(fc_count 39023%N)c0=Some(fc_X(fc_count 171%N)(fc_count 3%N)).
Proof. exact(fc_compN 15758%N 23265%N _ _ _ fc_prefix_10 fc_edge_11). Qed.
Lemma fc_edge_12 :
 csteps fc_tm(fc_count 1387%N)(fc_X(fc_count 171%N)(fc_count 3%N))=Some(fc_M(fc_count 175%N)(fc_count 1%N)).
Proof. pose proof(fc_N_step3 171%N ltac:(easy))as H;fc_small;exact H. Qed.
Lemma fc_prefix_12 : csteps fc_tm(fc_count 40410%N)c0=Some(fc_M(fc_count 175%N)(fc_count 1%N)).
Proof. exact(fc_compN 39023%N 1387%N _ _ _ fc_prefix_11 fc_edge_12). Qed.
Lemma fc_edge_13 :
 csteps fc_tm(fc_count 62329%N)(fc_M(fc_count 175%N)(fc_count 1%N))=Some(fc_X(fc_count 6%N)(fc_count 348%N)).
Proof. pose proof(fc_N_M_step 175%N ltac:(easy))as H;fc_small;exact H. Qed.
Lemma fc_prefix_13 : csteps fc_tm(fc_count 102739%N)c0=Some(fc_X(fc_count 6%N)(fc_count 348%N)).
Proof. exact(fc_compN 40410%N 62329%N _ _ _ fc_prefix_12 fc_edge_13). Qed.
Lemma fc_edge_14 :
 csteps fc_tm(fc_count 155295%N)(fc_X(fc_count 6%N)(fc_count 348%N))=Some(fc_X(fc_count 441%N)(fc_count 0%N)).
Proof. pose proof(fc_N_bulk 87%N 6%N 0%N ltac:(easy))as H;fc_small;exact H. Qed.
Lemma fc_prefix_14 : csteps fc_tm(fc_count 258034%N)c0=Some(fc_X(fc_count 441%N)(fc_count 0%N)).
Proof. exact(fc_compN 102739%N 155295%N _ _ _ fc_prefix_13 fc_edge_14). Qed.
Lemma fc_edge_15 :
 csteps fc_tm(fc_count 394269%N)(fc_X(fc_count 441%N)(fc_count 0%N))=Some(fc_L(fc_count 886%N)).
Proof. pose proof(fc_N_step0 441%N ltac:(easy))as H;fc_small;exact H. Qed.
Lemma fc_prefix_15 : csteps fc_tm(fc_count 652303%N)c0=Some(fc_L(fc_count 886%N)).
Proof. exact(fc_compN 258034%N 394269%N _ _ _ fc_prefix_14 fc_edge_15). Qed.
Lemma fc_edge_16 :
 csteps fc_tm(fc_count 5%N)(fc_L(fc_count 886%N))=Some(fc_M(fc_count 1%N)(fc_count 886%N)).
Proof. pose proof(fc_L_step(fc_count 886%N))as H;fc_small;exact H. Qed.
Lemma fc_prefix_16 : csteps fc_tm(fc_count 652308%N)c0=Some(fc_M(fc_count 1%N)(fc_count 886%N)).
Proof. exact(fc_compN 652303%N 5%N _ _ _ fc_prefix_15 fc_edge_16). Qed.
Lemma fc_edge_17 :
 csteps fc_tm(fc_count 3577%N)(fc_M(fc_count 1%N)(fc_count 886%N))=Some(fc_X(fc_count 6%N)(fc_count 885%N)).
Proof. pose proof(fc_N_M_one 886%N ltac:(easy))as H;fc_small;exact H. Qed.
Lemma fc_prefix_17 : csteps fc_tm(fc_count 655885%N)c0=Some(fc_X(fc_count 6%N)(fc_count 885%N)).
Proof. exact(fc_compN 652308%N 3577%N _ _ _ fc_prefix_16 fc_edge_17). Qed.
Lemma fc_edge_18 :
 csteps fc_tm(fc_count 986765%N)(fc_X(fc_count 6%N)(fc_count 885%N))=Some(fc_X(fc_count 1111%N)(fc_count 1%N)).
Proof. pose proof(fc_N_bulk 221%N 6%N 1%N ltac:(easy))as H;fc_small;exact H. Qed.
Lemma fc_prefix_18 : csteps fc_tm(fc_count 1642650%N)c0=Some(fc_X(fc_count 1111%N)(fc_count 1%N)).
Proof. exact(fc_compN 655885%N 986765%N _ _ _ fc_prefix_17 fc_edge_18). Qed.
Lemma fc_edge_19 :
 csteps fc_tm(fc_count 2484223%N)(fc_X(fc_count 1111%N)(fc_count 1%N))=Some(fc_X(fc_count 4%N)(fc_count 2224%N)).
Proof. pose proof(fc_N_step1 1111%N ltac:(easy))as H;fc_small;exact H. Qed.
Lemma fc_prefix_19 : csteps fc_tm(fc_count 4126873%N)c0=Some(fc_X(fc_count 4%N)(fc_count 2224%N)).
Proof. exact(fc_compN 1642650%N 2484223%N _ _ _ fc_prefix_18 fc_edge_19). Qed.
Lemma fc_edge_20 :
 csteps fc_tm(fc_count 6198844%N)(fc_X(fc_count 4%N)(fc_count 2224%N))=Some(fc_X(fc_count 2784%N)(fc_count 0%N)).
Proof. pose proof(fc_N_bulk 556%N 4%N 0%N ltac:(easy))as H;fc_small;exact H. Qed.
Lemma fc_prefix_20 : csteps fc_tm(fc_count 10325717%N)c0=Some(fc_X(fc_count 2784%N)(fc_count 0%N)).
Proof. exact(fc_compN 4126873%N 6198844%N _ _ _ fc_prefix_19 fc_edge_20). Qed.
Lemma fc_edge_21 :
 csteps fc_tm(fc_count 15534735%N)(fc_X(fc_count 2784%N)(fc_count 0%N))=Some(fc_L(fc_count 5572%N)).
Proof. pose proof(fc_N_step0 2784%N ltac:(easy))as H;fc_small;exact H. Qed.
Lemma fc_prefix_21 : csteps fc_tm(fc_count 25860452%N)c0=Some(fc_L(fc_count 5572%N)).
Proof. exact(fc_compN 10325717%N 15534735%N _ _ _ fc_prefix_20 fc_edge_21). Qed.
Lemma fc_edge_22 :
 csteps fc_tm(fc_count 5%N)(fc_L(fc_count 5572%N))=Some(fc_M(fc_count 1%N)(fc_count 5572%N)).
Proof. pose proof(fc_L_step(fc_count 5572%N))as H;fc_small;exact H. Qed.
Lemma fc_prefix_22 : csteps fc_tm(fc_count 25860457%N)c0=Some(fc_M(fc_count 1%N)(fc_count 5572%N)).
Proof. exact(fc_compN 25860452%N 5%N _ _ _ fc_prefix_21 fc_edge_22). Qed.
Lemma fc_edge_23 :
 csteps fc_tm(fc_count 22321%N)(fc_M(fc_count 1%N)(fc_count 5572%N))=Some(fc_X(fc_count 6%N)(fc_count 5571%N)).
Proof. pose proof(fc_N_M_one 5572%N ltac:(easy))as H;fc_small;exact H. Qed.
Lemma fc_prefix_23 : csteps fc_tm(fc_count 25882778%N)c0=Some(fc_X(fc_count 6%N)(fc_count 5571%N)).
Proof. exact(fc_compN 25860457%N 22321%N _ _ _ fc_prefix_22 fc_edge_23). Qed.
Lemma fc_edge_24 :
 csteps fc_tm(fc_count 38815920%N)(fc_X(fc_count 6%N)(fc_count 5571%N))=Some(fc_X(fc_count 6966%N)(fc_count 3%N)).
Proof. pose proof(fc_N_bulk 1392%N 6%N 3%N ltac:(easy))as H;fc_small;exact H. Qed.
Lemma fc_prefix_24 : csteps fc_tm(fc_count 64698698%N)c0=Some(fc_X(fc_count 6966%N)(fc_count 3%N)).
Proof. exact(fc_compN 25882778%N 38815920%N _ _ _ fc_prefix_23 fc_edge_24). Qed.
Lemma fc_edge_25 :
 csteps fc_tm(fc_count 55747%N)(fc_X(fc_count 6966%N)(fc_count 3%N))=Some(fc_M(fc_count 6970%N)(fc_count 1%N)).
Proof. pose proof(fc_N_step3 6966%N ltac:(easy))as H;fc_small;exact H. Qed.
Lemma fc_prefix_25 : csteps fc_tm(fc_count 64754445%N)c0=Some(fc_M(fc_count 6970%N)(fc_count 1%N)).
Proof. exact(fc_compN 64698698%N 55747%N _ _ _ fc_prefix_24 fc_edge_25). Qed.
Lemma fc_edge_26 :
 csteps fc_tm(fc_count 97203649%N)(fc_M(fc_count 6970%N)(fc_count 1%N))=Some(fc_X(fc_count 6%N)(fc_count 13938%N)).
Proof. pose proof(fc_N_M_step 6970%N ltac:(easy))as H;fc_small;exact H. Qed.
Lemma fc_prefix_26 : csteps fc_tm(fc_count 161958094%N)c0=Some(fc_X(fc_count 6%N)(fc_count 13938%N)).
Proof. exact(fc_compN 64754445%N 97203649%N _ _ _ fc_prefix_25 fc_edge_26). Qed.
Lemma fc_edge_27 :
 csteps fc_tm(fc_count 242921900%N)(fc_X(fc_count 6%N)(fc_count 13938%N))=Some(fc_X(fc_count 17426%N)(fc_count 2%N)).
Proof. pose proof(fc_N_bulk 3484%N 6%N 2%N ltac:(easy))as H;fc_small;exact H. Qed.
Lemma fc_prefix_27 : csteps fc_tm(fc_count 404879994%N)c0=Some(fc_X(fc_count 17426%N)(fc_count 2%N)).
Proof. exact(fc_compN 161958094%N 242921900%N _ _ _ fc_prefix_26 fc_edge_27). Qed.
Lemma fc_edge_28 :
 csteps fc_tm(fc_count 607784087%N)(fc_X(fc_count 17426%N)(fc_count 2%N))=Some(fc_phase(fc_count 34861%N)[]).
Proof. pose proof(fc_N_step2 17426%N ltac:(easy))as H;fc_small;exact H. Qed.
Lemma fc_prefix_28 : csteps fc_tm(fc_count 1012664081%N)c0=Some(fc_phase(fc_count 34861%N)[]).
Proof. exact(fc_compN 404879994%N 607784087%N _ _ _ fc_prefix_27 fc_edge_28). Qed.

Theorem fc_native_prefix :
 csteps fc_tm(fc_count 1012664081%N)c0=Some(fc_phase(fc_count 34861%N)[]).
Proof. exact fc_prefix_28. Qed.
Theorem fc_sound : NonHalt fc_tm /\ QHBound(fc_count fc_boundN)fc_tm.
Proof.
 destruct(fc_eventual_B_bound _ _ fc_native_prefix)as[Hnh Hb].
 split;[exact Hnh|].
 intros q s Hq;eapply Nat.le_trans;[exact(Hb q s Hq)|].
 apply fc_count_le;unfold fc_boundN;easy.
Qed.
Theorem fc_B_forever : forall n,fc_count 1012664081%N<=n ->VisitsAt fc_tm StB n.
Proof.
 intros n Hn;destruct(fc_after_run _ _ fc_native_prefix(n-fc_count 1012664081%N))as(l&k&E).
 replace(fc_count 1012664081%N+(n-fc_count 1012664081%N))with n in E by lia.
 exists(lift(StB,(l,S0,repeat S0 k)));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem fc_A_quiet : QuietFrom fc_tm StA(fc_count 1012664081%N).
Proof.
 intros n Hn(c&Ec&Hs);destruct(fc_B_forever n Hn)as(c'&Ec'&Hs').
 rewrite Ec in Ec';injection Ec' as <-;congruence.
Qed.
Theorem fc_quasihalts : QuasiHaltsSt fc_tm.
Proof.
 exists StA;split.
 - exists 0;exists InitES;split;reflexivity.
 - exists(fc_count 1012664081%N);exact fc_A_quiet.
Qed.
Theorem fc_below_champion : QHBound score fc_tm.
Proof.
 intros q s Hq;pose proof(proj2 fc_sound q s Hq)as H.
 eapply Nat.le_trans;[exact H|].
 rewrite fc_score_count.
 apply fc_count_le.
 unfold fc_boundN,scoreN.
 vm_compute;discriminate.
Qed.
Print Assumptions fc_sound.
Print Assumptions fc_quasihalts.
