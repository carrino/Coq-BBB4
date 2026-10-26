(** Bounds transported from existing binary counter proofs. *)
From Coq Require Import Arith Lia List.
From SmallBB Require Import Statement StatementTr CTape Mirror Size Bounds CycleCensus Legacy32.
Require SmallLegacy.Counter32.
Require BBB4.Machines.CountersTr.LAPT_0RB0LC_1LC1RB_0RB1LA_______.
Require BBB4.Machines.CountersTr.LAPT_0RB0LC_1LC1RB_1LA1LA_______.
Require BBB4.Machines.CountersTr.LAPT_0RB0LC_1LC1RB_1RB1LA_______.
Require BBB4.Machines.CountersTr.LAPT_0RB0LC_1LC1RB_1RC1LA_______.
Require BBB4.Machines.CountersTr.LAPT_0RB0RB_0LC1RA_1RB1LC_______.
Require BBB4.Machines.CountersTr.LAPT_0RB1LA_1LA1RC_1RB0LA_______.
Require BBB4.Machines.CountersTr.LAPT_0RB1LA_1LC1RC_1RB0LA_______.
Require BBB4.Machines.CountersTr.LAPT_0RB1LA_1RC0LA_1LA1RB_______.
Require BBB4.Machines.CountersTr.LAPT_0RB1LA_1RC0LA_1LB1RB_______.
Require BBB4.Machines.CountersTr.LAPT_0RB1LC_1LA1RB_0LA0LA_______.
Require BBB4.Machines.CountersTr.LAPT_0RB1LC_1LA1RB_0RB0LA_______.
Require BBB4.Machines.CountersTr.LAPT_0RB1LC_1LA1RB_0RC0LA_______.
Require BBB4.Machines.CountersTr.LAPT_0RB1LC_1LA1RB_1LA0LA_______.
Require BBB4.Machines.CountersTr.LAPT_0RB1LC_1LA1RB_1RA0LA_______.
Require BBB4.Machines.CountersTr.LAPT_0RB1LC_1LA1RB_1RB0LA_______.
Require BBB4.Machines.CountersTr.LAPT_1RB0LB_0RC1LA_1LB1RC_______.
Require BBB4.Machines.CountersTr.LAPT_1RB0LC_1LA1RA_0RA1LC_______.
Require BBB4.Machines.CountersTr.LAPT_1RB0LC_1LA1RA_0RB1LC_______.
Require BBB4.Machines.CountersTr.LAPT_1RB0LC_1LC1RA_0RA1LC_______.
Require BBB4.Machines.CountersTr.LAPT_1RB0LC_1LC1RA_0RB1LC_______.
Require BBB4.Machines.CountersTr.LAPT_1RB0LC_1LC1RB_0RB1LA_______.
Require BBB4.Machines.CountersTr.LAPT_1RB0RB_0LC1RA_1RB1LC_______.
Require BBB4.Machines.CountersTr.LAPT_1RB1LA_0LA1RC_0LA0RB_______.
Require BBB4.Machines.CountersTr.LAPT_1RB1LA_0LA1RC_0LC0RB_______.
Require BBB4.Machines.CountersTr.LAPT_1RB1LA_0LA1RC_0RB0RB_______.
Require BBB4.Machines.CountersTr.LAPT_1RB1LA_0LA1RC_1LA0RB_______.
Require BBB4.Machines.CountersTr.LAPT_1RB1LA_0LA1RC_1LB0RB_______.
Require BBB4.Machines.CountersTr.LAPT_1RB1LA_0LA1RC_1RB0RB_______.
Require BBB4.Machines.CountersTr.LAPT_1RB1LA_1LA1RC_0LA0RB_______.
Require BBB4.Machines.CountersTr.LAPT_1RB1LA_1LB1RC_0LA0RB_______.
Require BBB4.Machines.CountersTr.LAPT_1RB1LA_1RC1RC_0LA0RB_______.
Require BBB4.Machines.CountersTr.LAPT_1RB1LB_1LA0RC_0LA1RC_______.
Require BBB4.Machines.CountersTr.LAPT_1RB1LB_1LA0RC_0LB1RC_______.
Require BBB4.Machines.CountersTr.LAPT_1RB1LC_0LA1RB_1LA0RB_______.
Require BBB4.Machines.CountersTr.LAPT_1RB1LC_0LC0RB_1LA1LC_______.
Require BBB4.Machines.CountersTr.LAPT_1RB1LC_0LC1RB_1LA0RB_______.
Require BBB4.Machines.CountersTr.LAPT_1RB1LC_1LA1RB_0RB0LA_______.
Require BBB4.Machines.CountersTr.LAPT_1RB1RA_1LC1RA_0RB0LC_______.
Require BBB4.Machines.CountersTr.LAPT_1RB1RB_0LC0RA_1RA1LC_______.
Import ListNotations.
(* 0LB0LB_0RC1LA1LB1RC *)
Definition known32_000:TM:=machine_of_codes 3 2 [1;1;5;6;7;11].
Lemma known32_000_bound:NonHalt known32_000 /\ Bounds 55 55 known32_000.
Proof.
 assert(H:NonHalt(mirror_tm known32_000) /\ Bounds 55 55(mirror_tm known32_000)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB0RB_0LC1RA_1RB1LC_______.tm_0RB0RB_0LC1RA_1RB1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_000 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB0RB_0LC1RA_1RB1LC_______.nqhtr_0RB0RB_0LC1RA_1RB1LC_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LB0RB_0LC1RB1RA1LC *)
Definition known32_001:TM:=machine_of_codes 3 2 [1;4;2;10;9;8].
Lemma known32_001_bound:NonHalt known32_001 /\ Bounds 55 55 known32_001.
Proof.
 assert(H:NonHalt(mirror_tm known32_001) /\ Bounds 55 55(mirror_tm known32_001)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_000).
 - split.
   + intros [] [] tr H; cbv [known32_001 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_000_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LB0RC_1RA1LB0LB1RC *)
Definition known32_002:TM:=machine_of_codes 3 2 [1;5;9;7;1;11].
Lemma known32_002_bound:NonHalt known32_002 /\ Bounds 55 55 known32_002.
Proof.
 assert(H:NonHalt(mirror_tm known32_002) /\ Bounds 55 55(mirror_tm known32_002)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_001).
 - split.
   + intros [] [] tr H; cbv [known32_002 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_001_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LB0RC_1RC1LB0LB1RA *)
Definition known32_003:TM:=machine_of_codes 3 2 [1;5;11;7;1;9].
Lemma known32_003_bound:NonHalt known32_003 /\ Bounds 55 55 known32_003.
Proof.
 assert(H:NonHalt(mirror_tm known32_003) /\ Bounds 55 55(mirror_tm known32_003)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB0LC_1LC1RB_0RB1LA_______.tm_0RB0LC_1LC1RB_0RB1LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_003 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB0LC_1LC1RB_0RB1LA_______.nqhtr_0RB0LC_1LC1RB_0RB1LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LB0RC_1RC1LB1LB1RA *)
Definition known32_004:TM:=machine_of_codes 3 2 [1;5;11;7;7;9].
Lemma known32_004_bound:NonHalt known32_004 /\ Bounds 55 55 known32_004.
Proof.
 assert(H:NonHalt(mirror_tm known32_004) /\ Bounds 55 55(mirror_tm known32_004)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB0LC_1LC1RB_1RB1LA_______.tm_0RB0LC_1LC1RB_1RB1LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_004 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB0LC_1LC1RB_1RB1LA_______.nqhtr_0RB0LC_1LC1RB_1RB1LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LB0RC_1RC1LB1LC1RA *)
Definition known32_005:TM:=machine_of_codes 3 2 [1;5;11;7;8;9].
Lemma known32_005_bound:NonHalt known32_005 /\ Bounds 55 55 known32_005.
Proof.
 assert(H:NonHalt(mirror_tm known32_005) /\ Bounds 55 55(mirror_tm known32_005)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB0LC_1LC1RB_1RC1LA_______.tm_0RB0LC_1LC1RB_1RC1LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_005 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB0LC_1LC1RB_1RC1LA_______.nqhtr_0RB0LC_1LC1RB_1RC1LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LB0RC_1RC1LB1RA1RA *)
Definition known32_006:TM:=machine_of_codes 3 2 [1;5;11;7;9;9].
Lemma known32_006_bound:NonHalt known32_006 /\ Bounds 55 55 known32_006.
Proof.
 assert(H:NonHalt(mirror_tm known32_006) /\ Bounds 55 55(mirror_tm known32_006)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB0LC_1LC1RB_1LA1LA_______.tm_0RB0LC_1LC1RB_1LA1LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_006 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB0LC_1LC1RB_1LA1LA_______.nqhtr_0RB0LC_1LC1RB_1LA1LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LB1RA_1LC0RA1RA1LB *)
Definition known32_007:TM:=machine_of_codes 3 2 [1;9;8;3;9;7].
Lemma known32_007_bound:NonHalt known32_007 /\ Bounds 55 55 known32_007.
Proof.
 assert(H:NonHalt(mirror_tm known32_007) /\ Bounds 55 55(mirror_tm known32_007)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB1LA_1RC0LA_1LA1RB_______.tm_0RB1LA_1RC0LA_1LA1RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_007 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LA_1RC0LA_1LA1RB_______.nqhtr_0RB1LA_1RC0LA_1LA1RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LB1RA_1LC0RA1RB1LB *)
Definition known32_008:TM:=machine_of_codes 3 2 [1;9;8;3;10;7].
Lemma known32_008_bound:NonHalt known32_008 /\ Bounds 55 55 known32_008.
Proof.
 assert(H:NonHalt(mirror_tm known32_008) /\ Bounds 55 55(mirror_tm known32_008)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB1LA_1RC0LA_1LB1RB_______.tm_0RB1LA_1RC0LA_1LB1RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_008 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LA_1RC0LA_1LB1RB_______.nqhtr_0RB1LA_1RC0LA_1LB1RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LB1RA_1RA1LC1LB0RA *)
Definition known32_009:TM:=machine_of_codes 3 2 [1;9;9;8;7;3].
Lemma known32_009_bound:NonHalt known32_009 /\ Bounds 55 55 known32_009.
Proof.
 assert(H:NonHalt(mirror_tm known32_009) /\ Bounds 55 55(mirror_tm known32_009)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB1LA_1LA1RC_1RB0LA_______.tm_0RB1LA_1LA1RC_1RB0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_009 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LA_1LA1RC_1RB0LA_______.nqhtr_0RB1LA_1LA1RC_1RB0LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LB1RA_1RC1LB0LA0RA *)
Definition known32_010:TM:=machine_of_codes 3 2 [1;9;11;7;0;3].
Lemma known32_010_bound:NonHalt known32_010 /\ Bounds 55 55 known32_010.
Proof.
 assert(H:NonHalt(mirror_tm known32_010) /\ Bounds 55 55(mirror_tm known32_010)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_002).
 - split.
   + intros [] [] tr H; cbv [known32_010 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_002_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LB1RA_1RC1LB0LB0RA *)
Definition known32_011:TM:=machine_of_codes 3 2 [1;9;11;7;1;3].
Lemma known32_011_bound:NonHalt known32_011 /\ Bounds 55 55 known32_011.
Proof.
 assert(H:NonHalt(mirror_tm known32_011) /\ Bounds 55 55(mirror_tm known32_011)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_003).
 - split.
   + intros [] [] tr H; cbv [known32_011 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_003_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LB1RA_1RC1LB1LA0RA *)
Definition known32_012:TM:=machine_of_codes 3 2 [1;9;11;7;6;3].
Lemma known32_012_bound:NonHalt known32_012 /\ Bounds 55 55 known32_012.
Proof.
 assert(H:NonHalt(mirror_tm known32_012) /\ Bounds 55 55(mirror_tm known32_012)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_005).
 - split.
   + intros [] [] tr H; cbv [known32_012 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_005_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LB1RA_1RC1LB1LB0RA *)
Definition known32_013:TM:=machine_of_codes 3 2 [1;9;11;7;7;3].
Lemma known32_013_bound:NonHalt known32_013 /\ Bounds 55 55 known32_013.
Proof.
 assert(H:NonHalt(mirror_tm known32_013) /\ Bounds 55 55(mirror_tm known32_013)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_006).
 - split.
   + intros [] [] tr H; cbv [known32_013 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_006_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LB1RA_1RC1LB1RA0RA *)
Definition known32_014:TM:=machine_of_codes 3 2 [1;9;11;7;9;3].
Lemma known32_014_bound:NonHalt known32_014 /\ Bounds 55 55 known32_014.
Proof.
 assert(H:NonHalt(mirror_tm known32_014) /\ Bounds 55 55(mirror_tm known32_014)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_004).
 - split.
   + intros [] [] tr H; cbv [known32_014 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_004_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LB1RA_1RC1LC1LB0RA *)
Definition known32_015:TM:=machine_of_codes 3 2 [1;9;11;8;7;3].
Lemma known32_015_bound:NonHalt known32_015 /\ Bounds 55 55 known32_015.
Proof.
 assert(H:NonHalt(mirror_tm known32_015) /\ Bounds 55 55(mirror_tm known32_015)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB1LA_1LC1RC_1RB0LA_______.tm_0RB1LA_1LC1RC_1RB0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_015 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LA_1LC1RC_1RB0LA_______.nqhtr_0RB1LA_1LC1RC_1RB0LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LB1RC_1RA1LB0LB0RA *)
Definition known32_016:TM:=machine_of_codes 3 2 [1;11;9;7;1;3].
Lemma known32_016_bound:NonHalt known32_016 /\ Bounds 55 55 known32_016.
Proof.
 assert(H:NonHalt(mirror_tm known32_016) /\ Bounds 55 55(mirror_tm known32_016)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB1LC_1LA1RB_0RB0LA_______.tm_0RB1LC_1LA1RB_0RB0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_016 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LC_1LA1RB_0RB0LA_______.nqhtr_0RB1LC_1LA1RB_0RB0LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LB1RC_1RA1LB0LC0RA *)
Definition known32_017:TM:=machine_of_codes 3 2 [1;11;9;7;2;3].
Lemma known32_017_bound:NonHalt known32_017 /\ Bounds 55 55 known32_017.
Proof.
 assert(H:NonHalt(mirror_tm known32_017) /\ Bounds 55 55(mirror_tm known32_017)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB1LC_1LA1RB_0RC0LA_______.tm_0RB1LC_1LA1RB_0RC0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_017 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LC_1LA1RB_0RC0LA_______.nqhtr_0RB1LC_1LA1RB_0RC0LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LB1RC_1RA1LB0RA0RA *)
Definition known32_018:TM:=machine_of_codes 3 2 [1;11;9;7;3;3].
Lemma known32_018_bound:NonHalt known32_018 /\ Bounds 55 55 known32_018.
Proof.
 assert(H:NonHalt(mirror_tm known32_018) /\ Bounds 55 55(mirror_tm known32_018)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB1LC_1LA1RB_0LA0LA_______.tm_0RB1LC_1LA1RB_0LA0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_018 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LC_1LA1RB_0LA0LA_______.nqhtr_0RB1LC_1LA1RB_0LA0LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LB1RC_1RA1LB1LA0RA *)
Definition known32_019:TM:=machine_of_codes 3 2 [1;11;9;7;6;3].
Lemma known32_019_bound:NonHalt known32_019 /\ Bounds 55 55 known32_019.
Proof.
 assert(H:NonHalt(mirror_tm known32_019) /\ Bounds 55 55(mirror_tm known32_019)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB1LC_1LA1RB_1RA0LA_______.tm_0RB1LC_1LA1RB_1RA0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_019 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LC_1LA1RB_1RA0LA_______.nqhtr_0RB1LC_1LA1RB_1RA0LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LB1RC_1RA1LB1LB0RA *)
Definition known32_020:TM:=machine_of_codes 3 2 [1;11;9;7;7;3].
Lemma known32_020_bound:NonHalt known32_020 /\ Bounds 55 55 known32_020.
Proof.
 assert(H:NonHalt(mirror_tm known32_020) /\ Bounds 55 55(mirror_tm known32_020)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB1LC_1LA1RB_1RB0LA_______.tm_0RB1LC_1LA1RB_1RB0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_020 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LC_1LA1RB_1RB0LA_______.nqhtr_0RB1LC_1LA1RB_1RB0LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LB1RC_1RA1LB1RA0RA *)
Definition known32_021:TM:=machine_of_codes 3 2 [1;11;9;7;9;3].
Lemma known32_021_bound:NonHalt known32_021 /\ Bounds 55 55 known32_021.
Proof.
 assert(H:NonHalt(mirror_tm known32_021) /\ Bounds 55 55(mirror_tm known32_021)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB1LC_1LA1RB_1LA0LA_______.tm_0RB1LC_1LA1RB_1LA0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_021 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LC_1LA1RB_1LA0LA_______.nqhtr_0RB1LC_1LA1RB_1LA0LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LC0LC_1LC1RB0RB1LA *)
Definition known32_022:TM:=machine_of_codes 3 2 [2;2;8;10;4;6].
Lemma known32_022_bound:NonHalt known32_022 /\ Bounds 55 55 known32_022.
Proof.
 assert(H:NonHalt(mirror_tm known32_022) /\ Bounds 55 55(mirror_tm known32_022)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB0RB_0LC1RA_1RB1LC_______.tm_0RB0RB_0LC1RA_1RB1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_022 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB0RB_0LC1RA_1RB1LC_______.nqhtr_0RB0RB_0LC1RA_1RB1LC_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LC0RB_0LC1RA1RB1LC *)
Definition known32_023:TM:=machine_of_codes 3 2 [2;4;2;9;10;8].
Lemma known32_023_bound:NonHalt known32_023 /\ Bounds 55 55 known32_023.
Proof.
 assert(H:NonHalt(mirror_tm known32_023) /\ Bounds 55 55(mirror_tm known32_023)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB0LC_1LC1RB_0RB1LA_______.tm_0RB0LC_1LC1RB_0RB1LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_023 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB0LC_1LC1RB_0RB1LA_______.nqhtr_0RB0LC_1LC1RB_0RB1LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LC0RB_0LC1RB1RA1LC *)
Definition known32_024:TM:=machine_of_codes 3 2 [2;4;2;10;9;8].
Lemma known32_024_bound:NonHalt known32_024 /\ Bounds 55 55 known32_024.
Proof.
 assert(H:NonHalt(mirror_tm known32_024) /\ Bounds 55 55(mirror_tm known32_024)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_001).
 - split.
   + intros [] [] tr H; cbv [known32_024 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_001_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LC0RB_1LB1RA1RB1LC *)
Definition known32_025:TM:=machine_of_codes 3 2 [2;4;7;9;10;8].
Lemma known32_025_bound:NonHalt known32_025 /\ Bounds 55 55 known32_025.
Proof.
 assert(H:NonHalt(mirror_tm known32_025) /\ Bounds 55 55(mirror_tm known32_025)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB0LC_1LC1RB_1RC1LA_______.tm_0RB0LC_1LC1RB_1RC1LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_025 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB0LC_1LC1RB_1RC1LA_______.nqhtr_0RB0LC_1LC1RB_1RC1LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LC0RB_1LC1RA1RB1LC *)
Definition known32_026:TM:=machine_of_codes 3 2 [2;4;8;9;10;8].
Lemma known32_026_bound:NonHalt known32_026 /\ Bounds 55 55 known32_026.
Proof.
 assert(H:NonHalt(mirror_tm known32_026) /\ Bounds 55 55(mirror_tm known32_026)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB0LC_1LC1RB_1RB1LA_______.tm_0RB0LC_1LC1RB_1RB1LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_026 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB0LC_1LC1RB_1RB1LA_______.nqhtr_0RB0LC_1LC1RB_1RB1LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LC0RB_1RA1RA1RB1LC *)
Definition known32_027:TM:=machine_of_codes 3 2 [2;4;9;9;10;8].
Lemma known32_027_bound:NonHalt known32_027 /\ Bounds 55 55 known32_027.
Proof.
 assert(H:NonHalt(mirror_tm known32_027) /\ Bounds 55 55(mirror_tm known32_027)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB0LC_1LC1RB_1LA1LA_______.tm_0RB0LC_1LC1RB_1LA1LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_027 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB0LC_1LC1RB_1LA1LA_______.nqhtr_0RB0LC_1LC1RB_1LA1LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LC0RC_1RA1LB0LB1RC *)
Definition known32_028:TM:=machine_of_codes 3 2 [2;5;9;7;1;11].
Lemma known32_028_bound:NonHalt known32_028 /\ Bounds 55 55 known32_028.
Proof.
 assert(H:NonHalt(mirror_tm known32_028) /\ Bounds 55 55(mirror_tm known32_028)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_000).
 - split.
   + intros [] [] tr H; cbv [known32_028 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_000_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LC1RA_0LA0RA1RB1LC *)
Definition known32_029:TM:=machine_of_codes 3 2 [2;9;0;3;10;8].
Lemma known32_029_bound:NonHalt known32_029 /\ Bounds 55 55 known32_029.
Proof.
 assert(H:NonHalt(mirror_tm known32_029) /\ Bounds 55 55(mirror_tm known32_029)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_002).
 - split.
   + intros [] [] tr H; cbv [known32_029 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_002_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LC1RA_0LC0RA1RB1LC *)
Definition known32_030:TM:=machine_of_codes 3 2 [2;9;2;3;10;8].
Lemma known32_030_bound:NonHalt known32_030 /\ Bounds 55 55 known32_030.
Proof.
 assert(H:NonHalt(mirror_tm known32_030) /\ Bounds 55 55(mirror_tm known32_030)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_003).
 - split.
   + intros [] [] tr H; cbv [known32_030 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_003_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LC1RA_1LA0RA1RB1LC *)
Definition known32_031:TM:=machine_of_codes 3 2 [2;9;6;3;10;8].
Lemma known32_031_bound:NonHalt known32_031 /\ Bounds 55 55 known32_031.
Proof.
 assert(H:NonHalt(mirror_tm known32_031) /\ Bounds 55 55(mirror_tm known32_031)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_005).
 - split.
   + intros [] [] tr H; cbv [known32_031 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_005_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LC1RA_1LC0RA1RA1LB *)
Definition known32_032:TM:=machine_of_codes 3 2 [2;9;8;3;9;7].
Lemma known32_032_bound:NonHalt known32_032 /\ Bounds 55 55 known32_032.
Proof.
 assert(H:NonHalt(mirror_tm known32_032) /\ Bounds 55 55(mirror_tm known32_032)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB1LA_1LA1RC_1RB0LA_______.tm_0RB1LA_1LA1RC_1RB0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_032 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LA_1LA1RC_1RB0LA_______.nqhtr_0RB1LA_1LA1RC_1RB0LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LC1RA_1LC0RA1RB1LB *)
Definition known32_033:TM:=machine_of_codes 3 2 [2;9;8;3;10;7].
Lemma known32_033_bound:NonHalt known32_033 /\ Bounds 55 55 known32_033.
Proof.
 assert(H:NonHalt(mirror_tm known32_033) /\ Bounds 55 55(mirror_tm known32_033)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB1LA_1LC1RC_1RB0LA_______.tm_0RB1LA_1LC1RC_1RB0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_033 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LA_1LC1RC_1RB0LA_______.nqhtr_0RB1LA_1LC1RC_1RB0LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LC1RA_1LC0RA1RB1LC *)
Definition known32_034:TM:=machine_of_codes 3 2 [2;9;8;3;10;8].
Lemma known32_034_bound:NonHalt known32_034 /\ Bounds 55 55 known32_034.
Proof.
 assert(H:NonHalt(mirror_tm known32_034) /\ Bounds 55 55(mirror_tm known32_034)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_006).
 - split.
   + intros [] [] tr H; cbv [known32_034 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_006_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LC1RA_1RA0RA1RB1LC *)
Definition known32_035:TM:=machine_of_codes 3 2 [2;9;9;3;10;8].
Lemma known32_035_bound:NonHalt known32_035 /\ Bounds 55 55 known32_035.
Proof.
 assert(H:NonHalt(mirror_tm known32_035) /\ Bounds 55 55(mirror_tm known32_035)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_004).
 - split.
   + intros [] [] tr H; cbv [known32_035 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_004_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LC1RA_1RA1LC1LB0RA *)
Definition known32_036:TM:=machine_of_codes 3 2 [2;9;9;8;7;3].
Lemma known32_036_bound:NonHalt known32_036 /\ Bounds 55 55 known32_036.
Proof.
 assert(H:NonHalt(mirror_tm known32_036) /\ Bounds 55 55(mirror_tm known32_036)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB1LA_1RC0LA_1LA1RB_______.tm_0RB1LA_1RC0LA_1LA1RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_036 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LA_1RC0LA_1LA1RB_______.nqhtr_0RB1LA_1RC0LA_1LA1RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LC1RA_1RC1LC1LB0RA *)
Definition known32_037:TM:=machine_of_codes 3 2 [2;9;11;8;7;3].
Lemma known32_037_bound:NonHalt known32_037 /\ Bounds 55 55 known32_037.
Proof.
 assert(H:NonHalt(mirror_tm known32_037) /\ Bounds 55 55(mirror_tm known32_037)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB1LA_1RC0LA_1LB1RB_______.tm_0RB1LA_1RC0LA_1LB1RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_037 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LA_1RC0LA_1LB1RB_______.nqhtr_0RB1LA_1RC0LA_1LB1RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LC1RB_0LB0RA1RA1LC *)
Definition known32_038:TM:=machine_of_codes 3 2 [2;10;1;3;9;8].
Lemma known32_038_bound:NonHalt known32_038 /\ Bounds 55 55 known32_038.
Proof.
 assert(H:NonHalt(mirror_tm known32_038) /\ Bounds 55 55(mirror_tm known32_038)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB1LC_1LA1RB_0RC0LA_______.tm_0RB1LC_1LA1RB_0RC0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_038 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LC_1LA1RB_0RC0LA_______.nqhtr_0RB1LC_1LA1RB_0RC0LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LC1RB_0LC0RA1RA1LC *)
Definition known32_039:TM:=machine_of_codes 3 2 [2;10;2;3;9;8].
Lemma known32_039_bound:NonHalt known32_039 /\ Bounds 55 55 known32_039.
Proof.
 assert(H:NonHalt(mirror_tm known32_039) /\ Bounds 55 55(mirror_tm known32_039)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB1LC_1LA1RB_0RB0LA_______.tm_0RB1LC_1LA1RB_0RB0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_039 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LC_1LA1RB_0RB0LA_______.nqhtr_0RB1LC_1LA1RB_0RB0LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LC1RB_0RA0RA1RA1LC *)
Definition known32_040:TM:=machine_of_codes 3 2 [2;10;3;3;9;8].
Lemma known32_040_bound:NonHalt known32_040 /\ Bounds 55 55 known32_040.
Proof.
 assert(H:NonHalt(mirror_tm known32_040) /\ Bounds 55 55(mirror_tm known32_040)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB1LC_1LA1RB_0LA0LA_______.tm_0RB1LC_1LA1RB_0LA0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_040 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LC_1LA1RB_0LA0LA_______.nqhtr_0RB1LC_1LA1RB_0LA0LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LC1RB_1LA0RA1RA1LC *)
Definition known32_041:TM:=machine_of_codes 3 2 [2;10;6;3;9;8].
Lemma known32_041_bound:NonHalt known32_041 /\ Bounds 55 55 known32_041.
Proof.
 assert(H:NonHalt(mirror_tm known32_041) /\ Bounds 55 55(mirror_tm known32_041)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB1LC_1LA1RB_1RA0LA_______.tm_0RB1LC_1LA1RB_1RA0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_041 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LC_1LA1RB_1RA0LA_______.nqhtr_0RB1LC_1LA1RB_1RA0LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LC1RB_1LC0RA1RA1LC *)
Definition known32_042:TM:=machine_of_codes 3 2 [2;10;8;3;9;8].
Lemma known32_042_bound:NonHalt known32_042 /\ Bounds 55 55 known32_042.
Proof.
 assert(H:NonHalt(mirror_tm known32_042) /\ Bounds 55 55(mirror_tm known32_042)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB1LC_1LA1RB_1RB0LA_______.tm_0RB1LC_1LA1RB_1RB0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_042 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LC_1LA1RB_1RB0LA_______.nqhtr_0RB1LC_1LA1RB_1RB0LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0LC1RB_1RA0RA1RA1LC *)
Definition known32_043:TM:=machine_of_codes 3 2 [2;10;9;3;9;8].
Lemma known32_043_bound:NonHalt known32_043 /\ Bounds 55 55 known32_043.
Proof.
 assert(H:NonHalt(mirror_tm known32_043) /\ Bounds 55 55(mirror_tm known32_043)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB1LC_1LA1RB_1LA0LA_______.tm_0RB1LC_1LA1RB_1LA0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_043 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LC_1LA1RB_1LA0LA_______.nqhtr_0RB1LC_1LA1RB_1LA0LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 0RB0LB_0RC1LB1LA1RC *)
Definition known32_044:TM:=machine_of_codes 3 2 [4;1;5;7;6;11].
Lemma known32_044_bound:NonHalt known32_044 /\ Bounds 55 55 known32_044.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_000).
 - split.
   + intros [] [] tr H; cbv [known32_044 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_000_recur.
Qed.
(* 0RB0LC_1LA1RB0RB1LC *)
Definition known32_045:TM:=machine_of_codes 3 2 [4;2;6;10;4;8].
Lemma known32_045_bound:NonHalt known32_045 /\ Bounds 55 55 known32_045.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_001).
 - split.
   + intros [] [] tr H; cbv [known32_045 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_001_recur.
Qed.
(* 0RB0LC_1LC1RB0RB1LA *)
Definition known32_046:TM:=machine_of_codes 3 2 [4;2;8;10;4;6].
Lemma known32_046_bound:NonHalt known32_046 /\ Bounds 55 55 known32_046.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB0LC_1LC1RB_0RB1LA_______.tm_0RB0LC_1LC1RB_0RB1LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_046 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB0LC_1LC1RB_0RB1LA_______.nqhtr_0RB0LC_1LC1RB_0RB1LA_______.
Qed.
(* 0RB0LC_1LC1RB1LA1LA *)
Definition known32_047:TM:=machine_of_codes 3 2 [4;2;8;10;6;6].
Lemma known32_047_bound:NonHalt known32_047 /\ Bounds 55 55 known32_047.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB0LC_1LC1RB_1LA1LA_______.tm_0RB0LC_1LC1RB_1LA1LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_047 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB0LC_1LC1RB_1LA1LA_______.nqhtr_0RB0LC_1LC1RB_1LA1LA_______.
Qed.
(* 0RB0LC_1LC1RB1RB1LA *)
Definition known32_048:TM:=machine_of_codes 3 2 [4;2;8;10;10;6].
Lemma known32_048_bound:NonHalt known32_048 /\ Bounds 55 55 known32_048.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB0LC_1LC1RB_1RB1LA_______.tm_0RB0LC_1LC1RB_1RB1LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_048 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB0LC_1LC1RB_1RB1LA_______.nqhtr_0RB0LC_1LC1RB_1RB1LA_______.
Qed.
(* 0RB0LC_1LC1RB1RC1LA *)
Definition known32_049:TM:=machine_of_codes 3 2 [4;2;8;10;11;6].
Lemma known32_049_bound:NonHalt known32_049 /\ Bounds 55 55 known32_049.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB0LC_1LC1RB_1RC1LA_______.tm_0RB0LC_1LC1RB_1RC1LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_049 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB0LC_1LC1RB_1RC1LA_______.nqhtr_0RB0LC_1LC1RB_1RC1LA_______.
Qed.
(* 0RB0RB_0LC1RA1RB1LC *)
Definition known32_050:TM:=machine_of_codes 3 2 [4;4;2;9;10;8].
Lemma known32_050_bound:NonHalt known32_050 /\ Bounds 55 55 known32_050.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB0RB_0LC1RA_1RB1LC_______.tm_0RB0RB_0LC1RA_1RB1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_050 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB0RB_0LC1RA_1RB1LC_______.nqhtr_0RB0RB_0LC1RA_1RB1LC_______.
Qed.
(* 0RB1LA_1LA1RC1RB0LA *)
Definition known32_051:TM:=machine_of_codes 3 2 [4;6;6;11;10;0].
Lemma known32_051_bound:NonHalt known32_051 /\ Bounds 55 55 known32_051.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB1LA_1LA1RC_1RB0LA_______.tm_0RB1LA_1LA1RC_1RB0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_051 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LA_1LA1RC_1RB0LA_______.nqhtr_0RB1LA_1LA1RC_1RB0LA_______.
Qed.
(* 0RB1LA_1LC1RB0RA0LA *)
Definition known32_052:TM:=machine_of_codes 3 2 [4;6;8;10;3;0].
Lemma known32_052_bound:NonHalt known32_052 /\ Bounds 55 55 known32_052.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_002).
 - split.
   + intros [] [] tr H; cbv [known32_052 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_002_recur.
Qed.
(* 0RB1LA_1LC1RB0RB0LA *)
Definition known32_053:TM:=machine_of_codes 3 2 [4;6;8;10;4;0].
Lemma known32_053_bound:NonHalt known32_053 /\ Bounds 55 55 known32_053.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_003).
 - split.
   + intros [] [] tr H; cbv [known32_053 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_003_recur.
Qed.
(* 0RB1LA_1LC1RB1LA0LA *)
Definition known32_054:TM:=machine_of_codes 3 2 [4;6;8;10;6;0].
Lemma known32_054_bound:NonHalt known32_054 /\ Bounds 55 55 known32_054.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_004).
 - split.
   + intros [] [] tr H; cbv [known32_054 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_004_recur.
Qed.
(* 0RB1LA_1LC1RB1RA0LA *)
Definition known32_055:TM:=machine_of_codes 3 2 [4;6;8;10;9;0].
Lemma known32_055_bound:NonHalt known32_055 /\ Bounds 55 55 known32_055.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_005).
 - split.
   + intros [] [] tr H; cbv [known32_055 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_005_recur.
Qed.
(* 0RB1LA_1LC1RB1RB0LA *)
Definition known32_056:TM:=machine_of_codes 3 2 [4;6;8;10;10;0].
Lemma known32_056_bound:NonHalt known32_056 /\ Bounds 55 55 known32_056.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_006).
 - split.
   + intros [] [] tr H; cbv [known32_056 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_006_recur.
Qed.
(* 0RB1LA_1LC1RC1RB0LA *)
Definition known32_057:TM:=machine_of_codes 3 2 [4;6;8;11;10;0].
Lemma known32_057_bound:NonHalt known32_057 /\ Bounds 55 55 known32_057.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB1LA_1LC1RC_1RB0LA_______.tm_0RB1LA_1LC1RC_1RB0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_057 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LA_1LC1RC_1RB0LA_______.nqhtr_0RB1LA_1LC1RC_1RB0LA_______.
Qed.
(* 0RB1LA_1RC0LA1LA1RB *)
Definition known32_058:TM:=machine_of_codes 3 2 [4;6;11;0;6;10].
Lemma known32_058_bound:NonHalt known32_058 /\ Bounds 55 55 known32_058.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB1LA_1RC0LA_1LA1RB_______.tm_0RB1LA_1RC0LA_1LA1RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_058 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LA_1RC0LA_1LA1RB_______.nqhtr_0RB1LA_1RC0LA_1LA1RB_______.
Qed.
(* 0RB1LA_1RC0LA1LB1RB *)
Definition known32_059:TM:=machine_of_codes 3 2 [4;6;11;0;7;10].
Lemma known32_059_bound:NonHalt known32_059 /\ Bounds 55 55 known32_059.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB1LA_1RC0LA_1LB1RB_______.tm_0RB1LA_1RC0LA_1LB1RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_059 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LA_1RC0LA_1LB1RB_______.nqhtr_0RB1LA_1RC0LA_1LB1RB_______.
Qed.
(* 0RB1LC_1LA1RB0LA0LA *)
Definition known32_060:TM:=machine_of_codes 3 2 [4;8;6;10;0;0].
Lemma known32_060_bound:NonHalt known32_060 /\ Bounds 55 55 known32_060.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB1LC_1LA1RB_0LA0LA_______.tm_0RB1LC_1LA1RB_0LA0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_060 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LC_1LA1RB_0LA0LA_______.nqhtr_0RB1LC_1LA1RB_0LA0LA_______.
Qed.
(* 0RB1LC_1LA1RB0RB0LA *)
Definition known32_061:TM:=machine_of_codes 3 2 [4;8;6;10;4;0].
Lemma known32_061_bound:NonHalt known32_061 /\ Bounds 55 55 known32_061.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB1LC_1LA1RB_0RB0LA_______.tm_0RB1LC_1LA1RB_0RB0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_061 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LC_1LA1RB_0RB0LA_______.nqhtr_0RB1LC_1LA1RB_0RB0LA_______.
Qed.
(* 0RB1LC_1LA1RB0RC0LA *)
Definition known32_062:TM:=machine_of_codes 3 2 [4;8;6;10;5;0].
Lemma known32_062_bound:NonHalt known32_062 /\ Bounds 55 55 known32_062.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB1LC_1LA1RB_0RC0LA_______.tm_0RB1LC_1LA1RB_0RC0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_062 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LC_1LA1RB_0RC0LA_______.nqhtr_0RB1LC_1LA1RB_0RC0LA_______.
Qed.
(* 0RB1LC_1LA1RB1LA0LA *)
Definition known32_063:TM:=machine_of_codes 3 2 [4;8;6;10;6;0].
Lemma known32_063_bound:NonHalt known32_063 /\ Bounds 55 55 known32_063.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB1LC_1LA1RB_1LA0LA_______.tm_0RB1LC_1LA1RB_1LA0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_063 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LC_1LA1RB_1LA0LA_______.nqhtr_0RB1LC_1LA1RB_1LA0LA_______.
Qed.
(* 0RB1LC_1LA1RB1RA0LA *)
Definition known32_064:TM:=machine_of_codes 3 2 [4;8;6;10;9;0].
Lemma known32_064_bound:NonHalt known32_064 /\ Bounds 55 55 known32_064.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB1LC_1LA1RB_1RA0LA_______.tm_0RB1LC_1LA1RB_1RA0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_064 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LC_1LA1RB_1RA0LA_______.nqhtr_0RB1LC_1LA1RB_1RA0LA_______.
Qed.
(* 0RB1LC_1LA1RB1RB0LA *)
Definition known32_065:TM:=machine_of_codes 3 2 [4;8;6;10;10;0].
Lemma known32_065_bound:NonHalt known32_065 /\ Bounds 55 55 known32_065.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_0RB1LC_1LA1RB_1RB0LA_______.tm_0RB1LC_1LA1RB_1RB0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_065 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LC_1LA1RB_1RB0LA_______.nqhtr_0RB1LC_1LA1RB_1RB0LA_______.
Qed.
(* 0RC0LB_0RC1LA1LB1RC *)
Definition known32_066:TM:=machine_of_codes 3 2 [5;1;5;6;7;11].
Lemma known32_066_bound:NonHalt known32_066 /\ Bounds 55 55 known32_066.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB0LC_1LC1RB_0RB1LA_______.tm_0RB0LC_1LC1RB_0RB1LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_066 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB0LC_1LC1RB_0RB1LA_______.nqhtr_0RB0LC_1LC1RB_0RB1LA_______.
Qed.
(* 0RC0LB_0RC1LB1LA1RC *)
Definition known32_067:TM:=machine_of_codes 3 2 [5;1;5;7;6;11].
Lemma known32_067_bound:NonHalt known32_067 /\ Bounds 55 55 known32_067.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_001).
 - split.
   + intros [] [] tr H; cbv [known32_067 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_001_recur.
Qed.
(* 0RC0LB_1LA1LA1LB1RC *)
Definition known32_068:TM:=machine_of_codes 3 2 [5;1;6;6;7;11].
Lemma known32_068_bound:NonHalt known32_068 /\ Bounds 55 55 known32_068.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB0LC_1LC1RB_1LA1LA_______.tm_0RB0LC_1LC1RB_1LA1LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_068 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB0LC_1LC1RB_1LA1LA_______.nqhtr_0RB0LC_1LC1RB_1LA1LA_______.
Qed.
(* 0RC0LB_1RB1LA1LB1RC *)
Definition known32_069:TM:=machine_of_codes 3 2 [5;1;10;6;7;11].
Lemma known32_069_bound:NonHalt known32_069 /\ Bounds 55 55 known32_069.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB0LC_1LC1RB_1RC1LA_______.tm_0RB0LC_1LC1RB_1RC1LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_069 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB0LC_1LC1RB_1RC1LA_______.nqhtr_0RB0LC_1LC1RB_1RC1LA_______.
Qed.
(* 0RC0LB_1RC1LA1LB1RC *)
Definition known32_070:TM:=machine_of_codes 3 2 [5;1;11;6;7;11].
Lemma known32_070_bound:NonHalt known32_070 /\ Bounds 55 55 known32_070.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB0LC_1LC1RB_1RB1LA_______.tm_0RB0LC_1LC1RB_1RB1LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_070 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB0LC_1LC1RB_1RB1LA_______.nqhtr_0RB0LC_1LC1RB_1RB1LA_______.
Qed.
(* 0RC0LC_1LA1RB0RB1LC *)
Definition known32_071:TM:=machine_of_codes 3 2 [5;2;6;10;4;8].
Lemma known32_071_bound:NonHalt known32_071 /\ Bounds 55 55 known32_071.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_000).
 - split.
   + intros [] [] tr H; cbv [known32_071 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_000_recur.
Qed.
(* 0RC0RC_1RC1LB0LB1RA *)
Definition known32_072:TM:=machine_of_codes 3 2 [5;5;11;7;1;9].
Lemma known32_072_bound:NonHalt known32_072 /\ Bounds 55 55 known32_072.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB0RB_0LC1RA_1RB1LC_______.tm_0RB0RB_0LC1RA_1RB1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_072 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB0RB_0LC1RA_1RB1LC_______.nqhtr_0RB0RB_0LC1RA_1RB1LC_______.
Qed.
(* 0RC1LA_0RA0LA1LB1RC *)
Definition known32_073:TM:=machine_of_codes 3 2 [5;6;3;0;7;11].
Lemma known32_073_bound:NonHalt known32_073 /\ Bounds 55 55 known32_073.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_002).
 - split.
   + intros [] [] tr H; cbv [known32_073 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_002_recur.
Qed.
(* 0RC1LA_0RC0LA1LB1RC *)
Definition known32_074:TM:=machine_of_codes 3 2 [5;6;5;0;7;11].
Lemma known32_074_bound:NonHalt known32_074 /\ Bounds 55 55 known32_074.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_003).
 - split.
   + intros [] [] tr H; cbv [known32_074 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_003_recur.
Qed.
(* 0RC1LA_1LA0LA1LB1RC *)
Definition known32_075:TM:=machine_of_codes 3 2 [5;6;6;0;7;11].
Lemma known32_075_bound:NonHalt known32_075 /\ Bounds 55 55 known32_075.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_004).
 - split.
   + intros [] [] tr H; cbv [known32_075 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_004_recur.
Qed.
(* 0RC1LA_1LA1RC1RB0LA *)
Definition known32_076:TM:=machine_of_codes 3 2 [5;6;6;11;10;0].
Lemma known32_076_bound:NonHalt known32_076 /\ Bounds 55 55 known32_076.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB1LA_1RC0LA_1LA1RB_______.tm_0RB1LA_1RC0LA_1LA1RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_076 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LA_1RC0LA_1LA1RB_______.nqhtr_0RB1LA_1RC0LA_1LA1RB_______.
Qed.
(* 0RC1LA_1LC1RC1RB0LA *)
Definition known32_077:TM:=machine_of_codes 3 2 [5;6;8;11;10;0].
Lemma known32_077_bound:NonHalt known32_077 /\ Bounds 55 55 known32_077.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB1LA_1RC0LA_1LB1RB_______.tm_0RB1LA_1RC0LA_1LB1RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_077 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LA_1RC0LA_1LB1RB_______.nqhtr_0RB1LA_1RC0LA_1LB1RB_______.
Qed.
(* 0RC1LA_1RA0LA1LB1RC *)
Definition known32_078:TM:=machine_of_codes 3 2 [5;6;9;0;7;11].
Lemma known32_078_bound:NonHalt known32_078 /\ Bounds 55 55 known32_078.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_005).
 - split.
   + intros [] [] tr H; cbv [known32_078 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_005_recur.
Qed.
(* 0RC1LA_1RC0LA1LA1RB *)
Definition known32_079:TM:=machine_of_codes 3 2 [5;6;11;0;6;10].
Lemma known32_079_bound:NonHalt known32_079 /\ Bounds 55 55 known32_079.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB1LA_1LA1RC_1RB0LA_______.tm_0RB1LA_1LA1RC_1RB0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_079 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LA_1LA1RC_1RB0LA_______.nqhtr_0RB1LA_1LA1RC_1RB0LA_______.
Qed.
(* 0RC1LA_1RC0LA1LB1RB *)
Definition known32_080:TM:=machine_of_codes 3 2 [5;6;11;0;7;10].
Lemma known32_080_bound:NonHalt known32_080 /\ Bounds 55 55 known32_080.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB1LA_1LC1RC_1RB0LA_______.tm_0RB1LA_1LC1RC_1RB0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_080 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LA_1LC1RC_1RB0LA_______.nqhtr_0RB1LA_1LC1RC_1RB0LA_______.
Qed.
(* 0RC1LA_1RC0LA1LB1RC *)
Definition known32_081:TM:=machine_of_codes 3 2 [5;6;11;0;7;11].
Lemma known32_081_bound:NonHalt known32_081 /\ Bounds 55 55 known32_081.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_006).
 - split.
   + intros [] [] tr H; cbv [known32_081 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_006_recur.
Qed.
(* 0RC1LB_0LA0LA1LA1RC *)
Definition known32_082:TM:=machine_of_codes 3 2 [5;7;0;0;6;11].
Lemma known32_082_bound:NonHalt known32_082 /\ Bounds 55 55 known32_082.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB1LC_1LA1RB_0LA0LA_______.tm_0RB1LC_1LA1RB_0LA0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_082 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LC_1LA1RB_0LA0LA_______.nqhtr_0RB1LC_1LA1RB_0LA0LA_______.
Qed.
(* 0RC1LB_0RB0LA1LA1RC *)
Definition known32_083:TM:=machine_of_codes 3 2 [5;7;4;0;6;11].
Lemma known32_083_bound:NonHalt known32_083 /\ Bounds 55 55 known32_083.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB1LC_1LA1RB_0RC0LA_______.tm_0RB1LC_1LA1RB_0RC0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_083 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LC_1LA1RB_0RC0LA_______.nqhtr_0RB1LC_1LA1RB_0RC0LA_______.
Qed.
(* 0RC1LB_0RC0LA1LA1RC *)
Definition known32_084:TM:=machine_of_codes 3 2 [5;7;5;0;6;11].
Lemma known32_084_bound:NonHalt known32_084 /\ Bounds 55 55 known32_084.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB1LC_1LA1RB_0RB0LA_______.tm_0RB1LC_1LA1RB_0RB0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_084 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LC_1LA1RB_0RB0LA_______.nqhtr_0RB1LC_1LA1RB_0RB0LA_______.
Qed.
(* 0RC1LB_1LA0LA1LA1RC *)
Definition known32_085:TM:=machine_of_codes 3 2 [5;7;6;0;6;11].
Lemma known32_085_bound:NonHalt known32_085 /\ Bounds 55 55 known32_085.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB1LC_1LA1RB_1LA0LA_______.tm_0RB1LC_1LA1RB_1LA0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_085 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LC_1LA1RB_1LA0LA_______.nqhtr_0RB1LC_1LA1RB_1LA0LA_______.
Qed.
(* 0RC1LB_1RA0LA1LA1RC *)
Definition known32_086:TM:=machine_of_codes 3 2 [5;7;9;0;6;11].
Lemma known32_086_bound:NonHalt known32_086 /\ Bounds 55 55 known32_086.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB1LC_1LA1RB_1RA0LA_______.tm_0RB1LC_1LA1RB_1RA0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_086 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LC_1LA1RB_1RA0LA_______.nqhtr_0RB1LC_1LA1RB_1RA0LA_______.
Qed.
(* 0RC1LB_1RC0LA1LA1RC *)
Definition known32_087:TM:=machine_of_codes 3 2 [5;7;11;0;6;11].
Lemma known32_087_bound:NonHalt known32_087 /\ Bounds 55 55 known32_087.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_0RB1LC_1LA1RB_1RB0LA_______.tm_0RB1LC_1LA1RB_1RB0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_087 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_0RB1LC_1LA1RB_1RB0LA_______.nqhtr_0RB1LC_1LA1RB_1RB0LA_______.
Qed.
(* 1LB0LB_0RC1LA1LB1RC *)
Definition known32_088:TM:=machine_of_codes 3 2 [7;1;5;6;7;11].
Lemma known32_088_bound:NonHalt known32_088 /\ Bounds 55 55 known32_088.
Proof.
 assert(H:NonHalt(mirror_tm known32_088) /\ Bounds 55 55(mirror_tm known32_088)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB0RB_0LC1RA_1RB1LC_______.tm_1RB0RB_0LC1RA_1RB1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_088 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0RB_0LC1RA_1RB1LC_______.nqhtr_1RB0RB_0LC1RA_1RB1LC_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB0LB_0RC1LB1LA1RC *)
Definition known32_089:TM:=machine_of_codes 3 2 [7;1;5;7;6;11].
Lemma known32_089_bound:NonHalt known32_089 /\ Bounds 55 55 known32_089.
Proof.
 assert(H:NonHalt(mirror_tm known32_089) /\ Bounds 55 55(mirror_tm known32_089)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_011).
 - split.
   + intros [] [] tr H; cbv [known32_089 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_011_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB0RB_0LC1RA1RB1LC *)
Definition known32_090:TM:=machine_of_codes 3 2 [7;4;2;9;10;8].
Lemma known32_090_bound:NonHalt known32_090 /\ Bounds 55 55 known32_090.
Proof.
 assert(H:NonHalt(mirror_tm known32_090) /\ Bounds 55 55(mirror_tm known32_090)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB0LB_0RC1LA_1LB1RC_______.tm_1RB0LB_0RC1LA_1LB1RC_______).
 - split.
   + intros [] [] tr H; cbv [known32_090 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0LB_0RC1LA_1LB1RC_______.nqhtr_1RB0LB_0RC1LA_1LB1RC_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB0RB_0LC1RB1RA1LC *)
Definition known32_091:TM:=machine_of_codes 3 2 [7;4;2;10;9;8].
Lemma known32_091_bound:NonHalt known32_091 /\ Bounds 55 55 known32_091.
Proof.
 assert(H:NonHalt(mirror_tm known32_091) /\ Bounds 55 55(mirror_tm known32_091)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_007).
 - split.
   + intros [] [] tr H; cbv [known32_091 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_007_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB0RC_1LC1LA1RA0LB *)
Definition known32_092:TM:=machine_of_codes 3 2 [7;5;8;6;9;1].
Lemma known32_092_bound:NonHalt known32_092 /\ Bounds 55 55 known32_092.
Proof.
 assert(H:NonHalt(mirror_tm known32_092) /\ Bounds 55 55(mirror_tm known32_092)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_010).
 - split.
   + intros [] [] tr H; cbv [known32_092 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_010_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB0RC_1RA1LA0LA1RC *)
Definition known32_093:TM:=machine_of_codes 3 2 [7;5;9;6;0;11].
Lemma known32_093_bound:NonHalt known32_093 /\ Bounds 55 55 known32_093.
Proof.
 assert(H:NonHalt(mirror_tm known32_093) /\ Bounds 55 55(mirror_tm known32_093)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB0LC_1LA1RA_0RA1LC_______.tm_1RB0LC_1LA1RA_0RA1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_093 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0LC_1LA1RA_0RA1LC_______.nqhtr_1RB0LC_1LA1RA_0RA1LC_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB0RC_1RA1LA0LB1RC *)
Definition known32_094:TM:=machine_of_codes 3 2 [7;5;9;6;1;11].
Lemma known32_094_bound:NonHalt known32_094 /\ Bounds 55 55 known32_094.
Proof.
 assert(H:NonHalt(mirror_tm known32_094) /\ Bounds 55 55(mirror_tm known32_094)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB0LC_1LA1RA_0RB1LC_______.tm_1RB0LC_1LA1RA_0RB1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_094 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0LC_1LA1RA_0RB1LC_______.nqhtr_1RB0LC_1LA1RA_0RB1LC_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB0RC_1RA1LB0LB1RC *)
Definition known32_095:TM:=machine_of_codes 3 2 [7;5;9;7;1;11].
Lemma known32_095_bound:NonHalt known32_095 /\ Bounds 55 55 known32_095.
Proof.
 assert(H:NonHalt(mirror_tm known32_095) /\ Bounds 55 55(mirror_tm known32_095)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_008).
 - split.
   + intros [] [] tr H; cbv [known32_095 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_008_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB0RC_1RC0LA1RA1RB *)
Definition known32_096:TM:=machine_of_codes 3 2 [7;5;11;0;9;10].
Lemma known32_096_bound:NonHalt known32_096 /\ Bounds 55 55 known32_096.
Proof.
 assert(H:NonHalt(mirror_tm known32_096) /\ Bounds 55 55(mirror_tm known32_096)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_009).
 - split.
   + intros [] [] tr H; cbv [known32_096 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_009_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB0RC_1RC1LA0LA1RC *)
Definition known32_097:TM:=machine_of_codes 3 2 [7;5;11;6;0;11].
Lemma known32_097_bound:NonHalt known32_097 /\ Bounds 55 55 known32_097.
Proof.
 assert(H:NonHalt(mirror_tm known32_097) /\ Bounds 55 55(mirror_tm known32_097)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB0LC_1LC1RA_0RA1LC_______.tm_1RB0LC_1LC1RA_0RA1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_097 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0LC_1LC1RA_0RA1LC_______.nqhtr_1RB0LC_1LC1RA_0RA1LC_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB0RC_1RC1LA0LB1RC *)
Definition known32_098:TM:=machine_of_codes 3 2 [7;5;11;6;1;11].
Lemma known32_098_bound:NonHalt known32_098 /\ Bounds 55 55 known32_098.
Proof.
 assert(H:NonHalt(mirror_tm known32_098) /\ Bounds 55 55(mirror_tm known32_098)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB0LC_1LC1RA_0RB1LC_______.tm_1RB0LC_1LC1RA_0RB1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_098 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0LC_1LC1RA_0RB1LC_______.nqhtr_1RB0LC_1LC1RA_0RB1LC_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB0RC_1RC1LB0LB1RA *)
Definition known32_099:TM:=machine_of_codes 3 2 [7;5;11;7;1;9].
Lemma known32_099_bound:NonHalt known32_099 /\ Bounds 55 55 known32_099.
Proof.
 assert(H:NonHalt(mirror_tm known32_099) /\ Bounds 55 55(mirror_tm known32_099)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB0LC_1LC1RB_0RB1LA_______.tm_1RB0LC_1LC1RB_0RB1LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_099 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0LC_1LC1RB_0RB1LA_______.nqhtr_1RB0LC_1LC1RB_0RB1LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB1LA_1RC1LA0LB0RC *)
Definition known32_100:TM:=machine_of_codes 3 2 [7;6;11;6;1;5].
Lemma known32_100_bound:NonHalt known32_100 /\ Bounds 55 55 known32_100.
Proof.
 assert(H:NonHalt(mirror_tm known32_100) /\ Bounds 55 55(mirror_tm known32_100)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1RA_1LC1RA_0RB0LC_______.tm_1RB1RA_1LC1RA_0RB0LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_100 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1RA_1LC1RA_0RB0LC_______.nqhtr_1RB1RA_1LC1RA_0RB0LC_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB1LB_0RC0LA1LA1RC *)
Definition known32_101:TM:=machine_of_codes 3 2 [7;7;5;0;6;11].
Lemma known32_101_bound:NonHalt known32_101 /\ Bounds 55 55 known32_101.
Proof.
 assert(H:NonHalt(mirror_tm known32_101) /\ Bounds 55 55(mirror_tm known32_101)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1RB_0LC0RA_1RA1LC_______.tm_1RB1RB_0LC0RA_1RA1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_101 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1RB_0LC0RA_1RA1LC_______.nqhtr_1RB1RB_0LC0RA_1RA1LC_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB1LC_1RC0LA1LA0RB *)
Definition known32_102:TM:=machine_of_codes 3 2 [7;8;11;0;6;4].
Lemma known32_102_bound:NonHalt known32_102 /\ Bounds 55 55 known32_102.
Proof.
 assert(H:NonHalt(mirror_tm known32_102) /\ Bounds 55 55(mirror_tm known32_102)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_017).
 - split.
   + intros [] [] tr H; cbv [known32_102 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_017_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB1RA_0RA0LC0RA1LC *)
Definition known32_103:TM:=machine_of_codes 3 2 [7;9;3;2;3;8].
Lemma known32_103_bound:NonHalt known32_103 /\ Bounds 55 55 known32_103.
Proof.
 assert(H:NonHalt(mirror_tm known32_103) /\ Bounds 55 55(mirror_tm known32_103)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_012).
 - split.
   + intros [] [] tr H; cbv [known32_103 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_012_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB1RA_0RA1LC0LB0LB *)
Definition known32_104:TM:=machine_of_codes 3 2 [7;9;3;8;1;1].
Lemma known32_104_bound:NonHalt known32_104 /\ Bounds 55 55 known32_104.
Proof.
 assert(H:NonHalt(mirror_tm known32_104) /\ Bounds 55 55(mirror_tm known32_104)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LA_0LA1RC_0RB0RB_______.tm_1RB1LA_0LA1RC_0RB0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_104 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_0LA1RC_0RB0RB_______.nqhtr_1RB1LA_0LA1RC_0RB0RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB1RA_0RA1LC0RA0LB *)
Definition known32_105:TM:=machine_of_codes 3 2 [7;9;3;8;3;1].
Lemma known32_105_bound:NonHalt known32_105 /\ Bounds 55 55 known32_105.
Proof.
 assert(H:NonHalt(mirror_tm known32_105) /\ Bounds 55 55(mirror_tm known32_105)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LA_0LA1RC_0LA0RB_______.tm_1RB1LA_0LA1RC_0LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_105 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_0LA1RC_0LA0RB_______.nqhtr_1RB1LA_0LA1RC_0LA0RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB1RA_0RA1LC0RC0LB *)
Definition known32_106:TM:=machine_of_codes 3 2 [7;9;3;8;5;1].
Lemma known32_106_bound:NonHalt known32_106 /\ Bounds 55 55 known32_106.
Proof.
 assert(H:NonHalt(mirror_tm known32_106) /\ Bounds 55 55(mirror_tm known32_106)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LA_0LA1RC_0LC0RB_______.tm_1RB1LA_0LA1RC_0LC0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_106 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_0LA1RC_0LC0RB_______.nqhtr_1RB1LA_0LA1RC_0LC0RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB1RA_0RA1LC1LB0LB *)
Definition known32_107:TM:=machine_of_codes 3 2 [7;9;3;8;7;1].
Lemma known32_107_bound:NonHalt known32_107 /\ Bounds 55 55 known32_107.
Proof.
 assert(H:NonHalt(mirror_tm known32_107) /\ Bounds 55 55(mirror_tm known32_107)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LA_0LA1RC_1RB0RB_______.tm_1RB1LA_0LA1RC_1RB0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_107 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_0LA1RC_1RB0RB_______.nqhtr_1RB1LA_0LA1RC_1RB0RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB1RA_0RA1LC1RA0LB *)
Definition known32_108:TM:=machine_of_codes 3 2 [7;9;3;8;9;1].
Lemma known32_108_bound:NonHalt known32_108 /\ Bounds 55 55 known32_108.
Proof.
 assert(H:NonHalt(mirror_tm known32_108) /\ Bounds 55 55(mirror_tm known32_108)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LA_0LA1RC_1LA0RB_______.tm_1RB1LA_0LA1RC_1LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_108 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_0LA1RC_1LA0RB_______.nqhtr_1RB1LA_0LA1RC_1LA0RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB1RA_0RA1LC1RB0LB *)
Definition known32_109:TM:=machine_of_codes 3 2 [7;9;3;8;10;1].
Lemma known32_109_bound:NonHalt known32_109 /\ Bounds 55 55 known32_109.
Proof.
 assert(H:NonHalt(mirror_tm known32_109) /\ Bounds 55 55(mirror_tm known32_109)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LA_0LA1RC_1LB0RB_______.tm_1RB1LA_0LA1RC_1LB0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_109 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_0LA1RC_1LB0RB_______.nqhtr_1RB1LA_0LA1RC_1LB0RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB1RA_0RC0LC0RA1LC *)
Definition known32_110:TM:=machine_of_codes 3 2 [7;9;5;2;3;8].
Lemma known32_110_bound:NonHalt known32_110 /\ Bounds 55 55 known32_110.
Proof.
 assert(H:NonHalt(mirror_tm known32_110) /\ Bounds 55 55(mirror_tm known32_110)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_013).
 - split.
   + intros [] [] tr H; cbv [known32_110 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_013_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB1RA_1LC0LC0RA1LC *)
Definition known32_111:TM:=machine_of_codes 3 2 [7;9;8;2;3;8].
Lemma known32_111_bound:NonHalt known32_111 /\ Bounds 55 55 known32_111.
Proof.
 assert(H:NonHalt(mirror_tm known32_111) /\ Bounds 55 55(mirror_tm known32_111)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_016).
 - split.
   + intros [] [] tr H; cbv [known32_111 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_016_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB1RA_1LC1LC0RA0LB *)
Definition known32_112:TM:=machine_of_codes 3 2 [7;9;8;8;3;1].
Lemma known32_112_bound:NonHalt known32_112 /\ Bounds 55 55 known32_112.
Proof.
 assert(H:NonHalt(mirror_tm known32_112) /\ Bounds 55 55(mirror_tm known32_112)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LA_1RC1RC_0LA0RB_______.tm_1RB1LA_1RC1RC_0LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_112 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_1RC1RC_0LA0RB_______.nqhtr_1RB1LA_1RC1RC_0LA0RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB1RA_1RA0LC0RA1LC *)
Definition known32_113:TM:=machine_of_codes 3 2 [7;9;9;2;3;8].
Lemma known32_113_bound:NonHalt known32_113 /\ Bounds 55 55 known32_113.
Proof.
 assert(H:NonHalt(mirror_tm known32_113) /\ Bounds 55 55(mirror_tm known32_113)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_014).
 - split.
   + intros [] [] tr H; cbv [known32_113 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_014_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB1RA_1RA1LC0RA0LB *)
Definition known32_114:TM:=machine_of_codes 3 2 [7;9;9;8;3;1].
Lemma known32_114_bound:NonHalt known32_114 /\ Bounds 55 55 known32_114.
Proof.
 assert(H:NonHalt(mirror_tm known32_114) /\ Bounds 55 55(mirror_tm known32_114)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LA_1LA1RC_0LA0RB_______.tm_1RB1LA_1LA1RC_0LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_114 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_1LA1RC_0LA0RB_______.nqhtr_1RB1LA_1LA1RC_0LA0RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB1RA_1RB1LC0RA0LB *)
Definition known32_115:TM:=machine_of_codes 3 2 [7;9;10;8;3;1].
Lemma known32_115_bound:NonHalt known32_115 /\ Bounds 55 55 known32_115.
Proof.
 assert(H:NonHalt(mirror_tm known32_115) /\ Bounds 55 55(mirror_tm known32_115)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LA_1LB1RC_0LA0RB_______.tm_1RB1LA_1LB1RC_0LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_115 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_1LB1RC_0LA0RB_______.nqhtr_1RB1LA_1LB1RC_0LA0RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB1RA_1RC0LC0RA1LC *)
Definition known32_116:TM:=machine_of_codes 3 2 [7;9;11;2;3;8].
Lemma known32_116_bound:NonHalt known32_116 /\ Bounds 55 55 known32_116.
Proof.
 assert(H:NonHalt(mirror_tm known32_116) /\ Bounds 55 55(mirror_tm known32_116)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_015).
 - split.
   + intros [] [] tr H; cbv [known32_116 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_015_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB1RB_1RA0LC0RA1LC *)
Definition known32_117:TM:=machine_of_codes 3 2 [7;10;9;2;3;8].
Lemma known32_117_bound:NonHalt known32_117 /\ Bounds 55 55 known32_117.
Proof.
 assert(H:NonHalt(mirror_tm known32_117) /\ Bounds 55 55(mirror_tm known32_117)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LB_1LA0RC_0LA1RC_______.tm_1RB1LB_1LA0RC_0LA1RC_______).
 - split.
   + intros [] [] tr H; cbv [known32_117 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LB_1LA0RC_0LA1RC_______.nqhtr_1RB1LB_1LA0RC_0LA1RC_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB1RB_1RA0LC0RB1LC *)
Definition known32_118:TM:=machine_of_codes 3 2 [7;10;9;2;4;8].
Lemma known32_118_bound:NonHalt known32_118 /\ Bounds 55 55 known32_118.
Proof.
 assert(H:NonHalt(mirror_tm known32_118) /\ Bounds 55 55(mirror_tm known32_118)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LB_1LA0RC_0LB1RC_______.tm_1RB1LB_1LA0RC_0LB1RC_______).
 - split.
   + intros [] [] tr H; cbv [known32_118 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LB_1LA0RC_0LB1RC_______.nqhtr_1RB1LB_1LA0RC_0LB1RC_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB1RC_0RA1LB1RA0LB *)
Definition known32_119:TM:=machine_of_codes 3 2 [7;11;3;7;9;1].
Lemma known32_119_bound:NonHalt known32_119 /\ Bounds 55 55 known32_119.
Proof.
 assert(H:NonHalt(mirror_tm known32_119) /\ Bounds 55 55(mirror_tm known32_119)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LC_0LA1RB_1LA0RB_______.tm_1RB1LC_0LA1RB_1LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_119 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LC_0LA1RB_1LA0RB_______.nqhtr_1RB1LC_0LA1RB_1LA0RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB1RC_0RC0LB1RA1RC *)
Definition known32_120:TM:=machine_of_codes 3 2 [7;11;5;1;9;11].
Lemma known32_120_bound:NonHalt known32_120 /\ Bounds 55 55 known32_120.
Proof.
 assert(H:NonHalt(mirror_tm known32_120) /\ Bounds 55 55(mirror_tm known32_120)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LC_0LC0RB_1LA1LC_______.tm_1RB1LC_0LC0RB_1LA1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_120 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LC_0LC0RB_1LA1LC_______.nqhtr_1RB1LC_0LC0RB_1LA1LC_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB1RC_0RC1LB1RA0LB *)
Definition known32_121:TM:=machine_of_codes 3 2 [7;11;5;7;9;1].
Lemma known32_121_bound:NonHalt known32_121 /\ Bounds 55 55 known32_121.
Proof.
 assert(H:NonHalt(mirror_tm known32_121) /\ Bounds 55 55(mirror_tm known32_121)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LC_0LC1RB_1LA0RB_______.tm_1RB1LC_0LC1RB_1LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_121 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LC_0LC1RB_1LA0RB_______.nqhtr_1RB1LC_0LC1RB_1LA0RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LB1RC_1RA1LB0LB0RA *)
Definition known32_122:TM:=machine_of_codes 3 2 [7;11;9;7;1;3].
Lemma known32_122_bound:NonHalt known32_122 /\ Bounds 55 55 known32_122.
Proof.
 assert(H:NonHalt(mirror_tm known32_122) /\ Bounds 55 55(mirror_tm known32_122)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LC_1LA1RB_0RB0LA_______.tm_1RB1LC_1LA1RB_0RB0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_122 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LC_1LA1RB_0RB0LA_______.nqhtr_1RB1LC_1LA1RB_0RB0LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC0LC_1LA1RB0RB1LC *)
Definition known32_123:TM:=machine_of_codes 3 2 [8;2;6;10;4;8].
Lemma known32_123_bound:NonHalt known32_123 /\ Bounds 55 55 known32_123.
Proof.
 assert(H:NonHalt(mirror_tm known32_123) /\ Bounds 55 55(mirror_tm known32_123)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_011).
 - split.
   + intros [] [] tr H; cbv [known32_123 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_011_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC0LC_1LC1RB0RB1LA *)
Definition known32_124:TM:=machine_of_codes 3 2 [8;2;8;10;4;6].
Lemma known32_124_bound:NonHalt known32_124 /\ Bounds 55 55 known32_124.
Proof.
 assert(H:NonHalt(mirror_tm known32_124) /\ Bounds 55 55(mirror_tm known32_124)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB0RB_0LC1RA_1RB1LC_______.tm_1RB0RB_0LC1RA_1RB1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_124 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0RB_0LC1RA_1RB1LC_______.nqhtr_1RB0RB_0LC1RA_1RB1LC_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC0RB_0LA1RB1RA1LA *)
Definition known32_125:TM:=machine_of_codes 3 2 [8;4;0;10;9;6].
Lemma known32_125_bound:NonHalt known32_125 /\ Bounds 55 55 known32_125.
Proof.
 assert(H:NonHalt(mirror_tm known32_125) /\ Bounds 55 55(mirror_tm known32_125)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB0LC_1LA1RA_0RA1LC_______.tm_1RB0LC_1LA1RA_0RA1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_125 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0LC_1LA1RA_0RA1LC_______.nqhtr_1RB0LC_1LA1RA_0RA1LC_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC0RB_0LA1RB1RB1LA *)
Definition known32_126:TM:=machine_of_codes 3 2 [8;4;0;10;10;6].
Lemma known32_126_bound:NonHalt known32_126 /\ Bounds 55 55 known32_126.
Proof.
 assert(H:NonHalt(mirror_tm known32_126) /\ Bounds 55 55(mirror_tm known32_126)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB0LC_1LC1RA_0RA1LC_______.tm_1RB0LC_1LC1RA_0RA1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_126 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0LC_1LC1RA_0RA1LC_______.nqhtr_1RB0LC_1LC1RA_0RA1LC_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC0RB_0LC1RA1RB1LC *)
Definition known32_127:TM:=machine_of_codes 3 2 [8;4;2;9;10;8].
Lemma known32_127_bound:NonHalt known32_127 /\ Bounds 55 55 known32_127.
Proof.
 assert(H:NonHalt(mirror_tm known32_127) /\ Bounds 55 55(mirror_tm known32_127)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB0LC_1LC1RB_0RB1LA_______.tm_1RB0LC_1LC1RB_0RB1LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_127 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0LC_1LC1RB_0RB1LA_______.nqhtr_1RB0LC_1LC1RB_0RB1LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC0RB_0LC1RB1RA1LA *)
Definition known32_128:TM:=machine_of_codes 3 2 [8;4;2;10;9;6].
Lemma known32_128_bound:NonHalt known32_128 /\ Bounds 55 55 known32_128.
Proof.
 assert(H:NonHalt(mirror_tm known32_128) /\ Bounds 55 55(mirror_tm known32_128)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB0LC_1LA1RA_0RB1LC_______.tm_1RB0LC_1LA1RA_0RB1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_128 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0LC_1LA1RA_0RB1LC_______.nqhtr_1RB0LC_1LA1RA_0RB1LC_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC0RB_0LC1RB1RA1LC *)
Definition known32_129:TM:=machine_of_codes 3 2 [8;4;2;10;9;8].
Lemma known32_129_bound:NonHalt known32_129 /\ Bounds 55 55 known32_129.
Proof.
 assert(H:NonHalt(mirror_tm known32_129) /\ Bounds 55 55(mirror_tm known32_129)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_008).
 - split.
   + intros [] [] tr H; cbv [known32_129 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_008_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC0RB_0LC1RB1RB1LA *)
Definition known32_130:TM:=machine_of_codes 3 2 [8;4;2;10;10;6].
Lemma known32_130_bound:NonHalt known32_130 /\ Bounds 55 55 known32_130.
Proof.
 assert(H:NonHalt(mirror_tm known32_130) /\ Bounds 55 55(mirror_tm known32_130)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB0LC_1LC1RA_0RB1LC_______.tm_1RB0LC_1LC1RA_0RB1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_130 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0LC_1LC1RA_0RB1LC_______.nqhtr_1RB0LC_1LC1RA_0RB1LC_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC0RB_1RA0LC1LB1LA *)
Definition known32_131:TM:=machine_of_codes 3 2 [8;4;9;2;7;6].
Lemma known32_131_bound:NonHalt known32_131 /\ Bounds 55 55 known32_131.
Proof.
 assert(H:NonHalt(mirror_tm known32_131) /\ Bounds 55 55(mirror_tm known32_131)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_010).
 - split.
   + intros [] [] tr H; cbv [known32_131 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_010_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC0RB_1RA1RC1RB0LA *)
Definition known32_132:TM:=machine_of_codes 3 2 [8;4;9;11;10;0].
Lemma known32_132_bound:NonHalt known32_132 /\ Bounds 55 55 known32_132.
Proof.
 assert(H:NonHalt(mirror_tm known32_132) /\ Bounds 55 55(mirror_tm known32_132)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_009).
 - split.
   + intros [] [] tr H; cbv [known32_132 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_009_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC0RC_1RA1LB0LB1RC *)
Definition known32_133:TM:=machine_of_codes 3 2 [8;5;9;7;1;11].
Lemma known32_133_bound:NonHalt known32_133 /\ Bounds 55 55 known32_133.
Proof.
 assert(H:NonHalt(mirror_tm known32_133) /\ Bounds 55 55(mirror_tm known32_133)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_007).
 - split.
   + intros [] [] tr H; cbv [known32_133 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_007_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC0RC_1RC1LB0LB1RA *)
Definition known32_134:TM:=machine_of_codes 3 2 [8;5;11;7;1;9].
Lemma known32_134_bound:NonHalt known32_134 /\ Bounds 55 55 known32_134.
Proof.
 assert(H:NonHalt(mirror_tm known32_134) /\ Bounds 55 55(mirror_tm known32_134)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB0LB_0RC1LA_1LB1RC_______.tm_1RB0LB_0RC1LA_1LB1RC_______).
 - split.
   + intros [] [] tr H; cbv [known32_134 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0LB_0RC1LA_1LB1RC_______.nqhtr_1RB0LB_0RC1LA_1LB1RC_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC1LA_0LC0RB1RB1LA *)
Definition known32_135:TM:=machine_of_codes 3 2 [8;6;2;4;10;6].
Lemma known32_135_bound:NonHalt known32_135 /\ Bounds 55 55 known32_135.
Proof.
 assert(H:NonHalt(mirror_tm known32_135) /\ Bounds 55 55(mirror_tm known32_135)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1RA_1LC1RA_0RB0LC_______.tm_1RB1RA_1LC1RA_0RB0LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_135 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1RA_1LC1RA_0RB0LC_______.nqhtr_1RB1RA_1LC1RA_0RB0LC_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC1LB_1LA0RC1RB0LA *)
Definition known32_136:TM:=machine_of_codes 3 2 [8;7;6;5;10;0].
Lemma known32_136_bound:NonHalt known32_136 /\ Bounds 55 55 known32_136.
Proof.
 assert(H:NonHalt(mirror_tm known32_136) /\ Bounds 55 55(mirror_tm known32_136)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_017).
 - split.
   + intros [] [] tr H; cbv [known32_136 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_017_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC1LC_1LA1RB0RB0LA *)
Definition known32_137:TM:=machine_of_codes 3 2 [8;8;6;10;4;0].
Lemma known32_137_bound:NonHalt known32_137 /\ Bounds 55 55 known32_137.
Proof.
 assert(H:NonHalt(mirror_tm known32_137) /\ Bounds 55 55(mirror_tm known32_137)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1RB_0LC0RA_1RA1LC_______.tm_1RB1RB_0LC0RA_1RA1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_137 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1RB_0LC0RA_1RA1LC_______.nqhtr_1RB1RB_0LC0RA_1RA1LC_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC1RA_0LC0LC0RA1LB *)
Definition known32_138:TM:=machine_of_codes 3 2 [8;9;2;2;3;7].
Lemma known32_138_bound:NonHalt known32_138 /\ Bounds 55 55 known32_138.
Proof.
 assert(H:NonHalt(mirror_tm known32_138) /\ Bounds 55 55(mirror_tm known32_138)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LA_0LA1RC_0RB0RB_______.tm_1RB1LA_0LA1RC_0RB0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_138 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_0LA1RC_0RB0RB_______.nqhtr_1RB1LA_0LA1RC_0RB0RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC1RA_0RA0LC0RA1LB *)
Definition known32_139:TM:=machine_of_codes 3 2 [8;9;3;2;3;7].
Lemma known32_139_bound:NonHalt known32_139 /\ Bounds 55 55 known32_139.
Proof.
 assert(H:NonHalt(mirror_tm known32_139) /\ Bounds 55 55(mirror_tm known32_139)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LA_0LA1RC_0LA0RB_______.tm_1RB1LA_0LA1RC_0LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_139 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_0LA1RC_0LA0RB_______.nqhtr_1RB1LA_0LA1RC_0LA0RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC1RA_0RA0LC1LB1LB *)
Definition known32_140:TM:=machine_of_codes 3 2 [8;9;3;2;7;7].
Lemma known32_140_bound:NonHalt known32_140 /\ Bounds 55 55 known32_140.
Proof.
 assert(H:NonHalt(mirror_tm known32_140) /\ Bounds 55 55(mirror_tm known32_140)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LA_1RC1RC_0LA0RB_______.tm_1RB1LA_1RC1RC_0LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_140 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_1RC1RC_0LA0RB_______.nqhtr_1RB1LA_1RC1RC_0LA0RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC1RA_0RA0LC1RA1LB *)
Definition known32_141:TM:=machine_of_codes 3 2 [8;9;3;2;9;7].
Lemma known32_141_bound:NonHalt known32_141 /\ Bounds 55 55 known32_141.
Proof.
 assert(H:NonHalt(mirror_tm known32_141) /\ Bounds 55 55(mirror_tm known32_141)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LA_1LA1RC_0LA0RB_______.tm_1RB1LA_1LA1RC_0LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_141 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_1LA1RC_0LA0RB_______.nqhtr_1RB1LA_1LA1RC_0LA0RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC1RA_0RA0LC1RC1LB *)
Definition known32_142:TM:=machine_of_codes 3 2 [8;9;3;2;11;7].
Lemma known32_142_bound:NonHalt known32_142 /\ Bounds 55 55 known32_142.
Proof.
 assert(H:NonHalt(mirror_tm known32_142) /\ Bounds 55 55(mirror_tm known32_142)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LA_1LB1RC_0LA0RB_______.tm_1RB1LA_1LB1RC_0LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_142 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_1LB1RC_0LA0RB_______.nqhtr_1RB1LA_1LB1RC_0LA0RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC1RA_0RA1LB0RA0LB *)
Definition known32_143:TM:=machine_of_codes 3 2 [8;9;3;7;3;1].
Lemma known32_143_bound:NonHalt known32_143 /\ Bounds 55 55 known32_143.
Proof.
 assert(H:NonHalt(mirror_tm known32_143) /\ Bounds 55 55(mirror_tm known32_143)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_012).
 - split.
   + intros [] [] tr H; cbv [known32_143 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_012_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC1RA_0RA1LB0RB0LB *)
Definition known32_144:TM:=machine_of_codes 3 2 [8;9;3;7;4;1].
Lemma known32_144_bound:NonHalt known32_144 /\ Bounds 55 55 known32_144.
Proof.
 assert(H:NonHalt(mirror_tm known32_144) /\ Bounds 55 55(mirror_tm known32_144)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_013).
 - split.
   + intros [] [] tr H; cbv [known32_144 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_013_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC1RA_0RA1LB1LB0LB *)
Definition known32_145:TM:=machine_of_codes 3 2 [8;9;3;7;7;1].
Lemma known32_145_bound:NonHalt known32_145 /\ Bounds 55 55 known32_145.
Proof.
 assert(H:NonHalt(mirror_tm known32_145) /\ Bounds 55 55(mirror_tm known32_145)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_016).
 - split.
   + intros [] [] tr H; cbv [known32_145 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_016_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC1RA_0RA1LB1RA0LB *)
Definition known32_146:TM:=machine_of_codes 3 2 [8;9;3;7;9;1].
Lemma known32_146_bound:NonHalt known32_146 /\ Bounds 55 55 known32_146.
Proof.
 assert(H:NonHalt(mirror_tm known32_146) /\ Bounds 55 55(mirror_tm known32_146)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_014).
 - split.
   + intros [] [] tr H; cbv [known32_146 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_014_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC1RA_0RA1LB1RB0LB *)
Definition known32_147:TM:=machine_of_codes 3 2 [8;9;3;7;10;1].
Lemma known32_147_bound:NonHalt known32_147 /\ Bounds 55 55 known32_147.
Proof.
 assert(H:NonHalt(mirror_tm known32_147) /\ Bounds 55 55(mirror_tm known32_147)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_015).
 - split.
   + intros [] [] tr H; cbv [known32_147 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_015_recur.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC1RA_0RB0LC0RA1LB *)
Definition known32_148:TM:=machine_of_codes 3 2 [8;9;4;2;3;7].
Lemma known32_148_bound:NonHalt known32_148 /\ Bounds 55 55 known32_148.
Proof.
 assert(H:NonHalt(mirror_tm known32_148) /\ Bounds 55 55(mirror_tm known32_148)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LA_0LA1RC_0LC0RB_______.tm_1RB1LA_0LA1RC_0LC0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_148 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_0LA1RC_0LC0RB_______.nqhtr_1RB1LA_0LA1RC_0LC0RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC1RA_1LC0LC0RA1LB *)
Definition known32_149:TM:=machine_of_codes 3 2 [8;9;8;2;3;7].
Lemma known32_149_bound:NonHalt known32_149 /\ Bounds 55 55 known32_149.
Proof.
 assert(H:NonHalt(mirror_tm known32_149) /\ Bounds 55 55(mirror_tm known32_149)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LA_0LA1RC_1RB0RB_______.tm_1RB1LA_0LA1RC_1RB0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_149 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_0LA1RC_1RB0RB_______.nqhtr_1RB1LA_0LA1RC_1RB0RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC1RA_1RA0LC0RA1LB *)
Definition known32_150:TM:=machine_of_codes 3 2 [8;9;9;2;3;7].
Lemma known32_150_bound:NonHalt known32_150 /\ Bounds 55 55 known32_150.
Proof.
 assert(H:NonHalt(mirror_tm known32_150) /\ Bounds 55 55(mirror_tm known32_150)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LA_0LA1RC_1LA0RB_______.tm_1RB1LA_0LA1RC_1LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_150 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_0LA1RC_1LA0RB_______.nqhtr_1RB1LA_0LA1RC_1LA0RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC1RA_1RC0LC0RA1LB *)
Definition known32_151:TM:=machine_of_codes 3 2 [8;9;11;2;3;7].
Lemma known32_151_bound:NonHalt known32_151 /\ Bounds 55 55 known32_151.
Proof.
 assert(H:NonHalt(mirror_tm known32_151) /\ Bounds 55 55(mirror_tm known32_151)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LA_0LA1RC_1LB0RB_______.tm_1RB1LA_0LA1RC_1LB0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_151 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_0LA1RC_1LB0RB_______.nqhtr_1RB1LA_0LA1RC_1LB0RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC1RB_0LC0RA1RA1LC *)
Definition known32_152:TM:=machine_of_codes 3 2 [8;10;2;3;9;8].
Lemma known32_152_bound:NonHalt known32_152 /\ Bounds 55 55 known32_152.
Proof.
 assert(H:NonHalt(mirror_tm known32_152) /\ Bounds 55 55(mirror_tm known32_152)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LC_1LA1RB_0RB0LA_______.tm_1RB1LC_1LA1RB_0RB0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_152 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LC_1LA1RB_0RB0LA_______.nqhtr_1RB1LC_1LA1RB_0RB0LA_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC1RB_1RA0LC0RA1LC *)
Definition known32_153:TM:=machine_of_codes 3 2 [8;10;9;2;3;8].
Lemma known32_153_bound:NonHalt known32_153 /\ Bounds 55 55 known32_153.
Proof.
 assert(H:NonHalt(mirror_tm known32_153) /\ Bounds 55 55(mirror_tm known32_153)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LC_0LA1RB_1LA0RB_______.tm_1RB1LC_0LA1RB_1LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_153 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LC_0LA1RB_1LA0RB_______.nqhtr_1RB1LC_0LA1RB_1LA0RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC1RB_1RA0LC0RB1LC *)
Definition known32_154:TM:=machine_of_codes 3 2 [8;10;9;2;4;8].
Lemma known32_154_bound:NonHalt known32_154 /\ Bounds 55 55 known32_154.
Proof.
 assert(H:NonHalt(mirror_tm known32_154) /\ Bounds 55 55(mirror_tm known32_154)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LC_0LC1RB_1LA0RB_______.tm_1RB1LC_0LC1RB_1LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_154 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LC_0LC1RB_1LA0RB_______.nqhtr_1RB1LC_0LC1RB_1LA0RB_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC1RB_1RA1RB0RB0LC *)
Definition known32_155:TM:=machine_of_codes 3 2 [8;10;9;10;4;2].
Lemma known32_155_bound:NonHalt known32_155 /\ Bounds 55 55 known32_155.
Proof.
 assert(H:NonHalt(mirror_tm known32_155) /\ Bounds 55 55(mirror_tm known32_155)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LC_0LC0RB_1LA1LC_______.tm_1RB1LC_0LC0RB_1LA1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_155 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LC_0LC0RB_1LA1LC_______.nqhtr_1RB1LC_0LC0RB_1LA1LC_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC1RC_0RA1LB1RA0LB *)
Definition known32_156:TM:=machine_of_codes 3 2 [8;11;3;7;9;1].
Lemma known32_156_bound:NonHalt known32_156 /\ Bounds 55 55 known32_156.
Proof.
 assert(H:NonHalt(mirror_tm known32_156) /\ Bounds 55 55(mirror_tm known32_156)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LB_1LA0RC_0LA1RC_______.tm_1RB1LB_1LA0RC_0LA1RC_______).
 - split.
   + intros [] [] tr H; cbv [known32_156 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LB_1LA0RC_0LA1RC_______.nqhtr_1RB1LB_1LA0RC_0LA1RC_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1LC1RC_0RC1LB1RA0LB *)
Definition known32_157:TM:=machine_of_codes 3 2 [8;11;5;7;9;1].
Lemma known32_157_bound:NonHalt known32_157 /\ Bounds 55 55 known32_157.
Proof.
 assert(H:NonHalt(mirror_tm known32_157) /\ Bounds 55 55(mirror_tm known32_157)).
 {
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LB_1LA0RC_0LB1RC_______.tm_1RB1LB_1LA0RC_0LB1RC_______).
 - split.
   + intros [] [] tr H; cbv [known32_157 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LB_1LA0RC_0LB1RC_______.nqhtr_1RB1LB_1LA0RC_0LB1RC_______.
 } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.
Qed.
(* 1RB0LB_0RC1LA1LB1RC *)
Definition known32_158:TM:=machine_of_codes 3 2 [10;1;5;6;7;11].
Lemma known32_158_bound:NonHalt known32_158 /\ Bounds 55 55 known32_158.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB0LB_0RC1LA_1LB1RC_______.tm_1RB0LB_0RC1LA_1LB1RC_______).
 - split.
   + intros [] [] tr H; cbv [known32_158 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0LB_0RC1LA_1LB1RC_______.nqhtr_1RB0LB_0RC1LA_1LB1RC_______.
Qed.
(* 1RB0LB_0RC1LB1LA1RC *)
Definition known32_159:TM:=machine_of_codes 3 2 [10;1;5;7;6;11].
Lemma known32_159_bound:NonHalt known32_159 /\ Bounds 55 55 known32_159.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_007).
 - split.
   + intros [] [] tr H; cbv [known32_159 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_007_recur.
Qed.
(* 1RB0LC_1LA1RA0RA1LC *)
Definition known32_160:TM:=machine_of_codes 3 2 [10;2;6;9;3;8].
Lemma known32_160_bound:NonHalt known32_160 /\ Bounds 55 55 known32_160.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB0LC_1LA1RA_0RA1LC_______.tm_1RB0LC_1LA1RA_0RA1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_160 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0LC_1LA1RA_0RA1LC_______.nqhtr_1RB0LC_1LA1RA_0RA1LC_______.
Qed.
(* 1RB0LC_1LA1RA0RB1LC *)
Definition known32_161:TM:=machine_of_codes 3 2 [10;2;6;9;4;8].
Lemma known32_161_bound:NonHalt known32_161 /\ Bounds 55 55 known32_161.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB0LC_1LA1RA_0RB1LC_______.tm_1RB0LC_1LA1RA_0RB1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_161 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0LC_1LA1RA_0RB1LC_______.nqhtr_1RB0LC_1LA1RA_0RB1LC_______.
Qed.
(* 1RB0LC_1LA1RB0RB1LC *)
Definition known32_162:TM:=machine_of_codes 3 2 [10;2;6;10;4;8].
Lemma known32_162_bound:NonHalt known32_162 /\ Bounds 55 55 known32_162.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_008).
 - split.
   + intros [] [] tr H; cbv [known32_162 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_008_recur.
Qed.
(* 1RB0LC_1LC0RA1LA1LB *)
Definition known32_163:TM:=machine_of_codes 3 2 [10;2;8;3;6;7].
Lemma known32_163_bound:NonHalt known32_163 /\ Bounds 55 55 known32_163.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_009).
 - split.
   + intros [] [] tr H; cbv [known32_163 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_009_recur.
Qed.
(* 1RB0LC_1LC1RA0RA1LC *)
Definition known32_164:TM:=machine_of_codes 3 2 [10;2;8;9;3;8].
Lemma known32_164_bound:NonHalt known32_164 /\ Bounds 55 55 known32_164.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB0LC_1LC1RA_0RA1LC_______.tm_1RB0LC_1LC1RA_0RA1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_164 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0LC_1LC1RA_0RA1LC_______.nqhtr_1RB0LC_1LC1RA_0RA1LC_______.
Qed.
(* 1RB0LC_1LC1RA0RB1LC *)
Definition known32_165:TM:=machine_of_codes 3 2 [10;2;8;9;4;8].
Lemma known32_165_bound:NonHalt known32_165 /\ Bounds 55 55 known32_165.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB0LC_1LC1RA_0RB1LC_______.tm_1RB0LC_1LC1RA_0RB1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_165 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0LC_1LC1RA_0RB1LC_______.nqhtr_1RB0LC_1LC1RA_0RB1LC_______.
Qed.
(* 1RB0LC_1LC1RB0RB1LA *)
Definition known32_166:TM:=machine_of_codes 3 2 [10;2;8;10;4;6].
Lemma known32_166_bound:NonHalt known32_166 /\ Bounds 55 55 known32_166.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB0LC_1LC1RB_0RB1LA_______.tm_1RB0LC_1LC1RB_0RB1LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_166 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0LC_1LC1RB_0RB1LA_______.nqhtr_1RB0LC_1LC1RB_0RB1LA_______.
Qed.
(* 1RB0LC_1RC1RA1LA0RB *)
Definition known32_167:TM:=machine_of_codes 3 2 [10;2;11;9;6;4].
Lemma known32_167_bound:NonHalt known32_167 /\ Bounds 55 55 known32_167.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_010).
 - split.
   + intros [] [] tr H; cbv [known32_167 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_010_recur.
Qed.
(* 1RB0RB_0LC1RA1RB1LC *)
Definition known32_168:TM:=machine_of_codes 3 2 [10;4;2;9;10;8].
Lemma known32_168_bound:NonHalt known32_168 /\ Bounds 55 55 known32_168.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB0RB_0LC1RA_1RB1LC_______.tm_1RB0RB_0LC1RA_1RB1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_168 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0RB_0LC1RA_1RB1LC_______.nqhtr_1RB0RB_0LC1RA_1RB1LC_______.
Qed.
(* 1RB0RB_0LC1RB1RA1LC *)
Definition known32_169:TM:=machine_of_codes 3 2 [10;4;2;10;9;8].
Lemma known32_169_bound:NonHalt known32_169 /\ Bounds 55 55 known32_169.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_011).
 - split.
   + intros [] [] tr H; cbv [known32_169 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_011_recur.
Qed.
(* 1RB1LA_0LA0RC0LA1RC *)
Definition known32_170:TM:=machine_of_codes 3 2 [10;6;0;5;0;11].
Lemma known32_170_bound:NonHalt known32_170 /\ Bounds 55 55 known32_170.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_012).
 - split.
   + intros [] [] tr H; cbv [known32_170 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_012_recur.
Qed.
(* 1RB1LA_0LA1RC0LA0RB *)
Definition known32_171:TM:=machine_of_codes 3 2 [10;6;0;11;0;4].
Lemma known32_171_bound:NonHalt known32_171 /\ Bounds 55 55 known32_171.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LA_0LA1RC_0LA0RB_______.tm_1RB1LA_0LA1RC_0LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_171 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_0LA1RC_0LA0RB_______.nqhtr_1RB1LA_0LA1RC_0LA0RB_______.
Qed.
(* 1RB1LA_0LA1RC0LC0RB *)
Definition known32_172:TM:=machine_of_codes 3 2 [10;6;0;11;2;4].
Lemma known32_172_bound:NonHalt known32_172 /\ Bounds 55 55 known32_172.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LA_0LA1RC_0LC0RB_______.tm_1RB1LA_0LA1RC_0LC0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_172 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_0LA1RC_0LC0RB_______.nqhtr_1RB1LA_0LA1RC_0LC0RB_______.
Qed.
(* 1RB1LA_0LA1RC0RB0RB *)
Definition known32_173:TM:=machine_of_codes 3 2 [10;6;0;11;4;4].
Lemma known32_173_bound:NonHalt known32_173 /\ Bounds 55 55 known32_173.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LA_0LA1RC_0RB0RB_______.tm_1RB1LA_0LA1RC_0RB0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_173 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_0LA1RC_0RB0RB_______.nqhtr_1RB1LA_0LA1RC_0RB0RB_______.
Qed.
(* 1RB1LA_0LA1RC1LA0RB *)
Definition known32_174:TM:=machine_of_codes 3 2 [10;6;0;11;6;4].
Lemma known32_174_bound:NonHalt known32_174 /\ Bounds 55 55 known32_174.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LA_0LA1RC_1LA0RB_______.tm_1RB1LA_0LA1RC_1LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_174 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_0LA1RC_1LA0RB_______.nqhtr_1RB1LA_0LA1RC_1LA0RB_______.
Qed.
(* 1RB1LA_0LA1RC1LB0RB *)
Definition known32_175:TM:=machine_of_codes 3 2 [10;6;0;11;7;4].
Lemma known32_175_bound:NonHalt known32_175 /\ Bounds 55 55 known32_175.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LA_0LA1RC_1LB0RB_______.tm_1RB1LA_0LA1RC_1LB0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_175 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_0LA1RC_1LB0RB_______.nqhtr_1RB1LA_0LA1RC_1LB0RB_______.
Qed.
(* 1RB1LA_0LA1RC1RB0RB *)
Definition known32_176:TM:=machine_of_codes 3 2 [10;6;0;11;10;4].
Lemma known32_176_bound:NonHalt known32_176 /\ Bounds 55 55 known32_176.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LA_0LA1RC_1RB0RB_______.tm_1RB1LA_0LA1RC_1RB0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_176 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_0LA1RC_1RB0RB_______.nqhtr_1RB1LA_0LA1RC_1RB0RB_______.
Qed.
(* 1RB1LA_0LC0RC0LA1RC *)
Definition known32_177:TM:=machine_of_codes 3 2 [10;6;2;5;0;11].
Lemma known32_177_bound:NonHalt known32_177 /\ Bounds 55 55 known32_177.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_013).
 - split.
   + intros [] [] tr H; cbv [known32_177 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_013_recur.
Qed.
(* 1RB1LA_1LA0RC0LA1RC *)
Definition known32_178:TM:=machine_of_codes 3 2 [10;6;6;5;0;11].
Lemma known32_178_bound:NonHalt known32_178 /\ Bounds 55 55 known32_178.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_014).
 - split.
   + intros [] [] tr H; cbv [known32_178 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_014_recur.
Qed.
(* 1RB1LA_1LA1RC0LA0RB *)
Definition known32_179:TM:=machine_of_codes 3 2 [10;6;6;11;0;4].
Lemma known32_179_bound:NonHalt known32_179 /\ Bounds 55 55 known32_179.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LA_1LA1RC_0LA0RB_______.tm_1RB1LA_1LA1RC_0LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_179 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_1LA1RC_0LA0RB_______.nqhtr_1RB1LA_1LA1RC_0LA0RB_______.
Qed.
(* 1RB1LA_1LB1RC0LA0RB *)
Definition known32_180:TM:=machine_of_codes 3 2 [10;6;7;11;0;4].
Lemma known32_180_bound:NonHalt known32_180 /\ Bounds 55 55 known32_180.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LA_1LB1RC_0LA0RB_______.tm_1RB1LA_1LB1RC_0LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_180 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_1LB1RC_0LA0RB_______.nqhtr_1RB1LA_1LB1RC_0LA0RB_______.
Qed.
(* 1RB1LA_1LC0RC0LA1RC *)
Definition known32_181:TM:=machine_of_codes 3 2 [10;6;8;5;0;11].
Lemma known32_181_bound:NonHalt known32_181 /\ Bounds 55 55 known32_181.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_015).
 - split.
   + intros [] [] tr H; cbv [known32_181 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_015_recur.
Qed.
(* 1RB1LA_1RC0RC0LA1RC *)
Definition known32_182:TM:=machine_of_codes 3 2 [10;6;11;5;0;11].
Lemma known32_182_bound:NonHalt known32_182 /\ Bounds 55 55 known32_182.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_016).
 - split.
   + intros [] [] tr H; cbv [known32_182 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_016_recur.
Qed.
(* 1RB1LA_1RC1RC0LA0RB *)
Definition known32_183:TM:=machine_of_codes 3 2 [10;6;11;11;0;4].
Lemma known32_183_bound:NonHalt known32_183 /\ Bounds 55 55 known32_183.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LA_1RC1RC_0LA0RB_______.tm_1RB1LA_1RC1RC_0LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_183 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_1RC1RC_0LA0RB_______.nqhtr_1RB1LA_1RC1RC_0LA0RB_______.
Qed.
(* 1RB1LB_1LA0RC0LA1RC *)
Definition known32_184:TM:=machine_of_codes 3 2 [10;7;6;5;0;11].
Lemma known32_184_bound:NonHalt known32_184 /\ Bounds 55 55 known32_184.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LB_1LA0RC_0LA1RC_______.tm_1RB1LB_1LA0RC_0LA1RC_______).
 - split.
   + intros [] [] tr H; cbv [known32_184 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LB_1LA0RC_0LA1RC_______.nqhtr_1RB1LB_1LA0RC_0LA1RC_______.
Qed.
(* 1RB1LB_1LA0RC0LB1RC *)
Definition known32_185:TM:=machine_of_codes 3 2 [10;7;6;5;1;11].
Lemma known32_185_bound:NonHalt known32_185 /\ Bounds 55 55 known32_185.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LB_1LA0RC_0LB1RC_______.tm_1RB1LB_1LA0RC_0LB1RC_______).
 - split.
   + intros [] [] tr H; cbv [known32_185 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LB_1LA0RC_0LB1RC_______.nqhtr_1RB1LB_1LA0RC_0LB1RC_______.
Qed.
(* 1RB1LC_0LA1RB1LA0RB *)
Definition known32_186:TM:=machine_of_codes 3 2 [10;8;0;10;6;4].
Lemma known32_186_bound:NonHalt known32_186 /\ Bounds 55 55 known32_186.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LC_0LA1RB_1LA0RB_______.tm_1RB1LC_0LA1RB_1LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_186 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LC_0LA1RB_1LA0RB_______.nqhtr_1RB1LC_0LA1RB_1LA0RB_______.
Qed.
(* 1RB1LC_0LC0RB1LA1LC *)
Definition known32_187:TM:=machine_of_codes 3 2 [10;8;2;4;6;8].
Lemma known32_187_bound:NonHalt known32_187 /\ Bounds 55 55 known32_187.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LC_0LC0RB_1LA1LC_______.tm_1RB1LC_0LC0RB_1LA1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_187 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LC_0LC0RB_1LA1LC_______.nqhtr_1RB1LC_0LC0RB_1LA1LC_______.
Qed.
(* 1RB1LC_0LC1RB1LA0RB *)
Definition known32_188:TM:=machine_of_codes 3 2 [10;8;2;10;6;4].
Lemma known32_188_bound:NonHalt known32_188 /\ Bounds 55 55 known32_188.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LC_0LC1RB_1LA0RB_______.tm_1RB1LC_0LC1RB_1LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_188 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LC_0LC1RB_1LA0RB_______.nqhtr_1RB1LC_0LC1RB_1LA0RB_______.
Qed.
(* 1RB1LC_1LA1RB0RB0LA *)
Definition known32_189:TM:=machine_of_codes 3 2 [10;8;6;10;4;0].
Lemma known32_189_bound:NonHalt known32_189 /\ Bounds 55 55 known32_189.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1LC_1LA1RB_0RB0LA_______.tm_1RB1LC_1LA1RB_0RB0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_189 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LC_1LA1RB_0RB0LA_______.nqhtr_1RB1LC_1LA1RB_0RB0LA_______.
Qed.
(* 1RB1RA_1LC1RA0RB0LC *)
Definition known32_190:TM:=machine_of_codes 3 2 [10;9;8;9;4;2].
Lemma known32_190_bound:NonHalt known32_190 /\ Bounds 55 55 known32_190.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1RA_1LC1RA_0RB0LC_______.tm_1RB1RA_1LC1RA_0RB0LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_190 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1RA_1LC1RA_0RB0LC_______.nqhtr_1RB1RA_1LC1RA_0RB0LC_______.
Qed.
(* 1RB1RB_0LC0RA1RA1LC *)
Definition known32_191:TM:=machine_of_codes 3 2 [10;10;2;3;9;8].
Lemma known32_191_bound:NonHalt known32_191 /\ Bounds 55 55 known32_191.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ LAPT_1RB1RB_0LC0RA_1RA1LC_______.tm_1RB1RB_0LC0RA_1RA1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_191 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1RB_0LC0RA_1RA1LC_______.nqhtr_1RB1RB_0LC0RA_1RA1LC_______.
Qed.
(* 1RB1RC_1LC0RA1RA0LB *)
Definition known32_192:TM:=machine_of_codes 3 2 [10;11;8;3;9;1].
Lemma known32_192_bound:NonHalt known32_192 /\ Bounds 55 55 known32_192.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh false _ Counter32.legacy32_017).
 - split.
   + intros [] [] tr H; cbv [known32_192 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_017_recur.
Qed.
(* 1RC0LB_0RA1LB1LA1RA *)
Definition known32_193:TM:=machine_of_codes 3 2 [11;1;3;7;6;9].
Lemma known32_193_bound:NonHalt known32_193 /\ Bounds 55 55 known32_193.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB0LC_1LA1RA_0RA1LC_______.tm_1RB0LC_1LA1RA_0RA1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_193 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0LC_1LA1RA_0RA1LC_______.nqhtr_1RB0LC_1LA1RA_0RA1LC_______.
Qed.
(* 1RC0LB_0RA1LB1LB1RA *)
Definition known32_194:TM:=machine_of_codes 3 2 [11;1;3;7;7;9].
Lemma known32_194_bound:NonHalt known32_194 /\ Bounds 55 55 known32_194.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB0LC_1LC1RA_0RA1LC_______.tm_1RB0LC_1LC1RA_0RA1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_194 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0LC_1LC1RA_0RA1LC_______.nqhtr_1RB0LC_1LC1RA_0RA1LC_______.
Qed.
(* 1RC0LB_0RC1LA1LB1RC *)
Definition known32_195:TM:=machine_of_codes 3 2 [11;1;5;6;7;11].
Lemma known32_195_bound:NonHalt known32_195 /\ Bounds 55 55 known32_195.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB0LC_1LC1RB_0RB1LA_______.tm_1RB0LC_1LC1RB_0RB1LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_195 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0LC_1LC1RB_0RB1LA_______.nqhtr_1RB0LC_1LC1RB_0RB1LA_______.
Qed.
(* 1RC0LB_0RC1LB1LA1RA *)
Definition known32_196:TM:=machine_of_codes 3 2 [11;1;5;7;6;9].
Lemma known32_196_bound:NonHalt known32_196 /\ Bounds 55 55 known32_196.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB0LC_1LA1RA_0RB1LC_______.tm_1RB0LC_1LA1RA_0RB1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_196 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0LC_1LA1RA_0RB1LC_______.nqhtr_1RB0LC_1LA1RA_0RB1LC_______.
Qed.
(* 1RC0LB_0RC1LB1LA1RC *)
Definition known32_197:TM:=machine_of_codes 3 2 [11;1;5;7;6;11].
Lemma known32_197_bound:NonHalt known32_197 /\ Bounds 55 55 known32_197.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_008).
 - split.
   + intros [] [] tr H; cbv [known32_197 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_008_recur.
Qed.
(* 1RC0LB_0RC1LB1LB1RA *)
Definition known32_198:TM:=machine_of_codes 3 2 [11;1;5;7;7;9].
Lemma known32_198_bound:NonHalt known32_198 /\ Bounds 55 55 known32_198.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB0LC_1LC1RA_0RB1LC_______.tm_1RB0LC_1LC1RA_0RB1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_198 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0LC_1LC1RA_0RB1LC_______.nqhtr_1RB0LC_1LC1RA_0RB1LC_______.
Qed.
(* 1RC0LB_1LA0RC1RB1RA *)
Definition known32_199:TM:=machine_of_codes 3 2 [11;1;6;5;10;9].
Lemma known32_199_bound:NonHalt known32_199 /\ Bounds 55 55 known32_199.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_010).
 - split.
   + intros [] [] tr H; cbv [known32_199 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_010_recur.
Qed.
(* 1RC0LB_1LA1LC1LB0RA *)
Definition known32_200:TM:=machine_of_codes 3 2 [11;1;6;8;7;3].
Lemma known32_200_bound:NonHalt known32_200 /\ Bounds 55 55 known32_200.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_009).
 - split.
   + intros [] [] tr H; cbv [known32_200 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_009_recur.
Qed.
(* 1RC0LC_1LA1RB0RB1LC *)
Definition known32_201:TM:=machine_of_codes 3 2 [11;2;6;10;4;8].
Lemma known32_201_bound:NonHalt known32_201 /\ Bounds 55 55 known32_201.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_007).
 - split.
   + intros [] [] tr H; cbv [known32_201 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_007_recur.
Qed.
(* 1RC0LC_1LC1RB0RB1LA *)
Definition known32_202:TM:=machine_of_codes 3 2 [11;2;8;10;4;6].
Lemma known32_202_bound:NonHalt known32_202 /\ Bounds 55 55 known32_202.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB0LB_0RC1LA_1LB1RC_______.tm_1RB0LB_0RC1LA_1LB1RC_______).
 - split.
   + intros [] [] tr H; cbv [known32_202 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0LB_0RC1LA_1LB1RC_______.nqhtr_1RB0LB_0RC1LA_1LB1RC_______.
Qed.
(* 1RC0RC_1RA1LB0LB1RC *)
Definition known32_203:TM:=machine_of_codes 3 2 [11;5;9;7;1;11].
Lemma known32_203_bound:NonHalt known32_203 /\ Bounds 55 55 known32_203.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_011).
 - split.
   + intros [] [] tr H; cbv [known32_203 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_011_recur.
Qed.
(* 1RC0RC_1RC1LB0LB1RA *)
Definition known32_204:TM:=machine_of_codes 3 2 [11;5;11;7;1;9].
Lemma known32_204_bound:NonHalt known32_204 /\ Bounds 55 55 known32_204.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB0RB_0LC1RA_1RB1LC_______.tm_1RB0RB_0LC1RA_1RB1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_204 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB0RB_0LC1RA_1RB1LC_______.nqhtr_1RB0RB_0LC1RA_1RB1LC_______.
Qed.
(* 1RC1LA_0LA0RC0LA1RB *)
Definition known32_205:TM:=machine_of_codes 3 2 [11;6;0;5;0;10].
Lemma known32_205_bound:NonHalt known32_205 /\ Bounds 55 55 known32_205.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LA_0LA1RC_0LA0RB_______.tm_1RB1LA_0LA1RC_0LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_205 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_0LA1RC_0LA0RB_______.nqhtr_1RB1LA_0LA1RC_0LA0RB_______.
Qed.
(* 1RC1LA_0LA0RC1LA1RB *)
Definition known32_206:TM:=machine_of_codes 3 2 [11;6;0;5;6;10].
Lemma known32_206_bound:NonHalt known32_206 /\ Bounds 55 55 known32_206.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LA_1LA1RC_0LA0RB_______.tm_1RB1LA_1LA1RC_0LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_206 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_1LA1RC_0LA0RB_______.nqhtr_1RB1LA_1LA1RC_0LA0RB_______.
Qed.
(* 1RC1LA_0LA0RC1LC1RB *)
Definition known32_207:TM:=machine_of_codes 3 2 [11;6;0;5;8;10].
Lemma known32_207_bound:NonHalt known32_207 /\ Bounds 55 55 known32_207.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LA_1LB1RC_0LA0RB_______.tm_1RB1LA_1LB1RC_0LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_207 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_1LB1RC_0LA0RB_______.nqhtr_1RB1LA_1LB1RC_0LA0RB_______.
Qed.
(* 1RC1LA_0LA0RC1RB1RB *)
Definition known32_208:TM:=machine_of_codes 3 2 [11;6;0;5;10;10].
Lemma known32_208_bound:NonHalt known32_208 /\ Bounds 55 55 known32_208.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LA_1RC1RC_0LA0RB_______.tm_1RB1LA_1RC1RC_0LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_208 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_1RC1RC_0LA0RB_______.nqhtr_1RB1LA_1RC1RC_0LA0RB_______.
Qed.
(* 1RC1LA_0LA1RB0LA0RB *)
Definition known32_209:TM:=machine_of_codes 3 2 [11;6;0;10;0;4].
Lemma known32_209_bound:NonHalt known32_209 /\ Bounds 55 55 known32_209.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_012).
 - split.
   + intros [] [] tr H; cbv [known32_209 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_012_recur.
Qed.
(* 1RC1LA_0LA1RB0LB0RB *)
Definition known32_210:TM:=machine_of_codes 3 2 [11;6;0;10;1;4].
Lemma known32_210_bound:NonHalt known32_210 /\ Bounds 55 55 known32_210.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_013).
 - split.
   + intros [] [] tr H; cbv [known32_210 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_013_recur.
Qed.
(* 1RC1LA_0LA1RB1LA0RB *)
Definition known32_211:TM:=machine_of_codes 3 2 [11;6;0;10;6;4].
Lemma known32_211_bound:NonHalt known32_211 /\ Bounds 55 55 known32_211.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_014).
 - split.
   + intros [] [] tr H; cbv [known32_211 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_014_recur.
Qed.
(* 1RC1LA_0LA1RB1LB0RB *)
Definition known32_212:TM:=machine_of_codes 3 2 [11;6;0;10;7;4].
Lemma known32_212_bound:NonHalt known32_212 /\ Bounds 55 55 known32_212.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_015).
 - split.
   + intros [] [] tr H; cbv [known32_212 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_015_recur.
Qed.
(* 1RC1LA_0LA1RB1RB0RB *)
Definition known32_213:TM:=machine_of_codes 3 2 [11;6;0;10;10;4].
Lemma known32_213_bound:NonHalt known32_213 /\ Bounds 55 55 known32_213.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_016).
 - split.
   + intros [] [] tr H; cbv [known32_213 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_016_recur.
Qed.
(* 1RC1LA_0LB0RC0LA1RB *)
Definition known32_214:TM:=machine_of_codes 3 2 [11;6;1;5;0;10].
Lemma known32_214_bound:NonHalt known32_214 /\ Bounds 55 55 known32_214.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LA_0LA1RC_0LC0RB_______.tm_1RB1LA_0LA1RC_0LC0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_214 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_0LA1RC_0LC0RB_______.nqhtr_1RB1LA_0LA1RC_0LC0RB_______.
Qed.
(* 1RC1LA_0RC0RC0LA1RB *)
Definition known32_215:TM:=machine_of_codes 3 2 [11;6;5;5;0;10].
Lemma known32_215_bound:NonHalt known32_215 /\ Bounds 55 55 known32_215.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LA_0LA1RC_0RB0RB_______.tm_1RB1LA_0LA1RC_0RB0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_215 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_0LA1RC_0RB0RB_______.nqhtr_1RB1LA_0LA1RC_0RB0RB_______.
Qed.
(* 1RC1LA_1LA0RC0LA1RB *)
Definition known32_216:TM:=machine_of_codes 3 2 [11;6;6;5;0;10].
Lemma known32_216_bound:NonHalt known32_216 /\ Bounds 55 55 known32_216.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LA_0LA1RC_1LA0RB_______.tm_1RB1LA_0LA1RC_1LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_216 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_0LA1RC_1LA0RB_______.nqhtr_1RB1LA_0LA1RC_1LA0RB_______.
Qed.
(* 1RC1LA_1LC0RC0LA1RB *)
Definition known32_217:TM:=machine_of_codes 3 2 [11;6;8;5;0;10].
Lemma known32_217_bound:NonHalt known32_217 /\ Bounds 55 55 known32_217.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LA_0LA1RC_1LB0RB_______.tm_1RB1LA_0LA1RC_1LB0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_217 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_0LA1RC_1LB0RB_______.nqhtr_1RB1LA_0LA1RC_1LB0RB_______.
Qed.
(* 1RC1LA_1RC0RC0LA1RB *)
Definition known32_218:TM:=machine_of_codes 3 2 [11;6;11;5;0;10].
Lemma known32_218_bound:NonHalt known32_218 /\ Bounds 55 55 known32_218.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LA_0LA1RC_1RB0RB_______.tm_1RB1LA_0LA1RC_1RB0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_218 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LA_0LA1RC_1RB0RB_______.nqhtr_1RB1LA_0LA1RC_1RB0RB_______.
Qed.
(* 1RC1LB_0RC0LA1LA1RC *)
Definition known32_219:TM:=machine_of_codes 3 2 [11;7;5;0;6;11].
Lemma known32_219_bound:NonHalt known32_219 /\ Bounds 55 55 known32_219.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LC_1LA1RB_0RB0LA_______.tm_1RB1LC_1LA1RB_0RB0LA_______).
 - split.
   + intros [] [] tr H; cbv [known32_219 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LC_1LA1RB_0RB0LA_______.nqhtr_1RB1LC_1LA1RB_0RB0LA_______.
Qed.
(* 1RC1LB_1LA0RC0LA1RC *)
Definition known32_220:TM:=machine_of_codes 3 2 [11;7;6;5;0;11].
Lemma known32_220_bound:NonHalt known32_220 /\ Bounds 55 55 known32_220.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LC_0LA1RB_1LA0RB_______.tm_1RB1LC_0LA1RB_1LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_220 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LC_0LA1RB_1LA0RB_______.nqhtr_1RB1LC_0LA1RB_1LA0RB_______.
Qed.
(* 1RC1LB_1LA0RC0LB1RC *)
Definition known32_221:TM:=machine_of_codes 3 2 [11;7;6;5;1;11].
Lemma known32_221_bound:NonHalt known32_221 /\ Bounds 55 55 known32_221.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LC_0LC1RB_1LA0RB_______.tm_1RB1LC_0LC1RB_1LA0RB_______).
 - split.
   + intros [] [] tr H; cbv [known32_221 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LC_0LC1RB_1LA0RB_______.nqhtr_1RB1LC_0LC1RB_1LA0RB_______.
Qed.
(* 1RC1LB_1LA1LB0LB0RC *)
Definition known32_222:TM:=machine_of_codes 3 2 [11;7;6;7;1;5].
Lemma known32_222_bound:NonHalt known32_222 /\ Bounds 55 55 known32_222.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LC_0LC0RB_1LA1LC_______.tm_1RB1LC_0LC0RB_1LA1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_222 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LC_0LC0RB_1LA1LC_______.nqhtr_1RB1LC_0LC0RB_1LA1LC_______.
Qed.
(* 1RC1LC_0LA1RB1LA0RB *)
Definition known32_223:TM:=machine_of_codes 3 2 [11;8;0;10;6;4].
Lemma known32_223_bound:NonHalt known32_223 /\ Bounds 55 55 known32_223.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LB_1LA0RC_0LA1RC_______.tm_1RB1LB_1LA0RC_0LA1RC_______).
 - split.
   + intros [] [] tr H; cbv [known32_223 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LB_1LA0RC_0LA1RC_______.nqhtr_1RB1LB_1LA0RC_0LA1RC_______.
Qed.
(* 1RC1LC_0LC1RB1LA0RB *)
Definition known32_224:TM:=machine_of_codes 3 2 [11;8;2;10;6;4].
Lemma known32_224_bound:NonHalt known32_224 /\ Bounds 55 55 known32_224.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1LB_1LA0RC_0LB1RC_______.tm_1RB1LB_1LA0RC_0LB1RC_______).
 - split.
   + intros [] [] tr H; cbv [known32_224 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1LB_1LA0RC_0LB1RC_______.nqhtr_1RB1LB_1LA0RC_0LB1RC_______.
Qed.
(* 1RC1RA_0RC0LB1LB1RA *)
Definition known32_225:TM:=machine_of_codes 3 2 [11;9;5;1;7;9].
Lemma known32_225_bound:NonHalt known32_225 /\ Bounds 55 55 known32_225.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1RA_1LC1RA_0RB0LC_______.tm_1RB1RA_1LC1RA_0RB0LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_225 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1RA_1LC1RA_0RB0LC_______.nqhtr_1RB1RA_1LC1RA_0RB0LC_______.
Qed.
(* 1RC1RB_1RA0LC1LB0RA *)
Definition known32_226:TM:=machine_of_codes 3 2 [11;10;9;2;7;3].
Lemma known32_226_bound:NonHalt known32_226 /\ Bounds 55 55 known32_226.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ Counter32.legacy32_017).
 - split.
   + intros [] [] tr H; cbv [known32_226 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact Counter32.legacy32_017_recur.
Qed.
(* 1RC1RC_1RA1LB0LB0RA *)
Definition known32_227:TM:=machine_of_codes 3 2 [11;11;9;7;1;3].
Lemma known32_227_bound:NonHalt known32_227 /\ Bounds 55 55 known32_227.
Proof.
 apply recurrence_bounds. eapply (legacy_neverqh true _ LAPT_1RB1RB_0LC0RA_1RA1LC_______.tm_1RB1RB_0LC0RA_1RA1LC_______).
 - split.
   + intros [] [] tr H; cbv [known32_227 machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;
     try discriminate; injection H as <-; unfold output_ok; simpl; lia.
   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.
 - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.
 - exact LAPT_1RB1RB_0LC0RA_1RA1LC_______.nqhtr_1RB1RB_0LC0RA_1RA1LC_______.
Qed.
Definition known32:list TM:= [known32_000;known32_001;known32_002;known32_003;known32_004;known32_005;known32_006;known32_007;known32_008;known32_009;known32_010;known32_011;known32_012;known32_013;known32_014;known32_015;known32_016;known32_017;known32_018;known32_019;known32_020;known32_021;known32_022;known32_023;known32_024;known32_025;known32_026;known32_027;known32_028;known32_029;known32_030;known32_031;known32_032;known32_033;known32_034;known32_035;known32_036;known32_037;known32_038;known32_039;known32_040;known32_041;known32_042;known32_043;known32_044;known32_045;known32_046;known32_047;known32_048;known32_049;known32_050;known32_051;known32_052;known32_053;known32_054;known32_055;known32_056;known32_057;known32_058;known32_059;known32_060;known32_061;known32_062;known32_063;known32_064;known32_065;known32_066;known32_067;known32_068;known32_069;known32_070;known32_071;known32_072;known32_073;known32_074;known32_075;known32_076;known32_077;known32_078;known32_079;known32_080;known32_081;known32_082;known32_083;known32_084;known32_085;known32_086;known32_087;known32_088;known32_089;known32_090;known32_091;known32_092;known32_093;known32_094;known32_095;known32_096;known32_097;known32_098;known32_099;known32_100;known32_101;known32_102;known32_103;known32_104;known32_105;known32_106;known32_107;known32_108;known32_109;known32_110;known32_111;known32_112;known32_113;known32_114;known32_115;known32_116;known32_117;known32_118;known32_119;known32_120;known32_121;known32_122;known32_123;known32_124;known32_125;known32_126;known32_127;known32_128;known32_129;known32_130;known32_131;known32_132;known32_133;known32_134;known32_135;known32_136;known32_137;known32_138;known32_139;known32_140;known32_141;known32_142;known32_143;known32_144;known32_145;known32_146;known32_147;known32_148;known32_149;known32_150;known32_151;known32_152;known32_153;known32_154;known32_155;known32_156;known32_157;known32_158;known32_159;known32_160;known32_161;known32_162;known32_163;known32_164;known32_165;known32_166;known32_167;known32_168;known32_169;known32_170;known32_171;known32_172;known32_173;known32_174;known32_175;known32_176;known32_177;known32_178;known32_179;known32_180;known32_181;known32_182;known32_183;known32_184;known32_185;known32_186;known32_187;known32_188;known32_189;known32_190;known32_191;known32_192;known32_193;known32_194;known32_195;known32_196;known32_197;known32_198;known32_199;known32_200;known32_201;known32_202;known32_203;known32_204;known32_205;known32_206;known32_207;known32_208;known32_209;known32_210;known32_211;known32_212;known32_213;known32_214;known32_215;known32_216;known32_217;known32_218;known32_219;known32_220;known32_221;known32_222;known32_223;known32_224;known32_225;known32_226;known32_227].
Lemma known32_sound:Forall(fun tm=>NonHalt tm /\ Bounds 55 55 tm)known32.
Proof. unfold known32.
 constructor; [exact known32_000_bound|].
 constructor; [exact known32_001_bound|].
 constructor; [exact known32_002_bound|].
 constructor; [exact known32_003_bound|].
 constructor; [exact known32_004_bound|].
 constructor; [exact known32_005_bound|].
 constructor; [exact known32_006_bound|].
 constructor; [exact known32_007_bound|].
 constructor; [exact known32_008_bound|].
 constructor; [exact known32_009_bound|].
 constructor; [exact known32_010_bound|].
 constructor; [exact known32_011_bound|].
 constructor; [exact known32_012_bound|].
 constructor; [exact known32_013_bound|].
 constructor; [exact known32_014_bound|].
 constructor; [exact known32_015_bound|].
 constructor; [exact known32_016_bound|].
 constructor; [exact known32_017_bound|].
 constructor; [exact known32_018_bound|].
 constructor; [exact known32_019_bound|].
 constructor; [exact known32_020_bound|].
 constructor; [exact known32_021_bound|].
 constructor; [exact known32_022_bound|].
 constructor; [exact known32_023_bound|].
 constructor; [exact known32_024_bound|].
 constructor; [exact known32_025_bound|].
 constructor; [exact known32_026_bound|].
 constructor; [exact known32_027_bound|].
 constructor; [exact known32_028_bound|].
 constructor; [exact known32_029_bound|].
 constructor; [exact known32_030_bound|].
 constructor; [exact known32_031_bound|].
 constructor; [exact known32_032_bound|].
 constructor; [exact known32_033_bound|].
 constructor; [exact known32_034_bound|].
 constructor; [exact known32_035_bound|].
 constructor; [exact known32_036_bound|].
 constructor; [exact known32_037_bound|].
 constructor; [exact known32_038_bound|].
 constructor; [exact known32_039_bound|].
 constructor; [exact known32_040_bound|].
 constructor; [exact known32_041_bound|].
 constructor; [exact known32_042_bound|].
 constructor; [exact known32_043_bound|].
 constructor; [exact known32_044_bound|].
 constructor; [exact known32_045_bound|].
 constructor; [exact known32_046_bound|].
 constructor; [exact known32_047_bound|].
 constructor; [exact known32_048_bound|].
 constructor; [exact known32_049_bound|].
 constructor; [exact known32_050_bound|].
 constructor; [exact known32_051_bound|].
 constructor; [exact known32_052_bound|].
 constructor; [exact known32_053_bound|].
 constructor; [exact known32_054_bound|].
 constructor; [exact known32_055_bound|].
 constructor; [exact known32_056_bound|].
 constructor; [exact known32_057_bound|].
 constructor; [exact known32_058_bound|].
 constructor; [exact known32_059_bound|].
 constructor; [exact known32_060_bound|].
 constructor; [exact known32_061_bound|].
 constructor; [exact known32_062_bound|].
 constructor; [exact known32_063_bound|].
 constructor; [exact known32_064_bound|].
 constructor; [exact known32_065_bound|].
 constructor; [exact known32_066_bound|].
 constructor; [exact known32_067_bound|].
 constructor; [exact known32_068_bound|].
 constructor; [exact known32_069_bound|].
 constructor; [exact known32_070_bound|].
 constructor; [exact known32_071_bound|].
 constructor; [exact known32_072_bound|].
 constructor; [exact known32_073_bound|].
 constructor; [exact known32_074_bound|].
 constructor; [exact known32_075_bound|].
 constructor; [exact known32_076_bound|].
 constructor; [exact known32_077_bound|].
 constructor; [exact known32_078_bound|].
 constructor; [exact known32_079_bound|].
 constructor; [exact known32_080_bound|].
 constructor; [exact known32_081_bound|].
 constructor; [exact known32_082_bound|].
 constructor; [exact known32_083_bound|].
 constructor; [exact known32_084_bound|].
 constructor; [exact known32_085_bound|].
 constructor; [exact known32_086_bound|].
 constructor; [exact known32_087_bound|].
 constructor; [exact known32_088_bound|].
 constructor; [exact known32_089_bound|].
 constructor; [exact known32_090_bound|].
 constructor; [exact known32_091_bound|].
 constructor; [exact known32_092_bound|].
 constructor; [exact known32_093_bound|].
 constructor; [exact known32_094_bound|].
 constructor; [exact known32_095_bound|].
 constructor; [exact known32_096_bound|].
 constructor; [exact known32_097_bound|].
 constructor; [exact known32_098_bound|].
 constructor; [exact known32_099_bound|].
 constructor; [exact known32_100_bound|].
 constructor; [exact known32_101_bound|].
 constructor; [exact known32_102_bound|].
 constructor; [exact known32_103_bound|].
 constructor; [exact known32_104_bound|].
 constructor; [exact known32_105_bound|].
 constructor; [exact known32_106_bound|].
 constructor; [exact known32_107_bound|].
 constructor; [exact known32_108_bound|].
 constructor; [exact known32_109_bound|].
 constructor; [exact known32_110_bound|].
 constructor; [exact known32_111_bound|].
 constructor; [exact known32_112_bound|].
 constructor; [exact known32_113_bound|].
 constructor; [exact known32_114_bound|].
 constructor; [exact known32_115_bound|].
 constructor; [exact known32_116_bound|].
 constructor; [exact known32_117_bound|].
 constructor; [exact known32_118_bound|].
 constructor; [exact known32_119_bound|].
 constructor; [exact known32_120_bound|].
 constructor; [exact known32_121_bound|].
 constructor; [exact known32_122_bound|].
 constructor; [exact known32_123_bound|].
 constructor; [exact known32_124_bound|].
 constructor; [exact known32_125_bound|].
 constructor; [exact known32_126_bound|].
 constructor; [exact known32_127_bound|].
 constructor; [exact known32_128_bound|].
 constructor; [exact known32_129_bound|].
 constructor; [exact known32_130_bound|].
 constructor; [exact known32_131_bound|].
 constructor; [exact known32_132_bound|].
 constructor; [exact known32_133_bound|].
 constructor; [exact known32_134_bound|].
 constructor; [exact known32_135_bound|].
 constructor; [exact known32_136_bound|].
 constructor; [exact known32_137_bound|].
 constructor; [exact known32_138_bound|].
 constructor; [exact known32_139_bound|].
 constructor; [exact known32_140_bound|].
 constructor; [exact known32_141_bound|].
 constructor; [exact known32_142_bound|].
 constructor; [exact known32_143_bound|].
 constructor; [exact known32_144_bound|].
 constructor; [exact known32_145_bound|].
 constructor; [exact known32_146_bound|].
 constructor; [exact known32_147_bound|].
 constructor; [exact known32_148_bound|].
 constructor; [exact known32_149_bound|].
 constructor; [exact known32_150_bound|].
 constructor; [exact known32_151_bound|].
 constructor; [exact known32_152_bound|].
 constructor; [exact known32_153_bound|].
 constructor; [exact known32_154_bound|].
 constructor; [exact known32_155_bound|].
 constructor; [exact known32_156_bound|].
 constructor; [exact known32_157_bound|].
 constructor; [exact known32_158_bound|].
 constructor; [exact known32_159_bound|].
 constructor; [exact known32_160_bound|].
 constructor; [exact known32_161_bound|].
 constructor; [exact known32_162_bound|].
 constructor; [exact known32_163_bound|].
 constructor; [exact known32_164_bound|].
 constructor; [exact known32_165_bound|].
 constructor; [exact known32_166_bound|].
 constructor; [exact known32_167_bound|].
 constructor; [exact known32_168_bound|].
 constructor; [exact known32_169_bound|].
 constructor; [exact known32_170_bound|].
 constructor; [exact known32_171_bound|].
 constructor; [exact known32_172_bound|].
 constructor; [exact known32_173_bound|].
 constructor; [exact known32_174_bound|].
 constructor; [exact known32_175_bound|].
 constructor; [exact known32_176_bound|].
 constructor; [exact known32_177_bound|].
 constructor; [exact known32_178_bound|].
 constructor; [exact known32_179_bound|].
 constructor; [exact known32_180_bound|].
 constructor; [exact known32_181_bound|].
 constructor; [exact known32_182_bound|].
 constructor; [exact known32_183_bound|].
 constructor; [exact known32_184_bound|].
 constructor; [exact known32_185_bound|].
 constructor; [exact known32_186_bound|].
 constructor; [exact known32_187_bound|].
 constructor; [exact known32_188_bound|].
 constructor; [exact known32_189_bound|].
 constructor; [exact known32_190_bound|].
 constructor; [exact known32_191_bound|].
 constructor; [exact known32_192_bound|].
 constructor; [exact known32_193_bound|].
 constructor; [exact known32_194_bound|].
 constructor; [exact known32_195_bound|].
 constructor; [exact known32_196_bound|].
 constructor; [exact known32_197_bound|].
 constructor; [exact known32_198_bound|].
 constructor; [exact known32_199_bound|].
 constructor; [exact known32_200_bound|].
 constructor; [exact known32_201_bound|].
 constructor; [exact known32_202_bound|].
 constructor; [exact known32_203_bound|].
 constructor; [exact known32_204_bound|].
 constructor; [exact known32_205_bound|].
 constructor; [exact known32_206_bound|].
 constructor; [exact known32_207_bound|].
 constructor; [exact known32_208_bound|].
 constructor; [exact known32_209_bound|].
 constructor; [exact known32_210_bound|].
 constructor; [exact known32_211_bound|].
 constructor; [exact known32_212_bound|].
 constructor; [exact known32_213_bound|].
 constructor; [exact known32_214_bound|].
 constructor; [exact known32_215_bound|].
 constructor; [exact known32_216_bound|].
 constructor; [exact known32_217_bound|].
 constructor; [exact known32_218_bound|].
 constructor; [exact known32_219_bound|].
 constructor; [exact known32_220_bound|].
 constructor; [exact known32_221_bound|].
 constructor; [exact known32_222_bound|].
 constructor; [exact known32_223_bound|].
 constructor; [exact known32_224_bound|].
 constructor; [exact known32_225_bound|].
 constructor; [exact known32_226_bound|].
 constructor; [exact known32_227_bound|].
 constructor. Qed.
