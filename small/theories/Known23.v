(** The instruction census reduces to the explicitly listed remaining machines. *)
From Coq Require Import Arith Lia List.
From SmallBB Require Import Statement StatementTr CTape Size Bounds Mirror CycleCensus
 Codes23 KnownCensus Census23State Weighted23 Weighted23Deep IR23 Remaining23.
Require SmallBB.Counters23.LAPQ_1RB1LA1RB_1LB2RB2LA.
Require SmallBB.Counters23.LAPQ_1RB2LA1RB_2LB1LA2RB.
Require SmallBB.Counters23.LAPQ_2RB2RB1LA_1LB1RB2LA.
Require SmallBB.Counters23.LAPQ_2RB2RB2LA_2LB1LA1RB.
Require SmallBB.Counters23.LAPT_1LB1LB1RB_1RA2LB0RA.
Require SmallBB.Counters23.LAPT_1RB2LA0RB_1LA1LA1RA.
Require SmallBB.Counters23.LAPT_1RB2RA2LB_1LB2LA0RA.
Require SmallBB.Counters23.LAPT_2LB2RB2LB_2RA0RA1LB.
Require SmallBB.Counters23.LAPT_2RB0RB1LA_2LA2RA2LA.
Require SmallBB.Counters23.LAPT_2RB1LB1RA_2LB0RA1LA.
Import ListNotations.
Lemma known23_recurrence:forall tm,NeverQuasiHaltsTr tm->NonHalt tm /\ QHBoundTr 67 tm.
Proof.
 intros tm H;split;[apply never_qh_tr_nonhalt;exact H|].
 intros tg s[Hv Hquiet];destruct(H tg ltac:(exists s;exact Hv)(S s))as(k&Hk&Hf).
 exfalso;apply(Hquiet k);[lia|exact Hf].
Qed.
Lemma known23_unmirror:forall tm,NonHalt(mirror_tm tm) /\ QHBoundTr 67(mirror_tm tm)->NonHalt tm /\ QHBoundTr 67 tm.
Proof.
 intros tm[HN HB];split;[apply mirror_nonhalt;exact HN|].
 intros tg s[Hv Hquiet];apply(HB tg s);split;[apply mirror_fires;exact Hv|].
 intros k Hk Hf;apply(Hquiet k Hk);apply mirror_fires;exact Hf.
Qed.
(* 0LB---1RA_1RA2RA2LB *)
Definition known23_000:TM:=machine_of_codes 2 3 [1;12;6;6;10;9].
Lemma known23_000_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_000 /\ Bounds 59 67 known23_000.
Proof.
 assert(H:NonHalt known23_000 /\ QHBoundTr 67 known23_000).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_006_tm) /\ QHBoundTr 67 (mirror_tm w23_006_tm)).
 destruct(weighted23_nth 6 (mirror_tm w23_006_tm) w23_006_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0LB---1RA_2RA2RA2LB *)
Definition known23_001:TM:=machine_of_codes 2 3 [1;12;6;10;10;9].
Lemma known23_001_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_001 /\ Bounds 59 67 known23_001.
Proof.
 assert(H:NonHalt known23_001 /\ QHBoundTr 67 known23_001).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_013_tm) /\ QHBoundTr 67 (mirror_tm w23_013_tm)).
 destruct(weighted23_nth 13 (mirror_tm w23_013_tm) w23_013_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0LB---2RA_1RA2LB1RA *)
Definition known23_002:TM:=machine_of_codes 2 3 [1;12;10;6;9;6].
Lemma known23_002_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_002 /\ Bounds 59 67 known23_002.
Proof.
 assert(H:NonHalt known23_002 /\ QHBoundTr 67 known23_002).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_004_tm) /\ QHBoundTr 67 (mirror_tm w23_004_tm)).
 destruct(weighted23_nth 4 (mirror_tm w23_004_tm) w23_004_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0LB---2RA_2RA2LB1RA *)
Definition known23_003:TM:=machine_of_codes 2 3 [1;12;10;10;9;6].
Lemma known23_003_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_003 /\ Bounds 59 67 known23_003.
Proof.
 assert(H:NonHalt known23_003 /\ QHBoundTr 67 known23_003).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_011_tm) /\ QHBoundTr 67 (mirror_tm w23_011_tm)).
 destruct(weighted23_nth 11 (mirror_tm w23_011_tm) w23_011_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0LB0RA1RA_2RA1LB2LB *)
Definition known23_004:TM:=machine_of_codes 2 3 [1;2;6;10;5;9].
Lemma known23_004_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_004 /\ Bounds 59 67 known23_004.
Proof.
 assert(H:NonHalt known23_004 /\ QHBoundTr 67 known23_004).
 {
 change(NonHalt w23_012_tm /\ QHBoundTr 67 w23_012_tm).
 destruct(weighted23_nth 12 w23_012_tm w23_012_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0LB0RA2RA_1RA2LB1LB *)
Definition known23_005:TM:=machine_of_codes 2 3 [1;2;10;6;9;5].
Lemma known23_005_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_005 /\ Bounds 59 67 known23_005.
Proof.
 assert(H:NonHalt known23_005 /\ QHBoundTr 67 known23_005).
 {
 change(NonHalt w23_003_tm /\ QHBoundTr 67 w23_003_tm).
 destruct(weighted23_nth 3 w23_003_tm w23_003_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0LB1RA---_1RA2RA1LB *)
Definition known23_006:TM:=machine_of_codes 2 3 [1;6;12;6;10;5].
Lemma known23_006_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_006 /\ Bounds 59 67 known23_006.
Proof.
 assert(H:NonHalt known23_006 /\ QHBoundTr 67 known23_006).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_005_tm) /\ QHBoundTr 67 (mirror_tm w23_005_tm)).
 destruct(weighted23_nth 5 (mirror_tm w23_005_tm) w23_005_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0LB1RA---_2RA2RA1LB *)
Definition known23_007:TM:=machine_of_codes 2 3 [1;6;12;10;10;5].
Lemma known23_007_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_007 /\ Bounds 59 67 known23_007.
Proof.
 assert(H:NonHalt known23_007 /\ QHBoundTr 67 known23_007).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_009_tm) /\ QHBoundTr 67 (mirror_tm w23_009_tm)).
 destruct(weighted23_nth 9 (mirror_tm w23_009_tm) w23_009_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0LB1RA0RA_2RA2LB1LB *)
Definition known23_008:TM:=machine_of_codes 2 3 [1;6;2;10;9;5].
Lemma known23_008_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_008 /\ Bounds 59 67 known23_008.
Proof.
 assert(H:NonHalt known23_008 /\ QHBoundTr 67 known23_008).
 {
 change(NonHalt w23_008_tm /\ QHBoundTr 67 w23_008_tm).
 destruct(weighted23_nth 8 w23_008_tm w23_008_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0LB1RA2RA_1RA2LB1LA *)
Definition known23_009:TM:=machine_of_codes 2 3 [1;6;10;6;9;4].
Lemma known23_009_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_009 /\ Bounds 59 67 known23_009.
Proof.
 assert(H:NonHalt known23_009 /\ QHBoundTr 67 known23_009).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_002_tm) /\ QHBoundTr 67 (mirror_tm w23_002_tm)).
 destruct(weighted23_nth 2 (mirror_tm w23_002_tm) w23_002_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0LB1RA2RA_2RA2LA1LB *)
Definition known23_010:TM:=machine_of_codes 2 3 [1;6;10;10;8;5].
Lemma known23_010_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_010 /\ Bounds 59 67 known23_010.
Proof.
 assert(H:NonHalt known23_010 /\ QHBoundTr 67 known23_010).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_007_tm) /\ QHBoundTr 67 (mirror_tm w23_007_tm)).
 destruct(weighted23_nth 7 (mirror_tm w23_007_tm) w23_007_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0LB2RA---_1RA1LB1RA *)
Definition known23_011:TM:=machine_of_codes 2 3 [1;10;12;6;5;6].
Lemma known23_011_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_011 /\ Bounds 59 67 known23_011.
Proof.
 assert(H:NonHalt known23_011 /\ QHBoundTr 67 known23_011).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_000_tm) /\ QHBoundTr 67 (mirror_tm w23_000_tm)).
 destruct(weighted23_nth 0 (mirror_tm w23_000_tm) w23_000_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0LB2RA---_2RA1LB1RA *)
Definition known23_012:TM:=machine_of_codes 2 3 [1;10;12;10;5;6].
Lemma known23_012_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_012 /\ Bounds 59 67 known23_012.
Proof.
 assert(H:NonHalt known23_012 /\ QHBoundTr 67 known23_012).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_010_tm) /\ QHBoundTr 67 (mirror_tm w23_010_tm)).
 destruct(weighted23_nth 10 (mirror_tm w23_010_tm) w23_010_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0LB2RA0RA_1RA1LB2LB *)
Definition known23_013:TM:=machine_of_codes 2 3 [1;10;2;6;5;9].
Lemma known23_013_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_013 /\ Bounds 59 67 known23_013.
Proof.
 assert(H:NonHalt known23_013 /\ QHBoundTr 67 known23_013).
 {
 change(NonHalt w23_001_tm /\ QHBoundTr 67 w23_001_tm).
 destruct(weighted23_nth 1 w23_001_tm w23_001_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0RB---1LA_1LA2LA2RB *)
Definition known23_014:TM:=machine_of_codes 2 3 [3;12;4;4;8;11].
Lemma known23_014_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_014 /\ Bounds 59 67 known23_014.
Proof.
 assert(H:NonHalt known23_014 /\ QHBoundTr 67 known23_014).
 {
 change(NonHalt w23_017_tm /\ QHBoundTr 67 w23_017_tm).
 destruct(weighted23_nth 17 w23_017_tm w23_017_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0RB---1LA_2LA2LA2RB *)
Definition known23_015:TM:=machine_of_codes 2 3 [3;12;4;8;8;11].
Lemma known23_015_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_015 /\ Bounds 59 67 known23_015.
Proof.
 assert(H:NonHalt known23_015 /\ QHBoundTr 67 known23_015).
 {
 change(NonHalt w23_027_tm /\ QHBoundTr 67 w23_027_tm).
 destruct(weighted23_nth 27 w23_027_tm w23_027_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0RB---2LA_1LA2RB1LA *)
Definition known23_016:TM:=machine_of_codes 2 3 [3;12;8;4;11;4].
Lemma known23_016_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_016 /\ Bounds 59 67 known23_016.
Proof.
 assert(H:NonHalt known23_016 /\ QHBoundTr 67 known23_016).
 {
 change(NonHalt w23_018_tm /\ QHBoundTr 67 w23_018_tm).
 destruct(weighted23_nth 18 w23_018_tm w23_018_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0RB---2LA_2LA2RB1LA *)
Definition known23_017:TM:=machine_of_codes 2 3 [3;12;8;8;11;4].
Lemma known23_017_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_017 /\ Bounds 59 67 known23_017.
Proof.
 assert(H:NonHalt known23_017 /\ QHBoundTr 67 known23_017).
 {
 change(NonHalt w23_022_tm /\ QHBoundTr 67 w23_022_tm).
 destruct(weighted23_nth 22 w23_022_tm w23_022_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0RB0LA1LA_2LA1RB2RB *)
Definition known23_018:TM:=machine_of_codes 2 3 [3;0;4;8;7;11].
Lemma known23_018_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_018 /\ Bounds 59 67 known23_018.
Proof.
 assert(H:NonHalt known23_018 /\ QHBoundTr 67 known23_018).
 {
 change(NonHalt w23_026_tm /\ QHBoundTr 67 w23_026_tm).
 destruct(weighted23_nth 26 w23_026_tm w23_026_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0RB0LA2LA_1LA2RB1RB *)
Definition known23_019:TM:=machine_of_codes 2 3 [3;0;8;4;11;7].
Lemma known23_019_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_019 /\ Bounds 59 67 known23_019.
Proof.
 assert(H:NonHalt known23_019 /\ QHBoundTr 67 known23_019).
 {
 change(NonHalt w23_020_tm /\ QHBoundTr 67 w23_020_tm).
 destruct(weighted23_nth 20 w23_020_tm w23_020_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0RB1LA---_1LA2LA1RB *)
Definition known23_020:TM:=machine_of_codes 2 3 [3;4;12;4;8;7].
Lemma known23_020_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_020 /\ Bounds 59 67 known23_020.
Proof.
 assert(H:NonHalt known23_020 /\ QHBoundTr 67 known23_020).
 {
 change(NonHalt w23_016_tm /\ QHBoundTr 67 w23_016_tm).
 destruct(weighted23_nth 16 w23_016_tm w23_016_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0RB1LA---_2LA2LA1RB *)
Definition known23_021:TM:=machine_of_codes 2 3 [3;4;12;8;8;7].
Lemma known23_021_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_021 /\ Bounds 59 67 known23_021.
Proof.
 assert(H:NonHalt known23_021 /\ QHBoundTr 67 known23_021).
 {
 change(NonHalt w23_023_tm /\ QHBoundTr 67 w23_023_tm).
 destruct(weighted23_nth 23 w23_023_tm w23_023_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0RB1LA0LA_2LA2RB1RB *)
Definition known23_022:TM:=machine_of_codes 2 3 [3;4;0;8;11;7].
Lemma known23_022_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_022 /\ Bounds 59 67 known23_022.
Proof.
 assert(H:NonHalt known23_022 /\ QHBoundTr 67 known23_022).
 {
 change(NonHalt w23_025_tm /\ QHBoundTr 67 w23_025_tm).
 destruct(weighted23_nth 25 w23_025_tm w23_025_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0RB1LA2LA_1LA2RB1RA *)
Definition known23_023:TM:=machine_of_codes 2 3 [3;4;8;4;11;6].
Lemma known23_023_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_023 /\ Bounds 59 67 known23_023.
Proof.
 assert(H:NonHalt known23_023 /\ QHBoundTr 67 known23_023).
 {
 change(NonHalt w23_019_tm /\ QHBoundTr 67 w23_019_tm).
 destruct(weighted23_nth 19 w23_019_tm w23_019_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0RB1LA2LA_2LA2RA1RB *)
Definition known23_024:TM:=machine_of_codes 2 3 [3;4;8;8;10;7].
Lemma known23_024_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_024 /\ Bounds 59 67 known23_024.
Proof.
 assert(H:NonHalt known23_024 /\ QHBoundTr 67 known23_024).
 {
 change(NonHalt w23_024_tm /\ QHBoundTr 67 w23_024_tm).
 destruct(weighted23_nth 24 w23_024_tm w23_024_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0RB2LA---_1LA1RB1LA *)
Definition known23_025:TM:=machine_of_codes 2 3 [3;8;12;4;7;4].
Lemma known23_025_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_025 /\ Bounds 59 67 known23_025.
Proof.
 assert(H:NonHalt known23_025 /\ QHBoundTr 67 known23_025).
 {
 change(NonHalt w23_014_tm /\ QHBoundTr 67 w23_014_tm).
 destruct(weighted23_nth 14 w23_014_tm w23_014_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0RB2LA---_2LA1RB1LA *)
Definition known23_026:TM:=machine_of_codes 2 3 [3;8;12;8;7;4].
Lemma known23_026_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_026 /\ Bounds 59 67 known23_026.
Proof.
 assert(H:NonHalt known23_026 /\ QHBoundTr 67 known23_026).
 {
 change(NonHalt w23_021_tm /\ QHBoundTr 67 w23_021_tm).
 destruct(weighted23_nth 21 w23_021_tm w23_021_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 0RB2LA0LA_1LA1RB2RB *)
Definition known23_027:TM:=machine_of_codes 2 3 [3;8;0;4;7;11].
Lemma known23_027_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_027 /\ Bounds 59 67 known23_027.
Proof.
 assert(H:NonHalt known23_027 /\ QHBoundTr 67 known23_027).
 {
 change(NonHalt w23_015_tm /\ QHBoundTr 67 w23_015_tm).
 destruct(weighted23_nth 15 w23_015_tm w23_015_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB0LA2RA_2RA2LB1RB *)
Definition known23_028:TM:=machine_of_codes 2 3 [5;0;10;10;9;7].
Lemma known23_028_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_028 /\ Bounds 59 67 known23_028.
Proof.
 assert(H:NonHalt known23_028 /\ QHBoundTr 67 known23_028).
 {
 change(NonHalt w23_061_tm /\ QHBoundTr 67 w23_061_tm).
 destruct(weighted23_nth 61 w23_061_tm w23_061_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB0LB1RA_1RA2RA2LB *)
Definition known23_029:TM:=machine_of_codes 2 3 [5;1;6;6;10;9].
Lemma known23_029_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_029 /\ Bounds 59 67 known23_029.
Proof.
 assert(H:NonHalt known23_029 /\ QHBoundTr 67 known23_029).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_041_tm) /\ QHBoundTr 67 (mirror_tm w23_041_tm)).
 destruct(weighted23_nth 41 (mirror_tm w23_041_tm) w23_041_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB0LB1RA_1RB2RA2LB *)
Definition known23_030:TM:=machine_of_codes 2 3 [5;1;6;7;10;9].
Lemma known23_030_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_030 /\ Bounds 59 67 known23_030.
Proof.
 assert(H:NonHalt known23_030 /\ QHBoundTr 67 known23_030).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_059_tm) /\ QHBoundTr 67 (mirror_tm w23_059_tm)).
 destruct(weighted23_nth 59 (mirror_tm w23_059_tm) w23_059_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB0LB1RA_2RA2RA2LB *)
Definition known23_031:TM:=machine_of_codes 2 3 [5;1;6;10;10;9].
Lemma known23_031_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_031 /\ Bounds 59 67 known23_031.
Proof.
 assert(H:NonHalt known23_031 /\ QHBoundTr 67 known23_031).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_064_tm) /\ QHBoundTr 67 (mirror_tm w23_064_tm)).
 destruct(weighted23_nth 64 (mirror_tm w23_064_tm) w23_064_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB0LB2RA_1RA2LB1RA *)
Definition known23_032:TM:=machine_of_codes 2 3 [5;1;10;6;9;6].
Lemma known23_032_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_032 /\ Bounds 59 67 known23_032.
Proof.
 assert(H:NonHalt known23_032 /\ QHBoundTr 67 known23_032).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_040_tm) /\ QHBoundTr 67 (mirror_tm w23_040_tm)).
 destruct(weighted23_nth 40 (mirror_tm w23_040_tm) w23_040_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB0LB2RA_1RB2LB1RA *)
Definition known23_033:TM:=machine_of_codes 2 3 [5;1;10;7;9;6].
Lemma known23_033_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_033 /\ Bounds 59 67 known23_033.
Proof.
 assert(H:NonHalt known23_033 /\ QHBoundTr 67 known23_033).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_057_tm) /\ QHBoundTr 67 (mirror_tm w23_057_tm)).
 destruct(weighted23_nth 57 (mirror_tm w23_057_tm) w23_057_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB0LB2RA_2RA2LB1RA *)
Definition known23_034:TM:=machine_of_codes 2 3 [5;1;10;10;9;6].
Lemma known23_034_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_034 /\ Bounds 59 67 known23_034.
Proof.
 assert(H:NonHalt known23_034 /\ QHBoundTr 67 known23_034).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_062_tm) /\ QHBoundTr 67 (mirror_tm w23_062_tm)).
 destruct(weighted23_nth 62 (mirror_tm w23_062_tm) w23_062_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB0LB2RA_2RA2LB1RB *)
Definition known23_035:TM:=machine_of_codes 2 3 [5;1;10;10;9;7].
Lemma known23_035_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_035 /\ Bounds 59 67 known23_035.
Proof.
 assert(H:NonHalt known23_035 /\ QHBoundTr 67 known23_035).
 {
 change(NonHalt w23_063_tm /\ QHBoundTr 67 w23_063_tm).
 destruct(weighted23_nth 63 w23_063_tm w23_063_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB0LB2RA_2RB2LB1RA *)
Definition known23_036:TM:=machine_of_codes 2 3 [5;1;10;11;9;6].
Lemma known23_036_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_036 /\ Bounds 59 67 known23_036.
Proof.
 assert(H:NonHalt known23_036 /\ QHBoundTr 67 known23_036).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_093_tm) /\ QHBoundTr 67 (mirror_tm w23_093_tm)).
 destruct(weighted23_nth 93 (mirror_tm w23_093_tm) w23_093_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB0RB1RA_2RB2RA0LA *)
Definition known23_037:TM:=machine_of_codes 2 3 [5;3;6;11;10;0].
Lemma known23_037_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_037 /\ Bounds 59 67 known23_037.
Proof.
 assert(H:NonHalt known23_037 /\ QHBoundTr 67 known23_037).
 {
 pose proof(ir23_nth 0 _ _ eq_refl)as[HN[_ HB]];split;[exact HN|exact HB].
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB0RB2RA_2RA2LB1RB *)
Definition known23_038:TM:=machine_of_codes 2 3 [5;3;10;10;9;7].
Lemma known23_038_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_038 /\ Bounds 59 67 known23_038.
Proof.
 assert(H:NonHalt known23_038 /\ QHBoundTr 67 known23_038).
 {
 change(NonHalt w23_065_tm /\ QHBoundTr 67 w23_065_tm).
 destruct(weighted23_nth 65 w23_065_tm w23_065_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1LA1RB_2RA2RB2LA *)
Definition known23_039:TM:=machine_of_codes 2 3 [5;4;7;10;11;8].
Lemma known23_039_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_039 /\ Bounds 59 67 known23_039.
Proof.
 assert(H:NonHalt known23_039 /\ QHBoundTr 67 known23_039).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_066_tm) /\ QHBoundTr 67 (mirror_tm w23_066_tm)).
 destruct(weighted23_nth 66 (mirror_tm w23_066_tm) w23_066_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1LA2RB_2RA2LA1RB *)
Definition known23_040:TM:=machine_of_codes 2 3 [5;4;11;10;8;7].
Lemma known23_040_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_040 /\ Bounds 59 67 known23_040.
Proof.
 assert(H:NonHalt known23_040 /\ QHBoundTr 67 known23_040).
 {
 change(NonHalt w23_067_tm /\ QHBoundTr 67 w23_067_tm).
 destruct(weighted23_nth 67 w23_067_tm w23_067_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1LB1RA_1RA2RA2LB *)
Definition known23_041:TM:=machine_of_codes 2 3 [5;5;6;6;10;9].
Lemma known23_041_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_041 /\ Bounds 59 67 known23_041.
Proof.
 assert(H:NonHalt known23_041 /\ QHBoundTr 67 known23_041).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_043_tm) /\ QHBoundTr 67 (mirror_tm w23_043_tm)).
 destruct(weighted23_nth 43 (mirror_tm w23_043_tm) w23_043_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1LB1RA_1RB2LB0RA *)
Definition known23_042:TM:=machine_of_codes 2 3 [5;5;6;7;9;2].
Lemma known23_042_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_042 /\ Bounds 59 67 known23_042.
Proof.
 assert(H:NonHalt known23_042 /\ QHBoundTr 67 known23_042).
 {
 pose proof(ir23_nth 1 _ _ eq_refl)as[HN[_ HB]];split;[exact HN|exact HB].
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1LB1RA_1RB2RA2LB *)
Definition known23_043:TM:=machine_of_codes 2 3 [5;5;6;7;10;9].
Lemma known23_043_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_043 /\ Bounds 59 67 known23_043.
Proof.
 assert(H:NonHalt known23_043 /\ QHBoundTr 67 known23_043).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_060_tm) /\ QHBoundTr 67 (mirror_tm w23_060_tm)).
 destruct(weighted23_nth 60 (mirror_tm w23_060_tm) w23_060_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1LB1RA_2RA2RA2LB *)
Definition known23_044:TM:=machine_of_codes 2 3 [5;5;6;10;10;9].
Lemma known23_044_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_044 /\ Bounds 59 67 known23_044.
Proof.
 assert(H:NonHalt known23_044 /\ QHBoundTr 67 known23_044).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_070_tm) /\ QHBoundTr 67 (mirror_tm w23_070_tm)).
 destruct(weighted23_nth 70 (mirror_tm w23_070_tm) w23_070_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1LB1RB_1RA2LB0RA *)
Definition known23_045:TM:=machine_of_codes 2 3 [5;5;7;6;9;2].
Lemma known23_045_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_045 /\ Bounds 59 67 known23_045.
Proof.
 assert(H:NonHalt known23_045 /\ QHBoundTr 67 known23_045).
 {
 assert(E:known23_045=LAPT_1LB1LB1RB_1RA2LB0RA.tm_1LB1LB1RB_1RA2LB0RA)by(apply same_table_sound;reflexivity). rewrite E.
 apply known23_recurrence. exact LAPT_1LB1LB1RB_1RA2LB0RA.nqhtr_1LB1LB1RB_1RA2LB0RA.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1LB2RA_1RA2LB1RA *)
Definition known23_046:TM:=machine_of_codes 2 3 [5;5;10;6;9;6].
Lemma known23_046_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_046 /\ Bounds 59 67 known23_046.
Proof.
 assert(H:NonHalt known23_046 /\ QHBoundTr 67 known23_046).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_042_tm) /\ QHBoundTr 67 (mirror_tm w23_042_tm)).
 destruct(weighted23_nth 42 (mirror_tm w23_042_tm) w23_042_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1LB2RA_1RB2LB1RA *)
Definition known23_047:TM:=machine_of_codes 2 3 [5;5;10;7;9;6].
Lemma known23_047_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_047 /\ Bounds 59 67 known23_047.
Proof.
 assert(H:NonHalt known23_047 /\ QHBoundTr 67 known23_047).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_058_tm) /\ QHBoundTr 67 (mirror_tm w23_058_tm)).
 destruct(weighted23_nth 58 (mirror_tm w23_058_tm) w23_058_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1LB2RA_2RA2LB1RA *)
Definition known23_048:TM:=machine_of_codes 2 3 [5;5;10;10;9;6].
Lemma known23_048_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_048 /\ Bounds 59 67 known23_048.
Proof.
 assert(H:NonHalt known23_048 /\ QHBoundTr 67 known23_048).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_068_tm) /\ QHBoundTr 67 (mirror_tm w23_068_tm)).
 destruct(weighted23_nth 68 (mirror_tm w23_068_tm) w23_068_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1LB2RA_2RA2LB1RB *)
Definition known23_049:TM:=machine_of_codes 2 3 [5;5;10;10;9;7].
Lemma known23_049_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_049 /\ Bounds 59 67 known23_049.
Proof.
 assert(H:NonHalt known23_049 /\ QHBoundTr 67 known23_049).
 {
 change(NonHalt w23_069_tm /\ QHBoundTr 67 w23_069_tm).
 destruct(weighted23_nth 69 w23_069_tm w23_069_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1LB2RA_2RB2LB1RA *)
Definition known23_050:TM:=machine_of_codes 2 3 [5;5;10;11;9;6].
Lemma known23_050_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_050 /\ Bounds 59 67 known23_050.
Proof.
 assert(H:NonHalt known23_050 /\ QHBoundTr 67 known23_050).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_094_tm) /\ QHBoundTr 67 (mirror_tm w23_094_tm)).
 destruct(weighted23_nth 94 (mirror_tm w23_094_tm) w23_094_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1RA0RA_2RA1LB2LB *)
Definition known23_051:TM:=machine_of_codes 2 3 [5;6;2;10;5;9].
Lemma known23_051_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_051 /\ Bounds 59 67 known23_051.
Proof.
 assert(H:NonHalt known23_051 /\ QHBoundTr 67 known23_051).
 {
 change(NonHalt w23_072_tm /\ QHBoundTr 67 w23_072_tm).
 destruct(weighted23_nth 72 w23_072_tm w23_072_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1RA1LB_0RA2LB--- *)
Definition known23_052:TM:=machine_of_codes 2 3 [5;6;5;2;9;12].
Lemma known23_052_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_052 /\ Bounds 59 67 known23_052.
Proof.
 assert(H:NonHalt known23_052 /\ QHBoundTr 67 known23_052).
 {
 change(NonHalt w23_028_tm /\ QHBoundTr 67 w23_028_tm).
 destruct(weighted23_nth 28 w23_028_tm w23_028_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1RA1LB_0RB2LB1RA *)
Definition known23_053:TM:=machine_of_codes 2 3 [5;6;5;3;9;6].
Lemma known23_053_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_053 /\ Bounds 59 67 known23_053.
Proof.
 assert(H:NonHalt known23_053 /\ QHBoundTr 67 known23_053).
 {
 change(NonHalt w23_037_tm /\ QHBoundTr 67 w23_037_tm).
 destruct(weighted23_nth 37 w23_037_tm w23_037_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1RA1LB_0RB2LB2RA *)
Definition known23_054:TM:=machine_of_codes 2 3 [5;6;5;3;9;10].
Lemma known23_054_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_054 /\ Bounds 59 67 known23_054.
Proof.
 assert(H:NonHalt known23_054 /\ QHBoundTr 67 known23_054).
 {
 change(NonHalt w23_038_tm /\ QHBoundTr 67 w23_038_tm).
 destruct(weighted23_nth 38 w23_038_tm w23_038_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1RA1LB_1RB2LB2RA *)
Definition known23_055:TM:=machine_of_codes 2 3 [5;6;5;7;9;10].
Lemma known23_055_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_055 /\ Bounds 59 67 known23_055.
Proof.
 assert(H:NonHalt known23_055 /\ QHBoundTr 67 known23_055).
 {
 change(NonHalt wd23_000_tm /\ QHBoundTr 67 wd23_000_tm).
 destruct(weighted23_deep_nth 0 wd23_000_tm 3 128 wd23_000_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1RA1LB_2RA2LB0RA *)
Definition known23_056:TM:=machine_of_codes 2 3 [5;6;5;10;9;2].
Lemma known23_056_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_056 /\ Bounds 59 67 known23_056.
Proof.
 assert(H:NonHalt known23_056 /\ QHBoundTr 67 known23_056).
 {
 change(NonHalt w23_073_tm /\ QHBoundTr 67 w23_073_tm).
 destruct(weighted23_nth 73 w23_073_tm w23_073_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1RA1LB_2RA2LB2RA *)
Definition known23_057:TM:=machine_of_codes 2 3 [5;6;5;10;9;10].
Lemma known23_057_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_057 /\ Bounds 59 67 known23_057.
Proof.
 assert(H:NonHalt known23_057 /\ QHBoundTr 67 known23_057).
 {
 change(NonHalt w23_075_tm /\ QHBoundTr 67 w23_075_tm).
 destruct(weighted23_nth 75 w23_075_tm w23_075_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1RA1LB_2RB2LB2RA *)
Definition known23_058:TM:=machine_of_codes 2 3 [5;6;5;11;9;10].
Lemma known23_058_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_058 /\ Bounds 59 67 known23_058.
Proof.
 assert(H:NonHalt known23_058 /\ QHBoundTr 67 known23_058).
 {
 change(NonHalt w23_095_tm /\ QHBoundTr 67 w23_095_tm).
 destruct(weighted23_nth 95 w23_095_tm w23_095_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1RA2RA_0RA2LB0LB *)
Definition known23_059:TM:=machine_of_codes 2 3 [5;6;10;2;9;1].
Lemma known23_059_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_059 /\ Bounds 59 67 known23_059.
Proof.
 assert(H:NonHalt known23_059 /\ QHBoundTr 67 known23_059).
 {
 change(NonHalt w23_029_tm /\ QHBoundTr 67 w23_029_tm).
 destruct(weighted23_nth 29 w23_029_tm w23_029_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1RA2RA_2RA0LB2LB *)
Definition known23_060:TM:=machine_of_codes 2 3 [5;6;10;10;1;9].
Lemma known23_060_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_060 /\ Bounds 59 67 known23_060.
Proof.
 assert(H:NonHalt known23_060 /\ QHBoundTr 67 known23_060).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_071_tm) /\ QHBoundTr 67 (mirror_tm w23_071_tm)).
 destruct(weighted23_nth 71 (mirror_tm w23_071_tm) w23_071_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1RA2RA_2RA2LB1RB *)
Definition known23_061:TM:=machine_of_codes 2 3 [5;6;10;10;9;7].
Lemma known23_061_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_061 /\ Bounds 59 67 known23_061.
Proof.
 assert(H:NonHalt known23_061 /\ QHBoundTr 67 known23_061).
 {
 change(NonHalt w23_074_tm /\ QHBoundTr 67 w23_074_tm).
 destruct(weighted23_nth 74 w23_074_tm w23_074_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1RB1LA_1RA2LA2RB *)
Definition known23_062:TM:=machine_of_codes 2 3 [5;7;4;6;8;11].
Lemma known23_062_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_062 /\ Bounds 59 67 known23_062.
Proof.
 assert(H:NonHalt known23_062 /\ QHBoundTr 67 known23_062).
 {
 change(NonHalt w23_044_tm /\ QHBoundTr 67 w23_044_tm).
 destruct(weighted23_nth 44 w23_044_tm w23_044_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1RB1LA_2RA2LA2RB *)
Definition known23_063:TM:=machine_of_codes 2 3 [5;7;4;10;8;11].
Lemma known23_063_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_063 /\ Bounds 59 67 known23_063.
Proof.
 assert(H:NonHalt known23_063 /\ QHBoundTr 67 known23_063).
 {
 change(NonHalt w23_078_tm /\ QHBoundTr 67 w23_078_tm).
 destruct(weighted23_nth 78 w23_078_tm w23_078_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1RB2LA_2RA2RB1LA *)
Definition known23_064:TM:=machine_of_codes 2 3 [5;7;8;10;11;4].
Lemma known23_064_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_064 /\ Bounds 59 67 known23_064.
Proof.
 assert(H:NonHalt known23_064 /\ QHBoundTr 67 known23_064).
 {
 change(NonHalt w23_076_tm /\ QHBoundTr 67 w23_076_tm).
 destruct(weighted23_nth 76 w23_076_tm w23_076_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB1RB2RA_2RA2LB1RB *)
Definition known23_065:TM:=machine_of_codes 2 3 [5;7;10;10;9;7].
Lemma known23_065_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_065 /\ Bounds 59 67 known23_065.
Proof.
 assert(H:NonHalt known23_065 /\ QHBoundTr 67 known23_065).
 {
 change(NonHalt w23_077_tm /\ QHBoundTr 67 w23_077_tm).
 destruct(weighted23_nth 77 w23_077_tm w23_077_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2LA1RA_2RA1LB--- *)
Definition known23_066:TM:=machine_of_codes 2 3 [5;8;6;10;5;12].
Lemma known23_066_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_066 /\ Bounds 59 67 known23_066.
Proof.
 assert(H:NonHalt known23_066 /\ QHBoundTr 67 known23_066).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_079_tm) /\ QHBoundTr 67 (mirror_tm w23_079_tm)).
 destruct(weighted23_nth 79 (mirror_tm w23_079_tm) w23_079_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2LA1RA_2RA2RB1LB *)
Definition known23_067:TM:=machine_of_codes 2 3 [5;8;6;10;11;5].
Lemma known23_067_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_067 /\ Bounds 59 67 known23_067.
Proof.
 assert(H:NonHalt known23_067 /\ QHBoundTr 67 known23_067).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_080_tm) /\ QHBoundTr 67 (mirror_tm w23_080_tm)).
 destruct(weighted23_nth 80 (mirror_tm w23_080_tm) w23_080_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2LA1RB_2RA1LA2RB *)
Definition known23_068:TM:=machine_of_codes 2 3 [5;8;7;10;4;11].
Lemma known23_068_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_068 /\ Bounds 59 67 known23_068.
Proof.
 assert(H:NonHalt known23_068 /\ QHBoundTr 67 known23_068).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_081_tm) /\ QHBoundTr 67 (mirror_tm w23_081_tm)).
 destruct(weighted23_nth 81 (mirror_tm w23_081_tm) w23_081_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2LA2RA_2RA2LB1RB *)
Definition known23_069:TM:=machine_of_codes 2 3 [5;8;10;10;9;7].
Lemma known23_069_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_069 /\ Bounds 59 67 known23_069.
Proof.
 assert(H:NonHalt known23_069 /\ QHBoundTr 67 known23_069).
 {
 change(NonHalt w23_082_tm /\ QHBoundTr 67 w23_082_tm).
 destruct(weighted23_nth 82 w23_082_tm w23_082_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2LA2RB_1RB2RA0LA *)
Definition known23_070:TM:=machine_of_codes 2 3 [5;8;11;7;10;0].
Lemma known23_070_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_070 /\ Bounds 59 67 known23_070.
Proof.
 assert(H:NonHalt known23_070 /\ QHBoundTr 67 known23_070).
 {
 apply known23_unmirror.
 assert(E:(mirror_tm known23_070)=LAPT_1RB2RA2LB_1LB2LA0RA.tm_1RB2RA2LB_1LB2LA0RA)by(apply same_table_sound;reflexivity). rewrite E.
 apply known23_recurrence. exact LAPT_1RB2RA2LB_1LB2LA0RA.nqhtr_1RB2RA2LB_1LB2LA0RA.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2LA2RB_2RA1RB1LA *)
Definition known23_071:TM:=machine_of_codes 2 3 [5;8;11;10;7;4].
Lemma known23_071_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_071 /\ Bounds 59 67 known23_071.
Proof.
 assert(H:NonHalt known23_071 /\ QHBoundTr 67 known23_071).
 {
 change(NonHalt w23_083_tm /\ QHBoundTr 67 w23_083_tm).
 destruct(weighted23_nth 83 w23_083_tm w23_083_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2LB1RA_0RA1LB--- *)
Definition known23_072:TM:=machine_of_codes 2 3 [5;9;6;2;5;12].
Lemma known23_072_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_072 /\ Bounds 59 67 known23_072.
Proof.
 assert(H:NonHalt known23_072 /\ QHBoundTr 67 known23_072).
 {
 change(NonHalt w23_030_tm /\ QHBoundTr 67 w23_030_tm).
 destruct(weighted23_nth 30 w23_030_tm w23_030_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2LB1RA_2RA1LB0RA *)
Definition known23_073:TM:=machine_of_codes 2 3 [5;9;6;10;5;2].
Lemma known23_073_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_073 /\ Bounds 59 67 known23_073.
Proof.
 assert(H:NonHalt known23_073 /\ QHBoundTr 67 known23_073).
 {
 change(NonHalt w23_084_tm /\ QHBoundTr 67 w23_084_tm).
 destruct(weighted23_nth 84 w23_084_tm w23_084_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2LB1RA_2RA1LB2RA *)
Definition known23_074:TM:=machine_of_codes 2 3 [5;9;6;10;5;10].
Lemma known23_074_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_074 /\ Bounds 59 67 known23_074.
Proof.
 assert(H:NonHalt known23_074 /\ QHBoundTr 67 known23_074).
 {
 change(NonHalt w23_086_tm /\ QHBoundTr 67 w23_086_tm).
 destruct(weighted23_nth 86 w23_086_tm w23_086_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2LB1RA_2RB1LB2RA *)
Definition known23_075:TM:=machine_of_codes 2 3 [5;9;6;11;5;10].
Lemma known23_075_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_075 /\ Bounds 59 67 known23_075.
Proof.
 assert(H:NonHalt known23_075 /\ QHBoundTr 67 known23_075).
 {
 change(NonHalt w23_092_tm /\ QHBoundTr 67 w23_092_tm).
 destruct(weighted23_nth 92 w23_092_tm w23_092_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2LB2RA_0RA---1LB *)
Definition known23_076:TM:=machine_of_codes 2 3 [5;9;10;2;12;5].
Lemma known23_076_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_076 /\ Bounds 59 67 known23_076.
Proof.
 assert(H:NonHalt known23_076 /\ QHBoundTr 67 known23_076).
 {
 change(NonHalt w23_031_tm /\ QHBoundTr 67 w23_031_tm).
 destruct(weighted23_nth 31 w23_031_tm w23_031_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2LB2RA_0RB1RA1LB *)
Definition known23_077:TM:=machine_of_codes 2 3 [5;9;10;3;6;5].
Lemma known23_077_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_077 /\ Bounds 59 67 known23_077.
Proof.
 assert(H:NonHalt known23_077 /\ QHBoundTr 67 known23_077).
 {
 change(NonHalt w23_035_tm /\ QHBoundTr 67 w23_035_tm).
 destruct(weighted23_nth 35 w23_035_tm w23_035_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2LB2RA_0RB2RA1LB *)
Definition known23_078:TM:=machine_of_codes 2 3 [5;9;10;3;10;5].
Lemma known23_078_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_078 /\ Bounds 59 67 known23_078.
Proof.
 assert(H:NonHalt known23_078 /\ QHBoundTr 67 known23_078).
 {
 change(NonHalt w23_039_tm /\ QHBoundTr 67 w23_039_tm).
 destruct(weighted23_nth 39 w23_039_tm w23_039_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2LB2RA_1RA0RA1LB *)
Definition known23_079:TM:=machine_of_codes 2 3 [5;9;10;6;2;5].
Lemma known23_079_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_079 /\ Bounds 59 67 known23_079.
Proof.
 assert(H:NonHalt known23_079 /\ QHBoundTr 67 known23_079).
 {
 change(NonHalt w23_045_tm /\ QHBoundTr 67 w23_045_tm).
 destruct(weighted23_nth 45 w23_045_tm w23_045_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2LB2RA_1RA1RA1LB *)
Definition known23_080:TM:=machine_of_codes 2 3 [5;9;10;6;6;5].
Lemma known23_080_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_080 /\ Bounds 59 67 known23_080.
Proof.
 assert(H:NonHalt known23_080 /\ QHBoundTr 67 known23_080).
 {
 change(NonHalt w23_046_tm /\ QHBoundTr 67 w23_046_tm).
 destruct(weighted23_nth 46 w23_046_tm w23_046_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2LB2RA_1RA2LB1RB *)
Definition known23_081:TM:=machine_of_codes 2 3 [5;9;10;6;9;7].
Lemma known23_081_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_081 /\ Bounds 59 67 known23_081.
Proof.
 assert(H:NonHalt known23_081 /\ QHBoundTr 67 known23_081).
 {
 split;[exact(proj1(remaining23_nth 0 known23_081 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 0 (eq_refl(Some known23_081))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2LB2RA_1RB1RA1LB *)
Definition known23_082:TM:=machine_of_codes 2 3 [5;9;10;7;6;5].
Lemma known23_082_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_082 /\ Bounds 59 67 known23_082.
Proof.
 assert(H:NonHalt known23_082 /\ QHBoundTr 67 known23_082).
 {
 change(NonHalt w23_054_tm /\ QHBoundTr 67 w23_054_tm).
 destruct(weighted23_nth 54 w23_054_tm w23_054_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2LB2RA_2RA2LB1RB *)
Definition known23_083:TM:=machine_of_codes 2 3 [5;9;10;10;9;7].
Lemma known23_083_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_083 /\ Bounds 59 67 known23_083.
Proof.
 assert(H:NonHalt known23_083 /\ QHBoundTr 67 known23_083).
 {
 change(NonHalt w23_085_tm /\ QHBoundTr 67 w23_085_tm).
 destruct(weighted23_nth 85 w23_085_tm w23_085_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2LB2RA_2RB1RA1LB *)
Definition known23_084:TM:=machine_of_codes 2 3 [5;9;10;11;6;5].
Lemma known23_084_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_084 /\ Bounds 59 67 known23_084.
Proof.
 assert(H:NonHalt known23_084 /\ QHBoundTr 67 known23_084).
 {
 change(NonHalt wd23_001_tm /\ QHBoundTr 67 wd23_001_tm).
 destruct(weighted23_deep_nth 1 wd23_001_tm 3 128 wd23_001_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RA0LB_1RA1RA1LA *)
Definition known23_085:TM:=machine_of_codes 2 3 [5;10;1;6;6;4].
Lemma known23_085_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_085 /\ Bounds 59 67 known23_085.
Proof.
 assert(H:NonHalt known23_085 /\ QHBoundTr 67 known23_085).
 {
 apply known23_unmirror.
 assert(E:(mirror_tm known23_085)=LAPT_1RB2LA0RB_1LA1LA1RA.tm_1RB2LA0RB_1LA1LA1RA)by(apply same_table_sound;reflexivity). rewrite E.
 apply known23_recurrence. exact LAPT_1RB2LA0RB_1LA1LA1RA.nqhtr_1RB2LA0RB_1LA1LA1RA.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RA0LB_1RB1RA1LA *)
Definition known23_086:TM:=machine_of_codes 2 3 [5;10;1;7;6;4].
Lemma known23_086_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_086 /\ Bounds 59 67 known23_086.
Proof.
 assert(H:NonHalt known23_086 /\ QHBoundTr 67 known23_086).
 {
 split;[exact(proj1(remaining23_nth 1 known23_086 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 1 (eq_refl(Some known23_086))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RA0LB_2RB1RA1LA *)
Definition known23_087:TM:=machine_of_codes 2 3 [5;10;1;11;6;4].
Lemma known23_087_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_087 /\ Bounds 59 67 known23_087.
Proof.
 assert(H:NonHalt known23_087 /\ QHBoundTr 67 known23_087).
 {
 split;[exact(proj1(remaining23_nth 2 known23_087 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 2 (eq_refl(Some known23_087))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RA0RA_1RA2LA1LB *)
Definition known23_088:TM:=machine_of_codes 2 3 [5;10;2;6;8;5].
Lemma known23_088_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_088 /\ Bounds 59 67 known23_088.
Proof.
 assert(H:NonHalt known23_088 /\ QHBoundTr 67 known23_088).
 {
 change(NonHalt w23_048_tm /\ QHBoundTr 67 w23_048_tm).
 destruct(weighted23_nth 48 w23_048_tm w23_048_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RA0RA_1RA2LB1LB *)
Definition known23_089:TM:=machine_of_codes 2 3 [5;10;2;6;9;5].
Lemma known23_089_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_089 /\ Bounds 59 67 known23_089.
Proof.
 assert(H:NonHalt known23_089 /\ QHBoundTr 67 known23_089).
 {
 change(NonHalt w23_049_tm /\ QHBoundTr 67 w23_049_tm).
 destruct(weighted23_nth 49 w23_049_tm w23_049_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RA1LA_1RA2LA2LB *)
Definition known23_090:TM:=machine_of_codes 2 3 [5;10;4;6;8;9].
Lemma known23_090_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_090 /\ Bounds 59 67 known23_090.
Proof.
 assert(H:NonHalt known23_090 /\ QHBoundTr 67 known23_090).
 {
 split;[exact(proj1(remaining23_nth 3 known23_090 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 3 (eq_refl(Some known23_090))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RA1LA_1RA2RA2LB *)
Definition known23_091:TM:=machine_of_codes 2 3 [5;10;4;6;10;9].
Lemma known23_091_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_091 /\ Bounds 59 67 known23_091.
Proof.
 assert(H:NonHalt known23_091 /\ QHBoundTr 67 known23_091).
 {
 split;[exact(proj1(remaining23_nth 4 known23_091 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 4 (eq_refl(Some known23_091))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RA1LA_1RB1RA2LB *)
Definition known23_092:TM:=machine_of_codes 2 3 [5;10;4;7;6;9].
Lemma known23_092_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_092 /\ Bounds 59 67 known23_092.
Proof.
 assert(H:NonHalt known23_092 /\ QHBoundTr 67 known23_092).
 {
 change(NonHalt w23_055_tm /\ QHBoundTr 67 w23_055_tm).
 destruct(weighted23_nth 55 w23_055_tm w23_055_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RA1LA_2RA2LB1RB *)
Definition known23_093:TM:=machine_of_codes 2 3 [5;10;4;10;9;7].
Lemma known23_093_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_093 /\ Bounds 59 67 known23_093.
Proof.
 assert(H:NonHalt known23_093 /\ QHBoundTr 67 known23_093).
 {
 change(NonHalt w23_087_tm /\ QHBoundTr 67 w23_087_tm).
 destruct(weighted23_nth 87 w23_087_tm w23_087_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RA1LB_0RA---2LB *)
Definition known23_094:TM:=machine_of_codes 2 3 [5;10;5;2;12;9].
Lemma known23_094_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_094 /\ Bounds 59 67 known23_094.
Proof.
 assert(H:NonHalt known23_094 /\ QHBoundTr 67 known23_094).
 {
 change(NonHalt w23_032_tm /\ QHBoundTr 67 w23_032_tm).
 destruct(weighted23_nth 32 w23_032_tm w23_032_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RA1LB_0RB1RA2LB *)
Definition known23_095:TM:=machine_of_codes 2 3 [5;10;5;3;6;9].
Lemma known23_095_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_095 /\ Bounds 59 67 known23_095.
Proof.
 assert(H:NonHalt known23_095 /\ QHBoundTr 67 known23_095).
 {
 change(NonHalt w23_036_tm /\ QHBoundTr 67 w23_036_tm).
 destruct(weighted23_nth 36 w23_036_tm w23_036_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RA1LB_1RA0RA2LB *)
Definition known23_096:TM:=machine_of_codes 2 3 [5;10;5;6;2;9].
Lemma known23_096_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_096 /\ Bounds 59 67 known23_096.
Proof.
 assert(H:NonHalt known23_096 /\ QHBoundTr 67 known23_096).
 {
 change(NonHalt w23_050_tm /\ QHBoundTr 67 w23_050_tm).
 destruct(weighted23_nth 50 w23_050_tm w23_050_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RA1LB_1RA1RA2LB *)
Definition known23_097:TM:=machine_of_codes 2 3 [5;10;5;6;6;9].
Lemma known23_097_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_097 /\ Bounds 59 67 known23_097.
Proof.
 assert(H:NonHalt known23_097 /\ QHBoundTr 67 known23_097).
 {
 change(NonHalt w23_051_tm /\ QHBoundTr 67 w23_051_tm).
 destruct(weighted23_nth 51 w23_051_tm w23_051_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RA1LB_1RB1RA2LB *)
Definition known23_098:TM:=machine_of_codes 2 3 [5;10;5;7;6;9].
Lemma known23_098_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_098 /\ Bounds 59 67 known23_098.
Proof.
 assert(H:NonHalt known23_098 /\ QHBoundTr 67 known23_098).
 {
 change(NonHalt w23_056_tm /\ QHBoundTr 67 w23_056_tm).
 destruct(weighted23_nth 56 w23_056_tm w23_056_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RA1LB_2RB1RA2LB *)
Definition known23_099:TM:=machine_of_codes 2 3 [5;10;5;11;6;9].
Lemma known23_099_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_099 /\ Bounds 59 67 known23_099.
Proof.
 assert(H:NonHalt known23_099 /\ QHBoundTr 67 known23_099).
 {
 apply known23_unmirror.
 assert(E:(mirror_tm known23_099)=LAPQ_1RB2LA1RB_2LB1LA2RB.tm_1RB2LA1RB_2LB1LA2RB)by(apply same_table_sound;reflexivity). rewrite E.
 exact LAPQ_1RB2LA1RB_2LB1LA2RB.qhtr_1RB2LA1RB_2LB1LA2RB.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RA1RA_0RA0LB2LB *)
Definition known23_100:TM:=machine_of_codes 2 3 [5;10;6;2;1;9].
Lemma known23_100_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_100 /\ Bounds 59 67 known23_100.
Proof.
 assert(H:NonHalt known23_100 /\ QHBoundTr 67 known23_100).
 {
 change(NonHalt w23_033_tm /\ QHBoundTr 67 w23_033_tm).
 destruct(weighted23_nth 33 w23_033_tm w23_033_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RA1RA_1RA2LB0LB *)
Definition known23_101:TM:=machine_of_codes 2 3 [5;10;6;6;9;1].
Lemma known23_101_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_101 /\ Bounds 59 67 known23_101.
Proof.
 assert(H:NonHalt known23_101 /\ QHBoundTr 67 known23_101).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_047_tm) /\ QHBoundTr 67 (mirror_tm w23_047_tm)).
 destruct(weighted23_nth 47 (mirror_tm w23_047_tm) w23_047_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RA1RB_0RA1LB2LB *)
Definition known23_102:TM:=machine_of_codes 2 3 [5;10;7;2;5;9].
Lemma known23_102_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_102 /\ Bounds 59 67 known23_102.
Proof.
 assert(H:NonHalt known23_102 /\ QHBoundTr 67 known23_102).
 {
 change(NonHalt w23_034_tm /\ QHBoundTr 67 w23_034_tm).
 destruct(weighted23_nth 34 w23_034_tm w23_034_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RA2RA_2RA2LB1RB *)
Definition known23_103:TM:=machine_of_codes 2 3 [5;10;10;10;9;7].
Lemma known23_103_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_103 /\ Bounds 59 67 known23_103.
Proof.
 assert(H:NonHalt known23_103 /\ QHBoundTr 67 known23_103).
 {
 change(NonHalt w23_088_tm /\ QHBoundTr 67 w23_088_tm).
 destruct(weighted23_nth 88 w23_088_tm w23_088_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RB0RB_1RA2LA0RB *)
Definition known23_104:TM:=machine_of_codes 2 3 [5;11;3;6;8;3].
Lemma known23_104_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_104 /\ Bounds 59 67 known23_104.
Proof.
 assert(H:NonHalt known23_104 /\ QHBoundTr 67 known23_104).
 {
 split;[exact(proj1(remaining23_nth 5 known23_104 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 5 (eq_refl(Some known23_104))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RB1LA_2RA1RB2LA *)
Definition known23_105:TM:=machine_of_codes 2 3 [5;11;4;10;7;8].
Lemma known23_105_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_105 /\ Bounds 59 67 known23_105.
Proof.
 assert(H:NonHalt known23_105 /\ QHBoundTr 67 known23_105).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_091_tm) /\ QHBoundTr 67 (mirror_tm w23_091_tm)).
 destruct(weighted23_nth 91 (mirror_tm w23_091_tm) w23_091_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RB1RA_1RA2LB0LB *)
Definition known23_106:TM:=machine_of_codes 2 3 [5;11;6;6;9;1].
Lemma known23_106_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_106 /\ Bounds 59 67 known23_106.
Proof.
 assert(H:NonHalt known23_106 /\ QHBoundTr 67 known23_106).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_053_tm) /\ QHBoundTr 67 (mirror_tm w23_053_tm)).
 destruct(weighted23_nth 53 (mirror_tm w23_053_tm) w23_053_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RB2LA_1RA1LA1RB *)
Definition known23_107:TM:=machine_of_codes 2 3 [5;11;8;6;4;7].
Lemma known23_107_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_107 /\ Bounds 59 67 known23_107.
Proof.
 assert(H:NonHalt known23_107 /\ QHBoundTr 67 known23_107).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_052_tm) /\ QHBoundTr 67 (mirror_tm w23_052_tm)).
 destruct(weighted23_nth 52 (mirror_tm w23_052_tm) w23_052_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RB2LA_2RA1LA1RB *)
Definition known23_108:TM:=machine_of_codes 2 3 [5;11;8;10;4;7].
Lemma known23_108_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_108 /\ Bounds 59 67 known23_108.
Proof.
 assert(H:NonHalt known23_108 /\ QHBoundTr 67 known23_108).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_089_tm) /\ QHBoundTr 67 (mirror_tm w23_089_tm)).
 destruct(weighted23_nth 89 (mirror_tm w23_089_tm) w23_089_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RB2RA_1RA2LB1RB *)
Definition known23_109:TM:=machine_of_codes 2 3 [5;11;10;6;9;7].
Lemma known23_109_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_109 /\ Bounds 59 67 known23_109.
Proof.
 assert(H:NonHalt known23_109 /\ QHBoundTr 67 known23_109).
 {
 split;[exact(proj1(remaining23_nth 6 known23_109 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 6 (eq_refl(Some known23_109))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1LB2RB2RA_2RA2LB1RB *)
Definition known23_110:TM:=machine_of_codes 2 3 [5;11;10;10;9;7].
Lemma known23_110_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_110 /\ Bounds 59 67 known23_110.
Proof.
 assert(H:NonHalt known23_110 /\ QHBoundTr 67 known23_110).
 {
 change(NonHalt w23_090_tm /\ QHBoundTr 67 w23_090_tm).
 destruct(weighted23_nth 90 w23_090_tm w23_090_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB0LB1LA_2LB2LA0RA *)
Definition known23_111:TM:=machine_of_codes 2 3 [7;1;4;9;8;2].
Lemma known23_111_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_111 /\ Bounds 59 67 known23_111.
Proof.
 assert(H:NonHalt known23_111 /\ QHBoundTr 67 known23_111).
 {
 pose proof(ir23_nth 3 _ _ eq_refl)as[HN[_ HB]];split;[exact HN|exact HB].
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB0LB2LA_2LA2RB1LB *)
Definition known23_112:TM:=machine_of_codes 2 3 [7;1;8;8;11;5].
Lemma known23_112_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_112 /\ Bounds 59 67 known23_112.
Proof.
 assert(H:NonHalt known23_112 /\ QHBoundTr 67 known23_112).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_129_tm) /\ QHBoundTr 67 (mirror_tm w23_129_tm)).
 destruct(weighted23_nth 129 (mirror_tm w23_129_tm) w23_129_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB0RA2LA_2LA2RB1LB *)
Definition known23_113:TM:=machine_of_codes 2 3 [7;2;8;8;11;5].
Lemma known23_113_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_113 /\ Bounds 59 67 known23_113.
Proof.
 assert(H:NonHalt known23_113 /\ QHBoundTr 67 known23_113).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_130_tm) /\ QHBoundTr 67 (mirror_tm w23_130_tm)).
 destruct(weighted23_nth 130 (mirror_tm w23_130_tm) w23_130_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB0RB1LA_1LA2LA2RB *)
Definition known23_114:TM:=machine_of_codes 2 3 [7;3;4;4;8;11].
Lemma known23_114_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_114 /\ Bounds 59 67 known23_114.
Proof.
 assert(H:NonHalt known23_114 /\ QHBoundTr 67 known23_114).
 {
 change(NonHalt w23_108_tm /\ QHBoundTr 67 w23_108_tm).
 destruct(weighted23_nth 108 w23_108_tm w23_108_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB0RB1LA_1LB2LA2RB *)
Definition known23_115:TM:=machine_of_codes 2 3 [7;3;4;5;8;11].
Lemma known23_115_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_115 /\ Bounds 59 67 known23_115.
Proof.
 assert(H:NonHalt known23_115 /\ QHBoundTr 67 known23_115).
 {
 change(NonHalt w23_125_tm /\ QHBoundTr 67 w23_125_tm).
 destruct(weighted23_nth 125 w23_125_tm w23_125_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB0RB1LA_2LA2LA2RB *)
Definition known23_116:TM:=machine_of_codes 2 3 [7;3;4;8;8;11].
Lemma known23_116_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_116 /\ Bounds 59 67 known23_116.
Proof.
 assert(H:NonHalt known23_116 /\ QHBoundTr 67 known23_116).
 {
 change(NonHalt w23_133_tm /\ QHBoundTr 67 w23_133_tm).
 destruct(weighted23_nth 133 w23_133_tm w23_133_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB0RB2LA_1LA2RB1LA *)
Definition known23_117:TM:=machine_of_codes 2 3 [7;3;8;4;11;4].
Lemma known23_117_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_117 /\ Bounds 59 67 known23_117.
Proof.
 assert(H:NonHalt known23_117 /\ QHBoundTr 67 known23_117).
 {
 change(NonHalt w23_109_tm /\ QHBoundTr 67 w23_109_tm).
 destruct(weighted23_nth 109 w23_109_tm w23_109_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB0RB2LA_1LB2RB1LA *)
Definition known23_118:TM:=machine_of_codes 2 3 [7;3;8;5;11;4].
Lemma known23_118_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_118 /\ Bounds 59 67 known23_118.
Proof.
 assert(H:NonHalt known23_118 /\ QHBoundTr 67 known23_118).
 {
 change(NonHalt w23_127_tm /\ QHBoundTr 67 w23_127_tm).
 destruct(weighted23_nth 127 w23_127_tm w23_127_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB0RB2LA_2LA2RB1LA *)
Definition known23_119:TM:=machine_of_codes 2 3 [7;3;8;8;11;4].
Lemma known23_119_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_119 /\ Bounds 59 67 known23_119.
Proof.
 assert(H:NonHalt known23_119 /\ QHBoundTr 67 known23_119).
 {
 change(NonHalt w23_131_tm /\ QHBoundTr 67 w23_131_tm).
 destruct(weighted23_nth 131 w23_131_tm w23_131_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB0RB2LA_2LA2RB1LB *)
Definition known23_120:TM:=machine_of_codes 2 3 [7;3;8;8;11;5].
Lemma known23_120_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_120 /\ Bounds 59 67 known23_120.
Proof.
 assert(H:NonHalt known23_120 /\ QHBoundTr 67 known23_120).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_132_tm) /\ QHBoundTr 67 (mirror_tm w23_132_tm)).
 destruct(weighted23_nth 132 (mirror_tm w23_132_tm) w23_132_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB0RB2LA_2LB2RB1LA *)
Definition known23_121:TM:=machine_of_codes 2 3 [7;3;8;9;11;4].
Lemma known23_121_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_121 /\ Bounds 59 67 known23_121.
Proof.
 assert(H:NonHalt known23_121 /\ QHBoundTr 67 known23_121).
 {
 change(NonHalt w23_161_tm /\ QHBoundTr 67 w23_161_tm).
 destruct(weighted23_nth 161 w23_161_tm w23_161_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1LA0LA_2LA1RB2RB *)
Definition known23_122:TM:=machine_of_codes 2 3 [7;4;0;8;7;11].
Lemma known23_122_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_122 /\ Bounds 59 67 known23_122.
Proof.
 assert(H:NonHalt known23_122 /\ QHBoundTr 67 known23_122).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_135_tm) /\ QHBoundTr 67 (mirror_tm w23_135_tm)).
 destruct(weighted23_nth 135 (mirror_tm w23_135_tm) w23_135_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1LA1RB_0LA2RB--- *)
Definition known23_123:TM:=machine_of_codes 2 3 [7;4;7;0;11;12].
Lemma known23_123_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_123 /\ Bounds 59 67 known23_123.
Proof.
 assert(H:NonHalt known23_123 /\ QHBoundTr 67 known23_123).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_096_tm) /\ QHBoundTr 67 (mirror_tm w23_096_tm)).
 destruct(weighted23_nth 96 (mirror_tm w23_096_tm) w23_096_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1LA1RB_0LB2RB1LA *)
Definition known23_124:TM:=machine_of_codes 2 3 [7;4;7;1;11;4].
Lemma known23_124_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_124 /\ Bounds 59 67 known23_124.
Proof.
 assert(H:NonHalt known23_124 /\ QHBoundTr 67 known23_124).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_106_tm) /\ QHBoundTr 67 (mirror_tm w23_106_tm)).
 destruct(weighted23_nth 106 (mirror_tm w23_106_tm) w23_106_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1LA1RB_0LB2RB2LA *)
Definition known23_125:TM:=machine_of_codes 2 3 [7;4;7;1;11;8].
Lemma known23_125_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_125 /\ Bounds 59 67 known23_125.
Proof.
 assert(H:NonHalt known23_125 /\ QHBoundTr 67 known23_125).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_107_tm) /\ QHBoundTr 67 (mirror_tm w23_107_tm)).
 destruct(weighted23_nth 107 (mirror_tm w23_107_tm) w23_107_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1LA1RB_1LB2RB2LA *)
Definition known23_126:TM:=machine_of_codes 2 3 [7;4;7;5;11;8].
Lemma known23_126_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_126 /\ Bounds 59 67 known23_126.
Proof.
 assert(H:NonHalt known23_126 /\ QHBoundTr 67 known23_126).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm wd23_002_tm) /\ QHBoundTr 67 (mirror_tm wd23_002_tm)).
 destruct(weighted23_deep_nth 2 (mirror_tm wd23_002_tm) 3 128 wd23_002_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1LA1RB_2LA2RB0LA *)
Definition known23_127:TM:=machine_of_codes 2 3 [7;4;7;8;11;0].
Lemma known23_127_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_127 /\ Bounds 59 67 known23_127.
Proof.
 assert(H:NonHalt known23_127 /\ QHBoundTr 67 known23_127).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_136_tm) /\ QHBoundTr 67 (mirror_tm w23_136_tm)).
 destruct(weighted23_nth 136 (mirror_tm w23_136_tm) w23_136_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1LA1RB_2LA2RB2LA *)
Definition known23_128:TM:=machine_of_codes 2 3 [7;4;7;8;11;8].
Lemma known23_128_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_128 /\ Bounds 59 67 known23_128.
Proof.
 assert(H:NonHalt known23_128 /\ QHBoundTr 67 known23_128).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_138_tm) /\ QHBoundTr 67 (mirror_tm w23_138_tm)).
 destruct(weighted23_nth 138 (mirror_tm w23_138_tm) w23_138_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1LA1RB_2LB2RB2LA *)
Definition known23_129:TM:=machine_of_codes 2 3 [7;4;7;9;11;8].
Lemma known23_129_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_129 /\ Bounds 59 67 known23_129.
Proof.
 assert(H:NonHalt known23_129 /\ QHBoundTr 67 known23_129).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_163_tm) /\ QHBoundTr 67 (mirror_tm w23_163_tm)).
 destruct(weighted23_nth 163 (mirror_tm w23_163_tm) w23_163_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1LA2LA_0LA2RB0RB *)
Definition known23_130:TM:=machine_of_codes 2 3 [7;4;8;0;11;3].
Lemma known23_130_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_130 /\ Bounds 59 67 known23_130.
Proof.
 assert(H:NonHalt known23_130 /\ QHBoundTr 67 known23_130).
 {
 change(NonHalt w23_097_tm /\ QHBoundTr 67 w23_097_tm).
 destruct(weighted23_nth 97 w23_097_tm w23_097_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1LA2LA_2LA0RB2RB *)
Definition known23_131:TM:=machine_of_codes 2 3 [7;4;8;8;3;11].
Lemma known23_131_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_131 /\ Bounds 59 67 known23_131.
Proof.
 assert(H:NonHalt known23_131 /\ QHBoundTr 67 known23_131).
 {
 change(NonHalt w23_134_tm /\ QHBoundTr 67 w23_134_tm).
 destruct(weighted23_nth 134 w23_134_tm w23_134_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1LA2LA_2LA2RB1LB *)
Definition known23_132:TM:=machine_of_codes 2 3 [7;4;8;8;11;5].
Lemma known23_132_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_132 /\ Bounds 59 67 known23_132.
Proof.
 assert(H:NonHalt known23_132 /\ QHBoundTr 67 known23_132).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_137_tm) /\ QHBoundTr 67 (mirror_tm w23_137_tm)).
 destruct(weighted23_nth 137 (mirror_tm w23_137_tm) w23_137_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1LB1RA_1LA2RA2LB *)
Definition known23_133:TM:=machine_of_codes 2 3 [7;5;6;4;10;9].
Lemma known23_133_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_133 /\ Bounds 59 67 known23_133.
Proof.
 assert(H:NonHalt known23_133 /\ QHBoundTr 67 known23_133).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_110_tm) /\ QHBoundTr 67 (mirror_tm w23_110_tm)).
 destruct(weighted23_nth 110 (mirror_tm w23_110_tm) w23_110_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1LB1RA_2LA2RA2LB *)
Definition known23_134:TM:=machine_of_codes 2 3 [7;5;6;8;10;9].
Lemma known23_134_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_134 /\ Bounds 59 67 known23_134.
Proof.
 assert(H:NonHalt known23_134 /\ QHBoundTr 67 known23_134).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_141_tm) /\ QHBoundTr 67 (mirror_tm w23_141_tm)).
 destruct(weighted23_nth 141 (mirror_tm w23_141_tm) w23_141_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1LB2LA_2LA2RB1LB *)
Definition known23_135:TM:=machine_of_codes 2 3 [7;5;8;8;11;5].
Lemma known23_135_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_135 /\ Bounds 59 67 known23_135.
Proof.
 assert(H:NonHalt known23_135 /\ QHBoundTr 67 known23_135).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_139_tm) /\ QHBoundTr 67 (mirror_tm w23_139_tm)).
 destruct(weighted23_nth 139 (mirror_tm w23_139_tm) w23_139_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1LB2RA_2LA2LB1RA *)
Definition known23_136:TM:=machine_of_codes 2 3 [7;5;10;8;9;6].
Lemma known23_136_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_136 /\ Bounds 59 67 known23_136.
Proof.
 assert(H:NonHalt known23_136 /\ QHBoundTr 67 known23_136).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_140_tm) /\ QHBoundTr 67 (mirror_tm w23_140_tm)).
 destruct(weighted23_nth 140 (mirror_tm w23_140_tm) w23_140_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1RA1LB_2LA2LB2RA *)
Definition known23_137:TM:=machine_of_codes 2 3 [7;6;5;8;9;10].
Lemma known23_137_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_137 /\ Bounds 59 67 known23_137.
Proof.
 assert(H:NonHalt known23_137 /\ QHBoundTr 67 known23_137).
 {
 change(NonHalt w23_142_tm /\ QHBoundTr 67 w23_142_tm).
 destruct(weighted23_nth 142 w23_142_tm w23_142_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1RA2LB_2LA2RA1LB *)
Definition known23_138:TM:=machine_of_codes 2 3 [7;6;9;8;10;5].
Lemma known23_138_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_138 /\ Bounds 59 67 known23_138.
Proof.
 assert(H:NonHalt known23_138 /\ QHBoundTr 67 known23_138).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_143_tm) /\ QHBoundTr 67 (mirror_tm w23_143_tm)).
 destruct(weighted23_nth 143 (mirror_tm w23_143_tm) w23_143_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1RB1LA_1LA2LA2RB *)
Definition known23_139:TM:=machine_of_codes 2 3 [7;7;4;4;8;11].
Lemma known23_139_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_139 /\ Bounds 59 67 known23_139.
Proof.
 assert(H:NonHalt known23_139 /\ QHBoundTr 67 known23_139).
 {
 change(NonHalt w23_111_tm /\ QHBoundTr 67 w23_111_tm).
 destruct(weighted23_nth 111 w23_111_tm w23_111_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1RB1LA_1LB2LA2RB *)
Definition known23_140:TM:=machine_of_codes 2 3 [7;7;4;5;8;11].
Lemma known23_140_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_140 /\ Bounds 59 67 known23_140.
Proof.
 assert(H:NonHalt known23_140 /\ QHBoundTr 67 known23_140).
 {
 change(NonHalt w23_126_tm /\ QHBoundTr 67 w23_126_tm).
 destruct(weighted23_nth 126 w23_126_tm w23_126_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1RB1LA_1LB2RB0LA *)
Definition known23_141:TM:=machine_of_codes 2 3 [7;7;4;5;11;0].
Lemma known23_141_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_141 /\ Bounds 59 67 known23_141.
Proof.
 assert(H:NonHalt known23_141 /\ QHBoundTr 67 known23_141).
 {
 pose proof(ir23_nth 5 _ _ eq_refl)as[HN[_ HB]];split;[exact HN|exact HB].
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1RB1LA_2LA2LA2RB *)
Definition known23_142:TM:=machine_of_codes 2 3 [7;7;4;8;8;11].
Lemma known23_142_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_142 /\ Bounds 59 67 known23_142.
Proof.
 assert(H:NonHalt known23_142 /\ QHBoundTr 67 known23_142).
 {
 change(NonHalt w23_146_tm /\ QHBoundTr 67 w23_146_tm).
 destruct(weighted23_nth 146 w23_146_tm w23_146_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1RB1LB_1LA2RB0LA *)
Definition known23_143:TM:=machine_of_codes 2 3 [7;7;5;4;11;0].
Lemma known23_143_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_143 /\ Bounds 59 67 known23_143.
Proof.
 assert(H:NonHalt known23_143 /\ QHBoundTr 67 known23_143).
 {
 apply known23_unmirror.
 assert(E:(mirror_tm known23_143)=LAPT_1LB1LB1RB_1RA2LB0RA.tm_1LB1LB1RB_1RA2LB0RA)by(apply same_table_sound;reflexivity). rewrite E.
 apply known23_recurrence. exact LAPT_1LB1LB1RB_1RA2LB0RA.nqhtr_1LB1LB1RB_1RA2LB0RA.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1RB2LA_1LA2RB1LA *)
Definition known23_144:TM:=machine_of_codes 2 3 [7;7;8;4;11;4].
Lemma known23_144_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_144 /\ Bounds 59 67 known23_144.
Proof.
 assert(H:NonHalt known23_144 /\ QHBoundTr 67 known23_144).
 {
 change(NonHalt w23_112_tm /\ QHBoundTr 67 w23_112_tm).
 destruct(weighted23_nth 112 w23_112_tm w23_112_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1RB2LA_1LB2RB1LA *)
Definition known23_145:TM:=machine_of_codes 2 3 [7;7;8;5;11;4].
Lemma known23_145_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_145 /\ Bounds 59 67 known23_145.
Proof.
 assert(H:NonHalt known23_145 /\ QHBoundTr 67 known23_145).
 {
 change(NonHalt w23_128_tm /\ QHBoundTr 67 w23_128_tm).
 destruct(weighted23_nth 128 w23_128_tm w23_128_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1RB2LA_2LA2RB1LA *)
Definition known23_146:TM:=machine_of_codes 2 3 [7;7;8;8;11;4].
Lemma known23_146_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_146 /\ Bounds 59 67 known23_146.
Proof.
 assert(H:NonHalt known23_146 /\ QHBoundTr 67 known23_146).
 {
 change(NonHalt w23_144_tm /\ QHBoundTr 67 w23_144_tm).
 destruct(weighted23_nth 144 w23_144_tm w23_144_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1RB2LA_2LA2RB1LB *)
Definition known23_147:TM:=machine_of_codes 2 3 [7;7;8;8;11;5].
Lemma known23_147_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_147 /\ Bounds 59 67 known23_147.
Proof.
 assert(H:NonHalt known23_147 /\ QHBoundTr 67 known23_147).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_145_tm) /\ QHBoundTr 67 (mirror_tm w23_145_tm)).
 destruct(weighted23_nth 145 (mirror_tm w23_145_tm) w23_145_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB1RB2LA_2LB2RB1LA *)
Definition known23_148:TM:=machine_of_codes 2 3 [7;7;8;9;11;4].
Lemma known23_148_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_148 /\ Bounds 59 67 known23_148.
Proof.
 assert(H:NonHalt known23_148 /\ QHBoundTr 67 known23_148).
 {
 change(NonHalt w23_162_tm /\ QHBoundTr 67 w23_162_tm).
 destruct(weighted23_nth 162 w23_162_tm w23_162_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LA0LA_1LA2RA1RB *)
Definition known23_149:TM:=machine_of_codes 2 3 [7;8;0;4;10;7].
Lemma known23_149_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_149 /\ Bounds 59 67 known23_149.
Proof.
 assert(H:NonHalt known23_149 /\ QHBoundTr 67 known23_149).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_114_tm) /\ QHBoundTr 67 (mirror_tm w23_114_tm)).
 destruct(weighted23_nth 114 (mirror_tm w23_114_tm) w23_114_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LA0LA_1LA2RB1RB *)
Definition known23_150:TM:=machine_of_codes 2 3 [7;8;0;4;11;7].
Lemma known23_150_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_150 /\ Bounds 59 67 known23_150.
Proof.
 assert(H:NonHalt known23_150 /\ QHBoundTr 67 known23_150).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_115_tm) /\ QHBoundTr 67 (mirror_tm w23_115_tm)).
 destruct(weighted23_nth 115 (mirror_tm w23_115_tm) w23_115_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LA0RB_1LA1LA1RA *)
Definition known23_151:TM:=machine_of_codes 2 3 [7;8;3;4;4;6].
Lemma known23_151_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_151 /\ Bounds 59 67 known23_151.
Proof.
 assert(H:NonHalt known23_151 /\ QHBoundTr 67 known23_151).
 {
 assert(E:known23_151=LAPT_1RB2LA0RB_1LA1LA1RA.tm_1RB2LA0RB_1LA1LA1RA)by(apply same_table_sound;reflexivity). rewrite E.
 apply known23_recurrence. exact LAPT_1RB2LA0RB_1LA1LA1RA.nqhtr_1RB2LA0RB_1LA1LA1RA.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LA0RB_1LB1LA1RA *)
Definition known23_152:TM:=machine_of_codes 2 3 [7;8;3;5;4;6].
Lemma known23_152_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_152 /\ Bounds 59 67 known23_152.
Proof.
 assert(H:NonHalt known23_152 /\ QHBoundTr 67 known23_152).
 {
 split;[exact(proj1(remaining23_nth 7 known23_152 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 7 (eq_refl(Some known23_152))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LA0RB_2LB1LA1RA *)
Definition known23_153:TM:=machine_of_codes 2 3 [7;8;3;9;4;6].
Lemma known23_153_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_153 /\ Bounds 59 67 known23_153.
Proof.
 assert(H:NonHalt known23_153 /\ QHBoundTr 67 known23_153).
 {
 split;[exact(proj1(remaining23_nth 8 known23_153 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 8 (eq_refl(Some known23_153))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LA1LA_0LA0RB2RB *)
Definition known23_154:TM:=machine_of_codes 2 3 [7;8;4;0;3;11].
Lemma known23_154_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_154 /\ Bounds 59 67 known23_154.
Proof.
 assert(H:NonHalt known23_154 /\ QHBoundTr 67 known23_154).
 {
 change(NonHalt w23_098_tm /\ QHBoundTr 67 w23_098_tm).
 destruct(weighted23_nth 98 w23_098_tm w23_098_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LA1LA_1LA2RB0RB *)
Definition known23_155:TM:=machine_of_codes 2 3 [7;8;4;4;11;3].
Lemma known23_155_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_155 /\ Bounds 59 67 known23_155.
Proof.
 assert(H:NonHalt known23_155 /\ QHBoundTr 67 known23_155).
 {
 change(NonHalt w23_113_tm /\ QHBoundTr 67 w23_113_tm).
 destruct(weighted23_nth 113 w23_113_tm w23_113_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LA1LB_0LA1RB2RB *)
Definition known23_156:TM:=machine_of_codes 2 3 [7;8;5;0;7;11].
Lemma known23_156_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_156 /\ Bounds 59 67 known23_156.
Proof.
 assert(H:NonHalt known23_156 /\ QHBoundTr 67 known23_156).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_099_tm) /\ QHBoundTr 67 (mirror_tm w23_099_tm)).
 destruct(weighted23_nth 99 (mirror_tm w23_099_tm) w23_099_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LA1RA_1LA2LA2RB *)
Definition known23_157:TM:=machine_of_codes 2 3 [7;8;6;4;8;11].
Lemma known23_157_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_157 /\ Bounds 59 67 known23_157.
Proof.
 assert(H:NonHalt known23_157 /\ QHBoundTr 67 known23_157).
 {
 split;[exact(proj1(remaining23_nth 9 known23_157 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 9 (eq_refl(Some known23_157))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LA1RA_1LA2RA2RB *)
Definition known23_158:TM:=machine_of_codes 2 3 [7;8;6;4;10;11].
Lemma known23_158_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_158 /\ Bounds 59 67 known23_158.
Proof.
 assert(H:NonHalt known23_158 /\ QHBoundTr 67 known23_158).
 {
 split;[exact(proj1(remaining23_nth 10 known23_158 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 10 (eq_refl(Some known23_158))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LA1RA_1LB1LA2RB *)
Definition known23_159:TM:=machine_of_codes 2 3 [7;8;6;5;4;11].
Lemma known23_159_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_159 /\ Bounds 59 67 known23_159.
Proof.
 assert(H:NonHalt known23_159 /\ QHBoundTr 67 known23_159).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_122_tm) /\ QHBoundTr 67 (mirror_tm w23_122_tm)).
 destruct(weighted23_nth 122 (mirror_tm w23_122_tm) w23_122_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LA1RA_2LA2RB1LB *)
Definition known23_160:TM:=machine_of_codes 2 3 [7;8;6;8;11;5].
Lemma known23_160_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_160 /\ Bounds 59 67 known23_160.
Proof.
 assert(H:NonHalt known23_160 /\ QHBoundTr 67 known23_160).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_147_tm) /\ QHBoundTr 67 (mirror_tm w23_147_tm)).
 destruct(weighted23_nth 147 (mirror_tm w23_147_tm) w23_147_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LA1RB_0LA---2RB *)
Definition known23_161:TM:=machine_of_codes 2 3 [7;8;7;0;12;11].
Lemma known23_161_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_161 /\ Bounds 59 67 known23_161.
Proof.
 assert(H:NonHalt known23_161 /\ QHBoundTr 67 known23_161).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_100_tm) /\ QHBoundTr 67 (mirror_tm w23_100_tm)).
 destruct(weighted23_nth 100 (mirror_tm w23_100_tm) w23_100_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LA1RB_0LB1LA2RB *)
Definition known23_162:TM:=machine_of_codes 2 3 [7;8;7;1;4;11].
Lemma known23_162_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_162 /\ Bounds 59 67 known23_162.
Proof.
 assert(H:NonHalt known23_162 /\ QHBoundTr 67 known23_162).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_103_tm) /\ QHBoundTr 67 (mirror_tm w23_103_tm)).
 destruct(weighted23_nth 103 (mirror_tm w23_103_tm) w23_103_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LA1RB_1LA0LA2RB *)
Definition known23_163:TM:=machine_of_codes 2 3 [7;8;7;4;0;11].
Lemma known23_163_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_163 /\ Bounds 59 67 known23_163.
Proof.
 assert(H:NonHalt known23_163 /\ QHBoundTr 67 known23_163).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_116_tm) /\ QHBoundTr 67 (mirror_tm w23_116_tm)).
 destruct(weighted23_nth 116 (mirror_tm w23_116_tm) w23_116_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LA1RB_1LA1LA2RB *)
Definition known23_164:TM:=machine_of_codes 2 3 [7;8;7;4;4;11].
Lemma known23_164_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_164 /\ Bounds 59 67 known23_164.
Proof.
 assert(H:NonHalt known23_164 /\ QHBoundTr 67 known23_164).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_117_tm) /\ QHBoundTr 67 (mirror_tm w23_117_tm)).
 destruct(weighted23_nth 117 (mirror_tm w23_117_tm) w23_117_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LA1RB_1LB1LA2RB *)
Definition known23_165:TM:=machine_of_codes 2 3 [7;8;7;5;4;11].
Lemma known23_165_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_165 /\ Bounds 59 67 known23_165.
Proof.
 assert(H:NonHalt known23_165 /\ QHBoundTr 67 known23_165).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_123_tm) /\ QHBoundTr 67 (mirror_tm w23_123_tm)).
 destruct(weighted23_nth 123 (mirror_tm w23_123_tm) w23_123_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LA1RB_2LB1LA2RB *)
Definition known23_166:TM:=machine_of_codes 2 3 [7;8;7;9;4;11].
Lemma known23_166_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_166 /\ Bounds 59 67 known23_166.
Proof.
 assert(H:NonHalt known23_166 /\ QHBoundTr 67 known23_166).
 {
 assert(E:known23_166=LAPQ_1RB2LA1RB_2LB1LA2RB.tm_1RB2LA1RB_2LB1LA2RB)by(apply same_table_sound;reflexivity). rewrite E.
 exact LAPQ_1RB2LA1RB_2LB1LA2RB.qhtr_1RB2LA1RB_2LB1LA2RB.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LA2LA_2LA2RB1LB *)
Definition known23_167:TM:=machine_of_codes 2 3 [7;8;8;8;11;5].
Lemma known23_167_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_167 /\ Bounds 59 67 known23_167.
Proof.
 assert(H:NonHalt known23_167 /\ QHBoundTr 67 known23_167).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_148_tm) /\ QHBoundTr 67 (mirror_tm w23_148_tm)).
 destruct(weighted23_nth 148 (mirror_tm w23_148_tm) w23_148_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LB0LB_1LA2RA0LB *)
Definition known23_168:TM:=machine_of_codes 2 3 [7;9;1;4;10;1].
Lemma known23_168_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_168 /\ Bounds 59 67 known23_168.
Proof.
 assert(H:NonHalt known23_168 /\ QHBoundTr 67 known23_168).
 {
 split;[exact(proj1(remaining23_nth 11 known23_168 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 11 (eq_refl(Some known23_168))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LB1LA_1LA2RB0RB *)
Definition known23_169:TM:=machine_of_codes 2 3 [7;9;4;4;11;3].
Lemma known23_169_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_169 /\ Bounds 59 67 known23_169.
Proof.
 assert(H:NonHalt known23_169 /\ QHBoundTr 67 known23_169).
 {
 change(NonHalt w23_119_tm /\ QHBoundTr 67 w23_119_tm).
 destruct(weighted23_nth 119 w23_119_tm w23_119_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LB1RA_2LA1LB2RA *)
Definition known23_170:TM:=machine_of_codes 2 3 [7;9;6;8;5;10].
Lemma known23_170_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_170 /\ Bounds 59 67 known23_170.
Proof.
 assert(H:NonHalt known23_170 /\ QHBoundTr 67 known23_170).
 {
 change(NonHalt w23_151_tm /\ QHBoundTr 67 w23_151_tm).
 destruct(weighted23_nth 151 w23_151_tm w23_151_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LB2LA_1LA2RB1LB *)
Definition known23_171:TM:=machine_of_codes 2 3 [7;9;8;4;11;5].
Lemma known23_171_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_171 /\ Bounds 59 67 known23_171.
Proof.
 assert(H:NonHalt known23_171 /\ QHBoundTr 67 known23_171).
 {
 split;[exact(proj1(remaining23_nth 12 known23_171 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 12 (eq_refl(Some known23_171))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LB2LA_2LA2RB1LB *)
Definition known23_172:TM:=machine_of_codes 2 3 [7;9;8;8;11;5].
Lemma known23_172_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_172 /\ Bounds 59 67 known23_172.
Proof.
 assert(H:NonHalt known23_172 /\ QHBoundTr 67 known23_172).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_150_tm) /\ QHBoundTr 67 (mirror_tm w23_150_tm)).
 destruct(weighted23_nth 150 (mirror_tm w23_150_tm) w23_150_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LB2RA_1LA1RA1LB *)
Definition known23_173:TM:=machine_of_codes 2 3 [7;9;10;4;6;5].
Lemma known23_173_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_173 /\ Bounds 59 67 known23_173.
Proof.
 assert(H:NonHalt known23_173 /\ QHBoundTr 67 known23_173).
 {
 change(NonHalt w23_118_tm /\ QHBoundTr 67 w23_118_tm).
 destruct(weighted23_nth 118 w23_118_tm w23_118_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2LB2RA_2LA1RA1LB *)
Definition known23_174:TM:=machine_of_codes 2 3 [7;9;10;8;6;5].
Lemma known23_174_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_174 /\ Bounds 59 67 known23_174.
Proof.
 assert(H:NonHalt known23_174 /\ QHBoundTr 67 known23_174).
 {
 change(NonHalt w23_149_tm /\ QHBoundTr 67 w23_149_tm).
 destruct(weighted23_nth 149 w23_149_tm w23_149_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2RA1LA_2LA1RB--- *)
Definition known23_175:TM:=machine_of_codes 2 3 [7;10;4;8;7;12].
Lemma known23_175_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_175 /\ Bounds 59 67 known23_175.
Proof.
 assert(H:NonHalt known23_175 /\ QHBoundTr 67 known23_175).
 {
 change(NonHalt w23_152_tm /\ QHBoundTr 67 w23_152_tm).
 destruct(weighted23_nth 152 w23_152_tm w23_152_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2RA1LA_2LA2LB1RB *)
Definition known23_176:TM:=machine_of_codes 2 3 [7;10;4;8;9;7].
Lemma known23_176_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_176 /\ Bounds 59 67 known23_176.
Proof.
 assert(H:NonHalt known23_176 /\ QHBoundTr 67 known23_176).
 {
 change(NonHalt w23_153_tm /\ QHBoundTr 67 w23_153_tm).
 destruct(weighted23_nth 153 w23_153_tm w23_153_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2RA1LB_2LA1RA2LB *)
Definition known23_177:TM:=machine_of_codes 2 3 [7;10;5;8;6;9].
Lemma known23_177_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_177 /\ Bounds 59 67 known23_177.
Proof.
 assert(H:NonHalt known23_177 /\ QHBoundTr 67 known23_177).
 {
 change(NonHalt w23_154_tm /\ QHBoundTr 67 w23_154_tm).
 destruct(weighted23_nth 154 w23_154_tm w23_154_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2RA2LA_2LA2RB1LB *)
Definition known23_178:TM:=machine_of_codes 2 3 [7;10;8;8;11;5].
Lemma known23_178_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_178 /\ Bounds 59 67 known23_178.
Proof.
 assert(H:NonHalt known23_178 /\ QHBoundTr 67 known23_178).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_155_tm) /\ QHBoundTr 67 (mirror_tm w23_155_tm)).
 destruct(weighted23_nth 155 (mirror_tm w23_155_tm) w23_155_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2RA2LB_1LB2LA0RA *)
Definition known23_179:TM:=machine_of_codes 2 3 [7;10;9;5;8;2].
Lemma known23_179_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_179 /\ Bounds 59 67 known23_179.
Proof.
 assert(H:NonHalt known23_179 /\ QHBoundTr 67 known23_179).
 {
 assert(E:known23_179=LAPT_1RB2RA2LB_1LB2LA0RA.tm_1RB2RA2LB_1LB2LA0RA)by(apply same_table_sound;reflexivity). rewrite E.
 apply known23_recurrence. exact LAPT_1RB2RA2LB_1LB2LA0RA.nqhtr_1RB2RA2LB_1LB2LA0RA.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2RA2LB_2LA1LB1RA *)
Definition known23_180:TM:=machine_of_codes 2 3 [7;10;9;8;5;6].
Lemma known23_180_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_180 /\ Bounds 59 67 known23_180.
Proof.
 assert(H:NonHalt known23_180 /\ QHBoundTr 67 known23_180).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_156_tm) /\ QHBoundTr 67 (mirror_tm w23_156_tm)).
 destruct(weighted23_nth 156 (mirror_tm w23_156_tm) w23_156_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2RB1LA_0LA1RB--- *)
Definition known23_181:TM:=machine_of_codes 2 3 [7;11;4;0;7;12].
Lemma known23_181_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_181 /\ Bounds 59 67 known23_181.
Proof.
 assert(H:NonHalt known23_181 /\ QHBoundTr 67 known23_181).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_101_tm) /\ QHBoundTr 67 (mirror_tm w23_101_tm)).
 destruct(weighted23_nth 101 (mirror_tm w23_101_tm) w23_101_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2RB1LA_2LA1RB0LA *)
Definition known23_182:TM:=machine_of_codes 2 3 [7;11;4;8;7;0].
Lemma known23_182_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_182 /\ Bounds 59 67 known23_182.
Proof.
 assert(H:NonHalt known23_182 /\ QHBoundTr 67 known23_182).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_157_tm) /\ QHBoundTr 67 (mirror_tm w23_157_tm)).
 destruct(weighted23_nth 157 (mirror_tm w23_157_tm) w23_157_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2RB1LA_2LA1RB2LA *)
Definition known23_183:TM:=machine_of_codes 2 3 [7;11;4;8;7;8].
Lemma known23_183_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_183 /\ Bounds 59 67 known23_183.
Proof.
 assert(H:NonHalt known23_183 /\ QHBoundTr 67 known23_183).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_159_tm) /\ QHBoundTr 67 (mirror_tm w23_159_tm)).
 destruct(weighted23_nth 159 (mirror_tm w23_159_tm) w23_159_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2RB1LA_2LB1RB2LA *)
Definition known23_184:TM:=machine_of_codes 2 3 [7;11;4;9;7;8].
Lemma known23_184_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_184 /\ Bounds 59 67 known23_184.
Proof.
 assert(H:NonHalt known23_184 /\ QHBoundTr 67 known23_184).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_160_tm) /\ QHBoundTr 67 (mirror_tm w23_160_tm)).
 destruct(weighted23_nth 160 (mirror_tm w23_160_tm) w23_160_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2RB2LA_0LA---1RB *)
Definition known23_185:TM:=machine_of_codes 2 3 [7;11;8;0;12;7].
Lemma known23_185_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_185 /\ Bounds 59 67 known23_185.
Proof.
 assert(H:NonHalt known23_185 /\ QHBoundTr 67 known23_185).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_102_tm) /\ QHBoundTr 67 (mirror_tm w23_102_tm)).
 destruct(weighted23_nth 102 (mirror_tm w23_102_tm) w23_102_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2RB2LA_0LB1LA1RB *)
Definition known23_186:TM:=machine_of_codes 2 3 [7;11;8;1;4;7].
Lemma known23_186_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_186 /\ Bounds 59 67 known23_186.
Proof.
 assert(H:NonHalt known23_186 /\ QHBoundTr 67 known23_186).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_104_tm) /\ QHBoundTr 67 (mirror_tm w23_104_tm)).
 destruct(weighted23_nth 104 (mirror_tm w23_104_tm) w23_104_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2RB2LA_0LB2LA1RB *)
Definition known23_187:TM:=machine_of_codes 2 3 [7;11;8;1;8;7].
Lemma known23_187_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_187 /\ Bounds 59 67 known23_187.
Proof.
 assert(H:NonHalt known23_187 /\ QHBoundTr 67 known23_187).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_105_tm) /\ QHBoundTr 67 (mirror_tm w23_105_tm)).
 destruct(weighted23_nth 105 (mirror_tm w23_105_tm) w23_105_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2RB2LA_1LA0LA1RB *)
Definition known23_188:TM:=machine_of_codes 2 3 [7;11;8;4;0;7].
Lemma known23_188_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_188 /\ Bounds 59 67 known23_188.
Proof.
 assert(H:NonHalt known23_188 /\ QHBoundTr 67 known23_188).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_120_tm) /\ QHBoundTr 67 (mirror_tm w23_120_tm)).
 destruct(weighted23_nth 120 (mirror_tm w23_120_tm) w23_120_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2RB2LA_1LA1LA1RB *)
Definition known23_189:TM:=machine_of_codes 2 3 [7;11;8;4;4;7].
Lemma known23_189_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_189 /\ Bounds 59 67 known23_189.
Proof.
 assert(H:NonHalt known23_189 /\ QHBoundTr 67 known23_189).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_121_tm) /\ QHBoundTr 67 (mirror_tm w23_121_tm)).
 destruct(weighted23_nth 121 (mirror_tm w23_121_tm) w23_121_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2RB2LA_1LA2RB1LB *)
Definition known23_190:TM:=machine_of_codes 2 3 [7;11;8;4;11;5].
Lemma known23_190_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_190 /\ Bounds 59 67 known23_190.
Proof.
 assert(H:NonHalt known23_190 /\ QHBoundTr 67 known23_190).
 {
 split;[exact(proj1(remaining23_nth 13 known23_190 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 13 (eq_refl(Some known23_190))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2RB2LA_1LB1LA1RB *)
Definition known23_191:TM:=machine_of_codes 2 3 [7;11;8;5;4;7].
Lemma known23_191_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_191 /\ Bounds 59 67 known23_191.
Proof.
 assert(H:NonHalt known23_191 /\ QHBoundTr 67 known23_191).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_124_tm) /\ QHBoundTr 67 (mirror_tm w23_124_tm)).
 destruct(weighted23_nth 124 (mirror_tm w23_124_tm) w23_124_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2RB2LA_2LA2RB1LB *)
Definition known23_192:TM:=machine_of_codes 2 3 [7;11;8;8;11;5].
Lemma known23_192_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_192 /\ Bounds 59 67 known23_192.
Proof.
 assert(H:NonHalt known23_192 /\ QHBoundTr 67 known23_192).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_158_tm) /\ QHBoundTr 67 (mirror_tm w23_158_tm)).
 destruct(weighted23_nth 158 (mirror_tm w23_158_tm) w23_158_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 1RB2RB2LA_2LB1LA1RB *)
Definition known23_193:TM:=machine_of_codes 2 3 [7;11;8;9;4;7].
Lemma known23_193_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_193 /\ Bounds 59 67 known23_193.
Proof.
 assert(H:NonHalt known23_193 /\ QHBoundTr 67 known23_193).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm wd23_003_tm) /\ QHBoundTr 67 (mirror_tm wd23_003_tm)).
 destruct(weighted23_deep_nth 3 (mirror_tm wd23_003_tm) 3 128 wd23_003_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB0LB1RA_1RB2LA2RA *)
Definition known23_194:TM:=machine_of_codes 2 3 [9;1;6;7;8;10].
Lemma known23_194_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_194 /\ Bounds 59 67 known23_194.
Proof.
 assert(H:NonHalt known23_194 /\ QHBoundTr 67 known23_194).
 {
 split;[exact(proj1(remaining23_nth 14 known23_194 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 14 (eq_refl(Some known23_194))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB0LB1RA_2RA2LA2RA *)
Definition known23_195:TM:=machine_of_codes 2 3 [9;1;6;10;8;10].
Lemma known23_195_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_195 /\ Bounds 59 67 known23_195.
Proof.
 assert(H:NonHalt known23_195 /\ QHBoundTr 67 known23_195).
 {
 apply known23_unmirror.
 assert(E:(mirror_tm known23_195)=LAPT_2RB0RB1LA_2LA2RA2LA.tm_2RB0RB1LA_2LA2RA2LA)by(apply same_table_sound;reflexivity). rewrite E.
 apply known23_recurrence. exact LAPT_2RB0RB1LA_2LA2RA2LA.nqhtr_2RB0RB1LA_2LA2RA2LA.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB0LB1RA_2RB2LA2RA *)
Definition known23_196:TM:=machine_of_codes 2 3 [9;1;6;11;8;10].
Lemma known23_196_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_196 /\ Bounds 59 67 known23_196.
Proof.
 assert(H:NonHalt known23_196 /\ QHBoundTr 67 known23_196).
 {
 split;[exact(proj1(remaining23_nth 15 known23_196 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 15 (eq_refl(Some known23_196))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB0RA1RA_2RA2LB1LA *)
Definition known23_197:TM:=machine_of_codes 2 3 [9;2;6;10;9;4].
Lemma known23_197_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_197 /\ Bounds 59 67 known23_197.
Proof.
 assert(H:NonHalt known23_197 /\ QHBoundTr 67 known23_197).
 {
 change(NonHalt w23_218_tm /\ QHBoundTr 67 w23_218_tm).
 destruct(weighted23_nth 218 w23_218_tm w23_218_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB0RA1RA_2RA2LB1LB *)
Definition known23_198:TM:=machine_of_codes 2 3 [9;2;6;10;9;5].
Lemma known23_198_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_198 /\ Bounds 59 67 known23_198.
Proof.
 assert(H:NonHalt known23_198 /\ QHBoundTr 67 known23_198).
 {
 change(NonHalt w23_219_tm /\ QHBoundTr 67 w23_219_tm).
 destruct(weighted23_nth 219 w23_219_tm w23_219_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB0RA2RA_1RA1LB2LB *)
Definition known23_199:TM:=machine_of_codes 2 3 [9;2;10;6;5;9].
Lemma known23_199_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_199 /\ Bounds 59 67 known23_199.
Proof.
 assert(H:NonHalt known23_199 /\ QHBoundTr 67 known23_199).
 {
 change(NonHalt w23_203_tm /\ QHBoundTr 67 w23_203_tm).
 destruct(weighted23_nth 203 w23_203_tm w23_203_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB0RB1RB_2RA0RB1LA *)
Definition known23_200:TM:=machine_of_codes 2 3 [9;3;7;10;3;4].
Lemma known23_200_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_200 /\ Bounds 59 67 known23_200.
Proof.
 assert(H:NonHalt known23_200 /\ QHBoundTr 67 known23_200).
 {
 split;[exact(proj1(remaining23_nth 16 known23_200 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 16 (eq_refl(Some known23_200))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1LA1RB_1RA2RB2LA *)
Definition known23_201:TM:=machine_of_codes 2 3 [9;4;7;6;11;8].
Lemma known23_201_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_201 /\ Bounds 59 67 known23_201.
Proof.
 assert(H:NonHalt known23_201 /\ QHBoundTr 67 known23_201).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_193_tm) /\ QHBoundTr 67 (mirror_tm w23_193_tm)).
 destruct(weighted23_nth 193 (mirror_tm w23_193_tm) w23_193_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1LA1RB_2RA2RB2LA *)
Definition known23_202:TM:=machine_of_codes 2 3 [9;4;7;10;11;8].
Lemma known23_202_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_202 /\ Bounds 59 67 known23_202.
Proof.
 assert(H:NonHalt known23_202 /\ QHBoundTr 67 known23_202).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_221_tm) /\ QHBoundTr 67 (mirror_tm w23_221_tm)).
 destruct(weighted23_nth 221 (mirror_tm w23_221_tm) w23_221_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1LA2RB_1RA2LA1RB *)
Definition known23_203:TM:=machine_of_codes 2 3 [9;4;11;6;8;7].
Lemma known23_203_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_203 /\ Bounds 59 67 known23_203.
Proof.
 assert(H:NonHalt known23_203 /\ QHBoundTr 67 known23_203).
 {
 change(NonHalt w23_205_tm /\ QHBoundTr 67 w23_205_tm).
 destruct(weighted23_nth 205 w23_205_tm w23_205_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA0LA_1RA2RB1LB *)
Definition known23_204:TM:=machine_of_codes 2 3 [9;6;0;6;11;5].
Lemma known23_204_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_204 /\ Bounds 59 67 known23_204.
Proof.
 assert(H:NonHalt known23_204 /\ QHBoundTr 67 known23_204).
 {
 change(NonHalt w23_176_tm /\ QHBoundTr 67 w23_176_tm).
 destruct(weighted23_nth 176 w23_176_tm w23_176_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA0LB_1RA2RA1LB *)
Definition known23_205:TM:=machine_of_codes 2 3 [9;6;1;6;10;5].
Lemma known23_205_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_205 /\ Bounds 59 67 known23_205.
Proof.
 assert(H:NonHalt known23_205 /\ QHBoundTr 67 known23_205).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_178_tm) /\ QHBoundTr 67 (mirror_tm w23_178_tm)).
 destruct(weighted23_nth 178 (mirror_tm w23_178_tm) w23_178_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA0LB_1RA2RB1LB *)
Definition known23_206:TM:=machine_of_codes 2 3 [9;6;1;6;11;5].
Lemma known23_206_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_206 /\ Bounds 59 67 known23_206.
Proof.
 assert(H:NonHalt known23_206 /\ QHBoundTr 67 known23_206).
 {
 change(NonHalt w23_179_tm /\ QHBoundTr 67 w23_179_tm).
 destruct(weighted23_nth 179 w23_179_tm w23_179_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA0LB_1RB2RA1LB *)
Definition known23_207:TM:=machine_of_codes 2 3 [9;6;1;7;10;5].
Lemma known23_207_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_207 /\ Bounds 59 67 known23_207.
Proof.
 assert(H:NonHalt known23_207 /\ QHBoundTr 67 known23_207).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_208_tm) /\ QHBoundTr 67 (mirror_tm w23_208_tm)).
 destruct(weighted23_nth 208 (mirror_tm w23_208_tm) w23_208_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA0LB_2RA2RA1LB *)
Definition known23_208:TM:=machine_of_codes 2 3 [9;6;1;10;10;5].
Lemma known23_208_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_208 /\ Bounds 59 67 known23_208.
Proof.
 assert(H:NonHalt known23_208 /\ QHBoundTr 67 known23_208).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_211_tm) /\ QHBoundTr 67 (mirror_tm w23_211_tm)).
 destruct(weighted23_nth 211 (mirror_tm w23_211_tm) w23_211_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA0LB_2RB2RA1LB *)
Definition known23_209:TM:=machine_of_codes 2 3 [9;6;1;11;10;5].
Lemma known23_209_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_209 /\ Bounds 59 67 known23_209.
Proof.
 assert(H:NonHalt known23_209 /\ QHBoundTr 67 known23_209).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_225_tm) /\ QHBoundTr 67 (mirror_tm w23_225_tm)).
 destruct(weighted23_nth 225 (mirror_tm w23_225_tm) w23_225_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA0RB_1RA2RB1LB *)
Definition known23_210:TM:=machine_of_codes 2 3 [9;6;3;6;11;5].
Lemma known23_210_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_210 /\ Bounds 59 67 known23_210.
Proof.
 assert(H:NonHalt known23_210 /\ QHBoundTr 67 known23_210).
 {
 change(NonHalt w23_180_tm /\ QHBoundTr 67 w23_180_tm).
 destruct(weighted23_nth 180 w23_180_tm w23_180_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA1LA_1RA2RB1LB *)
Definition known23_211:TM:=machine_of_codes 2 3 [9;6;4;6;11;5].
Lemma known23_211_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_211 /\ Bounds 59 67 known23_211.
Proof.
 assert(H:NonHalt known23_211 /\ QHBoundTr 67 known23_211).
 {
 change(NonHalt w23_181_tm /\ QHBoundTr 67 w23_181_tm).
 destruct(weighted23_nth 181 w23_181_tm w23_181_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA1LB_0RA2LB--- *)
Definition known23_212:TM:=machine_of_codes 2 3 [9;6;5;2;9;12].
Lemma known23_212_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_212 /\ Bounds 59 67 known23_212.
Proof.
 assert(H:NonHalt known23_212 /\ QHBoundTr 67 known23_212).
 {
 change(NonHalt w23_164_tm /\ QHBoundTr 67 w23_164_tm).
 destruct(weighted23_nth 164 w23_164_tm w23_164_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA1LB_0RB2LB1RA *)
Definition known23_213:TM:=machine_of_codes 2 3 [9;6;5;3;9;6].
Lemma known23_213_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_213 /\ Bounds 59 67 known23_213.
Proof.
 assert(H:NonHalt known23_213 /\ QHBoundTr 67 known23_213).
 {
 change(NonHalt w23_173_tm /\ QHBoundTr 67 w23_173_tm).
 destruct(weighted23_nth 173 w23_173_tm w23_173_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA1LB_0RB2LB2RA *)
Definition known23_214:TM:=machine_of_codes 2 3 [9;6;5;3;9;10].
Lemma known23_214_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_214 /\ Bounds 59 67 known23_214.
Proof.
 assert(H:NonHalt known23_214 /\ QHBoundTr 67 known23_214).
 {
 change(NonHalt w23_174_tm /\ QHBoundTr 67 w23_174_tm).
 destruct(weighted23_nth 174 w23_174_tm w23_174_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA1LB_1RA2RB1LB *)
Definition known23_215:TM:=machine_of_codes 2 3 [9;6;5;6;11;5].
Lemma known23_215_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_215 /\ Bounds 59 67 known23_215.
Proof.
 assert(H:NonHalt known23_215 /\ QHBoundTr 67 known23_215).
 {
 change(NonHalt w23_188_tm /\ QHBoundTr 67 w23_188_tm).
 destruct(weighted23_nth 188 w23_188_tm w23_188_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA1LB_1RB2LB2RA *)
Definition known23_216:TM:=machine_of_codes 2 3 [9;6;5;7;9;10].
Lemma known23_216_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_216 /\ Bounds 59 67 known23_216.
Proof.
 assert(H:NonHalt known23_216 /\ QHBoundTr 67 known23_216).
 {
 change(NonHalt wd23_004_tm /\ QHBoundTr 67 wd23_004_tm).
 destruct(weighted23_deep_nth 4 wd23_004_tm 3 128 wd23_004_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA1LB_2RA2LB0RA *)
Definition known23_217:TM:=machine_of_codes 2 3 [9;6;5;10;9;2].
Lemma known23_217_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_217 /\ Bounds 59 67 known23_217.
Proof.
 assert(H:NonHalt known23_217 /\ QHBoundTr 67 known23_217).
 {
 change(NonHalt w23_213_tm /\ QHBoundTr 67 w23_213_tm).
 destruct(weighted23_nth 213 w23_213_tm w23_213_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA1LB_2RA2LB2RA *)
Definition known23_218:TM:=machine_of_codes 2 3 [9;6;5;10;9;10].
Lemma known23_218_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_218 /\ Bounds 59 67 known23_218.
Proof.
 assert(H:NonHalt known23_218 /\ QHBoundTr 67 known23_218).
 {
 change(NonHalt w23_214_tm /\ QHBoundTr 67 w23_214_tm).
 destruct(weighted23_nth 214 w23_214_tm w23_214_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA1LB_2RA2RB1LB *)
Definition known23_219:TM:=machine_of_codes 2 3 [9;6;5;10;11;5].
Lemma known23_219_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_219 /\ Bounds 59 67 known23_219.
Proof.
 assert(H:NonHalt known23_219 /\ QHBoundTr 67 known23_219).
 {
 split;[exact(proj1(remaining23_nth 17 known23_219 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 17 (eq_refl(Some known23_219))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA1LB_2RB2LB2RA *)
Definition known23_220:TM:=machine_of_codes 2 3 [9;6;5;11;9;10].
Lemma known23_220_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_220 /\ Bounds 59 67 known23_220.
Proof.
 assert(H:NonHalt known23_220 /\ QHBoundTr 67 known23_220).
 {
 change(NonHalt w23_229_tm /\ QHBoundTr 67 w23_229_tm).
 destruct(weighted23_nth 229 w23_229_tm w23_229_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA1RA_1RA2RB1LB *)
Definition known23_221:TM:=machine_of_codes 2 3 [9;6;6;6;11;5].
Lemma known23_221_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_221 /\ Bounds 59 67 known23_221.
Proof.
 assert(H:NonHalt known23_221 /\ QHBoundTr 67 known23_221).
 {
 change(NonHalt w23_189_tm /\ QHBoundTr 67 w23_189_tm).
 destruct(weighted23_nth 189 w23_189_tm w23_189_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA1RB_1RA2RB1LB *)
Definition known23_222:TM:=machine_of_codes 2 3 [9;6;7;6;11;5].
Lemma known23_222_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_222 /\ Bounds 59 67 known23_222.
Proof.
 assert(H:NonHalt known23_222 /\ QHBoundTr 67 known23_222).
 {
 change(NonHalt w23_192_tm /\ QHBoundTr 67 w23_192_tm).
 destruct(weighted23_nth 192 w23_192_tm w23_192_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA1RB_2RA2RB1LB *)
Definition known23_223:TM:=machine_of_codes 2 3 [9;6;7;10;11;5].
Lemma known23_223_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_223 /\ Bounds 59 67 known23_223.
Proof.
 assert(H:NonHalt known23_223 /\ QHBoundTr 67 known23_223).
 {
 split;[exact(proj1(remaining23_nth 18 known23_223 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 18 (eq_refl(Some known23_223))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA2LB_1RA2RA1LB *)
Definition known23_224:TM:=machine_of_codes 2 3 [9;6;9;6;10;5].
Lemma known23_224_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_224 /\ Bounds 59 67 known23_224.
Proof.
 assert(H:NonHalt known23_224 /\ QHBoundTr 67 known23_224).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_197_tm) /\ QHBoundTr 67 (mirror_tm w23_197_tm)).
 destruct(weighted23_nth 197 (mirror_tm w23_197_tm) w23_197_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA2LB_1RA2RB1LB *)
Definition known23_225:TM:=machine_of_codes 2 3 [9;6;9;6;11;5].
Lemma known23_225_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_225 /\ Bounds 59 67 known23_225.
Proof.
 assert(H:NonHalt known23_225 /\ QHBoundTr 67 known23_225).
 {
 change(NonHalt w23_198_tm /\ QHBoundTr 67 w23_198_tm).
 destruct(weighted23_nth 198 w23_198_tm w23_198_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA2LB_1RB2RA1LB *)
Definition known23_226:TM:=machine_of_codes 2 3 [9;6;9;7;10;5].
Lemma known23_226_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_226 /\ Bounds 59 67 known23_226.
Proof.
 assert(H:NonHalt known23_226 /\ QHBoundTr 67 known23_226).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_209_tm) /\ QHBoundTr 67 (mirror_tm w23_209_tm)).
 destruct(weighted23_nth 209 (mirror_tm w23_209_tm) w23_209_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA2LB_2RA2RA1LB *)
Definition known23_227:TM:=machine_of_codes 2 3 [9;6;9;10;10;5].
Lemma known23_227_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_227 /\ Bounds 59 67 known23_227.
Proof.
 assert(H:NonHalt known23_227 /\ QHBoundTr 67 known23_227).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_222_tm) /\ QHBoundTr 67 (mirror_tm w23_222_tm)).
 destruct(weighted23_nth 222 (mirror_tm w23_222_tm) w23_222_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA2LB_2RB2RA1LB *)
Definition known23_228:TM:=machine_of_codes 2 3 [9;6;9;11;10;5].
Lemma known23_228_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_228 /\ Bounds 59 67 known23_228.
Proof.
 assert(H:NonHalt known23_228 /\ QHBoundTr 67 known23_228).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_226_tm) /\ QHBoundTr 67 (mirror_tm w23_226_tm)).
 destruct(weighted23_nth 226 (mirror_tm w23_226_tm) w23_226_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA2RA_0RA0LB1LB *)
Definition known23_229:TM:=machine_of_codes 2 3 [9;6;10;2;1;5].
Lemma known23_229_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_229 /\ Bounds 59 67 known23_229.
Proof.
 assert(H:NonHalt known23_229 /\ QHBoundTr 67 known23_229).
 {
 change(NonHalt w23_169_tm /\ QHBoundTr 67 w23_169_tm).
 destruct(weighted23_nth 169 w23_169_tm w23_169_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA2RA_1RA1LB0LB *)
Definition known23_230:TM:=machine_of_codes 2 3 [9;6;10;6;5;1].
Lemma known23_230_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_230 /\ Bounds 59 67 known23_230.
Proof.
 assert(H:NonHalt known23_230 /\ QHBoundTr 67 known23_230).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_199_tm) /\ QHBoundTr 67 (mirror_tm w23_199_tm)).
 destruct(weighted23_nth 199 (mirror_tm w23_199_tm) w23_199_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA2RA_1RA2RB1LB *)
Definition known23_231:TM:=machine_of_codes 2 3 [9;6;10;6;11;5].
Lemma known23_231_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_231 /\ Bounds 59 67 known23_231.
Proof.
 assert(H:NonHalt known23_231 /\ QHBoundTr 67 known23_231).
 {
 change(NonHalt w23_202_tm /\ QHBoundTr 67 w23_202_tm).
 destruct(weighted23_nth 202 w23_202_tm w23_202_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RA2RB_1RA2RB1LB *)
Definition known23_232:TM:=machine_of_codes 2 3 [9;6;11;6;11;5].
Lemma known23_232_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_232 /\ Bounds 59 67 known23_232.
Proof.
 assert(H:NonHalt known23_232 /\ QHBoundTr 67 known23_232).
 {
 change(NonHalt w23_206_tm /\ QHBoundTr 67 w23_206_tm).
 destruct(weighted23_nth 206 w23_206_tm w23_206_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RB1LA_1RA2LA2RB *)
Definition known23_233:TM:=machine_of_codes 2 3 [9;7;4;6;8;11].
Lemma known23_233_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_233 /\ Bounds 59 67 known23_233.
Proof.
 assert(H:NonHalt known23_233 /\ QHBoundTr 67 known23_233).
 {
 change(NonHalt w23_182_tm /\ QHBoundTr 67 w23_182_tm).
 destruct(weighted23_nth 182 w23_182_tm w23_182_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RB1LA_2RB0LA1RA *)
Definition known23_234:TM:=machine_of_codes 2 3 [9;7;4;11;0;6].
Lemma known23_234_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_234 /\ Bounds 59 67 known23_234.
Proof.
 assert(H:NonHalt known23_234 /\ QHBoundTr 67 known23_234).
 {
 apply known23_unmirror.
 assert(E:(mirror_tm known23_234)=LAPT_2RB1LB1RA_2LB0RA1LA.tm_2RB1LB1RA_2LB0RA1LA)by(apply same_table_sound;reflexivity). rewrite E.
 apply known23_recurrence. exact LAPT_2RB1LB1RA_2LB0RA1LA.nqhtr_2RB1LB1RA_2LB0RA1LA.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB1RB2LA_1RA2RB1LA *)
Definition known23_235:TM:=machine_of_codes 2 3 [9;7;8;6;11;4].
Lemma known23_235_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_235 /\ Bounds 59 67 known23_235.
Proof.
 assert(H:NonHalt known23_235 /\ QHBoundTr 67 known23_235).
 {
 change(NonHalt w23_194_tm /\ QHBoundTr 67 w23_194_tm).
 destruct(weighted23_nth 194 w23_194_tm w23_194_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2LA1RA_1RA2RB1LB *)
Definition known23_236:TM:=machine_of_codes 2 3 [9;8;6;6;11;5].
Lemma known23_236_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_236 /\ Bounds 59 67 known23_236.
Proof.
 assert(H:NonHalt known23_236 /\ QHBoundTr 67 known23_236).
 {
 change(NonHalt w23_190_tm /\ QHBoundTr 67 w23_190_tm).
 destruct(weighted23_nth 190 w23_190_tm w23_190_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2LA1RA_2RA1LB1LA *)
Definition known23_237:TM:=machine_of_codes 2 3 [9;8;6;10;5;4].
Lemma known23_237_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_237 /\ Bounds 59 67 known23_237.
Proof.
 assert(H:NonHalt known23_237 /\ QHBoundTr 67 known23_237).
 {
 split;[exact(proj1(remaining23_nth 19 known23_237 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 19 (eq_refl(Some known23_237))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2LA1RA_2RA1LB1RA *)
Definition known23_238:TM:=machine_of_codes 2 3 [9;8;6;10;5;6].
Lemma known23_238_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_238 /\ Bounds 59 67 known23_238.
Proof.
 assert(H:NonHalt known23_238 /\ QHBoundTr 67 known23_238).
 {
 split;[exact(proj1(remaining23_nth 20 known23_238 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 20 (eq_refl(Some known23_238))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2LA1RA_2RB1LB2RA *)
Definition known23_239:TM:=machine_of_codes 2 3 [9;8;6;11;5;10].
Lemma known23_239_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_239 /\ Bounds 59 67 known23_239.
Proof.
 assert(H:NonHalt known23_239 /\ QHBoundTr 67 known23_239).
 {
 change(NonHalt w23_230_tm /\ QHBoundTr 67 w23_230_tm).
 destruct(weighted23_nth 230 w23_230_tm w23_230_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2LA1RB_1RA1LA2RB *)
Definition known23_240:TM:=machine_of_codes 2 3 [9;8;7;6;4;11].
Lemma known23_240_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_240 /\ Bounds 59 67 known23_240.
Proof.
 assert(H:NonHalt known23_240 /\ QHBoundTr 67 known23_240).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_191_tm) /\ QHBoundTr 67 (mirror_tm w23_191_tm)).
 destruct(weighted23_nth 191 (mirror_tm w23_191_tm) w23_191_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2LA2RB_1RA1RB1LA *)
Definition known23_241:TM:=machine_of_codes 2 3 [9;8;11;6;7;4].
Lemma known23_241_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_241 /\ Bounds 59 67 known23_241.
Proof.
 assert(H:NonHalt known23_241 /\ QHBoundTr 67 known23_241).
 {
 change(NonHalt w23_204_tm /\ QHBoundTr 67 w23_204_tm).
 destruct(weighted23_nth 204 w23_204_tm w23_204_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2LA2RB_2RA1RB1LA *)
Definition known23_242:TM:=machine_of_codes 2 3 [9;8;11;10;7;4].
Lemma known23_242_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_242 /\ Bounds 59 67 known23_242.
Proof.
 assert(H:NonHalt known23_242 /\ QHBoundTr 67 known23_242).
 {
 change(NonHalt w23_224_tm /\ QHBoundTr 67 w23_224_tm).
 destruct(weighted23_nth 224 w23_224_tm w23_224_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2LB1RA_0RA1LB--- *)
Definition known23_243:TM:=machine_of_codes 2 3 [9;9;6;2;5;12].
Lemma known23_243_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_243 /\ Bounds 59 67 known23_243.
Proof.
 assert(H:NonHalt known23_243 /\ QHBoundTr 67 known23_243).
 {
 change(NonHalt w23_166_tm /\ QHBoundTr 67 w23_166_tm).
 destruct(weighted23_nth 166 w23_166_tm w23_166_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2LB1RA_0RB1LB2RA *)
Definition known23_244:TM:=machine_of_codes 2 3 [9;9;6;3;5;10].
Lemma known23_244_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_244 /\ Bounds 59 67 known23_244.
Proof.
 assert(H:NonHalt known23_244 /\ QHBoundTr 67 known23_244).
 {
 change(NonHalt w23_175_tm /\ QHBoundTr 67 w23_175_tm).
 destruct(weighted23_nth 175 w23_175_tm w23_175_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2LB1RA_1RB1LB2RA *)
Definition known23_245:TM:=machine_of_codes 2 3 [9;9;6;7;5;10].
Lemma known23_245_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_245 /\ Bounds 59 67 known23_245.
Proof.
 assert(H:NonHalt known23_245 /\ QHBoundTr 67 known23_245).
 {
 apply known23_unmirror.
 assert(E:(mirror_tm known23_245)=LAPQ_2RB2RB1LA_1LB1RB2LA.tm_2RB2RB1LA_1LB1RB2LA)by(apply same_table_sound;reflexivity). rewrite E.
 exact LAPQ_2RB2RB1LA_1LB1RB2LA.qhtr_2RB2RB1LA_1LB1RB2LA.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2LB1RA_2RA1LB0RA *)
Definition known23_246:TM:=machine_of_codes 2 3 [9;9;6;10;5;2].
Lemma known23_246_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_246 /\ Bounds 59 67 known23_246.
Proof.
 assert(H:NonHalt known23_246 /\ QHBoundTr 67 known23_246).
 {
 change(NonHalt w23_216_tm /\ QHBoundTr 67 w23_216_tm).
 destruct(weighted23_nth 216 w23_216_tm w23_216_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2LB1RA_2RA1LB2RA *)
Definition known23_247:TM:=machine_of_codes 2 3 [9;9;6;10;5;10].
Lemma known23_247_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_247 /\ Bounds 59 67 known23_247.
Proof.
 assert(H:NonHalt known23_247 /\ QHBoundTr 67 known23_247).
 {
 change(NonHalt w23_217_tm /\ QHBoundTr 67 w23_217_tm).
 destruct(weighted23_nth 217 w23_217_tm w23_217_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2LB1RA_2RB1LB2RA *)
Definition known23_248:TM:=machine_of_codes 2 3 [9;9;6;11;5;10].
Lemma known23_248_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_248 /\ Bounds 59 67 known23_248.
Proof.
 assert(H:NonHalt known23_248 /\ QHBoundTr 67 known23_248).
 {
 change(NonHalt w23_231_tm /\ QHBoundTr 67 w23_231_tm).
 destruct(weighted23_nth 231 w23_231_tm w23_231_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2LB2RA_0RA---1LB *)
Definition known23_249:TM:=machine_of_codes 2 3 [9;9;10;2;12;5].
Lemma known23_249_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_249 /\ Bounds 59 67 known23_249.
Proof.
 assert(H:NonHalt known23_249 /\ QHBoundTr 67 known23_249).
 {
 change(NonHalt w23_170_tm /\ QHBoundTr 67 w23_170_tm).
 destruct(weighted23_nth 170 w23_170_tm w23_170_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2LB2RA_0RB1RA1LB *)
Definition known23_250:TM:=machine_of_codes 2 3 [9;9;10;3;6;5].
Lemma known23_250_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_250 /\ Bounds 59 67 known23_250.
Proof.
 assert(H:NonHalt known23_250 /\ QHBoundTr 67 known23_250).
 {
 change(NonHalt w23_171_tm /\ QHBoundTr 67 w23_171_tm).
 destruct(weighted23_nth 171 w23_171_tm w23_171_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2LB2RA_0RB2RA1LB *)
Definition known23_251:TM:=machine_of_codes 2 3 [9;9;10;3;10;5].
Lemma known23_251_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_251 /\ Bounds 59 67 known23_251.
Proof.
 assert(H:NonHalt known23_251 /\ QHBoundTr 67 known23_251).
 {
 change(NonHalt w23_172_tm /\ QHBoundTr 67 w23_172_tm).
 destruct(weighted23_nth 172 w23_172_tm w23_172_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2LB2RA_1RA0RA1LB *)
Definition known23_252:TM:=machine_of_codes 2 3 [9;9;10;6;2;5].
Lemma known23_252_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_252 /\ Bounds 59 67 known23_252.
Proof.
 assert(H:NonHalt known23_252 /\ QHBoundTr 67 known23_252).
 {
 change(NonHalt w23_200_tm /\ QHBoundTr 67 w23_200_tm).
 destruct(weighted23_nth 200 w23_200_tm w23_200_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2LB2RA_1RA1RA1LB *)
Definition known23_253:TM:=machine_of_codes 2 3 [9;9;10;6;6;5].
Lemma known23_253_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_253 /\ Bounds 59 67 known23_253.
Proof.
 assert(H:NonHalt known23_253 /\ QHBoundTr 67 known23_253).
 {
 change(NonHalt w23_201_tm /\ QHBoundTr 67 w23_201_tm).
 destruct(weighted23_nth 201 w23_201_tm w23_201_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2LB2RA_1RB1RA1LB *)
Definition known23_254:TM:=machine_of_codes 2 3 [9;9;10;7;6;5].
Lemma known23_254_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_254 /\ Bounds 59 67 known23_254.
Proof.
 assert(H:NonHalt known23_254 /\ QHBoundTr 67 known23_254).
 {
 change(NonHalt w23_207_tm /\ QHBoundTr 67 w23_207_tm).
 destruct(weighted23_nth 207 w23_207_tm w23_207_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2LB2RA_2RB1RA1LB *)
Definition known23_255:TM:=machine_of_codes 2 3 [9;9;10;11;6;5].
Lemma known23_255_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_255 /\ Bounds 59 67 known23_255.
Proof.
 assert(H:NonHalt known23_255 /\ QHBoundTr 67 known23_255).
 {
 change(NonHalt wd23_005_tm /\ QHBoundTr 67 wd23_005_tm).
 destruct(weighted23_deep_nth 5 wd23_005_tm 3 128 wd23_005_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2RA0LB_1RA1LB1RA *)
Definition known23_256:TM:=machine_of_codes 2 3 [9;10;1;6;5;6].
Lemma known23_256_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_256 /\ Bounds 59 67 known23_256.
Proof.
 assert(H:NonHalt known23_256 /\ QHBoundTr 67 known23_256).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_177_tm) /\ QHBoundTr 67 (mirror_tm w23_177_tm)).
 destruct(weighted23_nth 177 (mirror_tm w23_177_tm) w23_177_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2RA0LB_2RA1LB1RA *)
Definition known23_257:TM:=machine_of_codes 2 3 [9;10;1;10;5;6].
Lemma known23_257_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_257 /\ Bounds 59 67 known23_257.
Proof.
 assert(H:NonHalt known23_257 /\ QHBoundTr 67 known23_257).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_212_tm) /\ QHBoundTr 67 (mirror_tm w23_212_tm)).
 destruct(weighted23_nth 212 (mirror_tm w23_212_tm) w23_212_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2RA0LB_2RB1LB1RA *)
Definition known23_258:TM:=machine_of_codes 2 3 [9;10;1;11;5;6].
Lemma known23_258_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_258 /\ Bounds 59 67 known23_258.
Proof.
 assert(H:NonHalt known23_258 /\ QHBoundTr 67 known23_258).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_227_tm) /\ QHBoundTr 67 (mirror_tm w23_227_tm)).
 destruct(weighted23_nth 227 (mirror_tm w23_227_tm) w23_227_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2RA0RB_1RB0LA1RA *)
Definition known23_259:TM:=machine_of_codes 2 3 [9;10;3;7;0;6].
Lemma known23_259_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_259 /\ Bounds 59 67 known23_259.
Proof.
 assert(H:NonHalt known23_259 /\ QHBoundTr 67 known23_259).
 {
 pose proof(ir23_nth 7 _ _ eq_refl)as[HN[_ HB]];split;[exact HN|exact HB].
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2RA1LA_1RA---2LB *)
Definition known23_260:TM:=machine_of_codes 2 3 [9;10;4;6;12;9].
Lemma known23_260_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_260 /\ Bounds 59 67 known23_260.
Proof.
 assert(H:NonHalt known23_260 /\ QHBoundTr 67 known23_260).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_184_tm) /\ QHBoundTr 67 (mirror_tm w23_184_tm)).
 destruct(weighted23_nth 184 (mirror_tm w23_184_tm) w23_184_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2RA1LA_1RA2LB1RB *)
Definition known23_261:TM:=machine_of_codes 2 3 [9;10;4;6;9;7].
Lemma known23_261_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_261 /\ Bounds 59 67 known23_261.
Proof.
 assert(H:NonHalt known23_261 /\ QHBoundTr 67 known23_261).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_183_tm) /\ QHBoundTr 67 (mirror_tm w23_183_tm)).
 destruct(weighted23_nth 183 (mirror_tm w23_183_tm) w23_183_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2RA1LB_0RA---2LB *)
Definition known23_262:TM:=machine_of_codes 2 3 [9;10;5;2;12;9].
Lemma known23_262_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_262 /\ Bounds 59 67 known23_262.
Proof.
 assert(H:NonHalt known23_262 /\ QHBoundTr 67 known23_262).
 {
 change(NonHalt w23_165_tm /\ QHBoundTr 67 w23_165_tm).
 destruct(weighted23_nth 165 w23_165_tm w23_165_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2RA1LB_1RA0RA2LB *)
Definition known23_263:TM:=machine_of_codes 2 3 [9;10;5;6;2;9].
Lemma known23_263_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_263 /\ Bounds 59 67 known23_263.
Proof.
 assert(H:NonHalt known23_263 /\ QHBoundTr 67 known23_263).
 {
 change(NonHalt w23_186_tm /\ QHBoundTr 67 w23_186_tm).
 destruct(weighted23_nth 186 w23_186_tm w23_186_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2RA1LB_1RA1RA2LB *)
Definition known23_264:TM:=machine_of_codes 2 3 [9;10;5;6;6;9].
Lemma known23_264_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_264 /\ Bounds 59 67 known23_264.
Proof.
 assert(H:NonHalt known23_264 /\ QHBoundTr 67 known23_264).
 {
 change(NonHalt w23_187_tm /\ QHBoundTr 67 w23_187_tm).
 destruct(weighted23_nth 187 w23_187_tm w23_187_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2RA1LB_1RB1RA2LB *)
Definition known23_265:TM:=machine_of_codes 2 3 [9;10;5;7;6;9].
Lemma known23_265_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_265 /\ Bounds 59 67 known23_265.
Proof.
 assert(H:NonHalt known23_265 /\ QHBoundTr 67 known23_265).
 {
 change(NonHalt w23_210_tm /\ QHBoundTr 67 w23_210_tm).
 destruct(weighted23_nth 210 w23_210_tm w23_210_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2RA1RA_0RA1LB0LB *)
Definition known23_266:TM:=machine_of_codes 2 3 [9;10;6;2;5;1].
Lemma known23_266_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_266 /\ Bounds 59 67 known23_266.
Proof.
 assert(H:NonHalt known23_266 /\ QHBoundTr 67 known23_266).
 {
 change(NonHalt w23_167_tm /\ QHBoundTr 67 w23_167_tm).
 destruct(weighted23_nth 167 w23_167_tm w23_167_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2RA1RA_2RA0LB1LB *)
Definition known23_267:TM:=machine_of_codes 2 3 [9;10;6;10;1;5].
Lemma known23_267_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_267 /\ Bounds 59 67 known23_267.
Proof.
 assert(H:NonHalt known23_267 /\ QHBoundTr 67 known23_267).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_215_tm) /\ QHBoundTr 67 (mirror_tm w23_215_tm)).
 destruct(weighted23_nth 215 (mirror_tm w23_215_tm) w23_215_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2RA1RB_2RA0LB1LB *)
Definition known23_268:TM:=machine_of_codes 2 3 [9;10;7;10;1;5].
Lemma known23_268_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_268 /\ Bounds 59 67 known23_268.
Proof.
 assert(H:NonHalt known23_268 /\ QHBoundTr 67 known23_268).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_220_tm) /\ QHBoundTr 67 (mirror_tm w23_220_tm)).
 destruct(weighted23_nth 220 (mirror_tm w23_220_tm) w23_220_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2RA2LB_1RA1LB1RA *)
Definition known23_269:TM:=machine_of_codes 2 3 [9;10;9;6;5;6].
Lemma known23_269_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_269 /\ Bounds 59 67 known23_269.
Proof.
 assert(H:NonHalt known23_269 /\ QHBoundTr 67 known23_269).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_196_tm) /\ QHBoundTr 67 (mirror_tm w23_196_tm)).
 destruct(weighted23_nth 196 (mirror_tm w23_196_tm) w23_196_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2RA2LB_2RA1LB1RA *)
Definition known23_270:TM:=machine_of_codes 2 3 [9;10;9;10;5;6].
Lemma known23_270_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_270 /\ Bounds 59 67 known23_270.
Proof.
 assert(H:NonHalt known23_270 /\ QHBoundTr 67 known23_270).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_223_tm) /\ QHBoundTr 67 (mirror_tm w23_223_tm)).
 destruct(weighted23_nth 223 (mirror_tm w23_223_tm) w23_223_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2RA2LB_2RB0RA1LB *)
Definition known23_271:TM:=machine_of_codes 2 3 [9;10;9;11;2;5].
Lemma known23_271_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_271 /\ Bounds 59 67 known23_271.
Proof.
 assert(H:NonHalt known23_271 /\ QHBoundTr 67 known23_271).
 {
 pose proof(ir23_nth 8 _ _ eq_refl)as[HN[_ HB]];split;[exact HN|exact HB].
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2RA2LB_2RB1LB1RA *)
Definition known23_272:TM:=machine_of_codes 2 3 [9;10;9;11;5;6].
Lemma known23_272_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_272 /\ Bounds 59 67 known23_272.
Proof.
 assert(H:NonHalt known23_272 /\ QHBoundTr 67 known23_272).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_228_tm) /\ QHBoundTr 67 (mirror_tm w23_228_tm)).
 destruct(weighted23_nth 228 (mirror_tm w23_228_tm) w23_228_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2RB1LA_1RA1RB2LA *)
Definition known23_273:TM:=machine_of_codes 2 3 [9;11;4;6;7;8].
Lemma known23_273_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_273 /\ Bounds 59 67 known23_273.
Proof.
 assert(H:NonHalt known23_273 /\ QHBoundTr 67 known23_273).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_185_tm) /\ QHBoundTr 67 (mirror_tm w23_185_tm)).
 destruct(weighted23_nth 185 (mirror_tm w23_185_tm) w23_185_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2RB1RA_0RA1LB2LB *)
Definition known23_274:TM:=machine_of_codes 2 3 [9;11;6;2;5;9].
Lemma known23_274_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_274 /\ Bounds 59 67 known23_274.
Proof.
 assert(H:NonHalt known23_274 /\ QHBoundTr 67 known23_274).
 {
 change(NonHalt w23_168_tm /\ QHBoundTr 67 w23_168_tm).
 destruct(weighted23_nth 168 w23_168_tm w23_168_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2RB2LA_1RA1LA1RB *)
Definition known23_275:TM:=machine_of_codes 2 3 [9;11;8;6;4;7].
Lemma known23_275_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_275 /\ Bounds 59 67 known23_275.
Proof.
 assert(H:NonHalt known23_275 /\ QHBoundTr 67 known23_275).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_195_tm) /\ QHBoundTr 67 (mirror_tm w23_195_tm)).
 destruct(weighted23_nth 195 (mirror_tm w23_195_tm) w23_195_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2LB2RB2LB_2RA0RA1LB *)
Definition known23_276:TM:=machine_of_codes 2 3 [9;11;9;10;2;5].
Lemma known23_276_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_276 /\ Bounds 59 67 known23_276.
Proof.
 assert(H:NonHalt known23_276 /\ QHBoundTr 67 known23_276).
 {
 assert(E:known23_276=LAPT_2LB2RB2LB_2RA0RA1LB.tm_2LB2RB2LB_2RA0RA1LB)by(apply same_table_sound;reflexivity). rewrite E.
 apply known23_recurrence. exact LAPT_2LB2RB2LB_2RA0RA1LB.nqhtr_2LB2RB2LB_2RA0RA1LB.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB0LA1LA_2LA2RB1RA *)
Definition known23_277:TM:=machine_of_codes 2 3 [11;0;4;8;11;6].
Lemma known23_277_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_277 /\ Bounds 59 67 known23_277.
Proof.
 assert(H:NonHalt known23_277 /\ QHBoundTr 67 known23_277).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_284_tm) /\ QHBoundTr 67 (mirror_tm w23_284_tm)).
 destruct(weighted23_nth 284 (mirror_tm w23_284_tm) w23_284_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB0LA1LA_2LA2RB1RB *)
Definition known23_278:TM:=machine_of_codes 2 3 [11;0;4;8;11;7].
Lemma known23_278_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_278 /\ Bounds 59 67 known23_278.
Proof.
 assert(H:NonHalt known23_278 /\ QHBoundTr 67 known23_278).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_285_tm) /\ QHBoundTr 67 (mirror_tm w23_285_tm)).
 destruct(weighted23_nth 285 (mirror_tm w23_285_tm) w23_285_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB0LA2LA_1LA1RB2RB *)
Definition known23_279:TM:=machine_of_codes 2 3 [11;0;8;4;7;11].
Lemma known23_279_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_279 /\ Bounds 59 67 known23_279.
Proof.
 assert(H:NonHalt known23_279 /\ QHBoundTr 67 known23_279).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_266_tm) /\ QHBoundTr 67 (mirror_tm w23_266_tm)).
 destruct(weighted23_nth 266 (mirror_tm w23_266_tm) w23_266_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB0LB1LB_2LA0LB1RA *)
Definition known23_280:TM:=machine_of_codes 2 3 [11;1;5;8;1;6].
Lemma known23_280_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_280 /\ Bounds 59 67 known23_280.
Proof.
 assert(H:NonHalt known23_280 /\ QHBoundTr 67 known23_280).
 {
 split;[exact(proj1(remaining23_nth 21 known23_280 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 21 (eq_refl(Some known23_280))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB0RB1LA_1LB2RA2LA *)
Definition known23_281:TM:=machine_of_codes 2 3 [11;3;4;5;10;8].
Lemma known23_281_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_281 /\ Bounds 59 67 known23_281.
Proof.
 assert(H:NonHalt known23_281 /\ QHBoundTr 67 known23_281).
 {
 split;[exact(proj1(remaining23_nth 22 known23_281 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 22 (eq_refl(Some known23_281))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB0RB1LA_2LA2RA2LA *)
Definition known23_282:TM:=machine_of_codes 2 3 [11;3;4;8;10;8].
Lemma known23_282_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_282 /\ Bounds 59 67 known23_282.
Proof.
 assert(H:NonHalt known23_282 /\ QHBoundTr 67 known23_282).
 {
 assert(E:known23_282=LAPT_2RB0RB1LA_2LA2RA2LA.tm_2RB0RB1LA_2LA2RA2LA)by(apply same_table_sound;reflexivity). rewrite E.
 apply known23_recurrence. exact LAPT_2RB0RB1LA_2LA2RA2LA.nqhtr_2RB0RB1LA_2LA2RA2LA.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB0RB1LA_2LB2RA2LA *)
Definition known23_283:TM:=machine_of_codes 2 3 [11;3;4;9;10;8].
Lemma known23_283_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_283 /\ Bounds 59 67 known23_283.
Proof.
 assert(H:NonHalt known23_283 /\ QHBoundTr 67 known23_283).
 {
 split;[exact(proj1(remaining23_nth 23 known23_283 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 23 (eq_refl(Some known23_283))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA0LB_1LA2LB1RB *)
Definition known23_284:TM:=machine_of_codes 2 3 [11;4;1;4;9;7].
Lemma known23_284_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_284 /\ Bounds 59 67 known23_284.
Proof.
 assert(H:NonHalt known23_284 /\ QHBoundTr 67 known23_284).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_244_tm) /\ QHBoundTr 67 (mirror_tm w23_244_tm)).
 destruct(weighted23_nth 244 (mirror_tm w23_244_tm) w23_244_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA0RA_1LA2LB1RB *)
Definition known23_285:TM:=machine_of_codes 2 3 [11;4;2;4;9;7].
Lemma known23_285_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_285 /\ Bounds 59 67 known23_285.
Proof.
 assert(H:NonHalt known23_285 /\ QHBoundTr 67 known23_285).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_245_tm) /\ QHBoundTr 67 (mirror_tm w23_245_tm)).
 destruct(weighted23_nth 245 (mirror_tm w23_245_tm) w23_245_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA0RB_1LA2LA1RB *)
Definition known23_286:TM:=machine_of_codes 2 3 [11;4;3;4;8;7].
Lemma known23_286_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_286 /\ Bounds 59 67 known23_286.
Proof.
 assert(H:NonHalt known23_286 /\ QHBoundTr 67 known23_286).
 {
 change(NonHalt w23_247_tm /\ QHBoundTr 67 w23_247_tm).
 destruct(weighted23_nth 247 w23_247_tm w23_247_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA0RB_1LA2LB1RB *)
Definition known23_287:TM:=machine_of_codes 2 3 [11;4;3;4;9;7].
Lemma known23_287_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_287 /\ Bounds 59 67 known23_287.
Proof.
 assert(H:NonHalt known23_287 /\ QHBoundTr 67 known23_287).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_248_tm) /\ QHBoundTr 67 (mirror_tm w23_248_tm)).
 destruct(weighted23_nth 248 (mirror_tm w23_248_tm) w23_248_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA0RB_1LB2LA1RB *)
Definition known23_288:TM:=machine_of_codes 2 3 [11;4;3;5;8;7].
Lemma known23_288_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_288 /\ Bounds 59 67 known23_288.
Proof.
 assert(H:NonHalt known23_288 /\ QHBoundTr 67 known23_288).
 {
 change(NonHalt w23_276_tm /\ QHBoundTr 67 w23_276_tm).
 destruct(weighted23_nth 276 w23_276_tm w23_276_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA0RB_2LA2LA1RB *)
Definition known23_289:TM:=machine_of_codes 2 3 [11;4;3;8;8;7].
Lemma known23_289_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_289 /\ Bounds 59 67 known23_289.
Proof.
 assert(H:NonHalt known23_289 /\ QHBoundTr 67 known23_289).
 {
 change(NonHalt w23_280_tm /\ QHBoundTr 67 w23_280_tm).
 destruct(weighted23_nth 280 w23_280_tm w23_280_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA0RB_2LB2LA1RB *)
Definition known23_290:TM:=machine_of_codes 2 3 [11;4;3;9;8;7].
Lemma known23_290_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_290 /\ Bounds 59 67 known23_290.
Proof.
 assert(H:NonHalt known23_290 /\ QHBoundTr 67 known23_290).
 {
 change(NonHalt w23_295_tm /\ QHBoundTr 67 w23_295_tm).
 destruct(weighted23_nth 295 w23_295_tm w23_295_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA1LA_1LA2LB1RB *)
Definition known23_291:TM:=machine_of_codes 2 3 [11;4;4;4;9;7].
Lemma known23_291_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_291 /\ Bounds 59 67 known23_291.
Proof.
 assert(H:NonHalt known23_291 /\ QHBoundTr 67 known23_291).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_249_tm) /\ QHBoundTr 67 (mirror_tm w23_249_tm)).
 destruct(weighted23_nth 249 (mirror_tm w23_249_tm) w23_249_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA1LB_1LA2LB1RB *)
Definition known23_292:TM:=machine_of_codes 2 3 [11;4;5;4;9;7].
Lemma known23_292_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_292 /\ Bounds 59 67 known23_292.
Proof.
 assert(H:NonHalt known23_292 /\ QHBoundTr 67 known23_292).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_252_tm) /\ QHBoundTr 67 (mirror_tm w23_252_tm)).
 destruct(weighted23_nth 252 (mirror_tm w23_252_tm) w23_252_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA1LB_2LA2LB1RB *)
Definition known23_293:TM:=machine_of_codes 2 3 [11;4;5;8;9;7].
Lemma known23_293_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_293 /\ Bounds 59 67 known23_293.
Proof.
 assert(H:NonHalt known23_293 /\ QHBoundTr 67 known23_293).
 {
 split;[exact(proj1(remaining23_nth 24 known23_293 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 24 (eq_refl(Some known23_293))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA1RA_1LA2LB1RB *)
Definition known23_294:TM:=machine_of_codes 2 3 [11;4;6;4;9;7].
Lemma known23_294_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_294 /\ Bounds 59 67 known23_294.
Proof.
 assert(H:NonHalt known23_294 /\ QHBoundTr 67 known23_294).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_254_tm) /\ QHBoundTr 67 (mirror_tm w23_254_tm)).
 destruct(weighted23_nth 254 (mirror_tm w23_254_tm) w23_254_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA1RB_0LA2RB--- *)
Definition known23_295:TM:=machine_of_codes 2 3 [11;4;7;0;11;12].
Lemma known23_295_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_295 /\ Bounds 59 67 known23_295.
Proof.
 assert(H:NonHalt known23_295 /\ QHBoundTr 67 known23_295).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_235_tm) /\ QHBoundTr 67 (mirror_tm w23_235_tm)).
 destruct(weighted23_nth 235 (mirror_tm w23_235_tm) w23_235_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA1RB_0LB2RB1LA *)
Definition known23_296:TM:=machine_of_codes 2 3 [11;4;7;1;11;4].
Lemma known23_296_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_296 /\ Bounds 59 67 known23_296.
Proof.
 assert(H:NonHalt known23_296 /\ QHBoundTr 67 known23_296).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_239_tm) /\ QHBoundTr 67 (mirror_tm w23_239_tm)).
 destruct(weighted23_nth 239 (mirror_tm w23_239_tm) w23_239_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA1RB_0LB2RB2LA *)
Definition known23_297:TM:=machine_of_codes 2 3 [11;4;7;1;11;8].
Lemma known23_297_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_297 /\ Bounds 59 67 known23_297.
Proof.
 assert(H:NonHalt known23_297 /\ QHBoundTr 67 known23_297).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_243_tm) /\ QHBoundTr 67 (mirror_tm w23_243_tm)).
 destruct(weighted23_nth 243 (mirror_tm w23_243_tm) w23_243_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA1RB_1LA2LB1RB *)
Definition known23_298:TM:=machine_of_codes 2 3 [11;4;7;4;9;7].
Lemma known23_298_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_298 /\ Bounds 59 67 known23_298.
Proof.
 assert(H:NonHalt known23_298 /\ QHBoundTr 67 known23_298).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_261_tm) /\ QHBoundTr 67 (mirror_tm w23_261_tm)).
 destruct(weighted23_nth 261 (mirror_tm w23_261_tm) w23_261_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA1RB_1LB2RB2LA *)
Definition known23_299:TM:=machine_of_codes 2 3 [11;4;7;5;11;8].
Lemma known23_299_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_299 /\ Bounds 59 67 known23_299.
Proof.
 assert(H:NonHalt known23_299 /\ QHBoundTr 67 known23_299).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm wd23_006_tm) /\ QHBoundTr 67 (mirror_tm wd23_006_tm)).
 destruct(weighted23_deep_nth 6 (mirror_tm wd23_006_tm) 3 128 wd23_006_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA1RB_2LA2LB1RB *)
Definition known23_300:TM:=machine_of_codes 2 3 [11;4;7;8;9;7].
Lemma known23_300_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_300 /\ Bounds 59 67 known23_300.
Proof.
 assert(H:NonHalt known23_300 /\ QHBoundTr 67 known23_300).
 {
 split;[exact(proj1(remaining23_nth 25 known23_300 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 25 (eq_refl(Some known23_300))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA1RB_2LA2RB0LA *)
Definition known23_301:TM:=machine_of_codes 2 3 [11;4;7;8;11;0].
Lemma known23_301_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_301 /\ Bounds 59 67 known23_301.
Proof.
 assert(H:NonHalt known23_301 /\ QHBoundTr 67 known23_301).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_288_tm) /\ QHBoundTr 67 (mirror_tm w23_288_tm)).
 destruct(weighted23_nth 288 (mirror_tm w23_288_tm) w23_288_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA1RB_2LA2RB2LA *)
Definition known23_302:TM:=machine_of_codes 2 3 [11;4;7;8;11;8].
Lemma known23_302_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_302 /\ Bounds 59 67 known23_302.
Proof.
 assert(H:NonHalt known23_302 /\ QHBoundTr 67 known23_302).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_289_tm) /\ QHBoundTr 67 (mirror_tm w23_289_tm)).
 destruct(weighted23_nth 289 (mirror_tm w23_289_tm) w23_289_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA1RB_2LB2RB2LA *)
Definition known23_303:TM:=machine_of_codes 2 3 [11;4;7;9;11;8].
Lemma known23_303_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_303 /\ Bounds 59 67 known23_303.
Proof.
 assert(H:NonHalt known23_303 /\ QHBoundTr 67 known23_303).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_299_tm) /\ QHBoundTr 67 (mirror_tm w23_299_tm)).
 destruct(weighted23_nth 299 (mirror_tm w23_299_tm) w23_299_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA2LA_0LA0RB1RB *)
Definition known23_304:TM:=machine_of_codes 2 3 [11;4;8;0;3;7].
Lemma known23_304_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_304 /\ Bounds 59 67 known23_304.
Proof.
 assert(H:NonHalt known23_304 /\ QHBoundTr 67 known23_304).
 {
 change(NonHalt w23_237_tm /\ QHBoundTr 67 w23_237_tm).
 destruct(weighted23_nth 237 w23_237_tm w23_237_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA2LA_1LA1RB0RB *)
Definition known23_305:TM:=machine_of_codes 2 3 [11;4;8;4;7;3].
Lemma known23_305_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_305 /\ Bounds 59 67 known23_305.
Proof.
 assert(H:NonHalt known23_305 /\ QHBoundTr 67 known23_305).
 {
 change(NonHalt w23_262_tm /\ QHBoundTr 67 w23_262_tm).
 destruct(weighted23_nth 262 w23_262_tm w23_262_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA2LA_1LA2LB1RB *)
Definition known23_306:TM:=machine_of_codes 2 3 [11;4;8;4;9;7].
Lemma known23_306_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_306 /\ Bounds 59 67 known23_306.
Proof.
 assert(H:NonHalt known23_306 /\ QHBoundTr 67 known23_306).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_265_tm) /\ QHBoundTr 67 (mirror_tm w23_265_tm)).
 destruct(weighted23_nth 265 (mirror_tm w23_265_tm) w23_265_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA2LB_1LA2LB1RB *)
Definition known23_307:TM:=machine_of_codes 2 3 [11;4;9;4;9;7].
Lemma known23_307_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_307 /\ Bounds 59 67 known23_307.
Proof.
 assert(H:NonHalt known23_307 /\ QHBoundTr 67 known23_307).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_268_tm) /\ QHBoundTr 67 (mirror_tm w23_268_tm)).
 destruct(weighted23_nth 268 (mirror_tm w23_268_tm) w23_268_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA2RB_1LA2LA1RB *)
Definition known23_308:TM:=machine_of_codes 2 3 [11;4;11;4;8;7].
Lemma known23_308_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_308 /\ Bounds 59 67 known23_308.
Proof.
 assert(H:NonHalt known23_308 /\ QHBoundTr 67 known23_308).
 {
 change(NonHalt w23_273_tm /\ QHBoundTr 67 w23_273_tm).
 destruct(weighted23_nth 273 w23_273_tm w23_273_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA2RB_1LA2LB1RB *)
Definition known23_309:TM:=machine_of_codes 2 3 [11;4;11;4;9;7].
Lemma known23_309_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_309 /\ Bounds 59 67 known23_309.
Proof.
 assert(H:NonHalt known23_309 /\ QHBoundTr 67 known23_309).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_274_tm) /\ QHBoundTr 67 (mirror_tm w23_274_tm)).
 destruct(weighted23_nth 274 (mirror_tm w23_274_tm) w23_274_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA2RB_1LB2LA1RB *)
Definition known23_310:TM:=machine_of_codes 2 3 [11;4;11;5;8;7].
Lemma known23_310_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_310 /\ Bounds 59 67 known23_310.
Proof.
 assert(H:NonHalt known23_310 /\ QHBoundTr 67 known23_310).
 {
 change(NonHalt w23_277_tm /\ QHBoundTr 67 w23_277_tm).
 destruct(weighted23_nth 277 w23_277_tm w23_277_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA2RB_2LA2LA1RB *)
Definition known23_311:TM:=machine_of_codes 2 3 [11;4;11;8;8;7].
Lemma known23_311_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_311 /\ Bounds 59 67 known23_311.
Proof.
 assert(H:NonHalt known23_311 /\ QHBoundTr 67 known23_311).
 {
 change(NonHalt w23_292_tm /\ QHBoundTr 67 w23_292_tm).
 destruct(weighted23_nth 292 w23_292_tm w23_292_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LA2RB_2LB2LA1RB *)
Definition known23_312:TM:=machine_of_codes 2 3 [11;4;11;9;8;7].
Lemma known23_312_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_312 /\ Bounds 59 67 known23_312.
Proof.
 assert(H:NonHalt known23_312 /\ QHBoundTr 67 known23_312).
 {
 change(NonHalt w23_296_tm /\ QHBoundTr 67 w23_296_tm).
 destruct(weighted23_nth 296 w23_296_tm w23_296_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LB1RA_1LA2RA2LB *)
Definition known23_313:TM:=machine_of_codes 2 3 [11;5;6;4;10;9].
Lemma known23_313_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_313 /\ Bounds 59 67 known23_313.
Proof.
 assert(H:NonHalt known23_313 /\ QHBoundTr 67 known23_313).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_255_tm) /\ QHBoundTr 67 (mirror_tm w23_255_tm)).
 destruct(weighted23_nth 255 (mirror_tm w23_255_tm) w23_255_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LB1RA_2LB0RA1LA *)
Definition known23_314:TM:=machine_of_codes 2 3 [11;5;6;9;2;4].
Lemma known23_314_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_314 /\ Bounds 59 67 known23_314.
Proof.
 assert(H:NonHalt known23_314 /\ QHBoundTr 67 known23_314).
 {
 assert(E:known23_314=LAPT_2RB1LB1RA_2LB0RA1LA.tm_2RB1LB1RA_2LB0RA1LA)by(apply same_table_sound;reflexivity). rewrite E.
 apply known23_recurrence. exact LAPT_2RB1LB1RA_2LB0RA1LA.nqhtr_2RB1LB1RA_2LB0RA1LA.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1LB2RA_1LA2LB1RA *)
Definition known23_315:TM:=machine_of_codes 2 3 [11;5;10;4;9;6].
Lemma known23_315_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_315 /\ Bounds 59 67 known23_315.
Proof.
 assert(H:NonHalt known23_315 /\ QHBoundTr 67 known23_315).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_270_tm) /\ QHBoundTr 67 (mirror_tm w23_270_tm)).
 destruct(weighted23_nth 270 (mirror_tm w23_270_tm) w23_270_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1RA1LB_1LA2LB2RA *)
Definition known23_316:TM:=machine_of_codes 2 3 [11;6;5;4;9;10].
Lemma known23_316_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_316 /\ Bounds 59 67 known23_316.
Proof.
 assert(H:NonHalt known23_316 /\ QHBoundTr 67 known23_316).
 {
 change(NonHalt w23_253_tm /\ QHBoundTr 67 w23_253_tm).
 destruct(weighted23_nth 253 w23_253_tm w23_253_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1RA1LB_2LA2LB2RA *)
Definition known23_317:TM:=machine_of_codes 2 3 [11;6;5;8;9;10].
Lemma known23_317_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_317 /\ Bounds 59 67 known23_317.
Proof.
 assert(H:NonHalt known23_317 /\ QHBoundTr 67 known23_317).
 {
 change(NonHalt w23_287_tm /\ QHBoundTr 67 w23_287_tm).
 destruct(weighted23_nth 287 w23_287_tm w23_287_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB1RA2LB_1LA2RA1LB *)
Definition known23_318:TM:=machine_of_codes 2 3 [11;6;9;4;10;5].
Lemma known23_318_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_318 /\ Bounds 59 67 known23_318.
Proof.
 assert(H:NonHalt known23_318 /\ QHBoundTr 67 known23_318).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_269_tm) /\ QHBoundTr 67 (mirror_tm w23_269_tm)).
 destruct(weighted23_nth 269 (mirror_tm w23_269_tm) w23_269_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2LA0LB_1LB0RA1LA *)
Definition known23_319:TM:=machine_of_codes 2 3 [11;8;1;5;2;4].
Lemma known23_319_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_319 /\ Bounds 59 67 known23_319.
Proof.
 assert(H:NonHalt known23_319 /\ QHBoundTr 67 known23_319).
 {
 pose proof(ir23_nth 10 _ _ eq_refl)as[HN[_ HB]];split;[exact HN|exact HB].
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2LA0RB_1LA1RB1LA *)
Definition known23_320:TM:=machine_of_codes 2 3 [11;8;3;4;7;4].
Lemma known23_320_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_320 /\ Bounds 59 67 known23_320.
Proof.
 assert(H:NonHalt known23_320 /\ QHBoundTr 67 known23_320).
 {
 change(NonHalt w23_246_tm /\ QHBoundTr 67 w23_246_tm).
 destruct(weighted23_nth 246 w23_246_tm w23_246_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2LA0RB_2LA1RB1LA *)
Definition known23_321:TM:=machine_of_codes 2 3 [11;8;3;8;7;4].
Lemma known23_321_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_321 /\ Bounds 59 67 known23_321.
Proof.
 assert(H:NonHalt known23_321 /\ QHBoundTr 67 known23_321).
 {
 change(NonHalt w23_279_tm /\ QHBoundTr 67 w23_279_tm).
 destruct(weighted23_nth 279 w23_279_tm w23_279_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2LA0RB_2LB1RB1LA *)
Definition known23_322:TM:=machine_of_codes 2 3 [11;8;3;9;7;4].
Lemma known23_322_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_322 /\ Bounds 59 67 known23_322.
Proof.
 assert(H:NonHalt known23_322 /\ QHBoundTr 67 known23_322).
 {
 change(NonHalt w23_293_tm /\ QHBoundTr 67 w23_293_tm).
 destruct(weighted23_nth 293 w23_293_tm w23_293_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2LA1LA_0LA1RB0RB *)
Definition known23_323:TM:=machine_of_codes 2 3 [11;8;4;0;7;3].
Lemma known23_323_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_323 /\ Bounds 59 67 known23_323.
Proof.
 assert(H:NonHalt known23_323 /\ QHBoundTr 67 known23_323).
 {
 change(NonHalt w23_232_tm /\ QHBoundTr 67 w23_232_tm).
 destruct(weighted23_nth 232 w23_232_tm w23_232_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2LA1LA_2LA0RB1RB *)
Definition known23_324:TM:=machine_of_codes 2 3 [11;8;4;8;3;7].
Lemma known23_324_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_324 /\ Bounds 59 67 known23_324.
Proof.
 assert(H:NonHalt known23_324 /\ QHBoundTr 67 known23_324).
 {
 change(NonHalt w23_281_tm /\ QHBoundTr 67 w23_281_tm).
 destruct(weighted23_nth 281 w23_281_tm w23_281_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2LA1LB_2LA0RB1RB *)
Definition known23_325:TM:=machine_of_codes 2 3 [11;8;5;8;3;7].
Lemma known23_325_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_325 /\ Bounds 59 67 known23_325.
Proof.
 assert(H:NonHalt known23_325 /\ QHBoundTr 67 known23_325).
 {
 change(NonHalt w23_286_tm /\ QHBoundTr 67 w23_286_tm).
 destruct(weighted23_nth 286 w23_286_tm w23_286_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2LA1RA_1LA---2RB *)
Definition known23_326:TM:=machine_of_codes 2 3 [11;8;6;4;12;11].
Lemma known23_326_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_326 /\ Bounds 59 67 known23_326.
Proof.
 assert(H:NonHalt known23_326 /\ QHBoundTr 67 known23_326).
 {
 change(NonHalt w23_257_tm /\ QHBoundTr 67 w23_257_tm).
 destruct(weighted23_nth 257 w23_257_tm w23_257_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2LA1RA_1LA2RB1LB *)
Definition known23_327:TM:=machine_of_codes 2 3 [11;8;6;4;11;5].
Lemma known23_327_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_327 /\ Bounds 59 67 known23_327.
Proof.
 assert(H:NonHalt known23_327 /\ QHBoundTr 67 known23_327).
 {
 change(NonHalt w23_256_tm /\ QHBoundTr 67 w23_256_tm).
 destruct(weighted23_nth 256 w23_256_tm w23_256_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2LA1RB_0LA---2RB *)
Definition known23_328:TM:=machine_of_codes 2 3 [11;8;7;0;12;11].
Lemma known23_328_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_328 /\ Bounds 59 67 known23_328.
Proof.
 assert(H:NonHalt known23_328 /\ QHBoundTr 67 known23_328).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_236_tm) /\ QHBoundTr 67 (mirror_tm w23_236_tm)).
 destruct(weighted23_nth 236 (mirror_tm w23_236_tm) w23_236_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2LA1RB_1LA0LA2RB *)
Definition known23_329:TM:=machine_of_codes 2 3 [11;8;7;4;0;11].
Lemma known23_329_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_329 /\ Bounds 59 67 known23_329.
Proof.
 assert(H:NonHalt known23_329 /\ QHBoundTr 67 known23_329).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_259_tm) /\ QHBoundTr 67 (mirror_tm w23_259_tm)).
 destruct(weighted23_nth 259 (mirror_tm w23_259_tm) w23_259_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2LA1RB_1LA1LA2RB *)
Definition known23_330:TM:=machine_of_codes 2 3 [11;8;7;4;4;11].
Lemma known23_330_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_330 /\ Bounds 59 67 known23_330.
Proof.
 assert(H:NonHalt known23_330 /\ QHBoundTr 67 known23_330).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_260_tm) /\ QHBoundTr 67 (mirror_tm w23_260_tm)).
 destruct(weighted23_nth 260 (mirror_tm w23_260_tm) w23_260_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2LA1RB_1LB1LA2RB *)
Definition known23_331:TM:=machine_of_codes 2 3 [11;8;7;5;4;11].
Lemma known23_331_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_331 /\ Bounds 59 67 known23_331.
Proof.
 assert(H:NonHalt known23_331 /\ QHBoundTr 67 known23_331).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_278_tm) /\ QHBoundTr 67 (mirror_tm w23_278_tm)).
 destruct(weighted23_nth 278 (mirror_tm w23_278_tm) w23_278_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2LA2RB_1LA1RB1LA *)
Definition known23_332:TM:=machine_of_codes 2 3 [11;8;11;4;7;4].
Lemma known23_332_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_332 /\ Bounds 59 67 known23_332.
Proof.
 assert(H:NonHalt known23_332 /\ QHBoundTr 67 known23_332).
 {
 change(NonHalt w23_272_tm /\ QHBoundTr 67 w23_272_tm).
 destruct(weighted23_nth 272 w23_272_tm w23_272_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2LA2RB_2LA1RB1LA *)
Definition known23_333:TM:=machine_of_codes 2 3 [11;8;11;8;7;4].
Lemma known23_333_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_333 /\ Bounds 59 67 known23_333.
Proof.
 assert(H:NonHalt known23_333 /\ QHBoundTr 67 known23_333).
 {
 change(NonHalt w23_291_tm /\ QHBoundTr 67 w23_291_tm).
 destruct(weighted23_nth 291 w23_291_tm w23_291_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2LA2RB_2LB0LA1RB *)
Definition known23_334:TM:=machine_of_codes 2 3 [11;8;11;9;0;7].
Lemma known23_334_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_334 /\ Bounds 59 67 known23_334.
Proof.
 assert(H:NonHalt known23_334 /\ QHBoundTr 67 known23_334).
 {
 pose proof(ir23_nth 11 _ _ eq_refl)as[HN[_ HB]];split;[exact HN|exact HB].
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2LA2RB_2LB1RB1LA *)
Definition known23_335:TM:=machine_of_codes 2 3 [11;8;11;9;7;4].
Lemma known23_335_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_335 /\ Bounds 59 67 known23_335.
Proof.
 assert(H:NonHalt known23_335 /\ QHBoundTr 67 known23_335).
 {
 change(NonHalt w23_294_tm /\ QHBoundTr 67 w23_294_tm).
 destruct(weighted23_nth 294 w23_294_tm w23_294_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2LB1LA_0LA1RB2RB *)
Definition known23_336:TM:=machine_of_codes 2 3 [11;9;4;0;7;11].
Lemma known23_336_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_336 /\ Bounds 59 67 known23_336.
Proof.
 assert(H:NonHalt known23_336 /\ QHBoundTr 67 known23_336).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_233_tm) /\ QHBoundTr 67 (mirror_tm w23_233_tm)).
 destruct(weighted23_nth 233 (mirror_tm w23_233_tm) w23_233_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2LB1RA_1LA1LB2RA *)
Definition known23_337:TM:=machine_of_codes 2 3 [11;9;6;4;5;10].
Lemma known23_337_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_337 /\ Bounds 59 67 known23_337.
Proof.
 assert(H:NonHalt known23_337 /\ QHBoundTr 67 known23_337).
 {
 change(NonHalt w23_258_tm /\ QHBoundTr 67 w23_258_tm).
 destruct(weighted23_nth 258 w23_258_tm w23_258_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2LB2RA_1LA1RA1LB *)
Definition known23_338:TM:=machine_of_codes 2 3 [11;9;10;4;6;5].
Lemma known23_338_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_338 /\ Bounds 59 67 known23_338.
Proof.
 assert(H:NonHalt known23_338 /\ QHBoundTr 67 known23_338).
 {
 change(NonHalt w23_271_tm /\ QHBoundTr 67 w23_271_tm).
 destruct(weighted23_nth 271 w23_271_tm w23_271_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2LB2RB_2LA0LA1RB *)
Definition known23_339:TM:=machine_of_codes 2 3 [11;9;11;8;0;7].
Lemma known23_339_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_339 /\ Bounds 59 67 known23_339.
Proof.
 assert(H:NonHalt known23_339 /\ QHBoundTr 67 known23_339).
 {
 apply known23_unmirror.
 assert(E:(mirror_tm known23_339)=LAPT_2LB2RB2LB_2RA0RA1LB.tm_2LB2RB2LB_2RA0RA1LB)by(apply same_table_sound;reflexivity). rewrite E.
 apply known23_recurrence. exact LAPT_2LB2RB2LB_2RA0RA1LB.nqhtr_2LB2RB2LB_2RA0RA1LB.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2RA1LA_1LA2LB1RB *)
Definition known23_340:TM:=machine_of_codes 2 3 [11;10;4;4;9;7].
Lemma known23_340_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_340 /\ Bounds 59 67 known23_340.
Proof.
 assert(H:NonHalt known23_340 /\ QHBoundTr 67 known23_340).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_250_tm) /\ QHBoundTr 67 (mirror_tm w23_250_tm)).
 destruct(weighted23_nth 250 (mirror_tm w23_250_tm) w23_250_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2RA1LA_2LA1RB1LA *)
Definition known23_341:TM:=machine_of_codes 2 3 [11;10;4;8;7;4].
Lemma known23_341_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_341 /\ Bounds 59 67 known23_341.
Proof.
 assert(H:NonHalt known23_341 /\ QHBoundTr 67 known23_341).
 {
 split;[exact(proj1(remaining23_nth 26 known23_341 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 26 (eq_refl(Some known23_341))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2RA1LA_2LA1RB1RA *)
Definition known23_342:TM:=machine_of_codes 2 3 [11;10;4;8;7;6].
Lemma known23_342_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_342 /\ Bounds 59 67 known23_342.
Proof.
 assert(H:NonHalt known23_342 /\ QHBoundTr 67 known23_342).
 {
 split;[exact(proj1(remaining23_nth 27 known23_342 eq_refl))|].
 rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 27 (eq_refl(Some known23_342))).
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2RA1LA_2LB1RB2LA *)
Definition known23_343:TM:=machine_of_codes 2 3 [11;10;4;9;7;8].
Lemma known23_343_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_343 /\ Bounds 59 67 known23_343.
Proof.
 assert(H:NonHalt known23_343 /\ QHBoundTr 67 known23_343).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_297_tm) /\ QHBoundTr 67 (mirror_tm w23_297_tm)).
 destruct(weighted23_nth 297 (mirror_tm w23_297_tm) w23_297_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2RA1LB_1LA1RA2LB *)
Definition known23_344:TM:=machine_of_codes 2 3 [11;10;5;4;6;9].
Lemma known23_344_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_344 /\ Bounds 59 67 known23_344.
Proof.
 assert(H:NonHalt known23_344 /\ QHBoundTr 67 known23_344).
 {
 change(NonHalt w23_251_tm /\ QHBoundTr 67 w23_251_tm).
 destruct(weighted23_nth 251 w23_251_tm w23_251_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2RA2LB_1LA1LB1RA *)
Definition known23_345:TM:=machine_of_codes 2 3 [11;10;9;4;5;6].
Lemma known23_345_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_345 /\ Bounds 59 67 known23_345.
Proof.
 assert(H:NonHalt known23_345 /\ QHBoundTr 67 known23_345).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_267_tm) /\ QHBoundTr 67 (mirror_tm w23_267_tm)).
 destruct(weighted23_nth 267 (mirror_tm w23_267_tm) w23_267_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2RA2LB_2LA1LB1RA *)
Definition known23_346:TM:=machine_of_codes 2 3 [11;10;9;8;5;6].
Lemma known23_346_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_346 /\ Bounds 59 67 known23_346.
Proof.
 assert(H:NonHalt known23_346 /\ QHBoundTr 67 known23_346).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_290_tm) /\ QHBoundTr 67 (mirror_tm w23_290_tm)).
 destruct(weighted23_nth 290 (mirror_tm w23_290_tm) w23_290_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2RB1LA_0LA1RB--- *)
Definition known23_347:TM:=machine_of_codes 2 3 [11;11;4;0;7;12].
Lemma known23_347_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_347 /\ Bounds 59 67 known23_347.
Proof.
 assert(H:NonHalt known23_347 /\ QHBoundTr 67 known23_347).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_234_tm) /\ QHBoundTr 67 (mirror_tm w23_234_tm)).
 destruct(weighted23_nth 234 (mirror_tm w23_234_tm) w23_234_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2RB1LA_0LB1RB2LA *)
Definition known23_348:TM:=machine_of_codes 2 3 [11;11;4;1;7;8].
Lemma known23_348_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_348 /\ Bounds 59 67 known23_348.
Proof.
 assert(H:NonHalt known23_348 /\ QHBoundTr 67 known23_348).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_242_tm) /\ QHBoundTr 67 (mirror_tm w23_242_tm)).
 destruct(weighted23_nth 242 (mirror_tm w23_242_tm) w23_242_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2RB1LA_1LB1RB2LA *)
Definition known23_349:TM:=machine_of_codes 2 3 [11;11;4;5;7;8].
Lemma known23_349_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_349 /\ Bounds 59 67 known23_349.
Proof.
 assert(H:NonHalt known23_349 /\ QHBoundTr 67 known23_349).
 {
 assert(E:known23_349=LAPQ_2RB2RB1LA_1LB1RB2LA.tm_2RB2RB1LA_1LB1RB2LA)by(apply same_table_sound;reflexivity). rewrite E.
 exact LAPQ_2RB2RB1LA_1LB1RB2LA.qhtr_2RB2RB1LA_1LB1RB2LA.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2RB1LA_2LA1RB0LA *)
Definition known23_350:TM:=machine_of_codes 2 3 [11;11;4;8;7;0].
Lemma known23_350_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_350 /\ Bounds 59 67 known23_350.
Proof.
 assert(H:NonHalt known23_350 /\ QHBoundTr 67 known23_350).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_282_tm) /\ QHBoundTr 67 (mirror_tm w23_282_tm)).
 destruct(weighted23_nth 282 (mirror_tm w23_282_tm) w23_282_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2RB1LA_2LA1RB2LA *)
Definition known23_351:TM:=machine_of_codes 2 3 [11;11;4;8;7;8].
Lemma known23_351_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_351 /\ Bounds 59 67 known23_351.
Proof.
 assert(H:NonHalt known23_351 /\ QHBoundTr 67 known23_351).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_283_tm) /\ QHBoundTr 67 (mirror_tm w23_283_tm)).
 destruct(weighted23_nth 283 (mirror_tm w23_283_tm) w23_283_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2RB1LA_2LB1RB2LA *)
Definition known23_352:TM:=machine_of_codes 2 3 [11;11;4;9;7;8].
Lemma known23_352_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_352 /\ Bounds 59 67 known23_352.
Proof.
 assert(H:NonHalt known23_352 /\ QHBoundTr 67 known23_352).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_298_tm) /\ QHBoundTr 67 (mirror_tm w23_298_tm)).
 destruct(weighted23_nth 298 (mirror_tm w23_298_tm) w23_298_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2RB2LA_0LA---1RB *)
Definition known23_353:TM:=machine_of_codes 2 3 [11;11;8;0;12;7].
Lemma known23_353_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_353 /\ Bounds 59 67 known23_353.
Proof.
 assert(H:NonHalt known23_353 /\ QHBoundTr 67 known23_353).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_238_tm) /\ QHBoundTr 67 (mirror_tm w23_238_tm)).
 destruct(weighted23_nth 238 (mirror_tm w23_238_tm) w23_238_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2RB2LA_0LB1LA1RB *)
Definition known23_354:TM:=machine_of_codes 2 3 [11;11;8;1;4;7].
Lemma known23_354_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_354 /\ Bounds 59 67 known23_354.
Proof.
 assert(H:NonHalt known23_354 /\ QHBoundTr 67 known23_354).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_240_tm) /\ QHBoundTr 67 (mirror_tm w23_240_tm)).
 destruct(weighted23_nth 240 (mirror_tm w23_240_tm) w23_240_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2RB2LA_0LB2LA1RB *)
Definition known23_355:TM:=machine_of_codes 2 3 [11;11;8;1;8;7].
Lemma known23_355_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_355 /\ Bounds 59 67 known23_355.
Proof.
 assert(H:NonHalt known23_355 /\ QHBoundTr 67 known23_355).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_241_tm) /\ QHBoundTr 67 (mirror_tm w23_241_tm)).
 destruct(weighted23_nth 241 (mirror_tm w23_241_tm) w23_241_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2RB2LA_1LA0LA1RB *)
Definition known23_356:TM:=machine_of_codes 2 3 [11;11;8;4;0;7].
Lemma known23_356_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_356 /\ Bounds 59 67 known23_356.
Proof.
 assert(H:NonHalt known23_356 /\ QHBoundTr 67 known23_356).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_263_tm) /\ QHBoundTr 67 (mirror_tm w23_263_tm)).
 destruct(weighted23_nth 263 (mirror_tm w23_263_tm) w23_263_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2RB2LA_1LA1LA1RB *)
Definition known23_357:TM:=machine_of_codes 2 3 [11;11;8;4;4;7].
Lemma known23_357_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_357 /\ Bounds 59 67 known23_357.
Proof.
 assert(H:NonHalt known23_357 /\ QHBoundTr 67 known23_357).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_264_tm) /\ QHBoundTr 67 (mirror_tm w23_264_tm)).
 destruct(weighted23_nth 264 (mirror_tm w23_264_tm) w23_264_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2RB2LA_1LB1LA1RB *)
Definition known23_358:TM:=machine_of_codes 2 3 [11;11;8;5;4;7].
Lemma known23_358_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_358 /\ Bounds 59 67 known23_358.
Proof.
 assert(H:NonHalt known23_358 /\ QHBoundTr 67 known23_358).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm w23_275_tm) /\ QHBoundTr 67 (mirror_tm w23_275_tm)).
 destruct(weighted23_nth 275 (mirror_tm w23_275_tm) w23_275_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
(* 2RB2RB2LA_2LB1LA1RB *)
Definition known23_359:TM:=machine_of_codes 2 3 [11;11;8;9;4;7].
Lemma known23_359_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt known23_359 /\ Bounds 59 67 known23_359.
Proof.
 assert(H:NonHalt known23_359 /\ QHBoundTr 67 known23_359).
 {
 apply known23_unmirror.
 change(NonHalt (mirror_tm wd23_007_tm) /\ QHBoundTr 67 (mirror_tm wd23_007_tm)).
 destruct(weighted23_deep_nth 7 (mirror_tm wd23_007_tm) 3 128 wd23_007_cert eq_refl)as[HN[_ HB]];split;assumption.
 } destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].
Qed.
Definition known23:list TM:= [known23_000;known23_001;known23_002;known23_003;known23_004;known23_005;known23_006;known23_007;known23_008;known23_009;known23_010;known23_011;known23_012;known23_013;known23_014;known23_015;known23_016;known23_017;known23_018;known23_019;known23_020;known23_021;known23_022;known23_023;known23_024;known23_025;known23_026;known23_027;known23_028;known23_029;known23_030;known23_031;known23_032;known23_033;known23_034;known23_035;known23_036;known23_037;known23_038;known23_039;known23_040;known23_041;known23_042;known23_043;known23_044;known23_045;known23_046;known23_047;known23_048;known23_049;known23_050;known23_051;known23_052;known23_053;known23_054;known23_055;known23_056;known23_057;known23_058;known23_059;known23_060;known23_061;known23_062;known23_063;known23_064;known23_065;known23_066;known23_067;known23_068;known23_069;known23_070;known23_071;known23_072;known23_073;known23_074;known23_075;known23_076;known23_077;known23_078;known23_079;known23_080;known23_081;known23_082;known23_083;known23_084;known23_085;known23_086;known23_087;known23_088;known23_089;known23_090;known23_091;known23_092;known23_093;known23_094;known23_095;known23_096;known23_097;known23_098;known23_099;known23_100;known23_101;known23_102;known23_103;known23_104;known23_105;known23_106;known23_107;known23_108;known23_109;known23_110;known23_111;known23_112;known23_113;known23_114;known23_115;known23_116;known23_117;known23_118;known23_119;known23_120;known23_121;known23_122;known23_123;known23_124;known23_125;known23_126;known23_127;known23_128;known23_129;known23_130;known23_131;known23_132;known23_133;known23_134;known23_135;known23_136;known23_137;known23_138;known23_139;known23_140;known23_141;known23_142;known23_143;known23_144;known23_145;known23_146;known23_147;known23_148;known23_149;known23_150;known23_151;known23_152;known23_153;known23_154;known23_155;known23_156;known23_157;known23_158;known23_159;known23_160;known23_161;known23_162;known23_163;known23_164;known23_165;known23_166;known23_167;known23_168;known23_169;known23_170;known23_171;known23_172;known23_173;known23_174;known23_175;known23_176;known23_177;known23_178;known23_179;known23_180;known23_181;known23_182;known23_183;known23_184;known23_185;known23_186;known23_187;known23_188;known23_189;known23_190;known23_191;known23_192;known23_193;known23_194;known23_195;known23_196;known23_197;known23_198;known23_199;known23_200;known23_201;known23_202;known23_203;known23_204;known23_205;known23_206;known23_207;known23_208;known23_209;known23_210;known23_211;known23_212;known23_213;known23_214;known23_215;known23_216;known23_217;known23_218;known23_219;known23_220;known23_221;known23_222;known23_223;known23_224;known23_225;known23_226;known23_227;known23_228;known23_229;known23_230;known23_231;known23_232;known23_233;known23_234;known23_235;known23_236;known23_237;known23_238;known23_239;known23_240;known23_241;known23_242;known23_243;known23_244;known23_245;known23_246;known23_247;known23_248;known23_249;known23_250;known23_251;known23_252;known23_253;known23_254;known23_255;known23_256;known23_257;known23_258;known23_259;known23_260;known23_261;known23_262;known23_263;known23_264;known23_265;known23_266;known23_267;known23_268;known23_269;known23_270;known23_271;known23_272;known23_273;known23_274;known23_275;known23_276;known23_277;known23_278;known23_279;known23_280;known23_281;known23_282;known23_283;known23_284;known23_285;known23_286;known23_287;known23_288;known23_289;known23_290;known23_291;known23_292;known23_293;known23_294;known23_295;known23_296;known23_297;known23_298;known23_299;known23_300;known23_301;known23_302;known23_303;known23_304;known23_305;known23_306;known23_307;known23_308;known23_309;known23_310;known23_311;known23_312;known23_313;known23_314;known23_315;known23_316;known23_317;known23_318;known23_319;known23_320;known23_321;known23_322;known23_323;known23_324;known23_325;known23_326;known23_327;known23_328;known23_329;known23_330;known23_331;known23_332;known23_333;known23_334;known23_335;known23_336;known23_337;known23_338;known23_339;known23_340;known23_341;known23_342;known23_343;known23_344;known23_345;known23_346;known23_347;known23_348;known23_349;known23_350;known23_351;known23_352;known23_353;known23_354;known23_355;known23_356;known23_357;known23_358;known23_359].
Lemma known23_sound:Forall(QHBoundTr 67)remaining23->Forall(fun tm=>NonHalt tm /\ Bounds 59 67 tm)known23.
Proof. intro H;unfold known23.
 constructor;[exact(known23_000_bound H)|].
 constructor;[exact(known23_001_bound H)|].
 constructor;[exact(known23_002_bound H)|].
 constructor;[exact(known23_003_bound H)|].
 constructor;[exact(known23_004_bound H)|].
 constructor;[exact(known23_005_bound H)|].
 constructor;[exact(known23_006_bound H)|].
 constructor;[exact(known23_007_bound H)|].
 constructor;[exact(known23_008_bound H)|].
 constructor;[exact(known23_009_bound H)|].
 constructor;[exact(known23_010_bound H)|].
 constructor;[exact(known23_011_bound H)|].
 constructor;[exact(known23_012_bound H)|].
 constructor;[exact(known23_013_bound H)|].
 constructor;[exact(known23_014_bound H)|].
 constructor;[exact(known23_015_bound H)|].
 constructor;[exact(known23_016_bound H)|].
 constructor;[exact(known23_017_bound H)|].
 constructor;[exact(known23_018_bound H)|].
 constructor;[exact(known23_019_bound H)|].
 constructor;[exact(known23_020_bound H)|].
 constructor;[exact(known23_021_bound H)|].
 constructor;[exact(known23_022_bound H)|].
 constructor;[exact(known23_023_bound H)|].
 constructor;[exact(known23_024_bound H)|].
 constructor;[exact(known23_025_bound H)|].
 constructor;[exact(known23_026_bound H)|].
 constructor;[exact(known23_027_bound H)|].
 constructor;[exact(known23_028_bound H)|].
 constructor;[exact(known23_029_bound H)|].
 constructor;[exact(known23_030_bound H)|].
 constructor;[exact(known23_031_bound H)|].
 constructor;[exact(known23_032_bound H)|].
 constructor;[exact(known23_033_bound H)|].
 constructor;[exact(known23_034_bound H)|].
 constructor;[exact(known23_035_bound H)|].
 constructor;[exact(known23_036_bound H)|].
 constructor;[exact(known23_037_bound H)|].
 constructor;[exact(known23_038_bound H)|].
 constructor;[exact(known23_039_bound H)|].
 constructor;[exact(known23_040_bound H)|].
 constructor;[exact(known23_041_bound H)|].
 constructor;[exact(known23_042_bound H)|].
 constructor;[exact(known23_043_bound H)|].
 constructor;[exact(known23_044_bound H)|].
 constructor;[exact(known23_045_bound H)|].
 constructor;[exact(known23_046_bound H)|].
 constructor;[exact(known23_047_bound H)|].
 constructor;[exact(known23_048_bound H)|].
 constructor;[exact(known23_049_bound H)|].
 constructor;[exact(known23_050_bound H)|].
 constructor;[exact(known23_051_bound H)|].
 constructor;[exact(known23_052_bound H)|].
 constructor;[exact(known23_053_bound H)|].
 constructor;[exact(known23_054_bound H)|].
 constructor;[exact(known23_055_bound H)|].
 constructor;[exact(known23_056_bound H)|].
 constructor;[exact(known23_057_bound H)|].
 constructor;[exact(known23_058_bound H)|].
 constructor;[exact(known23_059_bound H)|].
 constructor;[exact(known23_060_bound H)|].
 constructor;[exact(known23_061_bound H)|].
 constructor;[exact(known23_062_bound H)|].
 constructor;[exact(known23_063_bound H)|].
 constructor;[exact(known23_064_bound H)|].
 constructor;[exact(known23_065_bound H)|].
 constructor;[exact(known23_066_bound H)|].
 constructor;[exact(known23_067_bound H)|].
 constructor;[exact(known23_068_bound H)|].
 constructor;[exact(known23_069_bound H)|].
 constructor;[exact(known23_070_bound H)|].
 constructor;[exact(known23_071_bound H)|].
 constructor;[exact(known23_072_bound H)|].
 constructor;[exact(known23_073_bound H)|].
 constructor;[exact(known23_074_bound H)|].
 constructor;[exact(known23_075_bound H)|].
 constructor;[exact(known23_076_bound H)|].
 constructor;[exact(known23_077_bound H)|].
 constructor;[exact(known23_078_bound H)|].
 constructor;[exact(known23_079_bound H)|].
 constructor;[exact(known23_080_bound H)|].
 constructor;[exact(known23_081_bound H)|].
 constructor;[exact(known23_082_bound H)|].
 constructor;[exact(known23_083_bound H)|].
 constructor;[exact(known23_084_bound H)|].
 constructor;[exact(known23_085_bound H)|].
 constructor;[exact(known23_086_bound H)|].
 constructor;[exact(known23_087_bound H)|].
 constructor;[exact(known23_088_bound H)|].
 constructor;[exact(known23_089_bound H)|].
 constructor;[exact(known23_090_bound H)|].
 constructor;[exact(known23_091_bound H)|].
 constructor;[exact(known23_092_bound H)|].
 constructor;[exact(known23_093_bound H)|].
 constructor;[exact(known23_094_bound H)|].
 constructor;[exact(known23_095_bound H)|].
 constructor;[exact(known23_096_bound H)|].
 constructor;[exact(known23_097_bound H)|].
 constructor;[exact(known23_098_bound H)|].
 constructor;[exact(known23_099_bound H)|].
 constructor;[exact(known23_100_bound H)|].
 constructor;[exact(known23_101_bound H)|].
 constructor;[exact(known23_102_bound H)|].
 constructor;[exact(known23_103_bound H)|].
 constructor;[exact(known23_104_bound H)|].
 constructor;[exact(known23_105_bound H)|].
 constructor;[exact(known23_106_bound H)|].
 constructor;[exact(known23_107_bound H)|].
 constructor;[exact(known23_108_bound H)|].
 constructor;[exact(known23_109_bound H)|].
 constructor;[exact(known23_110_bound H)|].
 constructor;[exact(known23_111_bound H)|].
 constructor;[exact(known23_112_bound H)|].
 constructor;[exact(known23_113_bound H)|].
 constructor;[exact(known23_114_bound H)|].
 constructor;[exact(known23_115_bound H)|].
 constructor;[exact(known23_116_bound H)|].
 constructor;[exact(known23_117_bound H)|].
 constructor;[exact(known23_118_bound H)|].
 constructor;[exact(known23_119_bound H)|].
 constructor;[exact(known23_120_bound H)|].
 constructor;[exact(known23_121_bound H)|].
 constructor;[exact(known23_122_bound H)|].
 constructor;[exact(known23_123_bound H)|].
 constructor;[exact(known23_124_bound H)|].
 constructor;[exact(known23_125_bound H)|].
 constructor;[exact(known23_126_bound H)|].
 constructor;[exact(known23_127_bound H)|].
 constructor;[exact(known23_128_bound H)|].
 constructor;[exact(known23_129_bound H)|].
 constructor;[exact(known23_130_bound H)|].
 constructor;[exact(known23_131_bound H)|].
 constructor;[exact(known23_132_bound H)|].
 constructor;[exact(known23_133_bound H)|].
 constructor;[exact(known23_134_bound H)|].
 constructor;[exact(known23_135_bound H)|].
 constructor;[exact(known23_136_bound H)|].
 constructor;[exact(known23_137_bound H)|].
 constructor;[exact(known23_138_bound H)|].
 constructor;[exact(known23_139_bound H)|].
 constructor;[exact(known23_140_bound H)|].
 constructor;[exact(known23_141_bound H)|].
 constructor;[exact(known23_142_bound H)|].
 constructor;[exact(known23_143_bound H)|].
 constructor;[exact(known23_144_bound H)|].
 constructor;[exact(known23_145_bound H)|].
 constructor;[exact(known23_146_bound H)|].
 constructor;[exact(known23_147_bound H)|].
 constructor;[exact(known23_148_bound H)|].
 constructor;[exact(known23_149_bound H)|].
 constructor;[exact(known23_150_bound H)|].
 constructor;[exact(known23_151_bound H)|].
 constructor;[exact(known23_152_bound H)|].
 constructor;[exact(known23_153_bound H)|].
 constructor;[exact(known23_154_bound H)|].
 constructor;[exact(known23_155_bound H)|].
 constructor;[exact(known23_156_bound H)|].
 constructor;[exact(known23_157_bound H)|].
 constructor;[exact(known23_158_bound H)|].
 constructor;[exact(known23_159_bound H)|].
 constructor;[exact(known23_160_bound H)|].
 constructor;[exact(known23_161_bound H)|].
 constructor;[exact(known23_162_bound H)|].
 constructor;[exact(known23_163_bound H)|].
 constructor;[exact(known23_164_bound H)|].
 constructor;[exact(known23_165_bound H)|].
 constructor;[exact(known23_166_bound H)|].
 constructor;[exact(known23_167_bound H)|].
 constructor;[exact(known23_168_bound H)|].
 constructor;[exact(known23_169_bound H)|].
 constructor;[exact(known23_170_bound H)|].
 constructor;[exact(known23_171_bound H)|].
 constructor;[exact(known23_172_bound H)|].
 constructor;[exact(known23_173_bound H)|].
 constructor;[exact(known23_174_bound H)|].
 constructor;[exact(known23_175_bound H)|].
 constructor;[exact(known23_176_bound H)|].
 constructor;[exact(known23_177_bound H)|].
 constructor;[exact(known23_178_bound H)|].
 constructor;[exact(known23_179_bound H)|].
 constructor;[exact(known23_180_bound H)|].
 constructor;[exact(known23_181_bound H)|].
 constructor;[exact(known23_182_bound H)|].
 constructor;[exact(known23_183_bound H)|].
 constructor;[exact(known23_184_bound H)|].
 constructor;[exact(known23_185_bound H)|].
 constructor;[exact(known23_186_bound H)|].
 constructor;[exact(known23_187_bound H)|].
 constructor;[exact(known23_188_bound H)|].
 constructor;[exact(known23_189_bound H)|].
 constructor;[exact(known23_190_bound H)|].
 constructor;[exact(known23_191_bound H)|].
 constructor;[exact(known23_192_bound H)|].
 constructor;[exact(known23_193_bound H)|].
 constructor;[exact(known23_194_bound H)|].
 constructor;[exact(known23_195_bound H)|].
 constructor;[exact(known23_196_bound H)|].
 constructor;[exact(known23_197_bound H)|].
 constructor;[exact(known23_198_bound H)|].
 constructor;[exact(known23_199_bound H)|].
 constructor;[exact(known23_200_bound H)|].
 constructor;[exact(known23_201_bound H)|].
 constructor;[exact(known23_202_bound H)|].
 constructor;[exact(known23_203_bound H)|].
 constructor;[exact(known23_204_bound H)|].
 constructor;[exact(known23_205_bound H)|].
 constructor;[exact(known23_206_bound H)|].
 constructor;[exact(known23_207_bound H)|].
 constructor;[exact(known23_208_bound H)|].
 constructor;[exact(known23_209_bound H)|].
 constructor;[exact(known23_210_bound H)|].
 constructor;[exact(known23_211_bound H)|].
 constructor;[exact(known23_212_bound H)|].
 constructor;[exact(known23_213_bound H)|].
 constructor;[exact(known23_214_bound H)|].
 constructor;[exact(known23_215_bound H)|].
 constructor;[exact(known23_216_bound H)|].
 constructor;[exact(known23_217_bound H)|].
 constructor;[exact(known23_218_bound H)|].
 constructor;[exact(known23_219_bound H)|].
 constructor;[exact(known23_220_bound H)|].
 constructor;[exact(known23_221_bound H)|].
 constructor;[exact(known23_222_bound H)|].
 constructor;[exact(known23_223_bound H)|].
 constructor;[exact(known23_224_bound H)|].
 constructor;[exact(known23_225_bound H)|].
 constructor;[exact(known23_226_bound H)|].
 constructor;[exact(known23_227_bound H)|].
 constructor;[exact(known23_228_bound H)|].
 constructor;[exact(known23_229_bound H)|].
 constructor;[exact(known23_230_bound H)|].
 constructor;[exact(known23_231_bound H)|].
 constructor;[exact(known23_232_bound H)|].
 constructor;[exact(known23_233_bound H)|].
 constructor;[exact(known23_234_bound H)|].
 constructor;[exact(known23_235_bound H)|].
 constructor;[exact(known23_236_bound H)|].
 constructor;[exact(known23_237_bound H)|].
 constructor;[exact(known23_238_bound H)|].
 constructor;[exact(known23_239_bound H)|].
 constructor;[exact(known23_240_bound H)|].
 constructor;[exact(known23_241_bound H)|].
 constructor;[exact(known23_242_bound H)|].
 constructor;[exact(known23_243_bound H)|].
 constructor;[exact(known23_244_bound H)|].
 constructor;[exact(known23_245_bound H)|].
 constructor;[exact(known23_246_bound H)|].
 constructor;[exact(known23_247_bound H)|].
 constructor;[exact(known23_248_bound H)|].
 constructor;[exact(known23_249_bound H)|].
 constructor;[exact(known23_250_bound H)|].
 constructor;[exact(known23_251_bound H)|].
 constructor;[exact(known23_252_bound H)|].
 constructor;[exact(known23_253_bound H)|].
 constructor;[exact(known23_254_bound H)|].
 constructor;[exact(known23_255_bound H)|].
 constructor;[exact(known23_256_bound H)|].
 constructor;[exact(known23_257_bound H)|].
 constructor;[exact(known23_258_bound H)|].
 constructor;[exact(known23_259_bound H)|].
 constructor;[exact(known23_260_bound H)|].
 constructor;[exact(known23_261_bound H)|].
 constructor;[exact(known23_262_bound H)|].
 constructor;[exact(known23_263_bound H)|].
 constructor;[exact(known23_264_bound H)|].
 constructor;[exact(known23_265_bound H)|].
 constructor;[exact(known23_266_bound H)|].
 constructor;[exact(known23_267_bound H)|].
 constructor;[exact(known23_268_bound H)|].
 constructor;[exact(known23_269_bound H)|].
 constructor;[exact(known23_270_bound H)|].
 constructor;[exact(known23_271_bound H)|].
 constructor;[exact(known23_272_bound H)|].
 constructor;[exact(known23_273_bound H)|].
 constructor;[exact(known23_274_bound H)|].
 constructor;[exact(known23_275_bound H)|].
 constructor;[exact(known23_276_bound H)|].
 constructor;[exact(known23_277_bound H)|].
 constructor;[exact(known23_278_bound H)|].
 constructor;[exact(known23_279_bound H)|].
 constructor;[exact(known23_280_bound H)|].
 constructor;[exact(known23_281_bound H)|].
 constructor;[exact(known23_282_bound H)|].
 constructor;[exact(known23_283_bound H)|].
 constructor;[exact(known23_284_bound H)|].
 constructor;[exact(known23_285_bound H)|].
 constructor;[exact(known23_286_bound H)|].
 constructor;[exact(known23_287_bound H)|].
 constructor;[exact(known23_288_bound H)|].
 constructor;[exact(known23_289_bound H)|].
 constructor;[exact(known23_290_bound H)|].
 constructor;[exact(known23_291_bound H)|].
 constructor;[exact(known23_292_bound H)|].
 constructor;[exact(known23_293_bound H)|].
 constructor;[exact(known23_294_bound H)|].
 constructor;[exact(known23_295_bound H)|].
 constructor;[exact(known23_296_bound H)|].
 constructor;[exact(known23_297_bound H)|].
 constructor;[exact(known23_298_bound H)|].
 constructor;[exact(known23_299_bound H)|].
 constructor;[exact(known23_300_bound H)|].
 constructor;[exact(known23_301_bound H)|].
 constructor;[exact(known23_302_bound H)|].
 constructor;[exact(known23_303_bound H)|].
 constructor;[exact(known23_304_bound H)|].
 constructor;[exact(known23_305_bound H)|].
 constructor;[exact(known23_306_bound H)|].
 constructor;[exact(known23_307_bound H)|].
 constructor;[exact(known23_308_bound H)|].
 constructor;[exact(known23_309_bound H)|].
 constructor;[exact(known23_310_bound H)|].
 constructor;[exact(known23_311_bound H)|].
 constructor;[exact(known23_312_bound H)|].
 constructor;[exact(known23_313_bound H)|].
 constructor;[exact(known23_314_bound H)|].
 constructor;[exact(known23_315_bound H)|].
 constructor;[exact(known23_316_bound H)|].
 constructor;[exact(known23_317_bound H)|].
 constructor;[exact(known23_318_bound H)|].
 constructor;[exact(known23_319_bound H)|].
 constructor;[exact(known23_320_bound H)|].
 constructor;[exact(known23_321_bound H)|].
 constructor;[exact(known23_322_bound H)|].
 constructor;[exact(known23_323_bound H)|].
 constructor;[exact(known23_324_bound H)|].
 constructor;[exact(known23_325_bound H)|].
 constructor;[exact(known23_326_bound H)|].
 constructor;[exact(known23_327_bound H)|].
 constructor;[exact(known23_328_bound H)|].
 constructor;[exact(known23_329_bound H)|].
 constructor;[exact(known23_330_bound H)|].
 constructor;[exact(known23_331_bound H)|].
 constructor;[exact(known23_332_bound H)|].
 constructor;[exact(known23_333_bound H)|].
 constructor;[exact(known23_334_bound H)|].
 constructor;[exact(known23_335_bound H)|].
 constructor;[exact(known23_336_bound H)|].
 constructor;[exact(known23_337_bound H)|].
 constructor;[exact(known23_338_bound H)|].
 constructor;[exact(known23_339_bound H)|].
 constructor;[exact(known23_340_bound H)|].
 constructor;[exact(known23_341_bound H)|].
 constructor;[exact(known23_342_bound H)|].
 constructor;[exact(known23_343_bound H)|].
 constructor;[exact(known23_344_bound H)|].
 constructor;[exact(known23_345_bound H)|].
 constructor;[exact(known23_346_bound H)|].
 constructor;[exact(known23_347_bound H)|].
 constructor;[exact(known23_348_bound H)|].
 constructor;[exact(known23_349_bound H)|].
 constructor;[exact(known23_350_bound H)|].
 constructor;[exact(known23_351_bound H)|].
 constructor;[exact(known23_352_bound H)|].
 constructor;[exact(known23_353_bound H)|].
 constructor;[exact(known23_354_bound H)|].
 constructor;[exact(known23_355_bound H)|].
 constructor;[exact(known23_356_bound H)|].
 constructor;[exact(known23_357_bound H)|].
 constructor;[exact(known23_358_bound H)|].
 constructor;[exact(known23_359_bound H)|].
 constructor. Qed.
