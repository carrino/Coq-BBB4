From Coq Require Import List Bool NArith.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import Deferred_Defs TNF_QH.
From BBBWait42 Require Import Spec.
From BBBWait42 Require Import ControlRank.
From BBBWait42.ControlRankReplay Require Import Base.
Import ListNotations.
Definition cases : list annotated_case := [
 TaggedCase 204349%N 205095%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t0LC;t1LC;t0RD;t1LB;t1RA;t0LA]) (bool4 true true true true) (rank4 (rank CrX 2 0 4 3 0) (rank CrY 2 0 0 2 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 204351%N 205097%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t0LC;t1LC;t0RD;t1LB;t1RA;t0RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 4 3 0) (rank CrY 2 0 0 2 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 204353%N 205099%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t0LC;t1LC;t0RD;t1LB;t1RA;t1RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 4 3 0) (rank CrY 2 0 0 2 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 204366%N 205112%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t0LC;t1LC;t1LD;t1LB;t1RA;t0LA]) (bool4 true true true true) (rank4 (rank CrX 2 0 2 1 0) (rank CrY 2 0 0 6 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 204367%N 205113%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t0LC;t1LC;t1LD;t1LB;t1RA;t0RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 2 1 0) (rank CrY 2 0 0 6 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 204368%N 205114%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t0LC;t1LC;t1LD;t1LB;t1RA;t1RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 2 1 0) (rank CrY 2 0 0 6 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 204437%N 205183%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t0LC;t1LC;t1RD;t1LB;t1RA;t0LA]) (bool4 true true true true) (rank4 (rank CrX 2 0 6 5 0) (rank CrY 2 0 0 2 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 204438%N 205184%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t0LC;t1LC;t1RD;t1LB;t1RA;t0RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 6 5 0) (rank CrY 2 0 0 2 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 204440%N 205186%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t0LC;t1LC;t1RD;t1LB;t1RA;t1RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 6 5 0) (rank CrY 2 0 0 2 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 207476%N 208222%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0LC;t0RD;t1LB;t0RA;t1RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 4 3 0) (rank CrY 2 0 0 2 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 207481%N 208227%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0LC;t0RD;t1LB;t1RA;t1RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 4 3 0) (rank CrY 2 0 0 2 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 207487%N 208233%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0LC;t1LD;t0LB;t0RA;t1LB]) (bool4 true true true true) (rank4 (rank CrX 3 0 2 1 0) (rank CrY 2 0 0 6 1) (rank CrY 2 2 0 0 3) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 207489%N 208235%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0LC;t1LD;t1LB;t0RA;t1RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 2 1 0) (rank CrY 2 0 0 6 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 207490%N 208236%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0LC;t1LD;t1LB;t1RA;t0LA]) (bool4 true true true true) (rank4 (rank CrX 2 0 2 1 0) (rank CrY 2 0 0 6 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 207492%N 208238%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0LC;t1LD;t1LB;t1RA;t0RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 2 1 0) (rank CrY 2 0 0 6 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 207495%N 208241%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0LC;t1LD;t1LB;t1RA;t1RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 2 1 0) (rank CrY 2 0 0 6 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 207509%N 208255%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0LC;t1RD;t1LB;t0RA;t1RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 6 5 0) (rank CrY 2 0 0 2 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 207513%N 208259%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0LC;t1RD;t1LB;t1RA;t0LA]) (bool4 true true true true) (rank4 (rank CrX 2 0 6 5 0) (rank CrY 2 0 0 2 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 207515%N 208261%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0LC;t1RD;t1LB;t1RA;t1RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 6 5 0) (rank CrY 2 0 0 2 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 207630%N 208376%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0RA;t0LD;t0RD;t0RA;t1LB]) (bool4 true true true true) (rank4 (rank CrX 3 0 2 1 0) (rank CrY 2 0 0 4 1) (rank CrY 3 2 0 0 4) (rank CrY 2 6 5 0 0)) 0);
 TaggedCase 208334%N 209080%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0RC;t1LD;t0LB;t0RA;t0LA]) (bool4 true true true true) (rank4 (rank CrX 2 0 2 1 0) (rank CrY 2 0 0 6 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 208335%N 209081%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0RC;t1LD;t0LB;t0RA;t0LB]) (bool4 true true true true) (rank4 (rank CrX 3 0 2 1 0) (rank CrY 2 0 0 6 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 208336%N 209082%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0RC;t1LD;t0LB;t0RA;t0RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 2 1 0) (rank CrY 2 0 0 6 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 208342%N 209088%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0RC;t1LD;t0RD;t0RA;t0LB]) (bool4 true true true true) (rank4 (rank CrX 3 0 2 1 0) (rank CrY 2 0 0 6 1) (rank CrY 2 1 0 0 2) (rank CrG 1 4 2 0 0)) 0);
 TaggedCase 208355%N 209101%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0RC;t1LD;t1LB;t0RA;t1RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 2 1 0) (rank CrY 2 0 0 6 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 208357%N 209103%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0RC;t1LD;t1LB;t1RA;t0LA]) (bool4 true true true true) (rank4 (rank CrX 2 0 2 1 0) (rank CrY 2 0 0 6 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 208358%N 209104%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0RC;t1LD;t1LB;t1RA;t0LB]) (bool4 true true true true) (rank4 (rank CrX 3 0 2 1 0) (rank CrY 2 0 0 6 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 208359%N 209105%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0RC;t1LD;t1LB;t1RA;t0RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 2 1 0) (rank CrY 2 0 0 6 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 208360%N 209106%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0RC;t1LD;t1LB;t1RA;t1RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 2 1 0) (rank CrY 2 0 0 6 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 208436%N 209182%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0RC;t1RD;t0LB;t0RA;t0LA]) (bool4 true true true true) (rank4 (rank CrX 2 0 6 5 0) (rank CrY 2 0 0 2 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 208447%N 209193%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0RC;t1RD;t1LB;t1RA;t0LA]) (bool4 true true true true) (rank4 (rank CrX 2 0 6 5 0) (rank CrY 2 0 0 2 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 208466%N 209212%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0RD;t0LD;t0LB;t0RA;t0LA]) (bool4 true true true true) (rank4 (rank CrX 2 0 2 1 0) (rank CrY 2 0 0 4 1) (rank CrY 3 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 208467%N 209213%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0RD;t0LD;t0LB;t0RA;t0LB]) (bool4 true true true true) (rank4 (rank CrX 3 0 2 1 0) (rank CrY 2 0 0 4 1) (rank CrY 3 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 208469%N 209215%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0RD;t0LD;t0LB;t0RA;t0RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 2 1 0) (rank CrY 2 0 0 4 1) (rank CrY 3 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 208475%N 209221%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0RD;t0LD;t0LB;t0RA;t1RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 2 1 0) (rank CrY 2 0 0 4 1) (rank CrY 3 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 208481%N 209227%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0RD;t0LD;t1LB;t0RA;t0RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 2 1 0) (rank CrY 2 0 0 4 1) (rank CrY 3 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 208483%N 209229%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0RD;t0LD;t1LB;t1RA;t0LB]) (bool4 true true true true) (rank4 (rank CrX 3 0 2 1 0) (rank CrY 2 0 0 4 1) (rank CrY 3 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 208592%N 209338%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0RD;t1LD;t0LB;t0RA;t0LA]) (bool4 true true true true) (rank4 (rank CrX 2 0 2 1 0) (rank CrY 2 0 0 6 1) (rank CrY 3 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 208593%N 209339%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0RD;t1LD;t0LB;t0RA;t0LB]) (bool4 true true true true) (rank4 (rank CrX 3 0 2 1 0) (rank CrY 2 0 0 6 1) (rank CrY 3 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 208601%N 209347%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0RD;t1LD;t1LB;t1RA;t0LA]) (bool4 true true true true) (rank4 (rank CrX 2 0 2 1 0) (rank CrY 2 0 0 6 1) (rank CrY 3 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 208674%N 209420%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t0RD;t1RD;t1LB;t1RA;t0LA]) (bool4 true true true true) (rank4 (rank CrX 2 0 6 5 0) (rank CrY 2 0 0 2 1) (rank CrY 3 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 209800%N 210546%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t1LC;t1LD;t1LB;t0RA;t1RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 2 1 0) (rank CrY 2 0 0 6 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 209802%N 210548%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t1LC;t1LD;t1LB;t1RA;t0LA]) (bool4 true true true true) (rank4 (rank CrX 2 0 2 1 0) (rank CrY 2 0 0 6 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 209803%N 210549%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t1LC;t1LD;t1LB;t1RA;t0RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 2 1 0) (rank CrY 2 0 0 6 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 209804%N 210550%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t1LC;t1LD;t1LB;t1RA;t1RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 2 1 0) (rank CrY 2 0 0 6 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 209872%N 210618%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t1LC;t1RD;t1LB;t1RA;t0LA]) (bool4 true true true true) (rank4 (rank CrX 2 0 6 5 0) (rank CrY 2 0 0 2 1) (rank CrY 2 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 210211%N 210957%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t1RA;t0LD;t0RD;t1RA;t1LB]) (bool4 true true true true) (rank4 (rank CrX 3 0 2 1 0) (rank CrY 2 0 0 4 1) (rank CrY 3 2 0 0 4) (rank CrY 2 6 5 0 0)) 0);
 TaggedCase 210480%N 211226%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t1RA;t1LD;t0RD;t1RA;t1LB]) (bool4 true true true true) (rank4 (rank CrX 3 0 2 1 0) (rank CrY 2 0 0 6 1) (rank CrY 3 2 0 0 4) (rank CrY 2 6 5 0 0)) 0);
 TaggedCase 211082%N 211828%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t1RD;t0LD;t1LB;t0RA;t0LA]) (bool4 true true true true) (rank4 (rank CrX 2 0 3 2 0) (rank CrY 2 0 0 4 1) (rank CrY 3 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 211084%N 211830%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t1RD;t0LD;t1LB;t0RA;t0RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 3 2 0) (rank CrY 2 0 0 4 1) (rank CrY 3 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 211151%N 211897%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t1RD;t0RD;t0LB;t0RA;t0RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 4 3 0) (rank CrY 2 0 0 2 1) (rank CrY 3 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 211154%N 211900%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t1RD;t0RD;t0LB;t0RA;t1RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 4 3 0) (rank CrY 2 0 0 2 1) (rank CrY 3 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 211230%N 211976%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t1RD;t1LD;t0LB;t0RA;t0LA]) (bool4 true true true true) (rank4 (rank CrX 2 0 3 2 0) (rank CrY 2 0 0 6 1) (rank CrY 3 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 211232%N 211978%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t1RD;t1LD;t0LB;t0RA;t0RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 3 2 0) (rank CrY 2 0 0 6 1) (rank CrY 3 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 211234%N 211980%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t1RD;t1LD;t0LB;t0RA;t1RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 3 2 0) (rank CrY 2 0 0 6 1) (rank CrY 3 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 211310%N 212056%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t1RD;t1RD;t0LB;t0RA;t0LA]) (bool4 true true true true) (rank4 (rank CrX 2 0 6 5 0) (rank CrY 2 0 0 2 1) (rank CrY 3 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 211312%N 212058%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t1RD;t1RD;t0LB;t0RA;t0RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 6 5 0) (rank CrY 2 0 0 2 1) (rank CrY 3 1 0 0 2) (rank CrX 2 6 1 0 0)) 0);
 TaggedCase 211314%N 212060%N 4 (mkCRCase (row_to_tm [t1RB;t1RD;t1LC;t1RD;t1RD;t0LB;t0RA;t1RA]) (bool4 true true true true) (rank4 (rank CrX 2 0 6 5 0) (rank CrY 2 0 0 2 1) (rank CrY 3 1 0 0 2) (rank CrX 2 6 1 0 0)) 0)
].
Example all_checked : checked cases = true.
Proof. native_compute. reflexivity. Qed.
Example exact_count : length cases = 58.
Proof. reflexivity. Qed.
