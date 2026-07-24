(* UNTRUSTED-generated R_QH tier; the Coq kernel re-checks via vm_compute. *)
From Coq Require Import List ZArith Lia.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import NGram NGramHist NGramHistWrap.
From BBB4.Census Require Import TNF_QH.
Import ListNotations.

Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.


Definition tmq_h_00500 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StD)
  | StD, S1 => Some (mkTrans S0 DL StB)
  end.

Definition lsetq_h_00500 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00500 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00500 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951769851369%positive,4);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(4524118413994%positive,1);(296492628957918862%positive,4);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 37 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(4524118413994%positive,1);(296492628957918862%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00500 : iqh tmq_h_00500.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00500 StD 9 2 2 34 20000
                lsetq_h_00500 rsetq_h_00500 certq_h_00500 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00500); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00501 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StD)
  | StD, S1 => Some (mkTrans S0 DL StC)
  end.

Definition lsetq_h_00501 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00501 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00501 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951769851369%positive,4);(74507626043037%positive,0);(347836724567896542%positive,4);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(4524118413994%positive,1);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 37 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00501 : iqh tmq_h_00501.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00501 StD 9 2 2 34 20000
                lsetq_h_00501 rsetq_h_00501 certq_h_00501 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00501); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00502 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StD)
  | StD, S1 => Some (mkTrans S0 DR StB)
  end.

Definition lsetq_h_00502 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00502 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00502 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 50 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951767811561%positive,2);(19073951769851369%positive,4);(341503537589868009%positive,2);(19073951767810526%positive,4);(74507626043037%positive,0);(347836724567896542%positive,4);(347836724565857949%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(4524118413994%positive,1);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537589866974%positive,4);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(296492628957917866%positive,1);(19073951767811741%positive,0);(341503537589868189%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(347836724565857769%positive,2);(1333998195660265%positive,2);(347836724565856734%positive,4);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780391082%positive,1);(296492624780392078%positive,4);(296489532403937962%positive,3);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4);(296489536581464746%positive,3)] [4524071228074%positive;1358737207285225%positive;19073951767811561%positive;19073951769851369%positive;341503537589868009%positive;19073951767810526%positive;347836724567896542%positive;74507626043037%positive;347836724565857949%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537589866974%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;296492628957917866%positive;19073951767811741%positive;341503537589868189%positive;74507626041822%positive;294330779421%positive;347836724565857769%positive;1333998195660265%positive;347836724565856734%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780391082%positive;296492624780392078%positive;296489532403937962%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive;296489536581464746%positive]]
  | StB => [HMeas MLeft 50 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(19073951767810526%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(341503537589866974%positive,1);(19073951769850334%positive,1);(296492628957917866%positive,1);(74507626041822%positive,1);(347836724565856734%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780391082%positive,1);(296492624780392078%positive,1);(296489532403937962%positive,0);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1);(296489536581464746%positive,0)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;19073951767810526%positive;75289225785576%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;75285048258792%positive;4705315516174%positive;341503537589866974%positive;19073951769850334%positive;74507626041822%positive;347836724565856734%positive;4705576611598%positive;341503537591906782%positive;296492624780391082%positive;296492624780392078%positive;296489532403937962%positive;296489532403938958%positive;296492628957917866%positive;296489536581465742%positive;1333998195659230%positive;296489536581464746%positive]]
  | StC => [HMeas MRight 50 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951767811561%positive,2);(19073951769851369%positive,0);(341503537589868009%positive,2);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(347836724565857949%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(19073951767811741%positive,2);(341503537589868189%positive,2);(294330779421%positive,2);(347836724565857769%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;19073951767811561%positive;19073951769851369%positive;341503537589868009%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;347836724565857949%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;19073951767811741%positive;341503537589868189%positive;294330779421%positive;347836724565857769%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00502 : iqh tmq_h_00502.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00502 StD 9 2 2 34 20000
                lsetq_h_00502 rsetq_h_00502 certq_h_00502 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00502); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00503 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StD)
  | StD, S1 => Some (mkTrans S0 DR StC)
  end.

Definition lsetq_h_00503 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[(StD,S1);(StA,S1)])];
   [(S0,[(StD,S1);(StA,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00503 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00503 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 48 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073955106477545%positive,2);(19073951769851369%positive,4);(296489531549930154%positive,3);(347836727904523933%positive,0);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(4524118413994%positive,1);(1358737207284190%positive,4);(1149728881%positive,4);(296492623926383274%positive,1);(341503540928533993%positive,2);(4705315516174%positive,4);(74507626042857%positive,2);(19073955106476510%positive,4);(341503537591907817%positive,4);(341503540928532958%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(19073955106477725%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(347836727904523753%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,4);(347836727904522718%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(341503540928534173%positive,0);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073955106477545%positive;19073951769851369%positive;296489531549930154%positive;347836727904523933%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;1149728881%positive;296492623926383274%positive;341503540928533993%positive;4705315516174%positive;74507626042857%positive;19073955106476510%positive;341503537591907817%positive;341503540928532958%positive;19073951769850334%positive;1358737207285405%positive;19073955106477725%positive;74507626041822%positive;294330779421%positive;347836727904523753%positive;1333998195660265%positive;347836724567897577%positive;347836727904522718%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;341503540928534173%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 48 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(296489531549930154%positive,0);(75289225785576%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(296492623926383274%positive,1);(4705315516174%positive,1);(19073955106476510%positive,1);(341503540928532958%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(347836727904522718%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;296489531549930154%positive;75289225785576%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;296492623926383274%positive;4705315516174%positive;19073955106476510%positive;341503540928532958%positive;19073951769850334%positive;74507626041822%positive;347836727904522718%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 48 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073955106477545%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836727904523933%positive,2);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(341503540928533993%positive,2);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(19073955106477725%positive,2);(294330779421%positive,2);(347836727904523753%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(341503540928534173%positive,2);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;19073955106477545%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;347836727904523933%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;341503540928533993%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;19073955106477725%positive;294330779421%positive;347836727904523753%positive;1333998195660265%positive;347836724567897577%positive;341503540928534173%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00503 : iqh tmq_h_00503.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00503 StD 9 2 2 34 20000
                lsetq_h_00503 rsetq_h_00503 certq_h_00503 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00503); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00504 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StD)
  | StD, S1 => Some (mkTrans S1 DR StB)
  end.

Definition lsetq_h_00504 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00504 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00504 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951769851369%positive,4);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(4524118413994%positive,1);(296492628957918862%positive,4);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 37 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(4524118413994%positive,1);(296492628957918862%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00504 : iqh tmq_h_00504.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00504 StD 9 2 2 34 20000
                lsetq_h_00504 rsetq_h_00504 certq_h_00504 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00504); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00505 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StD)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00505 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S1,[(StD,S1);(StA,S1)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])];
   [(S1,[(StD,S1);(StA,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition rsetq_h_00505 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00505 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 48 [(4524071228074%positive,3);(19073955123254941%positive,0);(1358737207285225%positive,2);(19073951769851369%positive,4);(296489531549938346%positive,3);(74507626043037%positive,0);(347836724567896542%positive,4);(347836727921300969%positive,2);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(4524118413994%positive,1);(347836727921299934%positive,4);(1358737207284190%positive,4);(1149728881%positive,4);(341503540945311389%positive,0);(4705315516174%positive,4);(296492623926391466%positive,1);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(19073955123254761%positive,2);(74507626041822%positive,4);(294330779421%positive,4);(19073955123253726%positive,4);(347836727921301149%positive,0);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(341503540945311209%positive,2);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(341503540945310174%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;19073955123254941%positive;1358737207285225%positive;19073951769851369%positive;296489531549938346%positive;347836724567896542%positive;347836727921300969%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;4524118413994%positive;347836727921299934%positive;1358737207284190%positive;1149728881%positive;341503540945311389%positive;4705315516174%positive;296492623926391466%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;19073955123254761%positive;74507626041822%positive;294330779421%positive;19073955123253726%positive;347836727921301149%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;341503540945311209%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;341503540945310174%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 48 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(296489531549938346%positive,0);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(347836727921299934%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(296492623926391466%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(19073955123253726%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(341503540945310174%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;296489531549938346%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;347836727921299934%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;296492623926391466%positive;19073951769850334%positive;74507626041822%positive;19073955123253726%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;341503540945310174%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 48 [(19073955123254941%positive,2);(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(347836727921300969%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(341503540945311389%positive,2);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(19073955123254761%positive,2);(294330779421%positive,2);(347836727921301149%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(341503540945311209%positive,2);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;19073955123254941%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;347836727921300969%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;341503540945311389%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;19073955123254761%positive;294330779421%positive;347836727921301149%positive;1333998195660265%positive;347836724567897577%positive;341503540945311209%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00505 : iqh tmq_h_00505.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00505 StD 9 2 2 34 20000
                lsetq_h_00505 rsetq_h_00505 certq_h_00505 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00505); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00506 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DR StB)
  | StD, S1 => None
  end.

Definition lsetq_h_00506 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S1,[(StA,S1);(StB,S0)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StA,S1);(StB,S0)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00506 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00506 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 48 [(4524071228074%positive,3);(341503537522759145%positive,2);(19073951700701662%positive,4);(1358737207285225%positive,2);(19073951769851369%positive,4);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(4524118413994%positive,1);(1358737207284190%positive,4);(347836724498748905%positive,2);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537522758110%positive,4);(19073951700702877%positive,0);(341503537591907817%positive,4);(341503537522759325%positive,0);(296489531548267178%positive,3);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(19073951700702697%positive,2);(296492623924720298%positive,1);(347836724498747870%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(347836724498749085%positive,0);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;341503537522759145%positive;1358737207285225%positive;19073951700701662%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;347836724498748905%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537522758110%positive;19073951700702877%positive;341503537591907817%positive;341503537522759325%positive;296489531548267178%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;19073951700702697%positive;296492623924720298%positive;347836724498747870%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;347836724498749085%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 48 [(4524071228074%positive,0);(296489536581464296%positive,1);(19073951700701662%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(341503537522758110%positive,1);(296489531548267178%positive,0);(19073951769850334%positive,1);(74507626041822%positive,1);(296492623924720298%positive,1);(347836724498747870%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;19073951700701662%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;341503537522758110%positive;296489531548267178%positive;19073951769850334%positive;74507626041822%positive;296492623924720298%positive;347836724498747870%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 48 [(341503537522759145%positive,2);(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(347836724498748905%positive,2);(18415324912%positive,1);(1149728881%positive,0);(74507626042857%positive,2);(19073951700702877%positive,2);(341503537591907817%positive,0);(341503537522759325%positive,2);(341503537591907997%positive,2);(1358737207285405%positive,2);(294330779421%positive,2);(19073951700702697%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(347836724498749085%positive,2);(19073951769851549%positive,2);(75285048258792%positive,1)] [341503537522759145%positive;296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;347836724498748905%positive;18415324912%positive;1149728881%positive;75285048258792%positive;74507626042857%positive;19073951700702877%positive;341503537591907817%positive;341503537522759325%positive;1358737207285405%positive;294330779421%positive;19073951700702697%positive;1333998195660265%positive;347836724567897577%positive;347836724498749085%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00506 : iqh tmq_h_00506.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00506 StD 8 2 2 33 20000
                lsetq_h_00506 rsetq_h_00506 certq_h_00506 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 33) 2000 tmq_h_00506); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00507 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DR StC)
  | StD, S1 => None
  end.

Definition lsetq_h_00507 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[(StD,S0)])];
   [(S0,[(StD,S0)]);(S1,[(StA,S1);(StB,S0)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StA,S1);(StB,S0)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00507 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00507 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 48 [(4524071228074%positive,3);(1358737207285225%positive,2);(1192122104763881%positive,2);(19073951769851369%positive,4);(347836724567896542%positive,4);(74507626043037%positive,0);(21739795404641949%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(4524118413994%positive,1);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(21343971218642409%positive,2);(341503537591907817%positive,4);(1192122104762846%positive,4);(341503537591907997%positive,4);(21343971218641374%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(1192122104764061%positive,0);(74507626041822%positive,4);(18530788991161002%positive,1);(294330779421%positive,4);(18530595717632682%positive,3);(21739795404641769%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(21739795404640734%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(21343971218642589%positive,0);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;1192122104763881%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;21739795404641949%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;21343971218642409%positive;341503537591907817%positive;1192122104762846%positive;21343971218641374%positive;19073951769850334%positive;1358737207285405%positive;1192122104764061%positive;74507626041822%positive;18530788991161002%positive;294330779421%positive;18530595717632682%positive;21739795404641769%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;21739795404640734%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;21343971218642589%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 48 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(1192122104762846%positive,1);(21343971218641374%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(18530788991161002%positive,1);(18530595717632682%positive,0);(4705576611598%positive,1);(21739795404640734%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;1192122104762846%positive;21343971218641374%positive;19073951769850334%positive;74507626041822%positive;18530788991161002%positive;18530595717632682%positive;4705576611598%positive;21739795404640734%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 48 [(296489536581464296%positive,1);(1358737207285225%positive,2);(1192122104763881%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(21739795404641949%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(21343971218642409%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(1192122104764061%positive,2);(294330779421%positive,2);(21739795404641769%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(21343971218642589%positive,2);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;1192122104763881%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;21739795404641949%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;21343971218642409%positive;341503537591907817%positive;1358737207285405%positive;1192122104764061%positive;294330779421%positive;21739795404641769%positive;1333998195660265%positive;347836724567897577%positive;21343971218642589%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00507 : iqh tmq_h_00507.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00507 StD 8 2 2 33 20000
                lsetq_h_00507 rsetq_h_00507 certq_h_00507 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 33) 2000 tmq_h_00507); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00508 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S0 DL StC)
  end.

Definition lsetq_h_00508 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00508 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00508 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951769851369%positive,4);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(4524118413994%positive,1);(296492628957918862%positive,4);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 37 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(4524118413994%positive,1);(296492628957918862%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00508 : iqh tmq_h_00508.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00508 StD 10 2 2 35 20000
                lsetq_h_00508 rsetq_h_00508 certq_h_00508 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 35) 2000 tmq_h_00508); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00509 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S0 DR StB)
  end.

Definition lsetq_h_00509 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S1,[(StA,S1);(StA,S1)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StA,S1);(StA,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00509 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00509 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 48 [(4524071228074%positive,3);(341503540743984617%positive,2);(1358737207285225%positive,2);(19073951769851369%positive,4);(19073954921927134%positive,4);(341503540743983582%positive,4);(19073954921928349%positive,0);(74507626043037%positive,0);(347836724567896542%positive,4);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(4524118413994%positive,1);(1358737207284190%positive,4);(1149728881%positive,4);(347836727719974377%positive,2);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(341503540743984797%positive,0);(296489531549840042%positive,3);(74507626041822%positive,4);(294330779421%positive,4);(19073954921928169%positive,2);(347836727719973342%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(296492623926293162%positive,1);(341503537591906782%positive,4);(347836727719974557%positive,0);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;341503540743984617%positive;1358737207285225%positive;19073951769851369%positive;19073954921927134%positive;341503540743983582%positive;19073954921928349%positive;347836724567896542%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;1149728881%positive;347836727719974377%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;341503540743984797%positive;296489531549840042%positive;74507626041822%positive;294330779421%positive;19073954921928169%positive;347836727719973342%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;296492623926293162%positive;341503537591906782%positive;347836727719974557%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 48 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(19073954921927134%positive,1);(296489532403937512%positive,1);(341503540743983582%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(296489531549840042%positive,0);(74507626041822%positive,1);(347836727719973342%positive,1);(4705576611598%positive,1);(296492623926293162%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;19073954921927134%positive;296489532403937512%positive;341503540743983582%positive;75289225785576%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;296489531549840042%positive;74507626041822%positive;347836727719973342%positive;4705576611598%positive;296492623926293162%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 48 [(341503540743984617%positive,2);(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(19073954921928349%positive,2);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(347836727719974377%positive,2);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(341503540743984797%positive,2);(294330779421%positive,2);(19073954921928169%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(347836727719974557%positive,2);(19073951769851549%positive,2);(75285048258792%positive,1)] [341503540743984617%positive;296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;19073954921928349%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;347836727719974377%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;341503540743984797%positive;294330779421%positive;19073954921928169%positive;1333998195660265%positive;347836724567897577%positive;347836727719974557%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00509 : iqh tmq_h_00509.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00509 StD 10 2 2 35 20000
                lsetq_h_00509 rsetq_h_00509 certq_h_00509 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 35) 2000 tmq_h_00509); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00510 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S0 DR StC)
  end.

Definition lsetq_h_00510 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[(StD,S1);(StD,S0)])];
   [(S0,[(StD,S1);(StD,S0)]);(S1,[(StA,S1);(StA,S1)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StA,S1);(StA,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00510 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00510 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 48 [(4524071228074%positive,3);(296492627079975594%positive,1);(347836726830780894%positive,4);(1358737207285225%positive,2);(296489534703522474%positive,3);(19073951769851369%positive,4);(341503539854792349%positive,0);(74507626043037%positive,0);(347836724567896542%positive,4);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(4524118413994%positive,1);(341503539854792169%positive,2);(1358737207284190%positive,4);(19073954032735721%positive,2);(1149728881%positive,4);(19073954032734686%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(347836726830782109%positive,0);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(347836726830781929%positive,2);(74507626041822%positive,4);(294330779421%positive,4);(341503539854791134%positive,4);(1333998195660265%positive,2);(19073954032735901%positive,0);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;296492627079975594%positive;347836726830780894%positive;1358737207285225%positive;296489534703522474%positive;19073951769851369%positive;341503539854792349%positive;347836724567896542%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;4524118413994%positive;341503539854792169%positive;1358737207284190%positive;19073954032735721%positive;1149728881%positive;19073954032734686%positive;4705315516174%positive;74507626042857%positive;347836726830782109%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;347836726830781929%positive;74507626041822%positive;294330779421%positive;341503539854791134%positive;1333998195660265%positive;19073954032735901%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 48 [(4524071228074%positive,0);(296492627079975594%positive,1);(296489536581464296%positive,1);(347836726830780894%positive,1);(296489534703522474%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(19073954032734686%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(341503539854791134%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296492627079975594%positive;347836726830780894%positive;296489536581464296%positive;296489534703522474%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;19073954032734686%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;341503539854791134%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 48 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(341503539854792349%positive,2);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(341503539854792169%positive,2);(19073954032735721%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(347836726830782109%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(347836726830781929%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(19073954032735901%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;341503539854792349%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;341503539854792169%positive;19073954032735721%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;347836726830782109%positive;341503537591907817%positive;1358737207285405%positive;347836726830781929%positive;294330779421%positive;1333998195660265%positive;19073954032735901%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00510 : iqh tmq_h_00510.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00510 StD 10 2 2 35 20000
                lsetq_h_00510 rsetq_h_00510 certq_h_00510 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 35) 2000 tmq_h_00510); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00511 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Definition lsetq_h_00511 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00511 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00511 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951769851369%positive,4);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(4524118413994%positive,1);(296492628957918862%positive,4);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 37 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(4524118413994%positive,1);(296492628957918862%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00511 : iqh tmq_h_00511.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00511 StD 10 2 2 35 20000
                lsetq_h_00511 rsetq_h_00511 certq_h_00511 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 35) 2000 tmq_h_00511); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00512 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S1 DR StA)
  end.

Definition lsetq_h_00512 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00512 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00512 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951769851369%positive,4);(74507626043037%positive,0);(347836724567896542%positive,4);(1333998195660445%positive,0);(347836724567897757%positive,4);(4524118413994%positive,1);(296492628957918862%positive,4);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 37 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(4524118413994%positive,1);(296492628957918862%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00512 : iqh tmq_h_00512.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00512 StD 10 2 2 35 20000
                lsetq_h_00512 rsetq_h_00512 certq_h_00512 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 35) 2000 tmq_h_00512); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00513 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00513 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S1,[(StD,S1);(StD,S0)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StA,S1);(StA,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])];
   [(S1,[(StD,S1);(StD,S0)]);(S1,[(StA,S1);(StA,S1)])]].

Definition rsetq_h_00513 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00513 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 48 [(4524071228074%positive,3);(347836726847559145%positive,2);(1358737207285225%positive,2);(19073951769851369%positive,4);(341503539871568350%positive,4);(74507626043037%positive,0);(347836724567896542%positive,4);(19073954049513117%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(4524118413994%positive,1);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(347836726847558110%positive,4);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(341503539871569565%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(296489534703530666%positive,3);(19073954049512937%positive,2);(341503539871569385%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,4);(19073954049511902%positive,4);(4705576611598%positive,4);(347836726847559325%positive,0);(341503537591906782%positive,4);(296492624780392078%positive,4);(296492627079983786%positive,1);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;347836726847559145%positive;1358737207285225%positive;19073951769851369%positive;341503539871568350%positive;347836724567896542%positive;74507626043037%positive;19073954049513117%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;347836726847558110%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;341503539871569565%positive;74507626041822%positive;294330779421%positive;296489534703530666%positive;19073954049512937%positive;341503539871569385%positive;1333998195660265%positive;347836724567897577%positive;19073954049511902%positive;4705576611598%positive;347836726847559325%positive;341503537591906782%positive;296492624780392078%positive;296492627079983786%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 48 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(341503539871568350%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(347836726847558110%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(296489534703530666%positive,0);(19073954049511902%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296492627079983786%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;341503539871568350%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;347836726847558110%positive;19073951769850334%positive;74507626041822%positive;296489534703530666%positive;19073954049511902%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296492627079983786%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 48 [(347836726847559145%positive,2);(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(19073954049513117%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(341503539871569565%positive,2);(294330779421%positive,2);(19073954049512937%positive,2);(341503539871569385%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(347836726847559325%positive,2);(19073951769851549%positive,2);(75285048258792%positive,1)] [347836726847559145%positive;296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;19073954049513117%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;341503539871569565%positive;294330779421%positive;19073954049512937%positive;341503539871569385%positive;1333998195660265%positive;347836724567897577%positive;347836726847559325%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00513 : iqh tmq_h_00513.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00513 StD 10 2 2 35 20000
                lsetq_h_00513 rsetq_h_00513 certq_h_00513 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 35) 2000 tmq_h_00513); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00514 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => None
  end.

Definition lsetq_h_00514 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00514 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00514 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951769851369%positive,4);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(4524118413994%positive,1);(296492628957918862%positive,4);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 37 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(4524118413994%positive,1);(296492628957918862%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00514 : iqh tmq_h_00514.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00514 StD 8 2 2 33 20000
                lsetq_h_00514 rsetq_h_00514 certq_h_00514 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 33) 2000 tmq_h_00514); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00515 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S0 DL StB)
  end.

Definition lsetq_h_00515 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00515 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00515 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951769851369%positive,4);(74507626043037%positive,0);(347836724567896542%positive,4);(1333998195660445%positive,0);(347836724567897757%positive,4);(4524118413994%positive,1);(296492628957918862%positive,4);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 37 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(4524118413994%positive,1);(296492628957918862%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00515 : iqh tmq_h_00515.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00515 StD 9 2 2 34 20000
                lsetq_h_00515 rsetq_h_00515 certq_h_00515 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00515); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00516 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S0 DL StC)
  end.

Definition lsetq_h_00516 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00516 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00516 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951769851369%positive,4);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(4524118413994%positive,1);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(341503537591907997%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 37 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(75285048258792%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(1358737207285225%positive,2);(296492624780390632%positive,1);(19073951769851369%positive,0);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(75285048258792%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(1358737207285405%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(341503537591907997%positive,2)] [296489536581464296%positive;1358737207285225%positive;19073951769851369%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;74507626042857%positive;341503537591907817%positive;341503537591907997%positive;1358737207285405%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;75285048258792%positive]]
  | StD => []
  end.

Lemma cqh_h_00516 : iqh tmq_h_00516.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00516 StD 9 2 2 34 20000
                lsetq_h_00516 rsetq_h_00516 certq_h_00516 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00516); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00517 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S0 DR StB)
  end.

Definition lsetq_h_00517 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00517 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00517 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 50 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951767811561%positive,2);(19073951769851369%positive,4);(341503537589868009%positive,2);(19073951767810526%positive,4);(347836724567896542%positive,4);(74507626043037%positive,0);(347836724565857949%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(4524118413994%positive,1);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537589866974%positive,4);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(19073951767811741%positive,0);(341503537589868189%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(347836724565857769%positive,2);(1333998195660265%positive,2);(347836724565856734%positive,4);(347836724567897577%positive,4);(4705576611598%positive,4);(296492624780391082%positive,1);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403937962%positive,3);(296489532403938958%positive,4);(19073951769851549%positive,4);(296492628957917866%positive,1);(296489536581465742%positive,4);(1333998195659230%positive,4);(296489536581464746%positive,3)] [4524071228074%positive;1358737207285225%positive;19073951767811561%positive;19073951769851369%positive;341503537589868009%positive;19073951767810526%positive;74507626043037%positive;347836724567896542%positive;347836724565857949%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537589866974%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;19073951767811741%positive;296492628957917866%positive;341503537589868189%positive;74507626041822%positive;294330779421%positive;347836724565857769%positive;1333998195660265%positive;347836724565856734%positive;347836724567897577%positive;4705576611598%positive;296492624780391082%positive;341503537591906782%positive;296492624780392078%positive;296489532403937962%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive;296489536581464746%positive]]
  | StB => [HMeas MLeft 50 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(19073951767810526%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(75285048258792%positive,1);(4705315516174%positive,1);(341503537589866974%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(347836724565856734%positive,1);(4705576611598%positive,1);(296492624780391082%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403937962%positive,0);(296489532403938958%positive,1);(296492628957917866%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1);(296489536581464746%positive,0)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;19073951767810526%positive;75289225785576%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;341503537589866974%positive;19073951769850334%positive;296492628957917866%positive;74507626041822%positive;347836724565856734%positive;4705576611598%positive;296492624780391082%positive;341503537591906782%positive;296492624780392078%positive;296489532403937962%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive;296489536581464746%positive]]
  | StC => [HMeas MRight 50 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951767811561%positive,2);(19073951769851369%positive,0);(341503537589868009%positive,2);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(347836724565857949%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(75285048258792%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(19073951767811741%positive,2);(341503537589868189%positive,2);(294330779421%positive,2);(347836724565857769%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2)] [296489536581464296%positive;1358737207285225%positive;19073951767811561%positive;19073951769851369%positive;341503537589868009%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;347836724565857949%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;19073951767811741%positive;341503537589868189%positive;294330779421%positive;347836724565857769%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00517 : iqh tmq_h_00517.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00517 StD 9 2 2 34 20000
                lsetq_h_00517 rsetq_h_00517 certq_h_00517 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00517); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00518 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S0 DR StC)
  end.

Definition lsetq_h_00518 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00518 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00518 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 50 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951767811561%positive,2);(19073951769851369%positive,4);(341503537589868009%positive,2);(19073951767810526%positive,4);(347836724567896542%positive,4);(74507626043037%positive,0);(347836724565857949%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(4524118413994%positive,1);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537589866974%positive,4);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(296492628957917866%positive,1);(19073951767811741%positive,0);(341503537589868189%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(347836724565857769%positive,2);(1333998195660265%positive,2);(347836724565856734%positive,4);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780391082%positive,1);(296492624780392078%positive,4);(296489532403937962%positive,3);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4);(296489536581464746%positive,3)] [4524071228074%positive;1358737207285225%positive;19073951767811561%positive;19073951769851369%positive;341503537589868009%positive;19073951767810526%positive;74507626043037%positive;347836724567896542%positive;347836724565857949%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537589866974%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;296492628957917866%positive;19073951767811741%positive;341503537589868189%positive;74507626041822%positive;294330779421%positive;347836724565857769%positive;1333998195660265%positive;347836724565856734%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780391082%positive;296492624780392078%positive;296489532403937962%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive;296489536581464746%positive]]
  | StB => [HMeas MLeft 50 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(19073951767810526%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(341503537589866974%positive,1);(19073951769850334%positive,1);(296492628957917866%positive,1);(74507626041822%positive,1);(347836724565856734%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780391082%positive,1);(296492624780392078%positive,1);(296489532403937962%positive,0);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1);(296489536581464746%positive,0)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;19073951767810526%positive;75289225785576%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;75285048258792%positive;4705315516174%positive;341503537589866974%positive;19073951769850334%positive;74507626041822%positive;347836724565856734%positive;4705576611598%positive;341503537591906782%positive;296492624780391082%positive;296492624780392078%positive;296489532403937962%positive;296489532403938958%positive;296492628957917866%positive;296489536581465742%positive;1333998195659230%positive;296489536581464746%positive]]
  | StC => [HMeas MRight 50 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951767811561%positive,2);(19073951769851369%positive,0);(341503537589868009%positive,2);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(347836724565857949%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(19073951767811741%positive,2);(341503537589868189%positive,2);(294330779421%positive,2);(347836724565857769%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;19073951767811561%positive;19073951769851369%positive;341503537589868009%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;347836724565857949%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;19073951767811741%positive;341503537589868189%positive;294330779421%positive;347836724565857769%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00518 : iqh tmq_h_00518.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00518 StD 9 2 2 34 20000
                lsetq_h_00518 rsetq_h_00518 certq_h_00518 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00518); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00519 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Definition lsetq_h_00519 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00519 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00519 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951769851369%positive,4);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(4524118413994%positive,1);(296492628957918862%positive,4);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 37 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(4524118413994%positive,1);(296492628957918862%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00519 : iqh tmq_h_00519.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00519 StD 16 2 2 41 20000
                lsetq_h_00519 rsetq_h_00519 certq_h_00519 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 41) 2000 tmq_h_00519); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00520 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DR StB)
  end.

Definition lsetq_h_00520 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00520 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00520 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951769851369%positive,4);(74507626043037%positive,0);(347836724567896542%positive,4);(1333998195660445%positive,0);(347836724567897757%positive,4);(4524118413994%positive,1);(296492628957918862%positive,4);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 37 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(4524118413994%positive,1);(296492628957918862%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00520 : iqh tmq_h_00520.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00520 StD 9 2 2 34 20000
                lsetq_h_00520 rsetq_h_00520 certq_h_00520 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00520); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00521 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00521 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00521 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00521 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951769851369%positive,4);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(4524118413994%positive,1);(296492628957918862%positive,4);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 37 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(4524118413994%positive,1);(296492628957918862%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00521 : iqh tmq_h_00521.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00521 StD 9 2 2 34 20000
                lsetq_h_00521 rsetq_h_00521 certq_h_00521 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00521); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00522 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StA)
  | StD, S1 => None
  end.

Definition lsetq_h_00522 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00522 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00522 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951769851369%positive,4);(74507626043037%positive,0);(347836724567896542%positive,4);(1333998195660445%positive,0);(347836724567897757%positive,4);(4524118413994%positive,1);(296492628957918862%positive,4);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 37 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(4524118413994%positive,1);(296492628957918862%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00522 : iqh tmq_h_00522.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00522 StD 8 2 2 33 20000
                lsetq_h_00522 rsetq_h_00522 certq_h_00522 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 33) 2000 tmq_h_00522); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00523 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => None
  end.

Definition lsetq_h_00523 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StA,S1);(StB,S0)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])];
   [(S1,[(StD,S0)]);(S1,[(StA,S1);(StB,S0)])]].

Definition rsetq_h_00523 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00523 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 48 [(4524071228074%positive,3);(21739795421418985%positive,2);(1358737207285225%positive,2);(18530788991169194%positive,1);(19073951769851369%positive,4);(21739795421417950%positive,4);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(21343971235419805%positive,0);(4524118413994%positive,1);(1358737207284190%positive,4);(1149728881%positive,4);(1192122121541097%positive,2);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(1192122121540062%positive,4);(21739795421419165%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(21343971235419625%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(18530595717640874%positive,3);(341503537591906782%positive,4);(296492624780392078%positive,4);(21343971235418590%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(1192122121541277%positive,0);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;21739795421418985%positive;1358737207285225%positive;18530788991169194%positive;19073951769851369%positive;21739795421417950%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;21343971235419805%positive;4524118413994%positive;1358737207284190%positive;1149728881%positive;1192122121541097%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;1192122121540062%positive;21739795421419165%positive;74507626041822%positive;294330779421%positive;21343971235419625%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;18530595717640874%positive;341503537591906782%positive;296492624780392078%positive;21343971235418590%positive;296489532403938958%positive;19073951769851549%positive;1192122121541277%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 48 [(4524071228074%positive,0);(296489536581464296%positive,1);(18530788991169194%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(21739795421417950%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(1192122121540062%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(18530595717640874%positive,0);(341503537591906782%positive,1);(296492624780392078%positive,1);(21343971235418590%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;18530788991169194%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;21739795421417950%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;1192122121540062%positive;74507626041822%positive;4705576611598%positive;18530595717640874%positive;341503537591906782%positive;296492624780392078%positive;21343971235418590%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 48 [(21739795421418985%positive,2);(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(21343971235419805%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(1192122121541097%positive,2);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(21739795421419165%positive,2);(294330779421%positive,2);(21343971235419625%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(1192122121541277%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;21739795421418985%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;21343971235419805%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;1192122121541097%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;21739795421419165%positive;294330779421%positive;21343971235419625%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;1192122121541277%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00523 : iqh tmq_h_00523.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00523 StD 8 2 2 33 20000
                lsetq_h_00523 rsetq_h_00523 certq_h_00523 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 33) 2000 tmq_h_00523); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00524 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StA)
  end.

Definition lsetq_h_00524 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition rsetq_h_00524 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition certq_h_00524 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 37 [(347849918707528158%positive,1);(323514222544615102%positive,1);(1334049735266782%positive,1);(75285048259563%positive,1);(323514226923467755%positive,1);(323511130168161982%positive,1);(4705315516222%positive,1);(323511134547014635%positive,1);(1358788746891742%positive,1);(323514222544614379%positive,1);(4936435274410%positive,1);(19087145909481950%positive,1);(323511130168161259%positive,1);(341516731731538398%positive,1);(4936388088490%positive,0);(18416111347%positive,1);(74559165649374%positive,1);(323514226923468478%positive,1);(323511134547015358%positive,1);(75289427112939%positive,1);(4705589194558%positive,1)] [1334049735266782%positive;347849918707528158%positive;323514222544615102%positive;323514226923467755%positive;75285048259563%positive;323511130168161982%positive;323511134547014635%positive;4705315516222%positive;1358788746891742%positive;323514222544614379%positive;4936435274410%positive;19087145909481950%positive;323511130168161259%positive;341516731731538398%positive;4936388088490%positive;18416111347%positive;74559165649374%positive;323514226923468478%positive;323511134547015358%positive;75289427112939%positive;4705589194558%positive]]
  | StC => [HMeas MRight 37 [(19087145909482985%positive,0);(75285048259563%positive,1);(323514226923467755%positive,1);(1149729265%positive,0);(347849918707529373%positive,2);(294330785565%positive,2);(323511134547014635%positive,1);(74559165650589%positive,2);(1334049735267997%positive,2);(341516731731539433%positive,0);(323514222544614379%positive,1);(1358788746892777%positive,2);(323511130168161259%positive,1);(19087145909483165%positive,2);(18416111347%positive,1);(347849918707529193%positive,0);(74559165650409%positive,2);(75289427112939%positive,1);(1334049735267817%positive,2);(341516731731539613%positive,2);(1358788746892957%positive,2)] [19087145909482985%positive;75285048259563%positive;323514226923467755%positive;1149729265%positive;347849918707529373%positive;294330785565%positive;323511134547014635%positive;74559165650589%positive;1334049735267997%positive;341516731731539433%positive;323514222544614379%positive;1358788746892777%positive;323511130168161259%positive;19087145909483165%positive;18416111347%positive;347849918707529193%positive;74559165650409%positive;75289427112939%positive;1334049735267817%positive;341516731731539613%positive;1358788746892957%positive]]
  | StD => [HMeas MLeft 37 [(347849918707528158%positive,4);(19087145909482985%positive,4);(323514222544615102%positive,4);(1334049735266782%positive,4);(1149729265%positive,4);(323511130168161982%positive,4);(347849918707529373%positive,4);(294330785565%positive,4);(4705315516222%positive,4);(74559165650589%positive,0);(1334049735267997%positive,0);(341516731731539433%positive,4);(1358788746891742%positive,4);(4936435274410%positive,1);(1358788746892777%positive,2);(19087145909481950%positive,4);(341516731731538398%positive,4);(4936388088490%positive,3);(19087145909483165%positive,4);(347849918707529193%positive,4);(74559165649374%positive,4);(323514226923468478%positive,4);(74559165650409%positive,2);(323511134547015358%positive,4);(1334049735267817%positive,2);(4705589194558%positive,4);(341516731731539613%positive,4);(1358788746892957%positive,0)] [1334049735266782%positive;19087145909482985%positive;323514222544615102%positive;347849918707528158%positive;1149729265%positive;323511130168161982%positive;347849918707529373%positive;294330785565%positive;4705315516222%positive;74559165650589%positive;1334049735267997%positive;341516731731539433%positive;1358788746891742%positive;4936435274410%positive;19087145909481950%positive;1358788746892777%positive;341516731731538398%positive;4936388088490%positive;19087145909483165%positive;347849918707529193%positive;74559165649374%positive;323514226923468478%positive;74559165650409%positive;323511134547015358%positive;1334049735267817%positive;4705589194558%positive;341516731731539613%positive;1358788746892957%positive]]
  end.

Lemma cqh_h_00524 : iqh tmq_h_00524.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00524 StA 8 2 2 33 20000
                lsetq_h_00524 rsetq_h_00524 certq_h_00524 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 33) 2000 tmq_h_00524); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00525 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StA)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S0 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00525 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S1,[(StA,S1);(StC,S1)])];
   [(S1,[(StA,S1);(StC,S1)]);(S1,[(StB,S0);(StD,S1)])];
   [(S1,[(StB,S0);(StD,S1)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition rsetq_h_00525 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition certq_h_00525 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 41 [(5453667406779%positive,0);(351078360865895151%positive,1);(357411547841885946%positive,1);(306064359855454111%positive,1);(357411548697523962%positive,1);(1195563884074911%positive,1);(357411547841884911%positive,1);(351078365898634171%positive,0);(1150007538%positive,1);(351078360865896366%positive,1);(19641575789098746%positive,1);(351078361721533167%positive,1);(351078361721534382%positive,1);(19641576644736762%positive,1);(4722827818783%positive,1);(294402117422%positive,1);(19641576644735727%positive,1);(357411547841886126%positive,1);(19641575789097711%positive,1);(357411552874623931%positive,0);(357411548697522927%positive,1);(306067451359909791%positive,1);(357411548697524142%positive,1);(19641575789098926%positive,1);(306067452231907231%positive,1);(306064358983456671%positive,1);(19641576644736942%positive,1);(1195575963670431%positive,1);(5357030642619%positive,0);(351078360865896186%positive,1);(351078361721534202%positive,1)] [5453667406779%positive;351078360865895151%positive;357411547841885946%positive;306064359855454111%positive;357411548697523962%positive;1195563884074911%positive;357411547841884911%positive;351078365898634171%positive;1150007538%positive;351078360865896366%positive;19641575789098746%positive;351078361721533167%positive;351078361721534382%positive;19641576644736762%positive;4722827818783%positive;294402117422%positive;19641576644735727%positive;357411547841886126%positive;19641575789097711%positive;357411552874623931%positive;357411548697522927%positive;306067451359909791%positive;357411548697524142%positive;19641575789098926%positive;306067452231907231%positive;19641576644736942%positive;351078361721534202%positive;1195575963670431%positive;5357030642619%positive;351078360865896186%positive;306064358983456671%positive]]
  | StC => [HMeas MLeft 41 [(5453667406779%positive,1);(351078360865895151%positive,2);(306064359855454111%positive,2);(306064358983455225%positive,0);(1195563884074911%positive,2);(357411547841884911%positive,2);(351078365898634171%positive,1);(351078361721533167%positive,2);(306067451359908345%positive,0);(4722827818783%positive,2);(19641576644735727%positive,2);(19641575789097711%positive,2);(18419783537%positive,2);(306067452231905785%positive,2);(357411552874623931%positive,1);(1195575963668985%positive,0);(357411548697522927%positive,2);(306067451359909791%positive,2);(306067452231907231%positive,2);(306064358983456671%positive,2);(75565245100537%positive,2);(1195575963670431%positive,2);(5357030642619%positive,1);(1195563884073465%positive,0);(306064359855452665%positive,2)] [5453667406779%positive;351078360865895151%positive;306064359855454111%positive;306064358983455225%positive;1195563884074911%positive;357411547841884911%positive;351078365898634171%positive;351078361721533167%positive;306067451359908345%positive;4722827818783%positive;19641576644735727%positive;19641575789097711%positive;18419783537%positive;306067452231905785%positive;357411552874623931%positive;357411548697522927%positive;1195575963668985%positive;306067451359909791%positive;306067452231907231%positive;75565245100537%positive;1195575963670431%positive;5357030642619%positive;1195563884073465%positive;306064359855452665%positive;306064358983456671%positive]]
  | StD => [HMeas MRight 41 [(357411547841885946%positive,0);(357411548697523962%positive,1);(306064358983455225%positive,2);(1150007538%positive,0);(351078360865896366%positive,2);(19641575789098746%positive,0);(306067451359908345%positive,2);(351078361721534382%positive,2);(19641576644736762%positive,1);(294402117422%positive,2);(357411547841886126%positive,2);(18419783537%positive,1);(306067452231905785%positive,1);(1195575963668985%positive,2);(357411548697524142%positive,2);(19641575789098926%positive,2);(19641576644736942%positive,2);(75565245100537%positive,1);(1195563884073465%positive,2);(306064359855452665%positive,1);(351078360865896186%positive,0);(351078361721534202%positive,1)] [357411547841885946%positive;357411548697523962%positive;306064358983455225%positive;1150007538%positive;351078360865896366%positive;19641575789098746%positive;306067451359908345%positive;351078361721534382%positive;19641576644736762%positive;294402117422%positive;357411547841886126%positive;18419783537%positive;306067452231905785%positive;1195575963668985%positive;357411548697524142%positive;19641575789098926%positive;19641576644736942%positive;75565245100537%positive;1195563884073465%positive;306064359855452665%positive;351078360865896186%positive;351078361721534202%positive]]
  end.

Lemma cqh_h_00525 : iqh tmq_h_00525.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00525 StA 13 2 2 38 20000
                lsetq_h_00525 rsetq_h_00525 certq_h_00525 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 38) 2000 tmq_h_00525); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00526 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StA)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S0 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00526 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition rsetq_h_00526 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition certq_h_00526 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 35 [(5453667406779%positive,0);(351078360865895151%positive,1);(357411547841885946%positive,1);(306064359855454111%positive,1);(357411548697523962%positive,1);(1195563884074911%positive,1);(357411547841884911%positive,1);(1150007538%positive,1);(351078360865896366%positive,1);(19641575789098746%positive,1);(351078361721533167%positive,1);(351078361721534382%positive,1);(19641576644736762%positive,1);(4722827818783%positive,1);(19641576644735727%positive,1);(294402117422%positive,1);(357411547841886126%positive,1);(19641575789097711%positive,1);(357411548697522927%positive,1);(357411548697524142%positive,1);(19641575789098926%positive,1);(306067452231907231%positive,1);(19641576644736942%positive,1);(1195575963670431%positive,1);(5357030642619%positive,0);(351078360865896186%positive,1);(351078361721534202%positive,1)] [5453667406779%positive;351078360865895151%positive;357411547841885946%positive;306064359855454111%positive;357411548697523962%positive;1195563884074911%positive;357411547841884911%positive;1150007538%positive;351078360865896366%positive;19641575789098746%positive;351078361721533167%positive;351078361721534382%positive;19641576644736762%positive;4722827818783%positive;19641576644735727%positive;294402117422%positive;357411547841886126%positive;19641575789097711%positive;357411548697522927%positive;357411548697524142%positive;19641575789098926%positive;306067452231907231%positive;19641576644736942%positive;1195575963670431%positive;5357030642619%positive;351078360865896186%positive;351078361721534202%positive]]
  | StC => [HMeas MLeft 35 [(5453667406779%positive,1);(351078360865895151%positive,2);(306064359855454111%positive,2);(1195563884074911%positive,2);(357411547841884911%positive,2);(351078361721533167%positive,2);(4722827818783%positive,2);(19641576644735727%positive,2);(18419783537%positive,2);(19641575789097711%positive,2);(306067452231905785%positive,2);(1195575963668985%positive,0);(357411548697522927%positive,2);(306067452231907231%positive,2);(75565245100537%positive,2);(1195575963670431%positive,2);(5357030642619%positive,1);(1195563884073465%positive,0);(306064359855452665%positive,2)] [5453667406779%positive;351078360865895151%positive;306064359855454111%positive;1195563884074911%positive;357411547841884911%positive;351078361721533167%positive;4722827818783%positive;19641576644735727%positive;18419783537%positive;19641575789097711%positive;306067452231905785%positive;357411548697522927%positive;1195575963668985%positive;306067452231907231%positive;75565245100537%positive;1195575963670431%positive;5357030642619%positive;1195563884073465%positive;306064359855452665%positive]]
  | StD => [HMeas MRight 35 [(357411547841885946%positive,0);(357411548697523962%positive,1);(1150007538%positive,0);(351078360865896366%positive,2);(19641575789098746%positive,0);(351078361721534382%positive,2);(19641576644736762%positive,1);(294402117422%positive,2);(357411547841886126%positive,2);(18419783537%positive,1);(306067452231905785%positive,1);(1195575963668985%positive,2);(357411548697524142%positive,2);(19641575789098926%positive,2);(19641576644736942%positive,2);(75565245100537%positive,1);(1195563884073465%positive,2);(306064359855452665%positive,1);(351078360865896186%positive,0);(351078361721534202%positive,1)] [357411547841885946%positive;357411548697523962%positive;1150007538%positive;351078360865896366%positive;19641575789098746%positive;351078361721534382%positive;19641576644736762%positive;294402117422%positive;357411547841886126%positive;18419783537%positive;306067452231905785%positive;1195575963668985%positive;357411548697524142%positive;19641575789098926%positive;19641576644736942%positive;75565245100537%positive;1195563884073465%positive;306064359855452665%positive;351078360865896186%positive;351078361721534202%positive]]
  end.

Lemma cqh_h_00526 : iqh tmq_h_00526.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00526 StA 13 2 2 38 20000
                lsetq_h_00526 rsetq_h_00526 certq_h_00526 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 38) 2000 tmq_h_00526); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00527 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StB)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S0 DL StA)
  end.

Definition lsetq_h_00527 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition rsetq_h_00527 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition certq_h_00527 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 37 [(312234334099559403%positive,1);(19067385031905758%positive,1);(348966818560669374%positive,1);(305078164816613854%positive,1);(1207992429007326%positive,1);(76229085033451%positive,1);(85196976747499%positive,1);(4764317814590%positive,1);(5324811046718%positive,1);(4711490319018%positive,1);(312234334099928766%positive,1);(1207991674032606%positive,1);(312234334099928043%positive,1);(20800043155%positive,1);(348966818560668651%positive,1);(305078165571588574%positive,1);(312234334099560126%positive,1);(348966818560300734%positive,1);(348966818560300011%positive,1);(4711489950378%positive,0);(75499210494430%positive,1)] [312234334099559403%positive;19067385031905758%positive;348966818560669374%positive;305078164816613854%positive;1207992429007326%positive;76229085033451%positive;85196976747499%positive;4764317814590%positive;5324811046718%positive;4711490319018%positive;312234334099928766%positive;1207991674032606%positive;312234334099928043%positive;20800043155%positive;348966818560668651%positive;305078165571588574%positive;312234334099560126%positive;348966818560300734%positive;348966818560300011%positive;4711489950378%positive;75499210494430%positive]]
  | StC => [HMeas MLeft 37 [(1136457873%positive,0);(75499210495645%positive,2);(1207991674033821%positive,2);(1207992429008361%positive,2);(19067385031906793%positive,0);(305078165571589789%positive,2);(312234334099559403%positive,1);(290945206557%positive,2);(76229085033451%positive,1);(85196976747499%positive,1);(75499210495465%positive,2);(1207991674033641%positive,2);(19067385031906973%positive,2);(305078165571589609%positive,0);(305078164816615069%positive,2);(312234334099928043%positive,1);(20800043155%positive,1);(348966818560668651%positive,1);(305078164816614889%positive,0);(1207992429008541%positive,2);(348966818560300011%positive,1)] [1136457873%positive;75499210495645%positive;1207991674033821%positive;1207992429008361%positive;305078165571589789%positive;19067385031906793%positive;312234334099559403%positive;290945206557%positive;76229085033451%positive;85196976747499%positive;75499210495465%positive;1207991674033641%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;312234334099928043%positive;20800043155%positive;348966818560668651%positive;305078164816614889%positive;1207992429008541%positive;348966818560300011%positive]]
  | StD => [HMeas MRight 37 [(1136457873%positive,4);(75499210495645%positive,0);(1207991674033821%positive,0);(1207992429008361%positive,2);(19067385031906793%positive,4);(305078165571589789%positive,4);(19067385031905758%positive,4);(348966818560669374%positive,4);(305078164816613854%positive,4);(290945206557%positive,4);(1207992429007326%positive,4);(4764317814590%positive,4);(5324811046718%positive,4);(4711490319018%positive,1);(312234334099928766%positive,4);(75499210495465%positive,2);(1207991674033641%positive,2);(19067385031906973%positive,4);(305078165571589609%positive,4);(305078164816615069%positive,4);(1207991674032606%positive,4);(305078164816614889%positive,4);(305078165571588574%positive,4);(1207992429008541%positive,0);(312234334099560126%positive,4);(348966818560300734%positive,4);(4711489950378%positive,3);(75499210494430%positive,4)] [1136457873%positive;75499210495645%positive;1207991674033821%positive;1207992429008361%positive;305078165571589789%positive;19067385031906793%positive;19067385031905758%positive;348966818560669374%positive;305078164816613854%positive;290945206557%positive;1207992429007326%positive;4764317814590%positive;5324811046718%positive;4711490319018%positive;312234334099928766%positive;75499210495465%positive;1207991674033641%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;1207991674032606%positive;305078164816614889%positive;305078165571588574%positive;1207992429008541%positive;312234334099560126%positive;348966818560300734%positive;4711489950378%positive;75499210494430%positive]]
  end.

Lemma cqh_h_00527 : iqh tmq_h_00527.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00527 StA 13 2 2 38 20000
                lsetq_h_00527 rsetq_h_00527 certq_h_00527 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 38) 2000 tmq_h_00527); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00528 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S0 DL StA)
  end.

Definition lsetq_h_00528 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition rsetq_h_00528 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition certq_h_00528 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 35 [(1207989527598782%positive,2);(1207989527598059%positive,0);(312255777477710302%positive,2);(19067385031905758%positive,2);(348966818560669374%positive,2);(305078164816613854%positive,2);(4713636385450%positive,1);(85196976747499%positive,2);(1207989527967422%positive,2);(5324811046718%positive,2);(312255776722735582%positive,2);(19515985776038366%positive,2);(20800043155%positive,2);(348966818560668651%positive,2);(4714391360170%positive,1);(305078165571588574%positive,2);(1207989527966699%positive,0);(348966818560300734%positive,2);(348966818560300011%positive,2)] [1207989527598782%positive;1207989527598059%positive;312255777477710302%positive;19067385031905758%positive;348966818560669374%positive;305078164816613854%positive;4713636385450%positive;85196976747499%positive;1207989527967422%positive;5324811046718%positive;312255776722735582%positive;19515985776038366%positive;20800043155%positive;348966818560668651%positive;4714391360170%positive;305078165571588574%positive;1207989527966699%positive;348966818560300734%positive;348966818560300011%positive]]
  | StC => [HMeas MLeft 35 [(1136457873%positive,0);(1207989527598059%positive,2);(19067385031906793%positive,0);(305078165571589789%positive,2);(312255776722736617%positive,1);(19515985776039401%positive,1);(312255777477711517%positive,2);(290945206557%positive,2);(85196976747499%positive,1);(19067385031906973%positive,2);(305078165571589609%positive,0);(305078164816615069%positive,2);(20800043155%positive,1);(348966818560668651%positive,1);(312255776722736797%positive,2);(19515985776039581%positive,2);(312255777477711337%positive,1);(305078164816614889%positive,0);(1207989527966699%positive,2);(348966818560300011%positive,1)] [1136457873%positive;1207989527598059%positive;305078165571589789%positive;19067385031906793%positive;312255776722736617%positive;19515985776039401%positive;312255777477711517%positive;290945206557%positive;85196976747499%positive;348966818560300011%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;20800043155%positive;348966818560668651%positive;312255776722736797%positive;19515985776039581%positive;312255777477711337%positive;305078164816614889%positive;1207989527966699%positive]]
  | StD => [HMeas MRight 35 [(1136457873%positive,1);(1207989527598782%positive,1);(312255777477710302%positive,1);(19067385031906793%positive,1);(305078165571589789%positive,1);(19067385031905758%positive,1);(348966818560669374%positive,1);(312255776722736617%positive,1);(19515985776039401%positive,1);(312255777477711517%positive,1);(305078164816613854%positive,1);(4713636385450%positive,0);(290945206557%positive,1);(1207989527967422%positive,1);(5324811046718%positive,1);(312255776722735582%positive,1);(19067385031906973%positive,1);(305078165571589609%positive,1);(305078164816615069%positive,1);(19515985776038366%positive,1);(4714391360170%positive,0);(312255776722736797%positive,1);(19515985776039581%positive,1);(312255777477711337%positive,1);(305078164816614889%positive,1);(305078165571588574%positive,1);(348966818560300734%positive,1)] [1136457873%positive;1207989527598782%positive;312255777477710302%positive;305078165571589789%positive;19067385031906793%positive;19067385031905758%positive;348966818560669374%positive;312255776722736617%positive;19515985776039401%positive;312255777477711517%positive;305078164816613854%positive;4713636385450%positive;290945206557%positive;1207989527967422%positive;5324811046718%positive;312255776722735582%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;19515985776038366%positive;4714391360170%positive;312255776722736797%positive;19515985776039581%positive;312255777477711337%positive;305078164816614889%positive;305078165571588574%positive;348966818560300734%positive]]
  end.

Lemma cqh_h_00528 : iqh tmq_h_00528.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00528 StA 4 2 2 29 20000
                lsetq_h_00528 rsetq_h_00528 certq_h_00528 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00528); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00529 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => Some (mkTrans S0 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Definition lsetq_h_00529 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)])]].

Definition rsetq_h_00529 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00529 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(96506244151734932528823967%positive,0);(395289576045616243870191315455%positive,0);(395289576045508157479134423551%positive,0);(86815892754912382467697151%positive,0);(356478221541895532295539301886%positive,1);(1272356869486641675967%positive,0);(356478221541895532089555020255%positive,0);(395284740351525128597623269855%positive,0);(395289576045616244011751088126%positive,1);(5439425987881799326886367%positive,0);(86815892718883795727810207%positive,0);(6031566472647875933759967%positive,0);(5752220401271370238%positive,1);(79524556147012878315%positive,1);(75385173311315%positive,2);(309059144859841534%positive,3);(395284740351525128803607551486%positive,1);(86815892646826132970577918%positive,1);(86815892646825991410805247%positive,0);(87030815806108789221268990%positive,1);(22469610942466335%positive,0);(395289576045508157620694196222%positive,1);(19316196576851263%positive,0);(1272356869692626299902%positive,1);(1272356869486641938111%positive,0);(96505063562366014931246590%positive,1);(395289576045580215283451559583%positive,0);(86815892754912524027469822%positive,1)]]
  | StC => [HMeas MLeft 46 [(356478221541823474632781987485%positive,1);(5485676198033%positive,0);(395289551557455399771264122857%positive,0);(92035520718772838377%positive,0);(96506244151734932528823967%positive,1);(86890067004746519077322729%positive,0);(395289576045616243870191315455%positive,1);(395289576045508157479134423551%positive,1);(1472550408361321037469%positive,1);(20364736985982012145641%positive,0);(1272356869486641675967%positive,1);(395284740351453071140850237085%positive,1);(5439425987881799326886367%positive,1);(356478221541895532089555020255%positive,1);(356478197192193354998930857961%positive,0);(86815892718883795727810207%positive,1);(79524556147012878315%positive,0);(86890067112832910134214633%positive,0);(6031566472647875933759967%positive,1);(395284740351525128597623269855%positive,1);(395284716001822951506999107561%positive,0);(22469610942466335%positive,1);(87030809861357281091903465%positive,0);(356478221541931561023838879389%positive,1);(19316196576851263%positive,1);(395289551557563486162321014761%positive,0);(1272356869486641938111%positive,1);(395289576045580215283451559583%positive,1);(395284740351561157531907128989%positive,1);(75385173311315%positive,1);(96505057617614506801881065%positive,0);(86815892646825991410805247%positive,1);(86815892754912382467697151%positive,1)] [356478221541823474632781987485%positive;5485676198033%positive;395289551557455399771264122857%positive;92035520718772838377%positive;96506244151734932528823967%positive;86890067004746519077322729%positive;395289576045616243870191315455%positive;395289576045508157479134423551%positive;1472550408361321037469%positive;1272356869486641675967%positive;20364736985982012145641%positive;356478197192193354998930857961%positive;5439425987881799326886367%positive;395284740351453071140850237085%positive;356478221541895532089555020255%positive;86815892718883795727810207%positive;79524556147012878315%positive;86890067112832910134214633%positive;6031566472647875933759967%positive;395284740351525128597623269855%positive;395284716001822951506999107561%positive;22469610942466335%positive;87030809861357281091903465%positive;356478221541931561023838879389%positive;19316196576851263%positive;395289551557563486162321014761%positive;1272356869486641938111%positive;395289576045580215283451559583%positive;395284740351561157531907128989%positive;75385173311315%positive;96505057617614506801881065%positive;86815892646825991410805247%positive;86815892754912382467697151%positive]]
  | StD => [HRank [(356478221541823474632781987485%positive,0);(5752220401271370238%positive,0);(5485676198033%positive,1);(356478221541895532295539301886%positive,0);(395284740351525128803607551486%positive,0);(395289551557455399771264122857%positive,1);(87030815806108789221268990%positive,0);(96505063562366014931246590%positive,0);(92035520718772838377%positive,1);(1272356869692626299902%positive,0);(86890067004746519077322729%positive,1);(1472550408361321037469%positive,0);(309059144859841534%positive,0);(20364736985982012145641%positive,1);(395289576045616244011751088126%positive,0);(395284740351453071140850237085%positive,0);(86815892754912524027469822%positive,0);(356478197192193354998930857961%positive,1);(86890067112832910134214633%positive,1);(86815892646826132970577918%positive,0);(395284716001822951506999107561%positive,1);(87030809861357281091903465%positive,1);(356478221541931561023838879389%positive,0);(395289576045508157620694196222%positive,0);(395289551557563486162321014761%positive,1);(395284740351561157531907128989%positive,0);(96505057617614506801881065%positive,1)]]
  end.

Lemma cqh_h_00529 : iqh tmq_h_00529.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00529 StA 3 4 2 28 20000
                lsetq_h_00529 rsetq_h_00529 certq_h_00529 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00529); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition nghw_05 : list TM :=
  [tmq_h_00500;
   tmq_h_00501;
   tmq_h_00502;
   tmq_h_00503;
   tmq_h_00504;
   tmq_h_00505;
   tmq_h_00506;
   tmq_h_00507;
   tmq_h_00508;
   tmq_h_00509;
   tmq_h_00510;
   tmq_h_00511;
   tmq_h_00512;
   tmq_h_00513;
   tmq_h_00514;
   tmq_h_00515;
   tmq_h_00516;
   tmq_h_00517;
   tmq_h_00518;
   tmq_h_00519;
   tmq_h_00520;
   tmq_h_00521;
   tmq_h_00522;
   tmq_h_00523;
   tmq_h_00524;
   tmq_h_00525;
   tmq_h_00526;
   tmq_h_00527;
   tmq_h_00528;
   tmq_h_00529].

Lemma nghw_05_all : Forall iqh nghw_05.

Proof. unfold nghw_05. exact (Forall_cons _ cqh_h_00500 (Forall_cons _ cqh_h_00501 (Forall_cons _ cqh_h_00502 (Forall_cons _ cqh_h_00503 (Forall_cons _ cqh_h_00504 (Forall_cons _ cqh_h_00505 (Forall_cons _ cqh_h_00506 (Forall_cons _ cqh_h_00507 (Forall_cons _ cqh_h_00508 (Forall_cons _ cqh_h_00509 (Forall_cons _ cqh_h_00510 (Forall_cons _ cqh_h_00511 (Forall_cons _ cqh_h_00512 (Forall_cons _ cqh_h_00513 (Forall_cons _ cqh_h_00514 (Forall_cons _ cqh_h_00515 (Forall_cons _ cqh_h_00516 (Forall_cons _ cqh_h_00517 (Forall_cons _ cqh_h_00518 (Forall_cons _ cqh_h_00519 (Forall_cons _ cqh_h_00520 (Forall_cons _ cqh_h_00521 (Forall_cons _ cqh_h_00522 (Forall_cons _ cqh_h_00523 (Forall_cons _ cqh_h_00524 (Forall_cons _ cqh_h_00525 (Forall_cons _ cqh_h_00526 (Forall_cons _ cqh_h_00527 (Forall_cons _ cqh_h_00528 (Forall_cons _ cqh_h_00529 (Forall_nil iqh))))))))))))))))))))))))))))))). Qed.
