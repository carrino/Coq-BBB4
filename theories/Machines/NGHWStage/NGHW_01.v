(* UNTRUSTED-generated R_QH tier; the Coq kernel re-checks via vm_compute. *)
From Coq Require Import List ZArith Lia.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import NGram NGramHist NGramHistWrap.
From BBB4.Census Require Import TNF_QH.
Import ListNotations.

Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.


Definition tmq_h_00100 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StC)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S0 DR StA)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Definition lsetq_h_00100 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StD,S1);(StA,S1);(StC,S0)]);(S1,[(StA,S1);(StC,S0);(StD,S0);(StC,S1)])];
   [(S0,[(StD,S0);(StA,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StC,S1);(StC,S0)]);(S0,[(StC,S1);(StD,S1);(StA,S1);(StC,S0)])];
   [(S0,[(StD,S0);(StC,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S1);(StC,S0);(StD,S0);(StB,S0)])];
   [(S0,[(StD,S0);(StC,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S1);(StC,S0);(StD,S0);(StC,S1)])];
   [(S1,[(StA,S1);(StC,S0);(StD,S0);(StB,S0)]);(S0,[(StD,S0);(StA,S0)])];
   [(S1,[(StA,S1);(StC,S0);(StD,S0);(StC,S1)]);(S0,[(StD,S0);(StC,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00100 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StA,S1);(StC,S0)]);(S1,[(StC,S0)])]].

Definition certq_h_00100 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(21547646746469607060788137963%positive,0);(329592559599171151408826%positive,1);(309494104947282639%positive,2);(294401250930%positive,3);(4952181351617876715%positive,0);(4710303700818%positive,1);(19310633487430958%positive,2);(79232948558050569470%positive,3)]]
  | StB => []
  | StC => [HRank [(5273480953586813425085356%positive,0);(21547646746469607060788137963%positive,1);(1205837747412268%positive,0);(4952181351617876715%positive,1);(309494104947282639%positive,0)]]
  | StD => [HRank [(329592559599171151408826%positive,0);(294401250930%positive,0);(1205837747412268%positive,1);(4710303700818%positive,0);(19310633487430958%positive,1);(79232948558050569470%positive,2);(5273480953586813425085356%positive,3)]]
  end.

Lemma cqh_h_00100 : iqh tmq_h_00100.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00100 StB 1 4 2 26 20000
                lsetq_h_00100 rsetq_h_00100 certq_h_00100 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00100); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00101 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StC)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S0 DR StA)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Definition lsetq_h_00101 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StA,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StC,S1)]);(S1,[(StA,S1);(StD,S1)])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[(StA,S0)])];
   [(S0,[(StD,S0);(StD,S0)]);(S1,[(StA,S1);(StD,S1)])];
   [(S1,[(StA,S1);(StD,S1)]);(S0,[(StD,S0);(StD,S0)])]].

Definition rsetq_h_00101 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])]].

Definition certq_h_00101 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(19654839503845051%positive,0);(75565448417999%positive,1);(18416047730%positive,2);(75561070129899%positive,0);(18420569938%positive,1);(294455600942%positive,2)]]
  | StB => []
  | StC => [HRank [(75565446845692%positive,0);(19654839503845051%positive,1);(75565448417999%positive,2);(294729243948%positive,0);(75561070129899%positive,1)]]
  | StD => [HRank [(18416047730%positive,0);(294729243948%positive,1);(18420569938%positive,0);(294455600942%positive,1);(75565446845692%positive,2)]]
  end.

Lemma cqh_h_00101 : iqh tmq_h_00101.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00101 StB 1 2 2 26 20000
                lsetq_h_00101 rsetq_h_00101 certq_h_00101 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00101); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00102 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StC)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DR StA)
  | StD, S1 => Some (mkTrans S0 DL StC)
  end.

Definition lsetq_h_00102 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S1);(StC,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S0,[(StA,S0)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StA,S1);(StC,S0)])]].

Definition rsetq_h_00102 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])]].

Definition certq_h_00102 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(4801430049771%positive,0);(4722360538362%positive,1);(19666662489224171%positive,0);(75560078234874%positive,1);(19654774019749566%positive,2);(75560079717071%positive,3);(75564305511147%positive,0);(18399598418%positive,1);(4798527592126%positive,2);(4722362020559%positive,3);(18416113266%positive,4);(294657812270%positive,2)]]
  | StB => []
  | StC => [HRank [(4722362021804%positive,0);(4801430049771%positive,1);(75560079717071%positive,0);(294393700140%positive,0);(75564305511147%positive,1);(75560079718316%positive,0);(19666662489224171%positive,1);(4722362020559%positive,0)]]
  | StD => [HRank [(4722360538362%positive,0);(18399598418%positive,0);(294657812270%positive,1);(4722362021804%positive,2);(75560078234874%positive,0);(19654774019749566%positive,1);(18416113266%positive,0);(294393700140%positive,1);(4798527592126%positive,1);(75560079718316%positive,2)]]
  end.

Lemma cqh_h_00102 : iqh tmq_h_00102.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00102 StB 1 2 2 26 20000
                lsetq_h_00102 rsetq_h_00102 certq_h_00102 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00102); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00103 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StC)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DR StA)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00103 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StA,S0)]);(S0,[])];
   [(S0,[(StC,S1);(StD,S1)]);(S1,[(StA,S1);(StD,S0)])];
   [(S1,[(StA,S1);(StD,S0)]);(S0,[(StA,S0)])];
   [(S1,[(StA,S1);(StD,S0)]);(S0,[(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S1)])]].

Definition rsetq_h_00103 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])]].

Definition certq_h_00103 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(75561154073323%positive,0);(18421028690%positive,1);(294460847406%positive,2);(75565564327166%positive,3);(75565565866703%positive,0);(18416113266%positive,1)]]
  | StB => []
  | StC => [HRank [(294736584492%positive,0);(75561154073323%positive,1);(19654839587788476%positive,0);(75565565866703%positive,1)]]
  | StD => [HRank [(18421028690%positive,0);(294460847406%positive,1);(75565564327166%positive,2);(18416113266%positive,0);(294736584492%positive,1);(19654839587788476%positive,3)]]
  end.

Lemma cqh_h_00103 : iqh tmq_h_00103.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00103 StB 1 2 2 26 20000
                lsetq_h_00103 rsetq_h_00103 certq_h_00103 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00103); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00104 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StC)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DR StA)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Definition lsetq_h_00104 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StD,S1);(StA,S1);(StC,S0)]);(S1,[(StA,S1);(StD,S1);(StD,S0);(StC,S1)])];
   [(S1,[(StA,S1);(StD,S1);(StD,S0);(StB,S0)]);(S1,[(StD,S0);(StA,S0)])];
   [(S1,[(StA,S1);(StD,S1);(StD,S0);(StC,S1)]);(S1,[(StD,S0);(StC,S1);(StD,S1);(StA,S1)])];
   [(S1,[(StD,S0);(StA,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1);(StC,S0)]);(S0,[(StC,S1);(StD,S1);(StA,S1);(StC,S0)])];
   [(S1,[(StD,S0);(StC,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S1);(StD,S1);(StD,S0);(StB,S0)])];
   [(S1,[(StD,S0);(StC,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S1);(StD,S1);(StD,S0);(StC,S1)])]].

Definition rsetq_h_00104 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StA,S1);(StC,S0)]);(S1,[(StC,S0)])]].

Definition certq_h_00104 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(4952182726007411435%positive,0);(4710303700818%positive,1);(19310719386776878%positive,2);(21547646769528038253107793899%positive,0);(329592559621161383964351%positive,1);(309494104947290831%positive,2);(294401316466%positive,3);(79232948626811989246%positive,3)]]
  | StB => []
  | StC => [HRank [(5273480953938657148070908%positive,0);(21547646769528038253107793899%positive,1);(329592559621161383964351%positive,2);(309494104947290831%positive,3);(1205837747412780%positive,0);(4952182726007411435%positive,1)]]
  | StD => [HRank [(4710303700818%positive,0);(19310719386776878%positive,1);(79232948626811989246%positive,2);(5273480953938657148070908%positive,3);(294401316466%positive,0);(1205837747412780%positive,1)]]
  end.

Lemma cqh_h_00104 : iqh tmq_h_00104.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00104 StB 1 4 2 26 20000
                lsetq_h_00104 rsetq_h_00104 certq_h_00104 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00104); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00105 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StC)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00105 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition rsetq_h_00105 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition certq_h_00105 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 35 [(5307768541866%positive,1);(347849918707528158%positive,2);(323514226923467755%positive,2);(19087146765119966%positive,2);(1263727430424254%positive,2);(323511134547014635%positive,2);(1263715350828734%positive,2);(19087145909481950%positive,2);(341516731731538398%positive,2);(341516732587176414%positive,2);(1263727430423531%positive,0);(1263715350828011%positive,0);(18416111347%positive,2);(5211131777706%positive,1);(323514226923468478%positive,2);(347849919563166174%positive,2);(323511134547015358%positive,2);(75289427112939%positive,2);(4705589194558%positive,2)] [5307768541866%positive;347849918707528158%positive;323514226923467755%positive;19087146765119966%positive;1263727430424254%positive;323511134547014635%positive;1263715350828734%positive;19087145909481950%positive;341516731731538398%positive;341516732587176414%positive;1263727430423531%positive;1263715350828011%positive;18416111347%positive;5211131777706%positive;323514226923468478%positive;347849919563166174%positive;323511134547015358%positive;75289427112939%positive;4705589194558%positive]]
  | StC => [HMeas MRight 35 [(341516732587177449%positive,1);(19087145909482985%positive,0);(323514226923467755%positive,1);(1149729265%positive,0);(347849919563167389%positive,2);(323511134547014635%positive,1);(294330785565%positive,2);(347849918707529373%positive,2);(341516731731539433%positive,0);(347849919563167209%positive,1);(1263727430423531%positive,2);(19087145909483165%positive,2);(19087146765121181%positive,2);(1263715350828011%positive,2);(18416111347%positive,1);(347849918707529193%positive,0);(19087146765121001%positive,1);(75289427112939%positive,1);(341516731731539613%positive,2);(341516732587177629%positive,2)] [341516732587177449%positive;19087145909482985%positive;323514226923467755%positive;1149729265%positive;347849918707529373%positive;347849919563167389%positive;323511134547014635%positive;294330785565%positive;341516731731539433%positive;347849919563167209%positive;1263727430423531%positive;19087145909483165%positive;19087146765121181%positive;1263715350828011%positive;18416111347%positive;347849918707529193%positive;19087146765121001%positive;75289427112939%positive;341516731731539613%positive;341516732587177629%positive]]
  | StD => [HMeas MLeft 35 [(5307768541866%positive,0);(341516732587177449%positive,1);(347849918707528158%positive,1);(19087145909482985%positive,1);(1149729265%positive,1);(19087146765119966%positive,1);(1263727430424254%positive,1);(347849919563167389%positive,1);(294330785565%positive,1);(347849918707529373%positive,1);(1263715350828734%positive,1);(341516731731539433%positive,1);(347849919563167209%positive,1);(19087145909481950%positive,1);(341516731731538398%positive,1);(341516732587176414%positive,1);(19087145909483165%positive,1);(19087146765121181%positive,1);(347849918707529193%positive,1);(5211131777706%positive,0);(19087146765121001%positive,1);(323514226923468478%positive,1);(347849919563166174%positive,1);(323511134547015358%positive,1);(4705589194558%positive,1);(341516731731539613%positive,1);(341516732587177629%positive,1)] [5307768541866%positive;341516732587177449%positive;347849918707528158%positive;19087145909482985%positive;1149729265%positive;19087146765119966%positive;1263727430424254%positive;347849919563167389%positive;294330785565%positive;347849918707529373%positive;1263715350828734%positive;341516731731539433%positive;347849919563167209%positive;19087145909481950%positive;341516731731538398%positive;341516732587176414%positive;19087145909483165%positive;19087146765121181%positive;347849918707529193%positive;5211131777706%positive;19087146765121001%positive;323514226923468478%positive;347849919563166174%positive;323511134547015358%positive;4705589194558%positive;341516731731539613%positive;341516732587177629%positive]]
  end.

Lemma cqh_h_00105 : iqh tmq_h_00105.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00105 StA 18 2 2 43 20000
                lsetq_h_00105 rsetq_h_00105 certq_h_00105 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 43) 2000 tmq_h_00105); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00106 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StC)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => Some (mkTrans S0 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Definition lsetq_h_00106 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)])]].

Definition rsetq_h_00106 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00106 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(96506244151734932528823967%positive,0);(395289576045616243870191315455%positive,0);(395289576045508157479134423551%positive,0);(1272356869486641675967%positive,0);(86815892754912382467697151%positive,0);(356478221541895532295539301886%positive,1);(356478221541895532089555020255%positive,0);(395284740351525128597623269855%positive,0);(395289576045616244011751088126%positive,1);(5439425987881799326886367%positive,0);(86815892718883795727810207%positive,0);(6031566472647875933759967%positive,0);(5752220401271370238%positive,1);(79524556147012878315%positive,1);(75385173311315%positive,2);(309059144859841534%positive,3);(395284740351525128803607551486%positive,1);(86815892646826132970577918%positive,1);(86815892646825991410805247%positive,0);(87030815806108789221268990%positive,1);(22469610942466335%positive,0);(395289576045508157620694196222%positive,1);(19316196576851263%positive,0);(1272356869692626299902%positive,1);(96505063562366014931246590%positive,1);(395289576045580215283451559583%positive,0);(86815892754912524027469822%positive,1)]]
  | StC => [HMeas MLeft 45 [(356478221541823474632781987485%positive,1);(5485676198033%positive,0);(395289551557455399771264122857%positive,0);(92035520718772838377%positive,0);(96506244151734932528823967%positive,1);(86890067004746519077322729%positive,0);(395289576045616243870191315455%positive,1);(395289576045508157479134423551%positive,1);(1472550408361321037469%positive,1);(1272356869486641675967%positive,1);(20364736985982012145641%positive,0);(395284740351453071140850237085%positive,1);(5439425987881799326886367%positive,1);(356478221541895532089555020255%positive,1);(356478197192193354998930857961%positive,0);(86815892718883795727810207%positive,1);(79524556147012878315%positive,0);(86890067112832910134214633%positive,0);(6031566472647875933759967%positive,1);(395284740351525128597623269855%positive,1);(395284716001822951506999107561%positive,0);(22469610942466335%positive,1);(87030809861357281091903465%positive,0);(356478221541931561023838879389%positive,1);(19316196576851263%positive,1);(395289551557563486162321014761%positive,0);(395289576045580215283451559583%positive,1);(395284740351561157531907128989%positive,1);(75385173311315%positive,1);(96505057617614506801881065%positive,0);(86815892646825991410805247%positive,1);(86815892754912382467697151%positive,1)] [356478221541823474632781987485%positive;5485676198033%positive;395289551557455399771264122857%positive;92035520718772838377%positive;96506244151734932528823967%positive;86890067004746519077322729%positive;395289576045616243870191315455%positive;395289576045508157479134423551%positive;1472550408361321037469%positive;1272356869486641675967%positive;20364736985982012145641%positive;356478197192193354998930857961%positive;395284740351453071140850237085%positive;5439425987881799326886367%positive;356478221541895532089555020255%positive;86815892718883795727810207%positive;79524556147012878315%positive;86890067112832910134214633%positive;6031566472647875933759967%positive;395284740351525128597623269855%positive;395284716001822951506999107561%positive;22469610942466335%positive;87030809861357281091903465%positive;356478221541931561023838879389%positive;19316196576851263%positive;395289551557563486162321014761%positive;395289576045580215283451559583%positive;395284740351561157531907128989%positive;75385173311315%positive;96505057617614506801881065%positive;86815892646825991410805247%positive;86815892754912382467697151%positive]]
  | StD => [HRank [(356478221541823474632781987485%positive,0);(5752220401271370238%positive,0);(5485676198033%positive,1);(356478221541895532295539301886%positive,0);(395284740351525128803607551486%positive,0);(395289551557455399771264122857%positive,1);(87030815806108789221268990%positive,0);(96505063562366014931246590%positive,0);(92035520718772838377%positive,1);(1272356869692626299902%positive,0);(86890067004746519077322729%positive,1);(1472550408361321037469%positive,0);(309059144859841534%positive,0);(20364736985982012145641%positive,1);(395289576045616244011751088126%positive,0);(395284740351453071140850237085%positive,0);(86815892754912524027469822%positive,0);(356478197192193354998930857961%positive,1);(86890067112832910134214633%positive,1);(86815892646826132970577918%positive,0);(395284716001822951506999107561%positive,1);(87030809861357281091903465%positive,1);(356478221541931561023838879389%positive,0);(395289576045508157620694196222%positive,0);(395289551557563486162321014761%positive,1);(395284740351561157531907128989%positive,0);(96505057617614506801881065%positive,1)]]
  end.

Lemma cqh_h_00106 : iqh tmq_h_00106.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00106 StA 3 4 2 28 20000
                lsetq_h_00106 rsetq_h_00106 certq_h_00106 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00106); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00107 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StA)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00107 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00107 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition certq_h_00107 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 37 [(314652163455309742%positive,4);(356852788752799647%positive,4);(5445141436191%positive,4);(75791334364922%positive,2);(1212666493260527%positive,4);(4709410501563%positive,1);(356852788753168287%positive,4);(314652164210284282%positive,4);(75791334363887%positive,4);(321809154152691615%positive,4);(1212665738286842%positive,2);(1172076690%positive,4);(19665759941678842%positive,4);(1212666493261562%positive,2);(314652164210283247%positive,4);(4709410132923%positive,3);(321809154152322975%positive,4);(1212665738285807%positive,4);(19665759941677807%positive,4);(314652163455309562%positive,4);(75791334365102%positive,0);(4910418007839%positive,4);(314652164210284462%positive,4);(314652163455308527%positive,4);(1212665738287022%positive,0);(19665759941679022%positive,4);(1212666493261742%positive,0);(300075682094%positive,4)] [314652163455309742%positive;356852788752799647%positive;5445141436191%positive;75791334364922%positive;1212666493260527%positive;4709410501563%positive;314652164210284282%positive;75791334363887%positive;321809154152691615%positive;1212665738286842%positive;1172076690%positive;19665759941678842%positive;1212666493261562%positive;314652164210283247%positive;4709410132923%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;314652163455309562%positive;75791334365102%positive;4910418007839%positive;314652164210284462%positive;1212666493261742%positive;314652163455308527%positive;1212665738287022%positive;19665759941679022%positive;356852788753168287%positive;300075682094%positive]]
  | StC => [HMeas MRight 37 [(78566688125433%positive,1);(356852788752799647%positive,1);(321809154152690169%positive,1);(5445141436191%positive,1);(1212666493260527%positive,1);(321809154152321529%positive,1);(4709410501563%positive,1);(356852788753168287%positive,1);(75791334363887%positive,1);(21270083729%positive,1);(321809154152691615%positive,1);(314652164210283247%positive,1);(4709410132923%positive,0);(87122262979065%positive,1);(321809154152322975%positive,1);(1212665738285807%positive,1);(19665759941677807%positive,1);(356852788753166841%positive,1);(4910418007839%positive,1);(314652163455308527%positive,1);(356852788752798201%positive,1)] [78566688125433%positive;356852788752799647%positive;321809154152690169%positive;5445141436191%positive;1212666493260527%positive;321809154152321529%positive;4709410501563%positive;75791334363887%positive;21270083729%positive;321809154152691615%positive;314652164210283247%positive;4709410132923%positive;87122262979065%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;356852788753166841%positive;4910418007839%positive;314652163455308527%positive;356852788752798201%positive;356852788753168287%positive]]
  | StD => [HMeas MLeft 37 [(314652163455309742%positive,2);(78566688125433%positive,1);(321809154152690169%positive,1);(75791334364922%positive,2);(321809154152321529%positive,1);(314652164210284282%positive,0);(21270083729%positive,1);(1212665738286842%positive,2);(1172076690%positive,0);(19665759941678842%positive,0);(1212666493261562%positive,2);(87122262979065%positive,1);(314652163455309562%positive,0);(75791334365102%positive,2);(356852788753166841%positive,1);(314652164210284462%positive,2);(1212665738287022%positive,2);(19665759941679022%positive,2);(356852788752798201%positive,1);(1212666493261742%positive,2);(300075682094%positive,2)] [314652163455309742%positive;78566688125433%positive;321809154152690169%positive;75791334364922%positive;321809154152321529%positive;314652164210284282%positive;21270083729%positive;1212665738286842%positive;1172076690%positive;19665759941678842%positive;1212666493261562%positive;87122262979065%positive;314652163455309562%positive;75791334365102%positive;356852788753166841%positive;314652164210284462%positive;1212665738287022%positive;19665759941679022%positive;356852788752798201%positive;1212666493261742%positive;300075682094%positive]]
  end.

Lemma cqh_h_00107 : iqh tmq_h_00107.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00107 StA 9 2 2 34 20000
                lsetq_h_00107 rsetq_h_00107 certq_h_00107 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00107); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00108 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StA)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S0 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00108 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S1,[(StA,S1);(StC,S1)])];
   [(S1,[(StA,S1);(StC,S1)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition rsetq_h_00108 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition certq_h_00108 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 48 [(357411547841885946%positive,4);(351078360865895151%positive,4);(1396138856798126%positive,0);(306064359855454111%positive,4);(4670218605499%positive,1);(306064355677927327%positive,4);(76724903465711%positive,4);(306067448056411067%positive,1);(357411547841884911%positive,4);(1150007538%positive,4);(351078360865896366%positive,4);(76724903466926%positive,0);(19641575789098746%positive,4);(4722827818783%positive,4);(294402117422%positive,4);(4722566723359%positive,4);(357411547841886126%positive,4);(19641575789097711%positive,4);(351078365024605946%positive,2);(306064355679957947%positive,3);(19641575789098926%positive,4);(1371399845172986%positive,2);(306067452231907231%positive,4);(306067448054380447%positive,4);(357411552000595706%positive,2);(1396138856797946%positive,2);(1371399845171951%positive,4);(4670171419579%positive,3);(351078365024606126%positive,0);(351078365024604911%positive,4);(351078360865896186%positive,4);(1396138856796911%positive,4);(19641579947807471%positive,4);(19641579947808506%positive,2);(19641579947808686%positive,0);(1371399845173166%positive,0);(76724903466746%positive,2);(357411552000595886%positive,0);(357411552000594671%positive,4)] [357411547841885946%positive;351078360865895151%positive;1396138856798126%positive;306064359855454111%positive;4670218605499%positive;306064355677927327%positive;76724903465711%positive;306067448056411067%positive;357411547841884911%positive;1150007538%positive;351078360865896366%positive;76724903466926%positive;19641575789098746%positive;4722827818783%positive;294402117422%positive;4722566723359%positive;357411547841886126%positive;19641575789097711%positive;351078365024605946%positive;306064355679957947%positive;19641575789098926%positive;1371399845172986%positive;306067452231907231%positive;306067448054380447%positive;357411552000595706%positive;1396138856797946%positive;1371399845171951%positive;4670171419579%positive;351078365024606126%positive;351078365024604911%positive;351078360865896186%positive;1396138856796911%positive;19641579947807471%positive;19641579947808506%positive;19641579947808686%positive;1371399845173166%positive;76724903466746%positive;357411552000595886%positive;357411552000594671%positive]]
  | StC => [HMeas MLeft 48 [(351078360865895151%positive,1);(306064359855454111%positive,1);(4670218605499%positive,1);(306064355677927327%positive,1);(76724903465711%positive,1);(306067448056411067%positive,1);(357411547841884911%positive,1);(4722827818783%positive,1);(4722566723359%positive,1);(306067448054379001%positive,1);(18419783537%positive,1);(19641575789097711%positive,1);(306067452231905785%positive,1);(306064355679957947%positive,0);(306067452231907231%positive,1);(306067448054380447%positive,1);(75561067573753%positive,1);(75565245100537%positive,1);(1371399845171951%positive,1);(4670171419579%positive,0);(306064355677925881%positive,1);(351078365024604911%positive,1);(1396138856796911%positive,1);(19641579947807471%positive,1);(306064359855452665%positive,1);(357411552000594671%positive,1)] [351078360865895151%positive;306064359855454111%positive;4670218605499%positive;306064355677927327%positive;76724903465711%positive;306067448056411067%positive;357411547841884911%positive;4722827818783%positive;4722566723359%positive;306067448054379001%positive;18419783537%positive;19641575789097711%positive;306067452231905785%positive;306064355679957947%positive;306067452231907231%positive;306067448054380447%positive;75561067573753%positive;75565245100537%positive;1371399845171951%positive;4670171419579%positive;306064355677925881%positive;351078365024604911%positive;1396138856796911%positive;19641579947807471%positive;306064359855452665%positive;357411552000594671%positive]]
  | StD => [HMeas MRight 48 [(357411547841885946%positive,0);(1396138856798126%positive,2);(1150007538%positive,0);(351078360865896366%positive,2);(76724903466926%positive,2);(19641575789098746%positive,0);(294402117422%positive,2);(357411547841886126%positive,2);(306067448054379001%positive,1);(18419783537%positive,1);(306067452231905785%positive,1);(351078365024605946%positive,2);(19641575789098926%positive,2);(1371399845172986%positive,2);(357411552000595706%positive,2);(75561067573753%positive,1);(75565245100537%positive,1);(1396138856797946%positive,2);(306064355677925881%positive,1);(351078365024606126%positive,2);(351078360865896186%positive,0);(19641579947808506%positive,2);(19641579947808686%positive,2);(306064359855452665%positive,1);(1371399845173166%positive,2);(76724903466746%positive,2);(357411552000595886%positive,2)] [357411547841885946%positive;1396138856798126%positive;1150007538%positive;351078360865896366%positive;76724903466926%positive;19641575789098746%positive;294402117422%positive;357411547841886126%positive;306067448054379001%positive;18419783537%positive;306067452231905785%positive;351078365024605946%positive;19641575789098926%positive;1371399845172986%positive;357411552000595706%positive;75561067573753%positive;75565245100537%positive;1396138856797946%positive;306064355677925881%positive;351078365024606126%positive;351078360865896186%positive;19641579947808506%positive;19641579947808686%positive;306064359855452665%positive;1371399845173166%positive;76724903466746%positive;357411552000595886%positive]]
  end.

Lemma cqh_h_00108 : iqh tmq_h_00108.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00108 StA 9 2 2 34 20000
                lsetq_h_00108 rsetq_h_00108 certq_h_00108 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00108); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00109 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StA)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S0 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00109 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition rsetq_h_00109 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition certq_h_00109 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 37 [(357411547841885946%positive,4);(351078360865895151%positive,4);(1396138856798126%positive,0);(306064359855454111%positive,4);(4670218605499%positive,1);(306064355677927327%positive,4);(76724903465711%positive,4);(357411547841884911%positive,4);(1150007538%positive,4);(351078360865896366%positive,4);(76724903466926%positive,0);(19641575789098746%positive,4);(4722827818783%positive,4);(294402117422%positive,4);(4722566723359%positive,4);(357411547841886126%positive,4);(19641575789097711%positive,4);(19641575789098926%positive,4);(1371399845172986%positive,2);(306067452231907231%positive,4);(306067448054380447%positive,4);(1396138856797946%positive,2);(1371399845171951%positive,4);(4670171419579%positive,3);(351078360865896186%positive,4);(1396138856796911%positive,4);(1371399845173166%positive,0);(76724903466746%positive,2)] [357411547841885946%positive;351078360865895151%positive;1396138856798126%positive;306064359855454111%positive;4670218605499%positive;306064355677927327%positive;76724903465711%positive;357411547841884911%positive;1150007538%positive;351078360865896366%positive;76724903466926%positive;19641575789098746%positive;4722827818783%positive;294402117422%positive;4722566723359%positive;357411547841886126%positive;19641575789097711%positive;19641575789098926%positive;1371399845172986%positive;306067452231907231%positive;306067448054380447%positive;1396138856797946%positive;1371399845171951%positive;4670171419579%positive;351078360865896186%positive;1396138856796911%positive;1371399845173166%positive;76724903466746%positive]]
  | StC => [HMeas MLeft 37 [(351078360865895151%positive,1);(306064359855454111%positive,1);(4670218605499%positive,1);(306064355677927327%positive,1);(76724903465711%positive,1);(357411547841884911%positive,1);(4722827818783%positive,1);(4722566723359%positive,1);(306067448054379001%positive,1);(18419783537%positive,1);(19641575789097711%positive,1);(306067452231905785%positive,1);(306067452231907231%positive,1);(306067448054380447%positive,1);(75561067573753%positive,1);(75565245100537%positive,1);(1371399845171951%positive,1);(4670171419579%positive,0);(306064355677925881%positive,1);(306064359855452665%positive,1);(1396138856796911%positive,1)] [351078360865895151%positive;306064359855454111%positive;4670218605499%positive;306064355677927327%positive;76724903465711%positive;357411547841884911%positive;4722827818783%positive;4722566723359%positive;306067448054379001%positive;18419783537%positive;19641575789097711%positive;306067452231905785%positive;306067452231907231%positive;306067448054380447%positive;75561067573753%positive;75565245100537%positive;1371399845171951%positive;4670171419579%positive;306064355677925881%positive;1396138856796911%positive;306064359855452665%positive]]
  | StD => [HMeas MRight 37 [(357411547841885946%positive,0);(1396138856798126%positive,2);(1150007538%positive,0);(351078360865896366%positive,2);(76724903466926%positive,2);(19641575789098746%positive,0);(294402117422%positive,2);(357411547841886126%positive,2);(306067448054379001%positive,1);(18419783537%positive,1);(306067452231905785%positive,1);(19641575789098926%positive,2);(1371399845172986%positive,2);(75561067573753%positive,1);(75565245100537%positive,1);(1396138856797946%positive,2);(306064355677925881%positive,1);(351078360865896186%positive,0);(306064359855452665%positive,1);(1371399845173166%positive,2);(76724903466746%positive,2)] [357411547841885946%positive;1396138856798126%positive;1150007538%positive;351078360865896366%positive;76724903466926%positive;19641575789098746%positive;294402117422%positive;357411547841886126%positive;306067448054379001%positive;18419783537%positive;306067452231905785%positive;19641575789098926%positive;1371399845172986%positive;75561067573753%positive;75565245100537%positive;1396138856797946%positive;306064355677925881%positive;351078360865896186%positive;306064359855452665%positive;1371399845173166%positive;76724903466746%positive]]
  end.

Lemma cqh_h_00109 : iqh tmq_h_00109.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00109 StA 9 2 2 34 20000
                lsetq_h_00109 rsetq_h_00109 certq_h_00109 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00109); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00110 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StB)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StB)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00110 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StC,S1)]);(S1,[(StD,S1);(StB,S1)])];
   [(S1,[(StD,S1);(StB,S1)]);(S1,[(StC,S0)])];
   [(S1,[(StD,S1);(StB,S1)]);(S1,[(StC,S0);(StC,S1)])]].

Definition rsetq_h_00110 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StD,S1)]);(S1,[(StB,S1);(StC,S0)])];
   [(S0,[(StD,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StC,S0)]);(S0,[(StC,S1);(StD,S1)])];
   [(S1,[(StB,S1);(StC,S0)]);(S0,[(StD,S0)])]].

Definition certq_h_00110 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 21 [(294653722426%positive,1);(1254231578245098%positive,1);(20067708552181246%positive,2);(4899341956606%positive,2);(359526531203069930%positive,1);(21429450898%positive,2);(75769660666591%positive,2);(76682254447327%positive,2);(20067709290018794%positive,1);(22470407947810794%positive,1);(18412969331%positive,0);(359526530465232382%positive,2);(314090518117446367%positive,2);(87775030900222%positive,2)] [4899341956606%positive;22470407947810794%positive;18412969331%positive;359526530465232382%positive;21429450898%positive;359526531203069930%positive;294653722426%positive;314090518117446367%positive;1254231578245098%positive;76682254447327%positive;75769660666591%positive;87775030900222%positive;20067708552181246%positive;20067709290018794%positive]]
  | StC => [HRank [(299540056365%positive,0);(75769660666591%positive,0);(314090518855284397%positive,0);(76682254447327%positive,0);(75770398503853%positive,0);(4735397524397%positive,0);(18412969331%positive,1);(314090518117446367%positive,0);(19630657176073901%positive,0)]]
  | StD => [HMeas MLeft 21 [(294653722426%positive,1);(1254231578245098%positive,1);(20067708552181246%positive,1);(299540056365%positive,1);(4899341956606%positive,1);(359526531203069930%positive,1);(21429450898%positive,0);(314090518855284397%positive,1);(20067709290018794%positive,1);(75770398503853%positive,1);(22470407947810794%positive,1);(359526530465232382%positive,1);(4735397524397%positive,1);(19630657176073901%positive,1);(87775030900222%positive,1)] [4899341956606%positive;22470407947810794%positive;359526530465232382%positive;75770398503853%positive;21429450898%positive;359526531203069930%positive;294653722426%positive;4735397524397%positive;1254231578245098%positive;19630657176073901%positive;87775030900222%positive;314090518855284397%positive;20067708552181246%positive;20067709290018794%positive;299540056365%positive]]
  end.

Lemma cqh_h_00110 : iqh tmq_h_00110.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00110 StA 0 2 2 25 20000
                lsetq_h_00110 rsetq_h_00110 certq_h_00110 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00110); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00111 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StB)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StB)
  | StD, S0 => Some (mkTrans S0 DR StB)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00111 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S0)]);(S1,[(StD,S1);(StB,S1)])];
   [(S1,[(StC,S0);(StC,S1)]);(S1,[(StD,S1);(StB,S1)])];
   [(S1,[(StD,S1);(StB,S1)]);(S1,[(StC,S0)])];
   [(S1,[(StD,S1);(StB,S1)]);(S1,[(StC,S0);(StC,S1)])]].

Definition rsetq_h_00111 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S0)]);(S0,[])];
   [(S0,[(StB,S0);(StD,S0)]);(S0,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S1)]);(S1,[(StB,S1);(StC,S0)])];
   [(S1,[(StB,S1);(StC,S0)]);(S0,[(StB,S0);(StD,S0)])];
   [(S1,[(StB,S1);(StC,S0)]);(S0,[(StC,S1);(StD,S1)])]].

Definition certq_h_00111 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 23 [(294607443739%positive,0);(75220642689946%positive,1);(320682984416999402%positive,1);(20042686273681386%positive,1);(18945038460744415%positive,2);(359526531203069930%positive,1);(320682983679161854%positive,2);(21429450898%positive,2);(78291743110654%positive,2);(76682254447327%positive,2);(22470407947810794%positive,1);(359526530465232382%positive,2);(314090518117446367%positive,2);(87775030900222%positive,2)] [22470407947810794%positive;294607443739%positive;359526530465232382%positive;75220642689946%positive;320682983679161854%positive;18945038460744415%positive;21429450898%positive;359526531203069930%positive;314090518117446367%positive;78291743110654%positive;320682984416999402%positive;87775030900222%positive;20042686273681386%positive;76682254447327%positive]]
  | StC => [HRank [(18945039198581165%positive,0);(1184064697528749%positive,0);(75219902230969%positive,1);(18394877393%positive,2);(294607443739%positive,3);(299540056365%positive,0);(18945038460744415%positive,0);(314090518855284397%positive,0);(76682254447327%positive,0);(314090518117446367%positive,0);(19630657176073901%positive,0)]]
  | StD => [HMeas MLeft 23 [(18394877393%positive,1);(75220642689946%positive,1);(320682984416999402%positive,1);(20042686273681386%positive,1);(299540056365%positive,1);(359526531203069930%positive,1);(18945039198581165%positive,1);(320682983679161854%positive,1);(21429450898%positive,0);(78291743110654%positive,1);(314090518855284397%positive,1);(22470407947810794%positive,1);(359526530465232382%positive,1);(1184064697528749%positive,1);(75219902230969%positive,0);(19630657176073901%positive,1);(87775030900222%positive,1)] [18394877393%positive;22470407947810794%positive;359526530465232382%positive;75220642689946%positive;320682983679161854%positive;1184064697528749%positive;75219902230969%positive;21429450898%positive;359526531203069930%positive;78291743110654%positive;320682984416999402%positive;19630657176073901%positive;87775030900222%positive;314090518855284397%positive;18945039198581165%positive;20042686273681386%positive;299540056365%positive]]
  end.

Lemma cqh_h_00111 : iqh tmq_h_00111.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00111 StA 0 2 2 25 20000
                lsetq_h_00111 rsetq_h_00111 certq_h_00111 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00111); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00112 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StB)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StB)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00112 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StC,S1)]);(S1,[(StD,S1);(StB,S1)])];
   [(S1,[(StD,S1);(StB,S1)]);(S1,[(StC,S0)])];
   [(S1,[(StD,S1);(StB,S1)]);(S1,[(StC,S0);(StC,S1)])]].

Definition rsetq_h_00112 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[])];
   [(S0,[(StC,S1);(StD,S1)]);(S1,[(StB,S1);(StC,S0)])];
   [(S0,[(StC,S1);(StD,S1)]);(S1,[(StB,S1);(StD,S1)])];
   [(S1,[(StB,S1);(StC,S0)]);(S0,[(StC,S1);(StD,S1)])];
   [(S1,[(StB,S1);(StD,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition certq_h_00112 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 29 [(4739692492463%positive,0);(4714459558890%positive,31);(18412975475%positive,30);(294607486782%positive,28);(359526531203069930%positive,31);(1213489317509087%positive,32);(323519724416661482%positive,31);(21429450898%positive,32);(76682254447327%positive,32);(22470407947810794%positive,31);(87677370725087%positive,32);(20219982523660266%positive,31);(323519723678823934%positive,32);(359526530465232382%positive,32);(314090518117446367%positive,32);(359126514391151327%positive,32);(87775030900222%positive,32);(78984306587134%positive,32);(75839117981359%positive,0)] [4739692492463%positive;4714459558890%positive;18412975475%positive;294607486782%positive;359526531203069930%positive;1213489317509087%positive;323519724416661482%positive;21429450898%positive;76682254447327%positive;22470407947810794%positive;87677370725087%positive;20219982523660266%positive;359526530465232382%positive;323519723678823934%positive;314090518117446367%positive;359126514391151327%positive;87775030900222%positive;78984306587134%positive;75839117981359%positive]]
  | StC => [HRank [(4739692492463%positive,0);(299540056365%positive,0);(342489729325%positive,0);(75839117981359%positive,0);(18412975475%positive,1);(1213489317509087%positive,0);(359126515128989357%positive,0);(314090518855284397%positive,0);(76682254447327%positive,0);(87677370725087%positive,0);(1213490055344893%positive,0);(314090518117446367%positive,0);(75842876076797%positive,0);(19630657176073901%positive,0);(359126514391151327%positive,0);(22445406943180461%positive,0)]]
  | StD => [HMeas MLeft 29 [(4714459558890%positive,1);(299540056365%positive,1);(342489729325%positive,1);(294607486782%positive,1);(359526531203069930%positive,1);(359126515128989357%positive,1);(323519724416661482%positive,1);(21429450898%positive,0);(314090518855284397%positive,1);(22470407947810794%positive,1);(20219982523660266%positive,1);(1213490055344893%positive,1);(323519723678823934%positive,1);(359526530465232382%positive,1);(75842876076797%positive,1);(19630657176073901%positive,1);(22445406943180461%positive,1);(87775030900222%positive,1);(78984306587134%positive,1)] [4714459558890%positive;299540056365%positive;342489729325%positive;294607486782%positive;359526531203069930%positive;359126515128989357%positive;323519724416661482%positive;21429450898%positive;314090518855284397%positive;22470407947810794%positive;20219982523660266%positive;1213490055344893%positive;359526530465232382%positive;323519723678823934%positive;75842876076797%positive;19630657176073901%positive;22445406943180461%positive;87775030900222%positive;78984306587134%positive]]
  end.

Lemma cqh_h_00112 : iqh tmq_h_00112.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00112 StA 0 2 2 25 20000
                lsetq_h_00112 rsetq_h_00112 certq_h_00112 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00112); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00113 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StB)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Definition lsetq_h_00113 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StB,S1)]);(S1,[(StC,S0)])];
   [(S1,[(StD,S1);(StB,S1)]);(S1,[(StD,S1);(StC,S1)])];
   [(S1,[(StD,S1);(StC,S1)]);(S1,[(StD,S1);(StB,S1)])]].

Definition rsetq_h_00113 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StD,S1)]);(S1,[(StC,S1);(StD,S1)])];
   [(S1,[(StC,S1);(StD,S1)]);(S1,[(StB,S1);(StD,S1)])];
   [(S1,[(StC,S1);(StD,S1)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0)]);(S0,[])]].

Definition certq_h_00113 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 21 [(20230711151163359%positive,23);(87677387502303%positive,23);(21437839506%positive,23);(18417164275%positive,22);(87814759347710%positive,23);(22480578430367727%positive,23);(359689259259525103%positive,23);(359126583110793183%positive,23);(4939137512159%positive,23);(4739692492783%positive,23);(75839453525999%positive,23);(75838380307454%positive,0);(359689258186307070%positive,23);(294607617855%positive,23)] [18417164275%positive;87814759347710%positive;294607617855%positive;75839453525999%positive;359126583110793183%positive;22480578430367727%positive;359689258186307070%positive;20230711151163359%positive;4939137512159%positive;359689259259525103%positive;87677387502303%positive;75838380307454%positive;4739692492783%positive;21437839506%positive]]
  | StC => [HMeas MRight 21 [(20230711151163359%positive,1);(87677387502303%positive,1);(22445411238147837%positive,1);(18417164275%positive,0);(359126584184010493%positive,1);(22480578430367727%positive,1);(359689259259525103%positive,1);(359126583110793183%positive,1);(342489794861%positive,1);(4939137512159%positive,1);(4739692492783%positive,1);(1264419240670973%positive,1);(75839453525999%positive,1);(20230712224380669%positive,1);(294607617855%positive,1)] [18417164275%positive;1264419240670973%positive;294607617855%positive;359126584184010493%positive;75839453525999%positive;359126583110793183%positive;22480578430367727%positive;20230712224380669%positive;20230711151163359%positive;4939137512159%positive;342489794861%positive;359689259259525103%positive;87677387502303%positive;22445411238147837%positive;4739692492783%positive]]
  | StD => [HMeas MLeft 21 [(22445411238147837%positive,1);(21437839506%positive,0);(87814759347710%positive,1);(359126584184010493%positive,1);(342489794861%positive,1);(1264419240670973%positive,1);(20230712224380669%positive,1);(75838380307454%positive,1);(359689258186307070%positive,1)] [87814759347710%positive;1264419240670973%positive;359126584184010493%positive;20230712224380669%positive;75838380307454%positive;359689258186307070%positive;342489794861%positive;22445411238147837%positive;21437839506%positive]]
  end.

Lemma cqh_h_00113 : iqh tmq_h_00113.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00113 StA 0 2 2 25 20000
                lsetq_h_00113 rsetq_h_00113 certq_h_00113 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00113); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00114 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StB)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Definition lsetq_h_00114 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StB,S1)]);(S1,[(StC,S0)])];
   [(S1,[(StD,S1);(StB,S1)]);(S1,[(StD,S1);(StC,S1)])];
   [(S1,[(StD,S1);(StC,S1)]);(S1,[(StD,S1);(StB,S1)])]].

Definition rsetq_h_00114 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StD,S0)]);(S0,[(StB,S0)])];
   [(S1,[(StB,S1);(StD,S1)]);(S1,[(StC,S1);(StD,S1)])];
   [(S1,[(StC,S1);(StD,S1)]);(S1,[(StB,S1);(StD,S0)])];
   [(S1,[(StC,S1);(StD,S1)]);(S1,[(StB,S1);(StD,S1)])]].

Definition certq_h_00114 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 26 [(87677387502303%positive,1);(294674693915%positive,0);(21437839506%positive,1);(87814759347710%positive,1);(22480578430367727%positive,1);(359689259259525103%positive,1);(4625537791486%positive,1);(1184137711974383%positive,1);(359126583110793183%positive,1);(18946207765231599%positive,1);(75219905016799%positive,1);(78881294480095%positive,1);(18946206692013566%positive,1);(359689258186307070%positive,1);(323097786091829215%positive,1)] [87814759347710%positive;1184137711974383%positive;75219905016799%positive;18946206692013566%positive;359126583110793183%positive;78881294480095%positive;22480578430367727%positive;18946207765231599%positive;359689258186307070%positive;323097786091829215%positive;359689259259525103%positive;4625537791486%positive;87677387502303%positive;294674693915%positive;21437839506%positive]]
  | StC => [HMeas MRight 26 [(87677387502303%positive,3);(294674693915%positive,2);(22445411238147837%positive,3);(308130056493%positive,3);(359126584184010493%positive,3);(22480578430367727%positive,3);(359689259259525103%positive,3);(1184137711974383%positive,3);(4701037785533%positive,0);(359126583110793183%positive,3);(18946207765231599%positive,3);(323097787165046525%positive,3);(342489794861%positive,3);(75219905016799%positive,3);(75220978233789%positive,0);(78881294480095%positive,3);(20193611424462589%positive,3);(323097786091829215%positive,3);(18412965361%positive,1)] [87677387502303%positive;22445411238147837%positive;294674693915%positive;308130056493%positive;359126584184010493%positive;22480578430367727%positive;359689259259525103%positive;1184137711974383%positive;4701037785533%positive;359126583110793183%positive;18946207765231599%positive;323097787165046525%positive;342489794861%positive;75219905016799%positive;75220978233789%positive;78881294480095%positive;20193611424462589%positive;323097786091829215%positive;18412965361%positive]]
  | StD => [HMeas MLeft 26 [(22445411238147837%positive,1);(21437839506%positive,0);(87814759347710%positive,1);(308130056493%positive,1);(359126584184010493%positive,1);(4625537791486%positive,1);(4701037785533%positive,1);(323097787165046525%positive,1);(342489794861%positive,1);(75220978233789%positive,1);(18946206692013566%positive,1);(20193611424462589%positive,1);(359689258186307070%positive,1);(18412965361%positive,1)] [87814759347710%positive;308130056493%positive;359126584184010493%positive;75220978233789%positive;18946206692013566%positive;4701037785533%positive;20193611424462589%positive;323097787165046525%positive;359689258186307070%positive;342489794861%positive;18412965361%positive;4625537791486%positive;22445411238147837%positive;21437839506%positive]]
  end.

Lemma cqh_h_00114 : iqh tmq_h_00114.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00114 StA 0 2 2 25 20000
                lsetq_h_00114 rsetq_h_00114 certq_h_00114 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00114); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00115 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StC)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00115 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S1);(StC,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StB,S1);(StC,S1)]);(S1,[(StC,S0);(StB,S1);(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StB,S1);(StC,S1)]);(S1,[(StD,S1);(StD,S0);(StB,S1);(StC,S1)])];
   [(S1,[(StD,S1);(StD,S0);(StB,S1);(StC,S1)]);(S1,[(StC,S1);(StD,S0);(StB,S1);(StC,S1)])]].

Definition rsetq_h_00115 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S1)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S0)])]].

Definition certq_h_00115 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 45 [(395434628540408145892022414782%positive,1);(94123810330937555797929691%positive,0);(76808992811154%positive,1);(23569740566034747076315%positive,0);(1272372447534352952767%positive,1);(5425914401840887569505278%positive,1);(385531127115520226622573047231%positive,1);(385531127115591039569448332735%positive,1);(4714649329523%positive,0);(89763438484673474266%positive,0);(395434628540337337304932941531%positive,0);(395434628540408150251808227035%positive,0);(5425914472653834444790782%positive,1);(395434571953867782681404038142%positive,1);(86814638285051640077876955%positive,0);(19311202604547902%positive,1);(385531127115591035133283790555%positive,0);(86814638355864586953162459%positive,0);(355820491877327230204005243886%positive,1);(395434571953796969734528752638%positive,1);(1473108574575881547182%positive,1);(86870237274720671616130030%positive,1);(21914904931240238%positive,1);(86870255413249780749692635%positive,0);(96541657358480660797517246%positive,1);(86814638355860227167350206%positive,1);(385531052820176356801584225262%positive,1);(94123792192408446664367086%positive,1);(355820566172671100024994065855%positive,1);(355820566172741908535704809179%positive,0);(355820566172741912971869351359%positive,1);(79523277693636787931%positive,0)] [395434628540408145892022414782%positive;94123810330937555797929691%positive;76808992811154%positive;23569740566034747076315%positive;1272372447534352952767%positive;5425914401840887569505278%positive;385531127115520226622573047231%positive;385531127115591039569448332735%positive;4714649329523%positive;89763438484673474266%positive;395434628540337337304932941531%positive;395434628540408150251808227035%positive;5425914472653834444790782%positive;395434571953867782681404038142%positive;86814638285051640077876955%positive;19311202604547902%positive;385531127115591035133283790555%positive;86814638355864586953162459%positive;355820491877327230204005243886%positive;395434571953796969734528752638%positive;1473108574575881547182%positive;86870237274720671616130030%positive;21914904931240238%positive;86870255413249780749692635%positive;96541657358480660797517246%positive;86814638355860227167350206%positive;385531052820176356801584225262%positive;94123792192408446664367086%positive;355820566172671100024994065855%positive;355820566172741908535704809179%positive;355820566172741912971869351359%positive;79523277693636787931%positive]]
  | StC => [HRank [(385531127115591035171410132717%positive,0);(86814638285051678330044397%positive,0);(395434628540408150290060394477%positive,0);(94123810330937420875677421%positive,0);(1473108785377171659501%positive,0);(94123810330937555797929691%positive,1);(350638431580754669%positive,0);(23569740566034747076315%positive,1);(86814638355864625205329901%positive,0);(1272372447534352952767%positive,0);(395434628540337337343185108973%positive,0);(385531127115520226622573047231%positive,0);(385531127115591039569448332735%positive,0);(4970204856001229805%positive,0);(4714649329523%positive,1);(395434628540337337304932941531%positive,1);(395434628540408150251808227035%positive,1);(86870255413249645827440365%positive,0);(86814638285051640077876955%positive,1);(385531127115591035133283790555%positive,1);(355820566172741908573831151341%positive,0);(86814638355864586953162459%positive,1);(86870255413249780749692635%positive,1);(355820566172671100024994065855%positive,0);(355820566172741908535704809179%positive,1);(355820566172741912971869351359%positive,0);(79523277693636787931%positive,1)]]
  | StD => [HRank [(395434571953867782681404038142%positive,0);(395434571953796969734528752638%positive,0);(385531127115591035171410132717%positive,1);(395434628540408145892022414782%positive,0);(86870237274720671616130030%positive,0);(86814638285051678330044397%positive,1);(385531052820176356801584225262%positive,0);(395434628540408150290060394477%positive,1);(1473108574575881547182%positive,0);(94123810330937420875677421%positive,1);(96541657358480660797517246%positive,0);(89763438484673474266%positive,1);(76808992811154%positive,2);(355820491877327230204005243886%positive,0);(86814638355864625205329901%positive,1);(5425914401840887569505278%positive,0);(94123792192408446664367086%positive,0);(395434628540337337343185108973%positive,1);(5425914472653834444790782%positive,0);(19311202604547902%positive,0);(21914904931240238%positive,0);(355820566172741908573831151341%positive,1);(86870255413249645827440365%positive,1);(350638431580754669%positive,3);(86814638355860227167350206%positive,0);(1473108785377171659501%positive,1);(4970204856001229805%positive,1)]]
  end.

Lemma cqh_h_00115 : iqh tmq_h_00115.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00115 StA 0 4 2 25 20000
                lsetq_h_00115 rsetq_h_00115 certq_h_00115 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00115); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00116 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StB)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StA)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Definition lsetq_h_00116 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StC,S0)]);(S0,[(StB,S1);(StD,S1)])];
   [(S0,[(StB,S1);(StC,S0)]);(S1,[(StD,S0)])];
   [(S0,[(StB,S1);(StC,S0)]);(S1,[(StD,S0);(StB,S1)])];
   [(S0,[(StB,S1);(StD,S1)]);(S0,[(StB,S1);(StC,S0)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1)]);(S0,[(StB,S1);(StC,S0)])]].

Definition rsetq_h_00116 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S0);(StB,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S1)]);(S0,[(StB,S0);(StB,S0)])];
   [(S1,[(StC,S0);(StB,S1)]);(S1,[(StD,S1);(StD,S0)])];
   [(S1,[(StD,S1);(StD,S0)]);(S1,[(StC,S0);(StB,S1)])]].

Definition certq_h_00116 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 35 [(324213790123415515%positive,0);(339406014060032730%positive,1);(20230174866%positive,1);(324213792388339135%positive,2);(1207744659%positive,0);(302680954405050331%positive,1);(20263361758811583%positive,2);(302680956669973951%positive,2);(82862796305114%positive,1);(18917559526413759%positive,2);(339406014061138650%positive,1);(324213792388339675%positive,0);(1203315462238938%positive,2);(302680954405049791%positive,2);(324213790123414975%positive,2);(302680956669974491%positive,1);(18917559526414299%positive,1);(309194361151%positive,2);(20263361758812123%positive,0);(1203315463344858%positive,2)] [324213790123415515%positive;339406014060032730%positive;20230174866%positive;324213792388339135%positive;302680954405050331%positive;1207744659%positive;20263361758811583%positive;302680956669973951%positive;82862796305114%positive;18917559526413759%positive;339406014061138650%positive;324213792388339675%positive;1203315462238938%positive;302680954405049791%positive;324213790123414975%positive;302680956669974491%positive;18917559526414299%positive;309194361151%positive;20263361758812123%positive;1203315463344858%positive]]
  | StC => [HMeas MRight 35 [(324213790123415515%positive,1);(1203315462239661%positive,1);(324213790123414525%positive,1);(324213792388339135%positive,1);(1207744659%positive,1);(302680954405050331%positive,1);(20263361758811583%positive,1);(302680956669973951%positive,1);(324213792388338685%positive,1);(18917559526413759%positive,1);(324213792388339675%positive,1);(4715716202905%positive,0);(1203315463345581%positive,1);(302680954405049791%positive,1);(302680956669973501%positive,1);(339406014060033453%positive,1);(4713451278745%positive,0);(324213790123414975%positive,1);(302680956669974491%positive,1);(20263361758811133%positive,1);(18917559526414299%positive,1);(309194361151%positive,1);(20263361758812123%positive,1);(18917559526413309%positive,1);(5178924769069%positive,1);(302680954405049341%positive,1);(339406014061139373%positive,1)] [324213790123415515%positive;1203315462239661%positive;324213790123414525%positive;324213792388339135%positive;302680954405050331%positive;1207744659%positive;20263361758811583%positive;302680956669973951%positive;324213792388338685%positive;18917559526413759%positive;324213792388339675%positive;4715716202905%positive;1203315463345581%positive;302680954405049791%positive;302680956669973501%positive;339406014060033453%positive;4713451278745%positive;324213790123414975%positive;302680956669974491%positive;20263361758811133%positive;18917559526414299%positive;309194361151%positive;20263361758812123%positive;18917559526413309%positive;5178924769069%positive;302680954405049341%positive;339406014061139373%positive]]
  | StD => [HMeas MRight 35 [(339406014060032730%positive,2);(20230174866%positive,2);(1203315462239661%positive,2);(324213790123414525%positive,2);(82862796305114%positive,2);(324213792388338685%positive,2);(339406014061138650%positive,2);(4715716202905%positive,1);(1203315463345581%positive,2);(1203315462238938%positive,0);(302680956669973501%positive,2);(339406014060033453%positive,2);(4713451278745%positive,1);(20263361758811133%positive,2);(18917559526413309%positive,2);(5178924769069%positive,2);(302680954405049341%positive,2);(339406014061139373%positive,2);(1203315463344858%positive,0)] [339406014060032730%positive;20230174866%positive;1203315462239661%positive;324213790123414525%positive;82862796305114%positive;324213792388338685%positive;339406014061138650%positive;4715716202905%positive;1203315463345581%positive;1203315462238938%positive;302680956669973501%positive;339406014060033453%positive;4713451278745%positive;20263361758811133%positive;18917559526413309%positive;5178924769069%positive;302680954405049341%positive;339406014061139373%positive;1203315463344858%positive]]
  end.

Lemma cqh_h_00116 : iqh tmq_h_00116.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00116 StA 3 2 2 28 20000
                lsetq_h_00116 rsetq_h_00116 certq_h_00116 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00116); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00117 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StB)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Definition lsetq_h_00117 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StC,S0)]);(S0,[(StB,S1);(StD,S1)])];
   [(S0,[(StB,S1);(StC,S0)]);(S1,[(StD,S0)])];
   [(S0,[(StB,S1);(StC,S0)]);(S1,[(StD,S0);(StB,S1)])];
   [(S0,[(StB,S1);(StD,S1)]);(S0,[(StB,S1);(StC,S0)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1)]);(S0,[(StB,S1);(StC,S0)])]].

Definition rsetq_h_00117 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S0);(StB,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S1)]);(S0,[(StB,S0);(StB,S0)])];
   [(S1,[(StC,S0);(StB,S1)]);(S1,[(StD,S1);(StD,S0)])];
   [(S1,[(StD,S1);(StD,S0)]);(S1,[(StC,S0);(StB,S1)])]].

Definition certq_h_00117 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 35 [(324213790123415515%positive,0);(339406014060032730%positive,1);(20230174866%positive,1);(324213792388339135%positive,2);(1207744659%positive,0);(302680954405050331%positive,1);(20263361758811583%positive,2);(302680956669973951%positive,2);(82862796305114%positive,1);(18917559526413759%positive,2);(339406014061138650%positive,1);(324213792388339675%positive,0);(1203315462238938%positive,2);(302680954405049791%positive,2);(324213790123414975%positive,2);(302680956669974491%positive,1);(18917559526414299%positive,1);(309194361151%positive,2);(20263361758812123%positive,0);(1203315463344858%positive,2)] [324213790123415515%positive;339406014060032730%positive;20230174866%positive;324213792388339135%positive;302680954405050331%positive;1207744659%positive;20263361758811583%positive;302680956669973951%positive;82862796305114%positive;18917559526413759%positive;339406014061138650%positive;324213792388339675%positive;1203315462238938%positive;302680954405049791%positive;324213790123414975%positive;302680956669974491%positive;18917559526414299%positive;309194361151%positive;20263361758812123%positive;1203315463344858%positive]]
  | StC => [HMeas MRight 35 [(324213790123415515%positive,1);(1203315462239661%positive,1);(324213790123414525%positive,1);(324213792388339135%positive,1);(1207744659%positive,1);(302680954405050331%positive,1);(20263361758811583%positive,1);(302680956669973951%positive,1);(324213792388338685%positive,1);(18917559526413759%positive,1);(324213792388339675%positive,1);(4715716202905%positive,0);(1203315463345581%positive,1);(302680954405049791%positive,1);(302680956669973501%positive,1);(339406014060033453%positive,1);(4713451278745%positive,0);(324213790123414975%positive,1);(302680956669974491%positive,1);(20263361758811133%positive,1);(18917559526414299%positive,1);(309194361151%positive,1);(20263361758812123%positive,1);(18917559526413309%positive,1);(5178924769069%positive,1);(302680954405049341%positive,1);(339406014061139373%positive,1)] [324213790123415515%positive;1203315462239661%positive;324213790123414525%positive;324213792388339135%positive;302680954405050331%positive;1207744659%positive;20263361758811583%positive;302680956669973951%positive;324213792388338685%positive;18917559526413759%positive;324213792388339675%positive;4715716202905%positive;1203315463345581%positive;302680954405049791%positive;302680956669973501%positive;339406014060033453%positive;4713451278745%positive;324213790123414975%positive;302680956669974491%positive;20263361758811133%positive;18917559526414299%positive;309194361151%positive;20263361758812123%positive;18917559526413309%positive;5178924769069%positive;302680954405049341%positive;339406014061139373%positive]]
  | StD => [HMeas MRight 35 [(339406014060032730%positive,2);(20230174866%positive,2);(1203315462239661%positive,2);(324213790123414525%positive,2);(82862796305114%positive,2);(324213792388338685%positive,2);(339406014061138650%positive,2);(4715716202905%positive,1);(1203315463345581%positive,2);(1203315462238938%positive,0);(302680956669973501%positive,2);(339406014060033453%positive,2);(4713451278745%positive,1);(20263361758811133%positive,2);(18917559526413309%positive,2);(5178924769069%positive,2);(302680954405049341%positive,2);(339406014061139373%positive,2);(1203315463344858%positive,0)] [339406014060032730%positive;20230174866%positive;1203315462239661%positive;324213790123414525%positive;82862796305114%positive;324213792388338685%positive;339406014061138650%positive;4715716202905%positive;1203315463345581%positive;1203315462238938%positive;302680956669973501%positive;339406014060033453%positive;4713451278745%positive;20263361758811133%positive;18917559526413309%positive;5178924769069%positive;302680954405049341%positive;339406014061139373%positive;1203315463344858%positive]]
  end.

Lemma cqh_h_00117 : iqh tmq_h_00117.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00117 StA 0 2 2 25 20000
                lsetq_h_00117 rsetq_h_00117 certq_h_00117 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00117); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00118 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StB)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => None
  | StD, S1 => None
  end.

Definition lsetq_h_00118 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StC,S1)]);(S0,[(StB,S1);(StC,S1)])];
   [(S0,[(StB,S1);(StC,S1)]);(S1,[(StC,S0)])];
   [(S0,[(StB,S1);(StC,S1)]);(S1,[(StC,S0);(StB,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S1)]);(S0,[(StB,S1);(StC,S1)])];
   [(S1,[(StC,S0);(StB,S1)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StB,S1)]);(S1,[(StC,S0);(StB,S1)])]].

Definition rsetq_h_00118 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S0);(StB,S0)]);(S0,[])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StB,S0);(StB,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StC,S1);(StC,S0)])]].

Definition certq_h_00118 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 68 [(1203319757174490%positive,1);(73893763708634%positive,0);(314631546221721306%positive,0);(302668860970424026%positive,0);(18753501330%positive,0);(302668860969809626%positive,0);(314631546222335406%positive,1);(314631547480626606%positive,1);(18916803547158234%positive,0);(75207220753838%positive,1);(1203318498882990%positive,1);(18916803546543534%positive,1);(76814341469614%positive,1);(314631546222335706%positive,0);(75207220754138%positive,1);(314631547480012206%positive,1);(302668859711518126%positive,1);(18916803546543834%positive,0);(19664471454045614%positive,1);(1203318498883290%positive,1);(314631547480626906%positive,0);(76814341469914%positive,0);(1203318499497390%positive,1);(314631547480012506%positive,0);(1203319757788590%positive,1);(302668859711518426%positive,0);(75207221368238%positive,1);(19664471454045914%positive,0);(19664471453431514%positive,0);(302668859712132526%positive,1);(18916803547157934%positive,1);(302668860970423726%positive,1);(19664471453431214%positive,1);(1203318499497690%positive,1);(75207221368538%positive,1);(1203319757174190%positive,1);(300056021294%positive,1);(73893763708334%positive,1);(302668859712132826%positive,0);(314631546221721006%positive,1);(302668860969809326%positive,1);(1203319757788890%positive,1)] [1203319757174490%positive;73893763708634%positive;302668860970424026%positive;314631546221721306%positive;18753501330%positive;302668860969809626%positive;314631546222335406%positive;314631547480626606%positive;18916803547158234%positive;75207220753838%positive;1203318498882990%positive;18916803546543534%positive;76814341469614%positive;314631546222335706%positive;75207220754138%positive;314631547480012206%positive;18916803546543834%positive;302668859711518126%positive;19664471454045614%positive;1203318498883290%positive;314631547480626906%positive;76814341469914%positive;1203318499497390%positive;314631547480012506%positive;314631546221721006%positive;1203319757788590%positive;302668859711518426%positive;75207221368238%positive;19664471454045914%positive;302668859712132526%positive;18916803547157934%positive;302668860970423726%positive;19664471453431214%positive;1203318499497690%positive;75207221368538%positive;1203319757174190%positive;300056021294%positive;73893763708334%positive;302668859712132826%positive;19664471453431514%positive;302668860969809326%positive;1203319757788890%positive]]
  | StC => [HMeas MRight 68 [(1203318499496685%positive,1);(302668859712131821%positive,1);(314631547480011501%positive,1);(4713385652633%positive,1);(19664471453430509%positive,1);(1203319757787885%positive,1);(302668860970423021%positive,1);(314631546221720301%positive,1);(4714644558233%positive,0);(73893763707629%positive,1);(75207221367533%positive,1);(18916803547157229%positive,1);(4713386267033%positive,0);(4714643943833%positive,1);(75207220753133%positive,1);(1203319757173485%positive,1);(302668860969808621%positive,1);(18916803546542829%positive,1);(1203318498882285%positive,1);(314631547480625901%positive,1);(76814341468909%positive,1);(302668859711517421%positive,1);(314631546222334701%positive,1);(19664471454044909%positive,1)] [1203318499496685%positive;302668859712131821%positive;314631547480011501%positive;4713385652633%positive;19664471453430509%positive;1203319757787885%positive;302668860970423021%positive;314631546221720301%positive;4714644558233%positive;73893763707629%positive;75207221367533%positive;18916803547157229%positive;4713386267033%positive;4714643943833%positive;75207220753133%positive;1203319757173485%positive;302668860969808621%positive;18916803546542829%positive;1203318498882285%positive;314631547480625901%positive;76814341468909%positive;302668859711517421%positive;314631546222334701%positive;19664471454044909%positive]]
  | StD => []
  end.

Lemma cqh_h_00118 : iqh tmq_h_00118.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00118 StA 0 2 2 25 20000
                lsetq_h_00118 rsetq_h_00118 certq_h_00118 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00118); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00119 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StB)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => None
  end.

Definition lsetq_h_00119 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StC,S1)]);(S0,[(StB,S1);(StD,S0)])];
   [(S0,[(StB,S1);(StD,S0)]);(S0,[(StB,S1);(StC,S1)])];
   [(S0,[(StB,S1);(StD,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StB,S1);(StD,S0)]);(S1,[(StC,S0);(StB,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S1)]);(S0,[(StB,S1);(StD,S0)])]].

Definition rsetq_h_00119 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S0);(StB,S0)]);(S0,[])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StB,S0);(StB,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StB,S1)])];
   [(S1,[(StD,S0);(StB,S1)]);(S1,[(StC,S1);(StC,S0)])]].

Definition certq_h_00119 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 37 [(19665244546586030%positive,2);(75207219795374%positive,2);(339964292163359707%positive,1);(302668857749197787%positive,1);(314643915726575022%positive,2);(75207219795674%positive,2);(1203318497924526%positive,2);(73893763707867%positive,1);(19665244546586330%positive,0);(1203319756215726%positive,2);(20263450771%positive,1);(314643916984866222%positive,2);(300067817774%positive,2);(1172109458%positive,0);(1203318497924826%positive,2);(302668857748583387%positive,1);(339964292162745307%positive,1);(314643915726575322%positive,0);(1203319756216026%positive,2);(314643916984866522%positive,0);(82999094375387%positive,1)] [19665244546586030%positive;75207219795374%positive;339964292163359707%positive;302668857749197787%positive;314643915726575022%positive;75207219795674%positive;1203318497924526%positive;73893763707867%positive;19665244546586330%positive;1203319756215726%positive;20263450771%positive;314643916984866222%positive;300067817774%positive;1172109458%positive;302668857748583387%positive;1203318497924826%positive;339964292162745307%positive;314643915726575322%positive;314643916984866522%positive;1203319756216026%positive;82999094375387%positive]]
  | StC => [HMeas MRight 37 [(4711422718361%positive,1);(339964292163359707%positive,1);(302668857749197787%positive,1);(73893763707867%positive,1);(20263450771%positive,1);(5187443398461%positive,1);(339964292163360189%positive,1);(4618360231741%positive,1);(302668857749198269%positive,1);(302668857748583387%positive,1);(339964292162745307%positive,1);(4711423332761%positive,0);(75207219794669%positive,1);(19665244546585325%positive,1);(1203318497923821%positive,1);(314643915726574317%positive,1);(339964292162745789%positive,1);(302668857748583869%positive,1);(1203319756215021%positive,1);(82999094375387%positive,1);(314643916984865517%positive,1)] [4711422718361%positive;339964292163359707%positive;302668857749197787%positive;73893763707867%positive;20263450771%positive;5187443398461%positive;339964292163360189%positive;4618360231741%positive;302668857748583387%positive;302668857749198269%positive;339964292162745307%positive;4711423332761%positive;75207219794669%positive;19665244546585325%positive;314643915726574317%positive;1203318497923821%positive;339964292162745789%positive;302668857748583869%positive;1203319756215021%positive;82999094375387%positive;314643916984865517%positive]]
  | StD => [HMeas MRight 37 [(19665244546586030%positive,4);(4711422718361%positive,1);(75207219795374%positive,0);(314643915726575022%positive,4);(75207219795674%positive,2);(1203318497924526%positive,0);(19665244546586330%positive,4);(1203319756215726%positive,0);(314643916984866222%positive,4);(300067817774%positive,4);(5187443398461%positive,4);(339964292163360189%positive,4);(1172109458%positive,4);(4618360231741%positive,4);(302668857749198269%positive,4);(1203318497924826%positive,2);(314643915726575322%positive,4);(4711423332761%positive,3);(75207219794669%positive,4);(19665244546585325%positive,4);(1203319756216026%positive,2);(1203318497923821%positive,4);(314643916984866522%positive,4);(314643915726574317%positive,4);(339964292162745789%positive,4);(302668857748583869%positive,4);(1203319756215021%positive,4);(314643916984865517%positive,4)] [19665244546586030%positive;4711422718361%positive;75207219795374%positive;314643915726575022%positive;75207219795674%positive;1203318497924526%positive;19665244546586330%positive;1203319756215726%positive;314643916984866222%positive;300067817774%positive;5187443398461%positive;339964292163360189%positive;1172109458%positive;4618360231741%positive;1203318497924826%positive;302668857749198269%positive;314643915726575322%positive;4711423332761%positive;75207219794669%positive;19665244546585325%positive;1203319756216026%positive;1203318497923821%positive;314643916984866522%positive;314643915726574317%positive;339964292162745789%positive;302668857748583869%positive;1203319756215021%positive;314643916984865517%positive]]
  end.

Lemma cqh_h_00119 : iqh tmq_h_00119.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00119 StA 0 2 2 25 20000
                lsetq_h_00119 rsetq_h_00119 certq_h_00119 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00119); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00120 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StC)
  | StC, S0 => Some (mkTrans S1 DL StC)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Definition lsetq_h_00120 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S1)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S0)])]].

Definition rsetq_h_00120 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S1);(StC,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StB,S1);(StC,S1)]);(S1,[(StC,S0);(StB,S1);(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StB,S1);(StC,S1)]);(S1,[(StD,S1);(StD,S0);(StB,S1);(StC,S1)])];
   [(S1,[(StD,S1);(StD,S0);(StB,S1);(StC,S1)]);(S1,[(StC,S1);(StD,S0);(StB,S1);(StC,S1)])]].

Definition certq_h_00120 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 45 [(384842019199245203674016247230%positive,1);(345914586773754214201160892123%positive,0);(21875736092576062%positive,1);(384844437046254732549788462527%positive,1);(345914607802970400670371737023%positive,1);(5340788668563%positive,0);(20286373164956582784731%positive,0);(5278238034102935581285374%positive,1);(84377892658281315956878782%positive,1);(5872260086764530562423806%positive,1);(93956156254128913805213403%positive,0);(79235125651630403290%positive,0);(84377892586223621136374766%positive,1);(345914607803042458127119604734%positive,1);(84452066944144142385802971%positive,0);(384844437046272746811007884286%positive,1);(19311508611099950%positive,1);(384842019199227189174723861486%positive,1);(89603010155035705051%positive,0);(384844437046200689354260016575%positive,1);(1267780024859104570798%positive,1);(84452066998187337914248923%positive,0);(384841998239060192361859772123%positive,0);(75366860945106%positive,1);(84377892640266816664820718%positive,1);(384844416016984502885049171675%positive,0);(345914607803024443865900182975%positive,1);(384841998239114235557388218075%positive,0);(84451803411543394106998491%positive,0);(1433657247745151593919%positive,1);(384842019199173145979195415534%positive,1);(93955571093548030209027518%positive,1)] [384842019199245203674016247230%positive;345914586773754214201160892123%positive;21875736092576062%positive;384844437046254732549788462527%positive;345914607802970400670371737023%positive;5340788668563%positive;20286373164956582784731%positive;5278238034102935581285374%positive;84377892658281315956878782%positive;5872260086764530562423806%positive;93956156254128913805213403%positive;79235125651630403290%positive;84377892586223621136374766%positive;345914607803042458127119604734%positive;84452066944144142385802971%positive;384844437046272746811007884286%positive;19311508611099950%positive;384842019199227189174723861486%positive;89603010155035705051%positive;384844437046200689354260016575%positive;1267780024859104570798%positive;84452066998187337914248923%positive;384841998239060192361859772123%positive;75366860945106%positive;84377892640266816664820718%positive;384844416016984502885049171675%positive;345914607803024443865900182975%positive;384841998239114235557388218075%positive;84451803411543394106998491%positive;1433657247745151593919%positive;384842019199173145979195415534%positive;93955571093548030209027518%positive]]
  | StC => [HRank [(84377892640266951807319789%positive,0);(345914586773754214201160892123%positive,1);(384844437046254732549788462527%positive,0);(84377892586223756278873837%positive,0);(345914607802970400670371737023%positive,0);(5600188439699518445%positive,0);(5340788668563%positive,1);(384842019199227189309866360557%positive,0);(308984137407918829%positive,0);(20286373164956582784731%positive,1);(1267780024962035145453%positive,0);(384842019199173146114337914605%positive,0);(93956156254128913805213403%positive,1);(84451808545646969309478893%positive,0);(84452066944144142385802971%positive,1);(345914607803042458230049849325%positive,0);(93956161388232489007693805%positive,0);(89603010155035705051%positive,1);(384844437046272746913938128877%positive,0);(384844437046200689354260016575%positive,0);(84452066998187337914248923%positive,1);(384841998239060192361859772123%positive,1);(384844416016984502885049171675%positive,1);(345914607803024443865900182975%positive,0);(384841998239114235557388218075%positive,1);(84451803411543394106998491%positive,1);(1433657247745151593919%positive,0)]]
  | StD => [HRank [(384842019199245203674016247230%positive,0);(21875736092576062%positive,0);(1267780024859104570798%positive,0);(84377892586223756278873837%positive,1);(384844437046272746811007884286%positive,0);(345914607803042458127119604734%positive,0);(384842019199227189309866360557%positive,1);(5278238034102935581285374%positive,0);(19311508611099950%positive,0);(1267780024962035145453%positive,1);(5872260086764530562423806%positive,0);(5600188439699518445%positive,1);(84377892658281315956878782%positive,0);(79235125651630403290%positive,1);(84377892586223621136374766%positive,0);(84451808545646969309478893%positive,1);(84377892640266816664820718%positive,0);(345914607803042458230049849325%positive,1);(384842019199173145979195415534%positive,0);(93956161388232489007693805%positive,1);(384842019199227189174723861486%positive,0);(384844437046272746913938128877%positive,1);(384842019199173146114337914605%positive,1);(75366860945106%positive,2);(308984137407918829%positive,3);(84377892640266951807319789%positive,1);(93955571093548030209027518%positive,0)]]
  end.

Lemma cqh_h_00120 : iqh tmq_h_00120.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00120 StA 0 4 2 25 20000
                lsetq_h_00120 rsetq_h_00120 certq_h_00120 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00120); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00121 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StB)
  | StC, S0 => Some (mkTrans S1 DR StC)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S0 DL StB)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00121 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S1);(StB,S1);(StC,S0)]);(S1,[(StC,S0);(StB,S0)])];
   [(S1,[(StC,S1);(StB,S1);(StC,S1);(StB,S1)]);(S1,[(StD,S1);(StB,S1);(StC,S0);(StB,S0)])];
   [(S1,[(StC,S1);(StB,S1);(StC,S1);(StB,S1)]);(S1,[(StD,S1);(StB,S1);(StD,S1);(StB,S1)])];
   [(S1,[(StD,S1);(StB,S1);(StC,S0);(StB,S0)]);(S1,[(StC,S1);(StB,S1);(StC,S0)])];
   [(S1,[(StD,S1);(StB,S1);(StD,S1);(StB,S1)]);(S1,[(StC,S1);(StB,S1);(StC,S1);(StB,S1)])]].

Definition rsetq_h_00121 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0);(StD,S0);(StB,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0);(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StC,S0)]);(S1,[(StB,S1);(StC,S0);(StB,S0)])];
   [(S1,[(StB,S1);(StC,S0);(StB,S0)]);(S1,[(StB,S1);(StC,S1);(StB,S1);(StC,S0)])];
   [(S1,[(StB,S1);(StC,S1);(StB,S1);(StC,S0)]);(S1,[(StB,S1);(StD,S1);(StB,S1);(StC,S0)])];
   [(S1,[(StB,S1);(StC,S1);(StB,S1);(StC,S1)]);(S0,[(StD,S0);(StD,S0);(StD,S0);(StB,S0)])];
   [(S1,[(StB,S1);(StC,S1);(StB,S1);(StC,S1)]);(S0,[(StD,S0);(StD,S0);(StD,S0);(StD,S0)])];
   [(S1,[(StB,S1);(StC,S1);(StB,S1);(StC,S1)]);(S1,[(StB,S1);(StD,S1);(StB,S1);(StD,S1)])];
   [(S1,[(StB,S1);(StD,S1);(StB,S1);(StC,S0)]);(S1,[(StB,S1);(StC,S1);(StB,S1);(StC,S1)])];
   [(S1,[(StB,S1);(StD,S1);(StB,S1);(StD,S1)]);(S1,[(StB,S1);(StC,S1);(StB,S1);(StC,S1)])]].

Definition certq_h_00121 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 30 [(79083068373115059131%positive,0);(74061534762778%positive,0);(79083068373114928059%positive,0);(334078619782819788821915754463%positive,1);(353885660411385873220301742047%positive,1);(80406078863811900126%positive,1);(384955677401643427802459332318%positive,1);(334078619782742101728343285727%positive,1);(353885660411308186126729273311%positive,1);(394897864378902360657621409759%positive,1);(5270083423607570835118815%positive,1);(5170676081525763285114590%positive,1);(1169975442%positive,1);(394897864378824673564048941023%positive,1);(5208455013388720446824158%positive,1);(24059723934641166784505503454%positive,1)] [394897864378824673564048941023%positive;79083068373115059131%positive;334078619782742101728343285727%positive;353885660411308186126729273311%positive;394897864378902360657621409759%positive;5208455013388720446824158%positive;74061534762778%positive;334078619782819788821915754463%positive;353885660411385873220301742047%positive;79083068373114928059%positive;80406078863811900126%positive;384955677401643427802459332318%positive;5270083423607570835118815%positive;5170676081525763285114590%positive;1169975442%positive;24059723934641166784505503454%positive]]
  | StC => [HMeas MLeft 30 [(79083068373115059131%positive,1);(22945140776292025052653%positive,1);(79083068373114928059%positive,1);(334078619782819788821915754463%positive,1);(353885660411385873220301742047%positive,1);(353885660411308186126729477629%positive,1);(334078619782742101728343285727%positive,1);(353885660411308186126729273311%positive,1);(394897864378824673564049145341%positive,1);(394897864378902360657621409759%positive,1);(24059729837599270371562221037%positive,1);(5270083423607570835118815%positive,1);(5208455013388720446762477%positive,1);(394897864378824673564048941023%positive,1);(5025943206413037997%positive,1);(96410611420611498818514429%positive,1);(1226899396725037%positive,1);(384955677401643427802459270637%positive,1);(289302870161%positive,0);(353885660411385873220301618685%positive,1);(394897864378902360657621286397%positive,1)] [79083068373115059131%positive;22945140776292025052653%positive;79083068373114928059%positive;334078619782819788821915754463%positive;353885660411385873220301742047%positive;353885660411308186126729477629%positive;334078619782742101728343285727%positive;353885660411308186126729273311%positive;394897864378824673564049145341%positive;394897864378902360657621409759%positive;24059729837599270371562221037%positive;5270083423607570835118815%positive;5208455013388720446762477%positive;394897864378824673564048941023%positive;5025943206413037997%positive;96410611420611498818514429%positive;1226899396725037%positive;384955677401643427802459270637%positive;289302870161%positive;353885660411385873220301618685%positive;394897864378902360657621286397%positive]]
  | StD => [HMeas MLeft 30 [(22945140776292025052653%positive,64);(74061534762778%positive,31);(80406078863811900126%positive,0);(384955677401643427802459332318%positive,64);(353885660411308186126729477629%positive,64);(394897864378824673564049145341%positive,64);(24059729837599270371562221037%positive,64);(5208455013388720446762477%positive,64);(5170676081525763285114590%positive,64);(1169975442%positive,62);(5025943206413037997%positive,64);(96410611420611498818514429%positive,64);(1226899396725037%positive,64);(384955677401643427802459270637%positive,64);(289302870161%positive,63);(353885660411385873220301618685%positive,64);(5208455013388720446824158%positive,64);(394897864378902360657621286397%positive,64);(24059723934641166784505503454%positive,64)] [22945140776292025052653%positive;74061534762778%positive;80406078863811900126%positive;384955677401643427802459332318%positive;353885660411308186126729477629%positive;394897864378824673564049145341%positive;24059729837599270371562221037%positive;5208455013388720446762477%positive;5170676081525763285114590%positive;1169975442%positive;5025943206413037997%positive;96410611420611498818514429%positive;1226899396725037%positive;384955677401643427802459270637%positive;289302870161%positive;353885660411385873220301618685%positive;5208455013388720446824158%positive;394897864378902360657621286397%positive;24059723934641166784505503454%positive]]
  end.

Lemma cqh_h_00121 : iqh tmq_h_00121.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00121 StA 0 4 2 25 20000
                lsetq_h_00121 rsetq_h_00121 certq_h_00121 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00121); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00122 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DR StC)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S0 DR StC)
  end.

Definition lsetq_h_00122 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StB,S0)]);(S0,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S1)]);(S1,[(StC,S1);(StD,S0)])];
   [(S1,[(StC,S1);(StD,S0)]);(S0,[(StC,S0);(StB,S0)])];
   [(S1,[(StC,S1);(StD,S0)]);(S0,[(StD,S1);(StB,S1)])]].

Definition rsetq_h_00122 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StC,S1)]);(S1,[(StD,S0)])];
   [(S1,[(StB,S1);(StC,S1)]);(S1,[(StD,S0);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S0)]);(S1,[(StB,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StD,S1)]);(S1,[(StB,S1);(StC,S1)])]].

Definition certq_h_00122 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 23 [(1264127163847358%positive,1);(357996005630637563%positive,1);(20226036011620286%positive,1);(350118559203948255%positive,1);(18652752018%positive,1);(87401368736171%positive,1);(22374750417146558%positive,1);(357996008064407486%positive,1);(85472794202778%positive,0);(20226038208361979%positive,1);(350118554573436639%positive,1);(294469172542%positive,1);(18412904307%positive,0);(20226033577850363%positive,1);(75838361925343%positive,1);(357996010261149179%positive,1);(75833731413727%positive,1)] [357996010261149179%positive;350118554573436639%positive;1264127163847358%positive;357996005630637563%positive;20226036011620286%positive;20226038208361979%positive;350118559203948255%positive;20226033577850363%positive;75833731413727%positive;294469172542%positive;22374750417146558%positive;18412904307%positive;357996008064407486%positive;18652752018%positive;75838361925343%positive;85472794202778%positive;87401368736171%positive]]
  | StC => [HMeas MLeft 23 [(75836165182445%positive,2);(357996005630637563%positive,1);(350118559203948255%positive,2);(87401368736171%positive,1);(333878102313%positive,0);(350118557007205357%positive,2);(20226038208361979%positive,1);(350118554573436639%positive,2);(21882409726071789%positive,2);(18412904307%positive,2);(20226033577850363%positive,1);(75838361925343%positive,2);(357996010261149179%positive,1);(75833731413727%positive,2)] [333878102313%positive;75836165182445%positive;357996010261149179%positive;350118554573436639%positive;357996005630637563%positive;20226038208361979%positive;350118559203948255%positive;350118557007205357%positive;21882409726071789%positive;75833731413727%positive;75838361925343%positive;18412904307%positive;20226033577850363%positive;87401368736171%positive]]
  | StD => [HRank [(75836165182445%positive,0);(1264127163847358%positive,0);(20226036011620286%positive,0);(22374750417146558%positive,0);(85472794202778%positive,1);(18652752018%positive,2);(333878102313%positive,3);(350118557007205357%positive,0);(357996008064407486%positive,0);(21882409726071789%positive,0);(294469172542%positive,0)]]
  end.

Lemma cqh_h_00122 : iqh tmq_h_00122.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00122 StA 0 2 2 25 20000
                lsetq_h_00122 rsetq_h_00122 certq_h_00122 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00122); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00123 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StB)
  | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StC)
  end.

Definition lsetq_h_00123 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S1);(StB,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StB,S1)]);(S1,[(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StC,S1);(StB,S1)])];
   [(S1,[(StD,S0)]);(S0,[])]].

Definition rsetq_h_00123 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StC,S1)]);(S1,[(StC,S0)])];
   [(S1,[(StB,S1);(StC,S1)]);(S1,[(StC,S0);(StD,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S1,[(StB,S1);(StC,S1)])]].

Definition certq_h_00123 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 28 [(85478095845086%positive,2);(333895862590%positive,1);(350115188679078638%positive,1);(357433057037219758%positive,2);(21882199358796526%positive,1);(22339566131181486%positive,2);(357433060256871919%positive,2);(76808923870970%positive,0);(18412705650%positive,1);(357433060258969338%positive,0);(294402062126%positive,2);(1396222877202170%positive,0);(1228942877882286%positive,2);(19663088204084719%positive,2);(350118284275185374%positive,2);(19663088206182138%positive,0);(21304670355%positive,2);(75563433162462%positive,2);(4800557741551%positive,2);(87263929824751%positive,2);(19663084984432558%positive,2)] [85478095845086%positive;333895862590%positive;350115188679078638%positive;357433057037219758%positive;21882199358796526%positive;22339566131181486%positive;357433060256871919%positive;76808923870970%positive;18412705650%positive;357433060258969338%positive;294402062126%positive;1396222877202170%positive;1228942877882286%positive;19663088204084719%positive;350118284275185374%positive;19663088206182138%positive;21304670355%positive;75563433162462%positive;4800557741551%positive;87263929824751%positive;19663084984432558%positive]]
  | StC => [HRank [(357433060256871919%positive,0);(19663088204084719%positive,0);(75560213508845%positive,1);(4800557741551%positive,0);(4722579698413%positive,1);(21304670355%positive,0);(350118281055532781%positive,1);(5342380987373%positive,1);(87263929824751%positive,0);(21882392632325869%positive,1)]]
  | StD => [HMeas MRight 28 [(85478095845086%positive,30);(333895862590%positive,30);(350115188679078638%positive,30);(357433057037219758%positive,30);(21882199358796526%positive,30);(22339566131181486%positive,30);(76808923870970%positive,29);(18412705650%positive,29);(75560213508845%positive,0);(357433060258969338%positive,29);(294402062126%positive,30);(1396222877202170%positive,29);(1228942877882286%positive,30);(350118284275185374%positive,30);(4722579698413%positive,0);(19663088206182138%positive,29);(350118281055532781%positive,0);(75563433162462%positive,30);(5342380987373%positive,0);(21882392632325869%positive,0);(19663084984432558%positive,30)] [85478095845086%positive;333895862590%positive;350115188679078638%positive;357433057037219758%positive;21882199358796526%positive;22339566131181486%positive;76808923870970%positive;18412705650%positive;75560213508845%positive;357433060258969338%positive;294402062126%positive;1396222877202170%positive;1228942877882286%positive;350118284275185374%positive;4722579698413%positive;19663088206182138%positive;350118281055532781%positive;75563433162462%positive;5342380987373%positive;21882392632325869%positive;19663084984432558%positive]]
  end.

Lemma cqh_h_00123 : iqh tmq_h_00123.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00123 StA 0 2 2 25 20000
                lsetq_h_00123 rsetq_h_00123 certq_h_00123 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00123); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00124 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StB)
  | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Definition lsetq_h_00124 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S1);(StB,S1)]);(S1,[(StC,S1);(StD,S1)])];
   [(S1,[(StC,S1);(StB,S1)]);(S1,[(StD,S0)])];
   [(S1,[(StC,S1);(StD,S1)]);(S1,[(StC,S1);(StB,S1)])];
   [(S1,[(StD,S0)]);(S0,[])]].

Definition rsetq_h_00124 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StC,S1)]);(S1,[(StC,S0)])];
   [(S1,[(StB,S1);(StC,S1)]);(S1,[(StD,S1);(StC,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StC,S1)]);(S1,[(StB,S1);(StC,S1)])]].

Definition certq_h_00124 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 21 [(20934785171%positive,1);(294737606446%positive,1);(18412705650%positive,0);(19663088206706159%positive,1);(351240610771858927%positive,1);(85477357646814%positive,1);(4800557741551%positive,1);(85752101336559%positive,1);(19663090353141502%positive,1);(351240612918294270%positive,1);(350115260620830430%positive,1);(1228942877882110%positive,1);(21952538038204158%positive,1);(75563435783902%positive,1)] [19663090353141502%positive;294737606446%positive;18412705650%positive;351240612918294270%positive;19663088206706159%positive;85477357646814%positive;350115260620830430%positive;351240610771858927%positive;20934785171%positive;4800557741551%positive;1228942877882110%positive;21952538038204158%positive;75563435783902%positive;85752101336559%positive]]
  | StC => [HMeas MLeft 21 [(75565582217965%positive,1);(20934785171%positive,0);(333895928125%positive,1);(21882203653765101%positive,1);(19663088206706159%positive,1);(350115262767265773%positive,1);(351240610771858927%positive,1);(4722579698413%positive,1);(4800557741551%positive,1);(85752101336559%positive,1)] [19663088206706159%positive;350115262767265773%positive;351240610771858927%positive;75565582217965%positive;20934785171%positive;4722579698413%positive;4800557741551%positive;333895928125%positive;21882203653765101%positive;85752101336559%positive]]
  | StD => [HMeas MRight 21 [(75565582217965%positive,0);(333895928125%positive,23);(21882203653765101%positive,23);(294737606446%positive,23);(18412705650%positive,22);(350115262767265773%positive,23);(4722579698413%positive,0);(85477357646814%positive,23);(19663090353141502%positive,23);(351240612918294270%positive,23);(350115260620830430%positive,23);(1228942877882110%positive,23);(21952538038204158%positive,23);(75563435783902%positive,23)] [19663090353141502%positive;294737606446%positive;18412705650%positive;351240612918294270%positive;350115262767265773%positive;85477357646814%positive;350115260620830430%positive;75565582217965%positive;4722579698413%positive;333895928125%positive;1228942877882110%positive;21952538038204158%positive;21882203653765101%positive;75563435783902%positive]]
  end.

Lemma cqh_h_00124 : iqh tmq_h_00124.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00124 StA 0 2 2 25 20000
                lsetq_h_00124 rsetq_h_00124 certq_h_00124 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00124); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00125 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StB)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => None
  | StD, S1 => None
  end.

Definition lsetq_h_00125 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StC,S1)]);(S1,[(StB,S1);(StC,S1)])];
   [(S1,[(StB,S1);(StC,S1)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0)]);(S0,[])]].

Definition rsetq_h_00125 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S0);(StB,S0)]);(S0,[])];
   [(S1,[(StC,S1);(StB,S1)]);(S0,[(StB,S0);(StB,S0)])];
   [(S1,[(StC,S1);(StB,S1)]);(S1,[(StC,S1);(StB,S1)])]].

Definition certq_h_00125 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 21 [(83414632462046%positive,1);(75207221376734%positive,1);(302682055126742750%positive,1);(20364114066%positive,0);(21354145948038878%positive,1);(325838407982%positive,1);(1203319774574302%positive,1);(341666339401168606%positive,1);(73896984934110%positive,1);(18917628180887262%positive,1)] [341666339401168606%positive;83414632462046%positive;75207221376734%positive;302682055126742750%positive;20364114066%positive;21354145948038878%positive;73896984934110%positive;325838407982%positive;1203319774574302%positive;18917628180887262%positive]]
  | StC => [HMeas MRight 21 [(21354145948038637%positive,1);(73896984933101%positive,1);(4714661343641%positive,0);(83414632461037%positive,1);(75207221376493%positive,1);(302682055126742509%positive,1);(1203319774574061%positive,1);(341666339401168365%positive,1);(18917628180887021%positive,1)] [341666339401168365%positive;75207221376493%positive;83414632461037%positive;21354145948038637%positive;73896984933101%positive;302682055126742509%positive;4714661343641%positive;18917628180887021%positive;1203319774574061%positive]]
  | StD => []
  end.

Lemma cqh_h_00125 : iqh tmq_h_00125.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00125 StA 0 2 2 25 20000
                lsetq_h_00125 rsetq_h_00125 certq_h_00125 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00125); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00126 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StD)
  | StD, S1 => Some (mkTrans S1 DR StB)
  end.

Definition lsetq_h_00126 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StC,S1);(StB,S1);(StC,S1)]);(S1,[(StD,S1);(StC,S1);(StD,S1);(StC,S1)])];
   [(S1,[(StB,S1);(StC,S1);(StD,S0);(StC,S0)]);(S1,[(StD,S1);(StC,S1);(StD,S0)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StC,S1);(StD,S0)]);(S1,[(StD,S0);(StC,S0)])];
   [(S1,[(StD,S1);(StC,S1);(StD,S1);(StC,S1)]);(S1,[(StB,S1);(StC,S1);(StB,S1);(StC,S1)])];
   [(S1,[(StD,S1);(StC,S1);(StD,S1);(StC,S1)]);(S1,[(StB,S1);(StC,S1);(StD,S0);(StC,S0)])]].

Definition rsetq_h_00126 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S0);(StB,S0);(StB,S0)]);(S0,[])];
   [(S0,[(StB,S0);(StB,S0);(StB,S0);(StB,S0)]);(S0,[])];
   [(S1,[(StC,S1);(StB,S1);(StC,S1);(StB,S1)]);(S1,[(StC,S1);(StD,S1);(StC,S1);(StD,S1)])];
   [(S1,[(StC,S1);(StB,S1);(StC,S1);(StD,S0)]);(S1,[(StC,S1);(StD,S1);(StC,S1);(StD,S1)])];
   [(S1,[(StC,S1);(StD,S0)]);(S1,[(StC,S1);(StD,S0);(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StC,S0)]);(S1,[(StC,S1);(StD,S1);(StC,S1);(StD,S0)])];
   [(S1,[(StC,S1);(StD,S1);(StC,S1);(StD,S0)]);(S1,[(StC,S1);(StB,S1);(StC,S1);(StD,S0)])];
   [(S1,[(StC,S1);(StD,S1);(StC,S1);(StD,S1)]);(S0,[(StB,S0);(StB,S0);(StB,S0)])];
   [(S1,[(StC,S1);(StD,S1);(StC,S1);(StD,S1)]);(S0,[(StB,S0);(StB,S0);(StB,S0);(StB,S0)])];
   [(S1,[(StC,S1);(StD,S1);(StC,S1);(StD,S1)]);(S1,[(StC,S1);(StB,S1);(StC,S1);(StB,S1)])]].

Definition certq_h_00126 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 30 [(24719952154506103632233430782%positive,64);(24719949793322862197410623471%positive,64);(23574781220743957921534%positive,64);(298463508626%positive,63);(5168158120174797320552190%positive,64);(395519234472152763815431761903%positive,64);(332758492936272652480391077598%positive,64);(82865611900481565679%positive,0);(323010108750541331361775%positive,64);(375634860517560588711256055518%positive,64);(76406658211627%positive,31);(5168158120174797320613871%positive,64);(1205643411%positive,62);(5177975171407540926%positive,64);(332758492936198343086539464414%positive,64);(91707729618545059101327070%positive,64);(1264428892522814%positive,64);(395519234472152763815431700222%positive,64);(375634860517634898105107668702%positive,64)] [24719952154506103632233430782%positive;24719949793322862197410623471%positive;23574781220743957921534%positive;395519234472152763815431761903%positive;5168158120174797320552190%positive;298463508626%positive;332758492936272652480391077598%positive;82865611900481565679%positive;323010108750541331361775%positive;375634860517560588711256055518%positive;76406658211627%positive;5168158120174797320613871%positive;1205643411%positive;5177975171407540926%positive;332758492936198343086539464414%positive;91707729618545059101327070%positive;1264428892522814%positive;395519234472152763815431700222%positive;375634860517634898105107668702%positive]]
  | StC => [HMeas MRight 30 [(24719949793322862197410623471%positive,1);(395519234472152763815431761903%positive,1);(20797603036282513811959967213%positive,1);(5429500493333904293309421%positive,1);(79098892581111699865%positive,0);(20797603036356823205811711469%positive,1);(82865611900481565679%positive,1);(323010108750541331361775%positive,1);(375634860517634898105107607021%positive,1);(76406658211627%positive,0);(375634860517560588711255862765%positive,1);(5168158120174797320613871%positive,1);(1205643411%positive,1);(332758492936272652480391015917%positive,1);(332758492936198343086539271661%positive,1);(4943680786319481241%positive,0)] [375634860517634898105107607021%positive;76406658211627%positive;1205643411%positive;375634860517560588711255862765%positive;5168158120174797320613871%positive;332758492936272652480391015917%positive;332758492936198343086539271661%positive;20797603036282513811959967213%positive;79098892581111699865%positive;5429500493333904293309421%positive;20797603036356823205811711469%positive;4943680786319481241%positive;24719949793322862197410623471%positive;82865611900481565679%positive;323010108750541331361775%positive;395519234472152763815431761903%positive]]
  | StD => [HMeas MLeft 30 [(24719952154506103632233430782%positive,1);(23574781220743957921534%positive,1);(298463508626%positive,0);(5168158120174797320552190%positive,1);(332758492936272652480391077598%positive,1);(20797603036282513811959967213%positive,1);(5429500493333904293309421%positive,1);(79098892581111699865%positive,1);(20797603036356823205811711469%positive,1);(375634860517560588711256055518%positive,1);(375634860517634898105107607021%positive,1);(375634860517560588711255862765%positive,1);(5177975171407540926%positive,1);(332758492936198343086539464414%positive,1);(332758492936272652480391015917%positive,1);(91707729618545059101327070%positive,1);(332758492936198343086539271661%positive,1);(4943680786319481241%positive,1);(1264428892522814%positive,1);(395519234472152763815431700222%positive,1);(375634860517634898105107668702%positive,1)] [24719952154506103632233430782%positive;23574781220743957921534%positive;298463508626%positive;5168158120174797320552190%positive;332758492936272652480391077598%positive;20797603036282513811959967213%positive;5429500493333904293309421%positive;79098892581111699865%positive;20797603036356823205811711469%positive;375634860517560588711256055518%positive;375634860517634898105107607021%positive;375634860517560588711255862765%positive;5177975171407540926%positive;332758492936198343086539464414%positive;332758492936272652480391015917%positive;91707729618545059101327070%positive;332758492936198343086539271661%positive;4943680786319481241%positive;1264428892522814%positive;395519234472152763815431700222%positive;375634860517634898105107668702%positive]]
  end.

Lemma cqh_h_00126 : iqh tmq_h_00126.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00126 StA 0 4 2 25 20000
                lsetq_h_00126 rsetq_h_00126 certq_h_00126 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00126); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00127 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StB)
  | StC, S0 => Some (mkTrans S1 DL StB)
  | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => None
  | StD, S1 => None
  end.

Definition lsetq_h_00127 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S0);(StB,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StB,S0);(StB,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StC,S1);(StC,S0)])]].

Definition rsetq_h_00127 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StC,S1)]);(S0,[(StB,S1);(StC,S1)])];
   [(S0,[(StB,S1);(StC,S1)]);(S1,[(StC,S0)])];
   [(S0,[(StB,S1);(StC,S1)]);(S1,[(StC,S0);(StB,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S1)]);(S0,[(StB,S1);(StC,S1)])];
   [(S1,[(StC,S0);(StB,S1)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StB,S1)]);(S1,[(StC,S0);(StB,S1)])]].

Definition certq_h_00127 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 68 [(1228616256771802%positive,1);(339413435845932762%positive,0);(21213661725775578%positive,1);(349973901433337262%positive,1);(19663016263382446%positive,1);(75558785873326%positive,1);(21873368702441178%positive,1);(1228938379319002%positive,1);(349973901433337562%positive,0);(349968746046519002%positive,0);(21213339603228378%positive,1);(19663016263382746%positive,0);(349973900007273902%positive,1);(19657860876564186%positive,0);(21873046579893678%positive,1);(18400122738%positive,0);(19663014837319086%positive,1);(339418588380624602%positive,0);(339413434419869102%positive,1);(294401963822%positive,1);(75558785873626%positive,0);(75560211936686%positive,1);(1228616256771502%positive,1);(349968747472582062%positive,1);(19657862302627246%positive,1);(21213661725775278%positive,1);(339418589806687662%positive,1);(349973900007274202%positive,0);(21873368702440878%positive,1);(21873046579893978%positive,1);(75560211936986%positive,0);(19663014837319386%positive,0);(1228938379318702%positive,1);(19657862302627546%positive,0);(349968746046518702%positive,1);(349968747472582362%positive,0);(339413434419869402%positive,0);(339413435845932462%positive,1);(21213339603228078%positive,1);(19657860876563886%positive,1);(339418589806687962%positive,0);(339418588380624302%positive,1)] [339413435845932762%positive;1228616256771802%positive;349973901433337262%positive;21213661725775578%positive;19663016263382446%positive;75558785873326%positive;21873368702441178%positive;1228938379319002%positive;349973901433337562%positive;349968746046519002%positive;21213339603228378%positive;19663016263382746%positive;349973900007273902%positive;19657860876564186%positive;21873046579893678%positive;18400122738%positive;19663014837319086%positive;339418588380624602%positive;339413434419869102%positive;294401963822%positive;75558785873626%positive;75560211936686%positive;1228616256771502%positive;349968747472582062%positive;19657862302627246%positive;21213661725775278%positive;339418589806687662%positive;349973900007274202%positive;21873368702440878%positive;21873046579893978%positive;75560211936986%positive;19663014837319386%positive;1228938379318702%positive;19657862302627546%positive;349968747472582362%positive;349968746046518702%positive;339413434419869402%positive;339413435845932462%positive;21213339603228078%positive;19657860876563886%positive;339418589806687962%positive;339418588380624302%positive]]
  | StC => [HMeas MLeft 68 [(19657862302626541%positive,1);(349968747472581357%positive,1);(82864608145817%positive,1);(339418589806686957%positive,1);(1228616256770797%positive,1);(85442846814617%positive,0);(21213661725774573%positive,1);(339413435845931757%positive,1);(21873368702440173%positive,1);(1228938379317997%positive,1);(339413434419868397%positive,1);(349973901433336557%positive,1);(19657860876563181%positive,1);(349968746046517997%positive,1);(21213339603227373%positive,1);(19663016263381741%positive,1);(339418588380623597%positive,1);(75558785872621%positive,1);(85441588523417%positive,1);(82865866437017%positive,0);(19663014837318381%positive,1);(349973900007273197%positive,1);(21873046579892973%positive,1);(75560211935981%positive,1)] [19657862302626541%positive;349968747472581357%positive;82864608145817%positive;339418589806686957%positive;1228616256770797%positive;85442846814617%positive;21213661725774573%positive;339413435845931757%positive;21873368702440173%positive;1228938379317997%positive;21213339603227373%positive;349973901433336557%positive;349968746046517997%positive;19657860876563181%positive;19663016263381741%positive;339418588380623597%positive;75558785872621%positive;75560211935981%positive;85441588523417%positive;82865866437017%positive;21873046579892973%positive;19663014837318381%positive;349973900007273197%positive;339413434419868397%positive]]
  | StD => []
  end.

Lemma cqh_h_00127 : iqh tmq_h_00127.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00127 StA 0 2 2 25 20000
                lsetq_h_00127 rsetq_h_00127 certq_h_00127 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00127); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00128 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StB)
  | StC, S0 => Some (mkTrans S1 DL StB)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => None
  end.

Definition lsetq_h_00128 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S0);(StB,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StB,S0);(StB,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StB,S1)])];
   [(S1,[(StD,S0);(StB,S1)]);(S1,[(StC,S1);(StC,S0)])]].

Definition rsetq_h_00128 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StC,S1)]);(S0,[(StB,S1);(StD,S0)])];
   [(S0,[(StB,S1);(StD,S0)]);(S0,[(StB,S1);(StC,S1)])];
   [(S0,[(StB,S1);(StD,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StB,S1);(StD,S0)]);(S1,[(StC,S0);(StB,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S1)]);(S0,[(StB,S1);(StD,S0)])]].

Definition certq_h_00128 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 37 [(75563231835099%positive,1);(339405395668629210%positive,0);(1150007794%positive,0);(1228113745597870%positive,2);(21872544068720046%positive,2);(322952306689012699%positive,1);(18411919219%positive,1);(322947152728257499%positive,1);(21212837092054446%positive,2);(75558785872859%positive,1);(322952302243050459%positive,1);(21872544068720346%positive,2);(1228113745598170%positive,2);(349960707295278510%positive,2);(19649822125323694%positive,2);(294402055982%positive,2);(322947148282295259%positive,1);(21212837092054746%positive,2);(19649822125323994%positive,0);(349960707295278810%positive,0);(339405395668628910%positive,2)] [75563231835099%positive;1150007794%positive;339405395668629210%positive;1228113745597870%positive;21872544068720046%positive;322952306689012699%positive;18411919219%positive;322947152728257499%positive;21212837092054446%positive;75558785872859%positive;322952302243050459%positive;21872544068720346%positive;1228113745598170%positive;19649822125323694%positive;349960707295278510%positive;294402055982%positive;322947148282295259%positive;21212837092054746%positive;19649822125323994%positive;349960707295278810%positive;339405395668628910%positive]]
  | StC => [HMeas MLeft 37 [(349960707295277805%positive,1);(19649822125322989%positive,1);(75563231835099%positive,1);(322952306689012699%positive,1);(18411919219%positive,1);(339405395668628205%positive,1);(322947148282295741%positive,1);(322947152728257499%positive,1);(322952306689013181%positive,1);(75558785872859%positive,1);(322952302243050459%positive,1);(4722701989693%positive,1);(322947152728257981%positive,1);(21872544068719341%positive,1);(1228113745597165%positive,1);(322947148282295259%positive,1);(322952302243050941%positive,1);(78845777047961%positive,0);(4722424117053%positive,1);(21212837092053741%positive,1);(78844518756761%positive,1)] [349960707295277805%positive;19649822125322989%positive;75563231835099%positive;322952306689012699%positive;18411919219%positive;339405395668628205%positive;322947148282295741%positive;322947152728257499%positive;322952306689013181%positive;75558785872859%positive;322952302243050459%positive;4722701989693%positive;322947152728257981%positive;21872544068719341%positive;1228113745597165%positive;322947148282295259%positive;322952302243050941%positive;78845777047961%positive;4722424117053%positive;21212837092053741%positive;78844518756761%positive]]
  | StD => [HMeas MLeft 37 [(349960707295277805%positive,4);(19649822125322989%positive,4);(339405395668629210%positive,4);(1150007794%positive,4);(1228113745597870%positive,0);(21872544068720046%positive,0);(339405395668628205%positive,4);(322947148282295741%positive,4);(21212837092054446%positive,0);(322952306689013181%positive,4);(21872544068720346%positive,2);(1228113745598170%positive,2);(4722701989693%positive,4);(322947152728257981%positive,4);(349960707295278510%positive,4);(19649822125323694%positive,4);(21872544068719341%positive,4);(294402055982%positive,4);(1228113745597165%positive,4);(322952302243050941%positive,4);(78845777047961%positive,3);(21212837092054746%positive,2);(19649822125323994%positive,4);(349960707295278810%positive,4);(339405395668628910%positive,4);(4722424117053%positive,4);(21212837092053741%positive,4);(78844518756761%positive,1)] [349960707295277805%positive;19649822125322989%positive;1150007794%positive;339405395668629210%positive;1228113745597870%positive;21872544068720046%positive;339405395668628205%positive;322947148282295741%positive;21212837092054446%positive;322952306689013181%positive;1228113745598170%positive;21872544068720346%positive;4722701989693%positive;322947152728257981%positive;349960707295278510%positive;19649822125323694%positive;21872544068719341%positive;294402055982%positive;1228113745597165%positive;322952302243050941%positive;78845777047961%positive;21212837092054746%positive;19649822125323994%positive;349960707295278810%positive;339405395668628910%positive;4722424117053%positive;21212837092053741%positive;78844518756761%positive]]
  end.

Lemma cqh_h_00128 : iqh tmq_h_00128.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00128 StA 0 2 2 25 20000
                lsetq_h_00128 rsetq_h_00128 certq_h_00128 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00128); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00129 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StB)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => None
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00129 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S0);(StB,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S1)]);(S0,[(StB,S0);(StB,S0)])];
   [(S1,[(StC,S0);(StB,S1)]);(S1,[(StD,S1);(StD,S0)])];
   [(S1,[(StD,S1);(StD,S0)]);(S1,[(StC,S0);(StB,S1)])]].

Definition rsetq_h_00129 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StC,S0)]);(S0,[(StB,S1);(StD,S1)])];
   [(S0,[(StB,S1);(StC,S0)]);(S1,[(StD,S0)])];
   [(S0,[(StB,S1);(StC,S0)]);(S1,[(StD,S0);(StB,S1)])];
   [(S0,[(StB,S1);(StD,S1)]);(S0,[(StB,S1);(StC,S0)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1)]);(S0,[(StB,S1);(StC,S0)])]].

Definition certq_h_00129 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 35 [(20208375173052379%positive,0);(75838043189978%positive,1);(20208372606137791%positive,2);(19621843766661850%positive,2);(1150286195%positive,0);(18411659250%positive,1);(358963507077412287%positive,2);(358963509644326335%positive,2);(313949505414230746%positive,1);(294473357119%positive,2);(339963946149443547%positive,1);(19621263946076890%positive,2);(339963948716357595%positive,0);(358963507077412827%positive,1);(20208375173051839%positive,2);(313940228284871386%positive,1);(358963509644326875%positive,0);(339963946149443007%positive,2);(20208372606138331%positive,1);(339963948716357055%positive,2)] [20208375173052379%positive;75838043189978%positive;20208372606137791%positive;19621843766661850%positive;1150286195%positive;18411659250%positive;358963507077412287%positive;358963509644326335%positive;313949505414230746%positive;294473357119%positive;339963946149443547%positive;19621263946076890%positive;339963948716357595%positive;358963507077412827%positive;20208375173051839%positive;313940228284871386%positive;358963509644326875%positive;339963946149443007%positive;20208372606138331%positive;339963948716357055%positive]]
  | StC => [HMeas MLeft 35 [(20208375173052379%positive,1);(19621263946077613%positive,1);(20208375173051389%positive,1);(20208372606137791%positive,1);(1150286195%positive,1);(313940228284872109%positive,1);(339963946149442557%positive,1);(358963507077412287%positive,1);(339963948716356605%positive,1);(87637575102873%positive,0);(358963509644326335%positive,1);(294473357119%positive,1);(339963946149443547%positive,1);(339963948716357595%positive,1);(358963507077412827%positive,1);(4739877699373%positive,1);(313949505414231469%positive,1);(20208375173051839%positive,1);(20208372606137341%positive,1);(358963507077411837%positive,1);(19621843766662573%positive,1);(358963509644326875%positive,1);(339963946149443007%positive,1);(358963509644325885%positive,1);(20208372606138331%positive,1);(82999010423193%positive,0);(339963948716357055%positive,1)] [20208375173052379%positive;19621263946077613%positive;20208375173051389%positive;20208372606137791%positive;1150286195%positive;313940228284872109%positive;339963946149442557%positive;358963507077412287%positive;339963948716356605%positive;87637575102873%positive;358963509644326335%positive;294473357119%positive;339963946149443547%positive;339963948716357595%positive;358963507077412827%positive;4739877699373%positive;313949505414231469%positive;20208375173051839%positive;20208372606137341%positive;358963507077411837%positive;19621843766662573%positive;358963509644326875%positive;339963946149443007%positive;358963509644325885%positive;20208372606138331%positive;82999010423193%positive;339963948716357055%positive]]
  | StD => [HMeas MLeft 35 [(19621263946077613%positive,2);(75838043189978%positive,2);(20208375173051389%positive,2);(19621843766661850%positive,0);(18411659250%positive,2);(313940228284872109%positive,2);(339963946149442557%positive,2);(339963948716356605%positive,2);(87637575102873%positive,1);(313949505414230746%positive,2);(19621263946076890%positive,0);(4739877699373%positive,2);(313949505414231469%positive,2);(20208372606137341%positive,2);(358963507077411837%positive,2);(313940228284871386%positive,2);(19621843766662573%positive,2);(358963509644325885%positive,2);(82999010423193%positive,1)] [19621263946077613%positive;75838043189978%positive;20208375173051389%positive;19621843766661850%positive;313940228284872109%positive;18411659250%positive;339963946149442557%positive;339963948716356605%positive;87637575102873%positive;313949505414230746%positive;19621263946076890%positive;4739877699373%positive;313949505414231469%positive;20208372606137341%positive;358963507077411837%positive;313940228284871386%positive;19621843766662573%positive;358963509644325885%positive;82999010423193%positive]]
  end.

Lemma cqh_h_00129 : iqh tmq_h_00129.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00129 StA 0 2 2 25 20000
                lsetq_h_00129 rsetq_h_00129 certq_h_00129 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00129); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00130 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StC)
  | StC, S0 => Some (mkTrans S1 DL StC)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S0 DL StD)
  | StD, S1 => Some (mkTrans S0 DR StB)
  end.

Definition lsetq_h_00130 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S0);(StB,S1)]);(S0,[(StD,S1);(StC,S0)])];
   [(S0,[(StD,S1);(StC,S0)]);(S1,[(StC,S1);(StC,S0)])];
   [(S0,[(StD,S1);(StC,S0)]);(S1,[(StC,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StB,S0);(StB,S1)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StB,S0);(StB,S1)])];
   [(S1,[(StC,S1);(StC,S1)]);(S0,[])];
   [(S1,[(StC,S1);(StC,S1)]);(S0,[(StB,S0);(StB,S1)])]].

Definition rsetq_h_00130 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StC,S0)]);(S0,[])];
   [(S0,[(StB,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StB,S1);(StC,S0)]);(S1,[(StC,S0);(StB,S0)])];
   [(S0,[(StB,S1);(StC,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S1,[(StC,S0);(StD,S1)]);(S1,[(StC,S0);(StB,S0)])]].

Definition certq_h_00130 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(357410245040371631%positive,0);(19640272987584431%positive,0);(303393434971722478%positive,1);(357410245038273274%positive,2);(303393434920015258%positive,3);(303393434971723502%positive,1);(357410245040370426%positive,2);(1396133758203823%positive,0);(76719804872623%positive,0);(4629416417006%positive,1);(1396133758202618%positive,2);(303393439214982554%positive,3);(19640270168315642%positive,4);(1396153890863023%positive,0);(19640272987583226%positive,2);(76719804871418%positive,2);(4722781682970%positive,3);(357410245038274479%positive,0);(19640272985487279%positive,0);(303393434971722158%positive,1);(357415399001126831%positive,0);(303372203472680879%positive,0);(1208815973791663%positive,0);(19645426948339631%positive,0);(313948746598373102%positive,1);(357415399001125626%positive,2);(313948746598372078%positive,1);(75563080839599%positive,0);(303393437788893615%positive,0);(1185047658330031%positive,0);(4721925912495%positive,0);(76739937531823%positive,0);(4790477690606%positive,1);(75563082961818%positive,5);(19640270168315822%positive,1);(18417097938%positive,6);(75564506928538%positive,3);(75766422098671%positive,0);(18411329395%positive,1);(294405197102%positive,2);(294581270319%positive,0);(75560263668142%positive,1);(357415398999028474%positive,2);(19640272985486074%positive,2);(75560211961242%positive,3);(18400324818%positive,4);(4722513247514%positive,3);(1396153890861818%positive,2);(19645426948338426%positive,2);(19645426946241274%positive,2);(76739937530618%positive,2);(1150019794%positive,4);(303372203470582522%positive,2);(1208815971693306%positive,2);(357410242221103022%positive,1)]]
  | StC => [HRank [(303393439214981849%positive,0);(1396153890863023%positive,1);(75564506927533%positive,0);(303393439214981549%positive,0);(19640274411573977%positive,0);(294401965357%positive,0);(75563080839599%positive,1);(18400122833%positive,0);(357410242169395117%positive,0);(19640270116607917%positive,0);(303393437788893615%positive,1);(357410246464361177%positive,0);(303372203472680879%positive,1);(75560211960237%positive,0);(19640272985487279%positive,1);(75564506927833%positive,0);(76739937531823%positive,1);(4714726413017%positive,0);(76719804872623%positive,1);(357410245040371631%positive,1);(1208815973791663%positive,1);(294581402937%positive,0);(75766422098671%positive,1);(18411329395%positive,2);(294581270319%positive,1);(357415399001126831%positive,1);(303393434920014253%positive,0);(357410245038274479%positive,1);(1396133758203823%positive,1);(1185047658330031%positive,1);(4721925912495%positive,1);(19645426948339631%positive,1);(19640272987584431%positive,1)]]
  | StD => [HRank [(303393434971722478%positive,0);(357410245038273274%positive,1);(303393434920015258%positive,2);(303393434971723502%positive,0);(357410245040370426%positive,1);(4629416417006%positive,0);(1396133758202618%positive,1);(303393439214982554%positive,2);(19640270168315642%positive,3);(313948746598373102%positive,0);(19645426948338426%positive,1);(4790477690606%positive,0);(76739937530618%positive,1);(75564506927533%positive,2);(19640272987583226%positive,1);(76719804871418%positive,1);(4722781682970%positive,2);(303393434971722158%positive,0);(357415399001125626%positive,1);(1396153890861818%positive,1);(303393439214981549%positive,2);(75560263668142%positive,0);(19640274411573977%positive,1);(313948746598372078%positive,0);(1208815971693306%positive,1);(294401965357%positive,2);(19640272985486074%positive,1);(4722513247514%positive,2);(1150019794%positive,3);(18400122833%positive,4);(75563082961818%positive,4);(19640270168315822%positive,0);(18417097938%positive,5);(75560211961242%positive,2);(75564506928538%positive,2);(18400324818%positive,3);(4714726413017%positive,4);(19645426946241274%positive,1);(75560211960237%positive,2);(303372203470582522%positive,1);(357410242169395117%positive,2);(294405197102%positive,0);(357415398999028474%positive,1);(294581402937%positive,6);(303393434920014253%positive,2);(75564506927833%positive,1);(357410242221103022%positive,0);(303393439214981849%positive,1);(357410246464361177%positive,1);(19640270116607917%positive,2)]]
  end.

Lemma cqh_h_00130 : iqh tmq_h_00130.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00130 StA 0 2 2 25 20000
                lsetq_h_00130 rsetq_h_00130 certq_h_00130 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00130); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00131 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StC)
  | StC, S1 => Some (mkTrans S0 DR StB)
  | StD, S0 => Some (mkTrans S1 DR StD)
  | StD, S1 => Some (mkTrans S0 DL StC)
  end.

Definition lsetq_h_00131 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S0);(StD,S1);(StC,S0);(StB,S0)]);(S0,[(StC,S1);(StD,S0);(StB,S1);(StC,S0)])];
   [(S0,[(StC,S1);(StC,S0)]);(S0,[(StB,S0);(StD,S1);(StC,S0);(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0);(StB,S1);(StC,S0)]);(S1,[(StD,S0);(StC,S1);(StC,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StD,S0);(StB,S1);(StC,S0)]);(S1,[(StD,S0);(StC,S1);(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1);(StC,S0);(StC,S1)]);(S0,[(StB,S0);(StD,S1);(StC,S0);(StB,S0)])];
   [(S1,[(StD,S0);(StC,S1);(StD,S0);(StC,S1)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1);(StD,S0);(StC,S1)]);(S0,[(StB,S0);(StD,S1);(StC,S0);(StB,S0)])]].

Definition rsetq_h_00131 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StB,S0);(StD,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StB,S0);(StD,S1);(StC,S0)]);(S1,[(StC,S0);(StC,S1);(StC,S0)])];
   [(S1,[(StC,S0);(StC,S1);(StC,S0)]);(S1,[(StC,S0);(StB,S0)])]].

Definition certq_h_00131 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(346378814269948161015084920510%positive,0);(21612929773686854039926660074%positive,1);(1288852500653100412350%positive,0);(329788470965272795590078%positive,0);(20289719470313146789310%positive,0);(19310426245750575%positive,1);(84378777989537696759077866%positive,1);(20594315796614646410926%positive,0);(84466237461955669711564222%positive,0);(1267758703223959124399%positive,1);(84378777989537698906630875%positive,2);(80647602274534080190%positive,0);(329787136439631651986410%positive,1);(346378814269948161015084924606%positive,0);(21612929773686854042074143722%positive,1);(81435932105107952509235098%positive,2);(21613017233159272012879146430%positive,0);(81435932105108083751188911%positive,1);(21612929773686854042074213083%positive,2);(346378779750325391581479365611%positive,3);(81435932103982052602392474%positive,2);(1287144737288415400682%positive,3);(329787136439631652055771%positive,2);(346378779750325391581479431147%positive,3);(1287517975011956808682%positive,1);(19293610106670382%positive,0);(84378777989537698906561514%positive,1);(79229222862798658267%positive,2);(5272142341992122277882603%positive,3);(79234848574550650778%positive,2);(79234918943294828442%positive,2);(75365664521426%positive,3);(1287517975011956878043%positive,2);(80647594237307907051%positive,3);(1208941999125786%positive,4);(1150003410%positive,5)]]
  | StC => [HRank [(81435932105108083751188911%positive,0);(329787136439631652055771%positive,1);(1267758703223959124399%positive,0);(1287517975011956878043%positive,1);(80647594237307907051%positive,2);(329787136439534635826861%positive,3);(21612929773686854042074213083%positive,1);(84378777989537698906630875%positive,1);(346378779750325391581479431147%positive,2);(21612929773686853945057984173%positive,3);(19310426245750575%positive,0);(1267758703092717558521%positive,0);(346378779750325391581479365611%positive,2);(84378777989537567530663597%positive,3);(81435932105107952509623033%positive,0);(4709094430545%positive,0);(21612929773686853910698245805%positive,3);(79229222862798658267%positive,1);(308966820090434297%positive,0);(5272142341992122277882603%positive,2);(4951826428419592621%positive,3);(1287517974914940649133%positive,3);(84378777989537601890401965%positive,3)]]
  | StD => [HRank [(21612929773686853910698245805%positive,0);(84378777989537567530663597%positive,0);(346378814269948161015084920510%positive,1);(21612929773686854039926660074%positive,2);(329787136439534635826861%positive,0);(81435932103982052602392474%positive,3);(21612929773686853945057984173%positive,0);(84378777989537601890401965%positive,0);(346378814269948161015084924606%positive,1);(21612929773686854042074143722%positive,2);(1287517974914940649133%positive,0);(80647602274534080190%positive,1);(329787136439631651986410%positive,2);(81435932105107952509235098%positive,3);(1287144737288415400682%positive,4);(1208941999125786%positive,5);(1150003410%positive,6);(4709094430545%positive,7);(19293610106670382%positive,8);(1267758703092717558521%positive,9);(1288852500653100412350%positive,10);(4951826428419592621%positive,0);(20594315796614646410926%positive,1);(81435932105107952509623033%positive,2);(329788470965272795590078%positive,3);(84378777989537696759077866%positive,2);(79234848574550650778%positive,3);(84378777989537698906561514%positive,2);(1287517975011956808682%positive,2);(79234918943294828442%positive,3);(75365664521426%positive,4);(308966820090434297%positive,5);(20289719470313146789310%positive,6);(84466237461955669711564222%positive,10);(21613017233159272012879146430%positive,3)]]
  end.

Lemma cqh_h_00131 : iqh tmq_h_00131.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00131 StA 0 4 2 25 20000
                lsetq_h_00131 rsetq_h_00131 certq_h_00131 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00131); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00132 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DR StC)
  | StC, S0 => Some (mkTrans S1 DL StC)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Definition lsetq_h_00132 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S1)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S0)])]].

Definition rsetq_h_00132 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S1);(StC,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StB,S1);(StC,S1)]);(S1,[(StC,S0);(StB,S1);(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StB,S1);(StC,S1)]);(S1,[(StD,S1);(StD,S0);(StB,S1);(StC,S1)])];
   [(S1,[(StD,S1);(StD,S0);(StB,S1);(StC,S1)]);(S1,[(StC,S1);(StD,S0);(StB,S1);(StC,S1)])]].

Definition certq_h_00132 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 45 [(384842019199245203674016247230%positive,1);(345914586773754214201160892123%positive,0);(21875736092576062%positive,1);(384844437046254732549788462527%positive,1);(345914607802970400670371737023%positive,1);(5340788668563%positive,0);(20286373164956582784731%positive,0);(5278238034102935581285374%positive,1);(84377892658281315956878782%positive,1);(5872260086764530562423806%positive,1);(93956156254128913805213403%positive,0);(79235125651630403290%positive,0);(84377892586223621136374766%positive,1);(345914607803042458127119604734%positive,1);(84452066944144142385802971%positive,0);(384844437046272746811007884286%positive,1);(19311508611099950%positive,1);(384842019199227189174723861486%positive,1);(89603010155035705051%positive,0);(384844437046200689354260016575%positive,1);(1267780024859104570798%positive,1);(84452066998187337914248923%positive,0);(384841998239060192361859772123%positive,0);(75366860945106%positive,1);(84377892640266816664820718%positive,1);(384844416016984502885049171675%positive,0);(345914607803024443865900182975%positive,1);(384841998239114235557388218075%positive,0);(1433657247745151593919%positive,1);(84451803411543394106998491%positive,0);(384842019199173145979195415534%positive,1);(93955571093548030209027518%positive,1)] [384842019199245203674016247230%positive;345914586773754214201160892123%positive;21875736092576062%positive;384844437046254732549788462527%positive;345914607802970400670371737023%positive;5340788668563%positive;20286373164956582784731%positive;5278238034102935581285374%positive;84377892658281315956878782%positive;5872260086764530562423806%positive;93956156254128913805213403%positive;79235125651630403290%positive;84377892586223621136374766%positive;345914607803042458127119604734%positive;84452066944144142385802971%positive;384844437046272746811007884286%positive;19311508611099950%positive;384842019199227189174723861486%positive;89603010155035705051%positive;384844437046200689354260016575%positive;1267780024859104570798%positive;84452066998187337914248923%positive;384841998239060192361859772123%positive;75366860945106%positive;84377892640266816664820718%positive;384844416016984502885049171675%positive;345914607803024443865900182975%positive;384841998239114235557388218075%positive;1433657247745151593919%positive;84451803411543394106998491%positive;384842019199173145979195415534%positive;93955571093548030209027518%positive]]
  | StC => [HRank [(84377892640266951807319789%positive,0);(345914586773754214201160892123%positive,1);(384844437046254732549788462527%positive,0);(84377892586223756278873837%positive,0);(345914607802970400670371737023%positive,0);(5600188439699518445%positive,0);(5340788668563%positive,1);(384842019199227189309866360557%positive,0);(308984137407918829%positive,0);(20286373164956582784731%positive,1);(1267780024962035145453%positive,0);(384842019199173146114337914605%positive,0);(93956156254128913805213403%positive,1);(84452066944144142385802971%positive,1);(84451808545646969309478893%positive,0);(345914607803042458230049849325%positive,0);(93956161388232489007693805%positive,0);(89603010155035705051%positive,1);(384844437046272746913938128877%positive,0);(384844437046200689354260016575%positive,0);(84452066998187337914248923%positive,1);(384841998239060192361859772123%positive,1);(384844416016984502885049171675%positive,1);(345914607803024443865900182975%positive,0);(384841998239114235557388218075%positive,1);(1433657247745151593919%positive,0);(84451803411543394106998491%positive,1)]]
  | StD => [HRank [(384842019199245203674016247230%positive,0);(21875736092576062%positive,0);(1267780024859104570798%positive,0);(84377892586223756278873837%positive,1);(384844437046272746811007884286%positive,0);(345914607803042458127119604734%positive,0);(384842019199227189309866360557%positive,1);(5278238034102935581285374%positive,0);(19311508611099950%positive,0);(1267780024962035145453%positive,1);(5872260086764530562423806%positive,0);(5600188439699518445%positive,1);(84377892658281315956878782%positive,0);(79235125651630403290%positive,1);(84377892586223621136374766%positive,0);(84451808545646969309478893%positive,1);(84377892640266816664820718%positive,0);(345914607803042458230049849325%positive,1);(384842019199173145979195415534%positive,0);(93956161388232489007693805%positive,1);(384842019199227189174723861486%positive,0);(384844437046272746913938128877%positive,1);(384842019199173146114337914605%positive,1);(75366860945106%positive,2);(308984137407918829%positive,3);(84377892640266951807319789%positive,1);(93955571093548030209027518%positive,0)]]
  end.

Lemma cqh_h_00132 : iqh tmq_h_00132.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00132 StA 0 4 2 25 20000
                lsetq_h_00132 rsetq_h_00132 certq_h_00132 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00132); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00133 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DR StC)
  | StC, S0 => Some (mkTrans S1 DL StC)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S0 DL StD)
  | StD, S1 => Some (mkTrans S0 DR StB)
  end.

Definition lsetq_h_00133 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StC,S0)]);(S0,[(StD,S1);(StC,S0)])];
   [(S0,[(StD,S1);(StC,S0)]);(S1,[(StC,S1);(StC,S0)])];
   [(S0,[(StD,S1);(StC,S0)]);(S1,[(StC,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StB,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StB,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S1)]);(S0,[])];
   [(S1,[(StC,S1);(StC,S1)]);(S0,[(StB,S1);(StC,S0)])]].

Definition rsetq_h_00133 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StB,S1)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StB,S1)]);(S1,[(StC,S0);(StD,S1)])];
   [(S1,[(StC,S0);(StD,S1)]);(S1,[(StC,S0);(StB,S0)])]].

Definition certq_h_00133 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(76788524349359%positive,0);(1396202477680559%positive,0);(5179172230894%positive,1);(1396202477679354%positive,2);(75560128049583%positive,0);(357427834273626031%positive,0);(19657862220838831%positive,0);(339422231989244654%positive,1);(357427834271527674%positive,2);(303393434920014554%positive,3);(339422231989245678%positive,1);(357427834273624826%positive,2);(303393439214981850%positive,3);(19640270166873850%positive,4);(75560130171802%positive,5);(18417097938%positive,6);(76788524348154%positive,2);(19657862220837626%positive,2);(75564506927834%positive,3);(19640270166874030%positive,1);(19657862218740474%positive,2);(75766420656879%positive,0);(18399795059%positive,1);(75560211960538%positive,3);(294405106990%positive,2);(18400319186%positive,4)]]
  | StC => [HRank [(294401965357%positive,0);(303393439214982573%positive,0);(75560128049583%positive,1);(357427834273626031%positive,1);(294396853561%positive,0);(75564506928557%positive,0);(19657862220838831%positive,1);(75766420656879%positive,1);(18399795059%positive,2);(1396202477680559%positive,1);(76788524349359%positive,1)]]
  | StD => [HRank [(339422231989244654%positive,0);(19657862218740474%positive,1);(75560211960538%positive,2);(5179172230894%positive,0);(76788524348154%positive,1);(339422231989245678%positive,0);(19657862220837626%positive,1);(75564506927834%positive,2);(18400319186%positive,3);(294401965357%positive,4);(19640270166874030%positive,0);(303393439214982573%positive,1);(1396202477679354%positive,1);(357427834271527674%positive,1);(303393434920014554%positive,2);(357427834273624826%positive,1);(303393439214981850%positive,2);(19640270166873850%positive,3);(75560130171802%positive,4);(18417097938%positive,5);(294396853561%positive,6);(294405106990%positive,0);(75564506928557%positive,1)]]
  end.

Lemma cqh_h_00133 : iqh tmq_h_00133.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00133 StA 0 2 2 25 20000
                lsetq_h_00133 rsetq_h_00133 certq_h_00133 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00133); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00134 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DR StC)
  | StC, S0 => Some (mkTrans S1 DL StC)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S0 DR StB)
  end.

Definition lsetq_h_00134 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StC,S0)]);(S0,[(StD,S1);(StC,S0)])];
   [(S0,[(StD,S1);(StC,S0)]);(S1,[(StC,S1);(StC,S0)])];
   [(S0,[(StD,S1);(StC,S0)]);(S1,[(StC,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StB,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StB,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S1)]);(S0,[])];
   [(S1,[(StC,S1);(StC,S1)]);(S0,[(StB,S1);(StC,S0)])]].

Definition rsetq_h_00134 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StB,S1)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StB,S1)]);(S1,[(StC,S0);(StD,S1)])];
   [(S1,[(StC,S0);(StD,S1)]);(S1,[(StC,S0);(StB,S1)])]].

Definition certq_h_00134 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(76719804872623%positive,0);(4629416417006%positive,1);(76719804871418%positive,2);(19640270034794415%positive,0);(303393434970281710%positive,1);(19640270034793210%positive,2);(4722781682970%positive,3);(75560128050607%positive,0);(19657862352918446%positive,1);(19657862218741679%positive,0);(357427834271528879%positive,0);(339422231989245358%positive,1);(19657862220838831%positive,0);(357427834273626031%positive,0);(339422231989244654%positive,1);(357427834271527674%positive,2);(339422231938978522%positive,3);(76788524349359%positive,0);(1396202477680559%positive,0);(5179172230894%positive,1);(1396202477679354%positive,2);(294396720943%positive,0);(75560262227374%positive,1);(303393434970280686%positive,1);(19640270032696058%positive,2);(339422231855068591%positive,0);(76788524348154%positive,2);(339422231989245678%positive,1);(357427834273624826%positive,2);(339422236233945818%positive,3);(19657862220837626%positive,2);(75564506927834%positive,3);(75835140133615%positive,0);(4722513247514%positive,3);(19657862218740474%positive,2);(357427834405705646%positive,1);(18399795059%positive,1);(19657862352918266%positive,4);(75560130171866%positive,5);(18417098450%positive,6);(75560211960538%positive,3);(1150019794%positive,4);(294405106990%positive,2);(18400319186%positive,4)]]
  | StC => [HRank [(339422236233946541%positive,0);(75564506927533%positive,0);(19640270034794415%positive,1);(294401965357%positive,0);(18400122833%positive,0);(19657862302652333%positive,0);(357427834355439533%positive,0);(339422231855068591%positive,1);(75560211961261%positive,0);(19657862218741679%positive,1);(357427834273626031%positive,1);(339422231938979245%positive,0);(76719804872623%positive,1);(294396853565%positive,0);(75835140133615%positive,1);(75564506928557%positive,0);(19657862220838831%positive,1);(357427834271528879%positive,1);(18399795059%positive,2);(1396202477680559%positive,1);(76788524349359%positive,1);(75560128050607%positive,1);(294396720943%positive,1)]]
  | StD => [HRank [(19657862352918446%positive,0);(357427834405705646%positive,0);(339422236233946541%positive,1);(294405106990%positive,0);(75564506927533%positive,1);(4629416417006%positive,0);(76719804871418%positive,1);(303393434970281710%positive,0);(19640270034793210%positive,1);(4722781682970%positive,2);(339422231989244654%positive,0);(19657862218740474%positive,1);(75560211960538%positive,2);(5179172230894%positive,0);(76788524348154%positive,1);(339422231989245678%positive,0);(19657862220837626%positive,1);(75564506927834%positive,2);(18400319186%positive,3);(294401965357%positive,4);(339422231989245358%positive,0);(357427834271527674%positive,1);(339422231938978522%positive,2);(1396202477679354%positive,1);(75560262227374%positive,0);(303393434970280686%positive,0);(19640270032696058%positive,1);(4722513247514%positive,2);(1150019794%positive,3);(18400122833%positive,4);(19657862302652333%positive,1);(339422231938979245%positive,1);(357427834273624826%positive,1);(339422236233945818%positive,2);(75560211961261%positive,1);(19657862352918266%positive,3);(75560130171866%positive,4);(18417098450%positive,5);(294396853565%positive,6);(75564506928557%positive,1);(357427834355439533%positive,1)]]
  end.

Lemma cqh_h_00134 : iqh tmq_h_00134.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00134 StA 0 2 2 25 20000
                lsetq_h_00134 rsetq_h_00134 certq_h_00134 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00134); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00135 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StB)
  | StC, S0 => Some (mkTrans S1 DL StB)
  | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => None
  | StD, S1 => None
  end.

Definition lsetq_h_00135 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S0);(StB,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StC,S1);(StB,S1)]);(S0,[(StB,S0);(StB,S0)])];
   [(S1,[(StC,S1);(StB,S1)]);(S1,[(StC,S1);(StB,S1)])]].

Definition rsetq_h_00135 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StC,S1)]);(S1,[(StB,S1);(StC,S1)])];
   [(S1,[(StB,S1);(StC,S1)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0)]);(S0,[])]].

Definition certq_h_00135 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 21 [(294603388718%positive,1);(19663088205657822%positive,1);(1228942674286302%positive,1);(18412705650%positive,0);(350114706216679134%positive,1);(75558787446494%positive,1);(21882169090430686%positive,1);(350114710863967966%positive,1);(75563434735326%positive,1);(19663083558368990%positive,1)] [294603388718%positive;75558787446494%positive;18412705650%positive;21882169090430686%positive;350114710863967966%positive;19663088205657822%positive;1228942674286302%positive;350114706216679134%positive;75563434735326%positive;19663083558368990%positive]]
  | StC => [HMeas MLeft 21 [(350114706216678893%positive,1);(1228942674286061%positive,1);(350114710863967725%positive,1);(21882169090430445%positive,1);(19663083558368749%positive,1);(85477223330201%positive,0);(75558787445485%positive,1);(19663088205657581%positive,1);(75563434734317%positive,1)] [350114706216678893%positive;21882169090430445%positive;19663088205657581%positive;19663083558368749%positive;1228942674286061%positive;75563434734317%positive;85477223330201%positive;75558787445485%positive;350114710863967725%positive]]
  | StD => []
  end.

Lemma cqh_h_00135 : iqh tmq_h_00135.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00135 StA 0 2 2 25 20000
                lsetq_h_00135 rsetq_h_00135 certq_h_00135 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00135); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00136 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StC)
  | StC, S1 => Some (mkTrans S0 DR StD)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S0 DR StB)
  end.

Definition lsetq_h_00136 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1);(StC,S0)]);(S1,[(StD,S0);(StD,S1);(StC,S0);(StB,S0)])];
   [(S0,[(StC,S1);(StB,S1);(StC,S0);(StB,S0)]);(S1,[(StD,S0);(StD,S1);(StC,S0);(StD,S1)])];
   [(S0,[(StC,S1);(StB,S1);(StC,S0);(StC,S1)]);(S1,[(StD,S0);(StD,S1);(StC,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1);(StC,S0);(StD,S1)]);(S1,[(StD,S0);(StD,S1);(StC,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1);(StC,S0)])];
   [(S0,[(StC,S1);(StD,S0);(StD,S1);(StC,S0)]);(S0,[(StC,S1);(StA,S0)])];
   [(S0,[(StC,S1);(StD,S0);(StD,S1);(StC,S0)]);(S0,[(StC,S1);(StB,S1);(StC,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StD,S0);(StD,S1);(StC,S0)]);(S0,[(StC,S1);(StB,S1);(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S0)]);(S0,[(StC,S1);(StB,S1);(StC,S0);(StB,S0)])];
   [(S0,[(StD,S1);(StC,S0)]);(S0,[(StC,S1);(StD,S0)])];
   [(S1,[(StD,S0);(StD,S1);(StC,S0);(StB,S0)]);(S0,[(StC,S1);(StB,S1);(StC,S0);(StD,S1)])];
   [(S1,[(StD,S0);(StD,S1);(StC,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0);(StD,S1);(StC,S0)])];
   [(S1,[(StD,S0);(StD,S1);(StC,S0);(StD,S1)]);(S0,[(StC,S1);(StB,S1);(StC,S0);(StC,S1)])]].

Definition rsetq_h_00136 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StC,S1);(StD,S0)]);(S1,[(StC,S0);(StD,S1);(StC,S0)])];
   [(S1,[(StC,S0);(StD,S1);(StC,S0)]);(S1,[(StC,S0);(StB,S0)])]].

Definition certq_h_00136 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(4710365525295%positive,0);(81436005890900077619371695%positive,0);(21651613407756244100926910398%positive,1);(81436005890900239194369514%positive,2);(1287145076990262858490%positive,3);(1208941885881626%positive,4);(19343072136983870%positive,1);(18399865330%positive,2);(75345520324435%positive,3);(309036961043968734%positive,4);(1267608693856456219387%positive,5);(20594320105955036311471%positive,0);(81436005824331372842707678%positive,1);(84576692173425735661644539%positive,2);(4952178311434293679%positive,0);(329509054997805973830366%positive,1);(5089750358473591013894907%positive,2);(21651633196500820403017870075%positive,2);(1353227074948148790492847791%positive,0);(22231897801171266139145220030%positive,1);(84576692184259296619343338%positive,2);(19881837353749200196586%positive,3);(314244320810980090%positive,4);(19314841472136495%positive,0);(79234844942785256158%positive,1);(5272143563863073123138299%positive,2);(1302976091873071373193964283%positive,2);(21651633196518834801527352059%positive,2);(1302976091891085771703446267%positive,2);(4722579307802%positive,5);(1150019794%positive,6)]]
  | StC => [HRank [(18404251601%positive,0);(4710365525295%positive,1);(4709087352785%positive,0);(1302976091891085771703446267%positive,0);(5089750358473591013894907%positive,0);(1302976091873071373193964283%positive,0);(20594315937361222774701%positive,1);(5272143563863073123138299%positive,0);(4952177808292434349%positive,1);(1267608693856456219387%positive,0);(84576692173425735661644539%positive,0);(21651633196500820403017870075%positive,0);(75345520324435%positive,0);(21651633196518834801527352059%positive,0);(5089750364020709152079533%positive,1);(1207175629077805%positive,1);(4952178311434293679%positive,2);(20594320105955036311471%positive,2);(1353227074948148790492847791%positive,2);(81436005890900077619371695%positive,2);(19314841472136495%positive,1)]]
  | StD => [HRank [(22231897801171266139145220030%positive,0);(84576692184259296619343338%positive,1);(19881837353749200196586%positive,2);(314244320810980090%positive,3);(4722579307802%positive,4);(21651613407756244100926910398%positive,0);(81436005890900239194369514%positive,1);(1287145076990262858490%positive,2);(1208941885881626%positive,3);(1150019794%positive,5);(4709087352785%positive,6);(20594315937361222774701%positive,0);(4952177808292434349%positive,0);(309036961043968734%positive,0);(5089750364020709152079533%positive,0);(19343072136983870%positive,0);(1207175629077805%positive,0);(18399865330%positive,1);(81436005824331372842707678%positive,0);(329509054997805973830366%positive,0);(18404251601%positive,6);(79234844942785256158%positive,0)]]
  end.

Lemma cqh_h_00136 : iqh tmq_h_00136.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00136 StA 0 4 2 25 20000
                lsetq_h_00136 rsetq_h_00136 certq_h_00136 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00136); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00137 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StC)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StB)
  end.

Definition lsetq_h_00137 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S1);(StB,S1)]);(S1,[(StD,S0)])];
   [(S1,[(StC,S1);(StB,S1)]);(S1,[(StD,S0);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StD,S1)]);(S1,[(StC,S1);(StB,S1)])]].

Definition rsetq_h_00137 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StC,S0)]);(S0,[])];
   [(S0,[(StD,S1);(StC,S1)]);(S1,[(StB,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S1,[(StB,S1);(StD,S0)])];
   [(S1,[(StB,S1);(StC,S1)]);(S0,[(StD,S1);(StC,S0)])];
   [(S1,[(StB,S1);(StD,S0)]);(S0,[(StD,S1);(StC,S1)])]].

Definition certq_h_00137 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 29 [(85714520372719%positive,32);(1209366082352862%positive,32);(4722579699646%positive,0);(75565380892606%positive,0);(323093594137031646%positive,32);(19691942131496699%positive,31);(315071078209648379%positive,31);(78880271102942%positive,32);(4715600376571%positive,31);(76921648575983%positive,32);(315071076264441327%positive,32);(294603323183%positive,28);(350115191901254622%positive,32);(18412715506%positive,30);(351086679143871983%positive,32);(21942917311461115%positive,31);(20926396563%positive,32);(85477340869598%positive,32);(351086681089079035%positive,31)] [85714520372719%positive;1209366082352862%positive;4722579699646%positive;75565380892606%positive;323093594137031646%positive;19691942131496699%positive;315071078209648379%positive;78880271102942%positive;4715600376571%positive;76921648575983%positive;315071076264441327%positive;294603323183%positive;350115191901254622%positive;18412715506%positive;351086679143871983%positive;21942917311461115%positive;20926396563%positive;85477340869598%positive;351086681089079035%positive]]
  | StC => [HMeas MLeft 29 [(308126058813%positive,1);(85714520372719%positive,1);(19691942131496699%positive,1);(315071078209648379%positive,1);(333895862589%positive,1);(4715600376571%positive,1);(76921648575983%positive,1);(315071076264441327%positive,1);(294603323183%positive,1);(20193349498533821%positive,1);(21882199358797757%positive,1);(323093596082239421%positive,1);(351086679143871983%positive,1);(21942917311461115%positive,1);(20926396563%positive,0);(350115193846462397%positive,1);(75585245115373%positive,1);(351086681089079035%positive,1);(1209368027558893%positive,1)] [308126058813%positive;85714520372719%positive;19691942131496699%positive;315071078209648379%positive;333895862589%positive;4715600376571%positive;76921648575983%positive;315071076264441327%positive;294603323183%positive;20193349498533821%positive;21882199358797757%positive;323093596082239421%positive;351086679143871983%positive;21942917311461115%positive;20926396563%positive;350115193846462397%positive;75585245115373%positive;351086681089079035%positive;1209368027558893%positive]]
  | StD => [HRank [(308126058813%positive,0);(1209366082352862%positive,0);(4722579699646%positive,0);(75565380892606%positive,0);(323093594137031646%positive,0);(333895862589%positive,0);(78880271102942%positive,0);(20193349498533821%positive,0);(350115191901254622%positive,0);(18412715506%positive,1);(21882199358797757%positive,0);(323093596082239421%positive,0);(350115193846462397%positive,0);(85477340869598%positive,0);(75585245115373%positive,0);(1209368027558893%positive,0)]]
  end.

Lemma cqh_h_00137 : iqh tmq_h_00137.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00137 StA 0 2 2 25 20000
                lsetq_h_00137 rsetq_h_00137 certq_h_00137 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00137); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00138 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Definition lsetq_h_00138 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S0);(StB,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StC,S1);(StB,S1)]);(S1,[(StC,S1);(StD,S1)])];
   [(S1,[(StC,S1);(StD,S0)]);(S1,[(StC,S1);(StD,S1)])];
   [(S1,[(StC,S1);(StD,S1)]);(S0,[(StB,S0);(StB,S0)])];
   [(S1,[(StC,S1);(StD,S1)]);(S1,[(StC,S1);(StB,S1)])]].

Definition rsetq_h_00138 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StC,S1)]);(S1,[(StD,S1);(StC,S0)])];
   [(S1,[(StB,S1);(StC,S1)]);(S1,[(StD,S1);(StC,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StC,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StC,S1)]);(S1,[(StB,S1);(StC,S1)])]].

Definition certq_h_00138 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 24 [(20208991082608350%positive,27);(315211815899330543%positive,27);(4740028692271%positive,0);(351240612918294511%positive,27);(75840460124926%positive,27);(20208995729897182%positive,27);(350115255973541598%positive,27);(18421096306%positive,26);(21952537834608382%positive,27);(315211815899330302%positive,27);(19700738020923134%positive,27);(1150269811%positive,25);(19700738020923375%positive,27);(294603454270%positive,27);(351240612918294270%positive,27);(350115260620830430%positive,27);(21952537834608623%positive,27)] [351240612918294511%positive;20208991082608350%positive;21952537834608382%positive;315211815899330543%positive;4740028692271%positive;351240612918294270%positive;75840460124926%positive;350115260620830430%positive;315211815899330302%positive;19700738020923134%positive;1150269811%positive;20208995729897182%positive;350115255973541598%positive;21952537834608623%positive;294603454270%positive;19700738020923375%positive;18421096306%positive]]
  | StC => [HMeas MLeft 24 [(315211815899330543%positive,1);(4740028692271%positive,1);(350115255973541357%positive,1);(20208995729896429%positive,1);(351240612918294511%positive,1);(350115260620830189%positive,1);(20208991082607597%positive,1);(85477357547929%positive,0);(1150269811%positive,1);(19700738020923375%positive,1);(21952537834608623%positive,1)] [351240612918294511%positive;315211815899330543%positive;4740028692271%positive;350115255973541357%positive;85477357547929%positive;1150269811%positive;21952537834608623%positive;20208995729896429%positive;350115260620830189%positive;19700738020923375%positive;20208991082607597%positive]]
  | StD => [HMeas MRight 24 [(20208991082608350%positive,1);(350115255973541357%positive,1);(20208995729896429%positive,1);(75840460124926%positive,1);(20208995729897182%positive,1);(350115255973541598%positive,1);(350115260620830189%positive,1);(20208991082607597%positive,1);(18421096306%positive,0);(21952537834608382%positive,1);(315211815899330302%positive,1);(85477357547929%positive,1);(19700738020923134%positive,1);(294603454270%positive,1);(351240612918294270%positive,1);(350115260620830430%positive,1)] [20208991082608350%positive;21952537834608382%positive;351240612918294270%positive;350115255973541357%positive;75840460124926%positive;350115260620830430%positive;315211815899330302%positive;85477357547929%positive;19700738020923134%positive;20208995729897182%positive;350115255973541598%positive;294603454270%positive;20208995729896429%positive;350115260620830189%positive;20208991082607597%positive;18421096306%positive]]
  end.

Lemma cqh_h_00138 : iqh tmq_h_00138.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00138 StA 0 2 2 25 20000
                lsetq_h_00138 rsetq_h_00138 certq_h_00138 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00138); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00139 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S1 DR StB)
  | StC, S0 => Some (mkTrans S1 DL StC)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S0 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Definition lsetq_h_00139 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0);(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0);(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StC,S0)]);(S1,[(StB,S1);(StC,S0);(StB,S0)])];
   [(S1,[(StB,S1);(StC,S0);(StB,S0)]);(S1,[(StB,S1);(StC,S1);(StB,S1);(StC,S0)])];
   [(S1,[(StB,S1);(StC,S1);(StB,S1);(StC,S0)]);(S1,[(StB,S1);(StD,S1);(StB,S1);(StC,S0)])];
   [(S1,[(StB,S1);(StC,S1);(StB,S1);(StC,S1)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StB,S1);(StC,S1);(StB,S1);(StC,S1)]);(S0,[(StD,S0);(StD,S0);(StD,S0)])];
   [(S1,[(StB,S1);(StC,S1);(StB,S1);(StC,S1)]);(S0,[(StD,S0);(StD,S0);(StD,S0);(StD,S0)])];
   [(S1,[(StB,S1);(StC,S1);(StB,S1);(StC,S1)]);(S1,[(StB,S1);(StD,S1);(StB,S1);(StD,S1)])];
   [(S1,[(StB,S1);(StD,S1);(StB,S1);(StC,S0)]);(S1,[(StB,S1);(StC,S1);(StB,S1);(StC,S1)])];
   [(S1,[(StB,S1);(StD,S1);(StB,S1);(StD,S1)]);(S1,[(StB,S1);(StC,S1);(StB,S1);(StC,S1)])]].

Definition rsetq_h_00139 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S1);(StB,S1);(StC,S0)]);(S1,[(StC,S0);(StB,S0)])];
   [(S1,[(StC,S1);(StB,S1);(StC,S1);(StB,S1)]);(S1,[(StD,S1);(StB,S1);(StC,S0);(StB,S0)])];
   [(S1,[(StC,S1);(StB,S1);(StC,S1);(StB,S1)]);(S1,[(StD,S1);(StB,S1);(StD,S1);(StB,S1)])];
   [(S1,[(StD,S1);(StB,S1);(StC,S0);(StB,S0)]);(S1,[(StC,S1);(StB,S1);(StC,S0)])];
   [(S1,[(StD,S1);(StB,S1);(StD,S1);(StB,S1)]);(S1,[(StC,S1);(StB,S1);(StC,S1);(StB,S1)])]].

Definition certq_h_00139 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 37 [(5089742293446818899368671%positive,1);(376256210462429086717010501599%positive,1);(358233283783200316251870%positive,1);(87603975660709854139%positive,0);(23516013153897155146676690911%positive,1);(22389580236450019335902%positive,1);(5731732540531205066907358%positive,1);(1302919059011753145198108639%positive,1);(376256210462354485952577527775%positive,1);(80446546131260207838%positive,1);(375634823776332389324290449118%positive,1);(75558867791642%positive,0);(342203029924647867%positive,0);(1149991122%positive,1);(333547279107083467232990388191%positive,1);(20846704944188053928925126623%positive,1);(1469750822118571971307888607%positive,1);(333547279107008866468557414367%positive,1);(5475248478794365883%positive,0);(21583891079891801029962030814%positive,1)] [5089742293446818899368671%positive;376256210462429086717010501599%positive;358233283783200316251870%positive;87603975660709854139%positive;23516013153897155146676690911%positive;22389580236450019335902%positive;5731732540531205066907358%positive;1302919059011753145198108639%positive;376256210462354485952577527775%positive;80446546131260207838%positive;375634823776332389324290449118%positive;75558867791642%positive;342203029924647867%positive;1149991122%positive;333547279107083467232990388191%positive;20846704944188053928925126623%positive;1469750822118571971307888607%positive;333547279107008866468557414367%positive;5475248478794365883%positive;21583891079891801029962030814%positive]]
  | StC => [HMeas MRight 37 [(5089742293446818899368671%positive,1);(375634823776332389324290387437%positive,1);(376256210462429086717010501599%positive,1);(294317954801%positive,0);(81435876785221232376262141%positive,1);(87603975660709854139%positive,1);(23516013153897155146676690911%positive,1);(1205853802557229%positive,1);(4951910064311431597%positive,1);(1302919059011753145198108639%positive,1);(376256210462354485952577527775%positive,1);(333547279107083467232990592509%positive,1);(342203029924647867%positive,1);(20846704944188053928925330941%positive,1);(20594320313204807249389%positive,1);(358233283783200316190189%positive,1);(333547279107083467232990388191%positive,1);(333547279107008866468557618685%positive,1);(20846704944188053928925126623%positive,1);(1469750822118571971307888607%positive,1);(21583891079891801201760923117%positive,1);(376256210462429086717010378237%positive,1);(5731732540531205066845677%positive,1);(23516013153897155146676567549%positive,1);(333547279107008866468557414367%positive,1);(5475248478794365883%positive,1);(376256210462354485952577404413%positive,1)] [5089742293446818899368671%positive;375634823776332389324290387437%positive;376256210462429086717010501599%positive;294317954801%positive;81435876785221232376262141%positive;87603975660709854139%positive;23516013153897155146676690911%positive;1205853802557229%positive;4951910064311431597%positive;1302919059011753145198108639%positive;376256210462354485952577527775%positive;333547279107083467232990592509%positive;342203029924647867%positive;20846704944188053928925330941%positive;20594320313204807249389%positive;358233283783200316190189%positive;333547279107083467232990388191%positive;333547279107008866468557618685%positive;20846704944188053928925126623%positive;1469750822118571971307888607%positive;21583891079891801201760923117%positive;376256210462429086717010378237%positive;5731732540531205066845677%positive;23516013153897155146676567549%positive;333547279107008866468557414367%positive;5475248478794365883%positive;376256210462354485952577404413%positive]]
  | StD => [HMeas MRight 37 [(375634823776332389324290387437%positive,78);(294317954801%positive,77);(81435876785221232376262141%positive,78);(358233283783200316251870%positive,78);(22389580236450019335902%positive,78);(1205853802557229%positive,78);(5731732540531205066907358%positive,78);(4951910064311431597%positive,78);(80446546131260207838%positive,0);(375634823776332389324290449118%positive,78);(75558867791642%positive,38);(333547279107083467232990592509%positive,78);(20846704944188053928925330941%positive,78);(20594320313204807249389%positive,78);(358233283783200316190189%positive,78);(1149991122%positive,76);(333547279107008866468557618685%positive,78);(21583891079891801201760923117%positive,78);(376256210462429086717010378237%positive,78);(5731732540531205066845677%positive,78);(23516013153897155146676567549%positive,78);(376256210462354485952577404413%positive,78);(21583891079891801029962030814%positive,78)] [375634823776332389324290387437%positive;294317954801%positive;81435876785221232376262141%positive;358233283783200316251870%positive;22389580236450019335902%positive;1205853802557229%positive;5731732540531205066907358%positive;4951910064311431597%positive;80446546131260207838%positive;375634823776332389324290449118%positive;75558867791642%positive;333547279107083467232990592509%positive;20846704944188053928925330941%positive;20594320313204807249389%positive;358233283783200316190189%positive;1149991122%positive;333547279107008866468557618685%positive;21583891079891801201760923117%positive;376256210462429086717010378237%positive;5731732540531205066845677%positive;23516013153897155146676567549%positive;376256210462354485952577404413%positive;21583891079891801029962030814%positive]]
  end.

Lemma cqh_h_00139 : iqh tmq_h_00139.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00139 StA 0 4 2 25 20000
                lsetq_h_00139 rsetq_h_00139 certq_h_00139 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00139); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00140 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S0 DL StC)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StC)
  end.

Definition lsetq_h_00140 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StC,S1)]);(S1,[(StD,S0)])];
   [(S1,[(StB,S1);(StC,S1)]);(S1,[(StD,S0);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S0)]);(S1,[(StB,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StD,S1)]);(S1,[(StB,S1);(StC,S1)])]].

Definition rsetq_h_00140 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StB,S0)]);(S0,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S1)]);(S1,[(StC,S1);(StD,S0)])];
   [(S1,[(StC,S1);(StD,S0)]);(S0,[(StC,S0);(StB,S0)])];
   [(S1,[(StC,S1);(StD,S0)]);(S0,[(StD,S1);(StB,S1)])]].

Definition certq_h_00140 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 23 [(303236209926665723%positive,1);(19499469078196926%positive,1);(83515564226271%positive,1);(75496661905835%positive,1);(303236208987600607%positive,1);(20389542035%positive,0);(74032276436703%positive,1);(75495720219290%positive,0);(21379984538400251%positive,1);(18399335634%positive,1);(342079756712736251%positive,1);(308658735422%positive,1);(18952262864270843%positive,1);(1218716561240766%positive,1);(323652147989641150%positive,1);(20228258993207230%positive,1);(342079755773671135%positive,1)] [303236209926665723%positive;19499469078196926%positive;75495720219290%positive;303236208987600607%positive;83515564226271%positive;75496661905835%positive;20389542035%positive;74032276436703%positive;21379984538400251%positive;18399335634%positive;308658735422%positive;18952262864270843%positive;1218716561240766%positive;323652147989641150%positive;20228258993207230%positive;342079755773671135%positive;342079756712736251%positive]]
  | StC => [HMeas MRight 23 [(303236209926665723%positive,1);(79016636314605%positive,2);(83515564226271%positive,2);(19499468139131885%positive,2);(75496661905835%positive,1);(323652147050574829%positive,2);(303236208987600607%positive,2);(20389542035%positive,2);(74032276436703%positive,2);(294666198825%positive,0);(21379984538400251%positive,1);(342079756712736251%positive,1);(18952262864270843%positive,1);(342079755773671135%positive,2)] [303236209926665723%positive;83515564226271%positive;19499468139131885%positive;79016636314605%positive;303236208987600607%positive;294666198825%positive;75496661905835%positive;20389542035%positive;323652147050574829%positive;74032276436703%positive;21379984538400251%positive;18952262864270843%positive;342079755773671135%positive;342079756712736251%positive]]
  | StD => [HRank [(19499469078196926%positive,0);(79016636314605%positive,0);(19499468139131885%positive,0);(323652147050574829%positive,0);(1218716561240766%positive,0);(75495720219290%positive,1);(18399335634%positive,2);(294666198825%positive,3);(308658735422%positive,0);(323652147989641150%positive,0);(20228258993207230%positive,0)]]
  end.

Lemma cqh_h_00140 : iqh tmq_h_00140.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00140 StA 0 2 2 25 20000
                lsetq_h_00140 rsetq_h_00140 certq_h_00140 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00140); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00141 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StB)
  | StB, S1 => Some (mkTrans S0 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StC)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StD)
  | StD, S1 => Some (mkTrans S0 DL StB)
  end.

Definition lsetq_h_00141 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StB,S1);(StC,S0);(StB,S1)]);(S1,[(StC,S0);(StD,S1);(StC,S1);(StC,S0)])];
   [(S1,[(StC,S0);(StB,S1);(StD,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StD,S1);(StC,S1);(StC,S0)]);(S1,[(StC,S0);(StB,S1);(StD,S0)])]].

Definition rsetq_h_00141 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StC,S0);(StB,S1);(StC,S0)]);(S0,[(StD,S1);(StC,S0);(StD,S1);(StC,S0)])];
   [(S0,[(StD,S1);(StC,S0);(StB,S1);(StD,S0)]);(S1,[(StC,S1);(StC,S0);(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StC,S0);(StD,S1);(StC,S0)]);(S1,[(StC,S1);(StC,S1);(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S0);(StD,S1);(StC,S0)]);(S1,[(StC,S1);(StC,S1);(StC,S1);(StB,S0)])];
   [(S0,[(StD,S1);(StC,S0);(StD,S1);(StC,S0)]);(S1,[(StC,S1);(StC,S1);(StC,S1);(StC,S0)])];
   [(S0,[(StD,S1);(StC,S0);(StD,S1);(StC,S0)]);(S1,[(StC,S1);(StC,S1);(StC,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StC,S1);(StC,S0)]);(S0,[(StB,S1);(StC,S0);(StB,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0);(StD,S1);(StC,S1)]);(S0,[(StB,S1);(StC,S0);(StB,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S1);(StC,S0);(StD,S1)]);(S0,[(StB,S1);(StC,S0);(StB,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S1);(StC,S1);(StB,S0)]);(S0,[])];
   [(S1,[(StC,S1);(StC,S1);(StC,S1);(StC,S0)]);(S0,[(StB,S1);(StC,S0);(StB,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S1);(StC,S1);(StC,S1)]);(S0,[])];
   [(S1,[(StC,S1);(StC,S1);(StC,S1);(StC,S1)]);(S0,[(StB,S1);(StC,S0);(StB,S1);(StC,S0)])]].

Definition certq_h_00141 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(5267124108363128737476527%positive,0);(21651808131361361027927571182%positive,1);(5267123905701145505684218%positive,2);(5617639062531306202%positive,3);(4927926266002%positive,4);(345186231398587258058151800751%positive,0);(346428930101832636443028287214%positive,1);(345186155840723532143828073210%positive,2);(21622680723046560203646622426%positive,3);(346428930101832636443028549358%positive,1);(345186231398587258058151492346%positive,2);(5268901481033691821485999%positive,0);(79077416943712923374%positive,1);(5268901481033691821177594%positive,2);(24098560801617320753444870874%positive,3);(79077416943712595694%positive,1);(5174454151376298916903674%positive,2);(21003710703403870066197060314%positive,3);(345186155840723532143828381615%positive,0);(346428930101832636443028598510%positive,1);(345186245565686706667087133434%positive,2);(24562788316349338356532042458%positive,3);(330380373098166157258490%positive,4);(313944979909735386%positive,5);(5041204423494857455%positive,0);(300099266706%positive,6);(80369932643142679983%positive,0);(5286085969570658516135854%positive,1);(4790420224147%positive,1);(19692204779276590%positive,2)]]
  | StC => [HRank [(21003710703403870066197245357%positive,0);(91503517018063580589%positive,0);(5267124108363128737476527%positive,1);(1226347577772349%positive,0);(5041204423494857455%positive,1);(21943902588012845%positive,0);(80369932643142679983%positive,1);(21622680723046560203646807469%positive,0);(24098560801617320753445055917%positive,0);(5268901481033691821485999%positive,1);(345186231398587258058151800751%positive,1);(4790420224147%positive,2);(345186155840723532143828381615%positive,1)]]
  | StD => [HRank [(21651808131361361027927571182%positive,0);(5267123905701145505684218%positive,1);(5617639062531306202%positive,2);(4927926266002%positive,3);(5286085969570658516135854%positive,0);(21003710703403870066197245357%positive,1);(346428930101832636443028287214%positive,0);(345186155840723532143828073210%positive,1);(21622680723046560203646622426%positive,2);(346428930101832636443028549358%positive,0);(345186231398587258058151492346%positive,1);(79077416943712923374%positive,0);(5268901481033691821177594%positive,1);(24098560801617320753444870874%positive,2);(79077416943712595694%positive,0);(5174454151376298916903674%positive,1);(21003710703403870066197060314%positive,2);(346428930101832636443028598510%positive,0);(345186245565686706667087133434%positive,1);(24562788316349338356532042458%positive,2);(330380373098166157258490%positive,3);(313944979909735386%positive,4);(19692204779276590%positive,0);(91503517018063580589%positive,1);(300099266706%positive,5);(21622680723046560203646807469%positive,1);(1226347577772349%positive,6);(21943902588012845%positive,4);(24098560801617320753445055917%positive,1)]]
  end.

Lemma cqh_h_00141 : iqh tmq_h_00141.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00141 StA 0 4 2 25 20000
                lsetq_h_00141 rsetq_h_00141 certq_h_00141 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00141); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00142 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StB)
  | StB, S1 => Some (mkTrans S0 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StC)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00142 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S1);(StC,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StB,S1);(StC,S1)]);(S1,[(StC,S0);(StB,S1);(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StB,S1);(StC,S1)]);(S1,[(StD,S1);(StD,S0);(StB,S1);(StC,S1)])];
   [(S1,[(StD,S1);(StD,S0);(StB,S1);(StC,S1)]);(S1,[(StC,S1);(StD,S0);(StB,S1);(StC,S1)])]].

Definition rsetq_h_00142 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S1)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S0)])]].

Definition certq_h_00142 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 45 [(395434628540408145892022414782%positive,1);(94123810330937555797929691%positive,0);(76808992811154%positive,1);(23569740566034747076315%positive,0);(1272372447534352952767%positive,1);(5425914401840887569505278%positive,1);(385531127115520226622573047231%positive,1);(385531127115591039569448332735%positive,1);(4714649329523%positive,0);(89763438484673474266%positive,0);(395434628540337337304932941531%positive,0);(395434628540408150251808227035%positive,0);(5425914472653834444790782%positive,1);(395434571953867782681404038142%positive,1);(86814638285051640077876955%positive,0);(19311202604547902%positive,1);(385531127115591035133283790555%positive,0);(86814638355864586953162459%positive,0);(355820491877327230204005243886%positive,1);(395434571953796969734528752638%positive,1);(1473108574575881547182%positive,1);(86870237274720671616130030%positive,1);(21914904931240238%positive,1);(86870255413249780749692635%positive,0);(96541657358480660797517246%positive,1);(86814638355860227167350206%positive,1);(385531052820176356801584225262%positive,1);(94123792192408446664367086%positive,1);(355820566172671100024994065855%positive,1);(355820566172741908535704809179%positive,0);(355820566172741912971869351359%positive,1);(79523277693636787931%positive,0)] [395434628540408145892022414782%positive;94123810330937555797929691%positive;76808992811154%positive;23569740566034747076315%positive;1272372447534352952767%positive;5425914401840887569505278%positive;385531127115520226622573047231%positive;385531127115591039569448332735%positive;4714649329523%positive;89763438484673474266%positive;395434628540337337304932941531%positive;395434628540408150251808227035%positive;5425914472653834444790782%positive;395434571953867782681404038142%positive;86814638285051640077876955%positive;19311202604547902%positive;385531127115591035133283790555%positive;86814638355864586953162459%positive;355820491877327230204005243886%positive;395434571953796969734528752638%positive;1473108574575881547182%positive;86870237274720671616130030%positive;21914904931240238%positive;86870255413249780749692635%positive;96541657358480660797517246%positive;86814638355860227167350206%positive;385531052820176356801584225262%positive;94123792192408446664367086%positive;355820566172671100024994065855%positive;355820566172741908535704809179%positive;355820566172741912971869351359%positive;79523277693636787931%positive]]
  | StC => [HRank [(385531127115591035171410132717%positive,0);(86814638285051678330044397%positive,0);(395434628540408150290060394477%positive,0);(94123810330937420875677421%positive,0);(1473108785377171659501%positive,0);(94123810330937555797929691%positive,1);(350638431580754669%positive,0);(23569740566034747076315%positive,1);(86814638355864625205329901%positive,0);(1272372447534352952767%positive,0);(395434628540337337343185108973%positive,0);(385531127115520226622573047231%positive,0);(385531127115591039569448332735%positive,0);(4970204856001229805%positive,0);(4714649329523%positive,1);(395434628540337337304932941531%positive,1);(395434628540408150251808227035%positive,1);(86870255413249645827440365%positive,0);(86814638285051640077876955%positive,1);(385531127115591035133283790555%positive,1);(355820566172741908573831151341%positive,0);(86814638355864586953162459%positive,1);(86870255413249780749692635%positive,1);(355820566172671100024994065855%positive,0);(355820566172741908535704809179%positive,1);(355820566172741912971869351359%positive,0);(79523277693636787931%positive,1)]]
  | StD => [HRank [(395434571953867782681404038142%positive,0);(395434571953796969734528752638%positive,0);(385531127115591035171410132717%positive,1);(395434628540408145892022414782%positive,0);(86870237274720671616130030%positive,0);(86814638285051678330044397%positive,1);(385531052820176356801584225262%positive,0);(395434628540408150290060394477%positive,1);(1473108574575881547182%positive,0);(94123810330937420875677421%positive,1);(96541657358480660797517246%positive,0);(89763438484673474266%positive,1);(76808992811154%positive,2);(355820491877327230204005243886%positive,0);(86814638355864625205329901%positive,1);(5425914401840887569505278%positive,0);(94123792192408446664367086%positive,0);(395434628540337337343185108973%positive,1);(5425914472653834444790782%positive,0);(19311202604547902%positive,0);(21914904931240238%positive,0);(355820566172741908573831151341%positive,1);(86870255413249645827440365%positive,1);(350638431580754669%positive,3);(86814638355860227167350206%positive,0);(1473108785377171659501%positive,1);(4970204856001229805%positive,1)]]
  end.

Lemma cqh_h_00142 : iqh tmq_h_00142.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00142 StA 0 4 2 25 20000
                lsetq_h_00142 rsetq_h_00142 certq_h_00142 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00142); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00143 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StB)
  | StB, S1 => Some (mkTrans S0 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S1 DR StD)
  | StD, S1 => Some (mkTrans S0 DR StB)
  end.

Definition lsetq_h_00143 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1);(StB,S0);(StB,S1)]);(S1,[(StD,S0);(StB,S1);(StB,S0);(StB,S1)])];
   [(S1,[(StC,S0);(StD,S1);(StB,S0);(StB,S1)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S0)])];
   [(S1,[(StD,S0);(StB,S1);(StB,S0);(StB,S1)]);(S1,[(StC,S0);(StD,S1);(StB,S0);(StB,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StB,S0);(StD,S1)]);(S1,[(StC,S0);(StD,S1);(StB,S0);(StB,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S0)]);(S1,[(StC,S0)])]].

Definition rsetq_h_00143 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StB,S1);(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StB,S1);(StC,S1);(StD,S0)])];
   [(S1,[(StB,S0);(StB,S1);(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StB,S1);(StD,S0);(StB,S1)])];
   [(S1,[(StB,S0);(StB,S1);(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StB,S1);(StC,S1);(StC,S0)])];
   [(S1,[(StB,S0);(StB,S1);(StD,S0);(StB,S1)]);(S1,[(StB,S0);(StD,S1);(StB,S0)])];
   [(S1,[(StB,S0);(StD,S1);(StB,S0)]);(S1,[(StB,S0)])]].

Definition certq_h_00143 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(86869051760947036473781663%positive,0);(19662830306756910%positive,0);(373765766582526180455349480863%positive,0);(355815636012888166469312179615%positive,0);(345912134588070919409518434779%positive,1);(355815710112306189055974365690%positive,2);(345912134588022505713524201947%positive,1);(373765856398570017503367765438%positive,0);(5134327743716150167838638%positive,0);(1392386318737683443134%positive,0);(91251407857050067232091551%positive,0);(80538944943810883291%positive,1);(79006942324882%positive,2);(345912168916308855417568862126%positive,0);(5121378305403911964835231%positive,0);(21030279765222520624613087707%positive,1);(91251425947728295402854906%positive,2);(84451213114321228111650734%positive,0);(86869069851625264644545018%positive,2);(355815725828883589821336231358%positive,0);(19305769477267231%positive,0);(355815725828932003517330464190%positive,0);(21030279765270934320607320539%positive,1);(373765840681944203042011666938%positive,2);(373765856398521603807373532606%positive,0);(1325516871470486318526%positive,0);(21030206438310456159714516910%positive,0);(1263126680602217150939%positive,1);(81942049637450665551976954%positive,2)]]
  | StC => [HRank [(345912134588022505755708157341%positive,0);(86869051760947036473781663%positive,1);(5134345645806143942032109%positive,0);(21030279765222520666797043101%positive,0);(84451204733403796551629549%positive,0);(373765766582477630294981983961%positive,1);(21030279765270934362791275933%positive,0);(373765766582526180455349480863%positive,1);(345912134588071055748699912941%positive,0);(1392385984146846440429%positive,0);(345912134588070919451702390173%positive,0);(355815636012888166469312179615%positive,1);(345912134588022505713524201947%positive,2);(373765766582477630420173315053%positive,0);(1325516536879649315821%positive,0);(84451204733403931600203481%positive,1);(5121378305267572783160765%positive,0);(5121378256853876788927933%positive,0);(4934089128945775097%positive,1);(4715461971921%positive,2);(373765766582526044116167547885%positive,0);(21030279765271070530696883929%positive,1);(355815636012888030004938915545%positive,1);(345912134588070919409518434779%positive,2);(78945417533832634269%positive,0);(21030279765271070659788798701%positive,0);(5121378305267447591197657%positive,1);(314605253686760173%positive,0);(22278175746349543571161%positive,1);(355815636012839616308944682713%positive,1);(355815636012839616434136013805%positive,0);(91251407857050067232091551%positive,1);(19305769477267231%positive,3);(5121378305403911964835231%positive,1);(21030279765222520624613087707%positive,2);(5134345645806278990606041%positive,1);(355815636012888030130130246637%positive,0);(21030279765270934320607320539%positive,2);(5121378256853751596964825%positive,1);(345912134588071055619607998169%positive,1);(373765766582526043990976216793%positive,1);(21208264590074389577433%positive,1);(80538944943810883291%positive,2);(1263126680602217150939%positive,4)]]
  | StD => [HMeas MLeft 63 [(5134345645806143942032109%positive,62);(21030279765222520666797043101%positive,64);(373765766582477630294981983961%positive,0);(19662830306756910%positive,64);(345912134588071055748699912941%positive,62);(1392385984146846440429%positive,62);(355815710112306189055974365690%positive,63);(373765766582477630420173315053%positive,62);(373765856398570017503367765438%positive,64);(5134327743716150167838638%positive,64);(84451204733403931600203481%positive,0);(4715461971921%positive,64);(345912134588070919451702390173%positive,64);(21030279765271070530696883929%positive,0);(373765766582526044116167547885%positive,62);(355815636012888030004938915545%positive,0);(5121378305267572783160765%positive,64);(1392386318737683443134%positive,64);(79006942324882%positive,61);(78945417533832634269%positive,64);(5121378256853876788927933%positive,64);(345912168916308855417568862126%positive,64);(5121378305267447591197657%positive,0);(91251425947728295402854906%positive,63);(22278175746349543571161%positive,0);(84451213114321228111650734%positive,64);(86869069851625264644545018%positive,63);(355815636012839616308944682713%positive,0);(355815725828883589821336231358%positive,64);(314605253686760173%positive,62);(21030279765271070659788798701%positive,62);(84451204733403796551629549%positive,62);(355815636012839616434136013805%positive,62);(1325516536879649315821%positive,62);(345912134588022505755708157341%positive,64);(4934089128945775097%positive,63);(355815725828932003517330464190%positive,64);(5134345645806278990606041%positive,0);(21030279765270934362791275933%positive,64);(355815636012888030130130246637%positive,62);(373765840681944203042011666938%positive,63);(5121378256853751596964825%positive,0);(373765856398521603807373532606%positive,64);(1325516871470486318526%positive,64);(21030206438310456159714516910%positive,64);(345912134588071055619607998169%positive,0);(81942049637450665551976954%positive,63);(373765766582526043990976216793%positive,0);(21208264590074389577433%positive,0)] [5134345645806143942032109%positive;21030279765222520666797043101%positive;373765766582477630294981983961%positive;19662830306756910%positive;345912134588071055748699912941%positive;1392385984146846440429%positive;355815710112306189055974365690%positive;373765766582477630420173315053%positive;373765856398570017503367765438%positive;5134327743716150167838638%positive;84451204733403931600203481%positive;4715461971921%positive;345912134588070919451702390173%positive;21030279765271070530696883929%positive;373765766582526044116167547885%positive;355815636012888030004938915545%positive;5121378305267572783160765%positive;1392386318737683443134%positive;79006942324882%positive;78945417533832634269%positive;5121378256853876788927933%positive;345912168916308855417568862126%positive;5121378305267447591197657%positive;91251425947728295402854906%positive;22278175746349543571161%positive;84451213114321228111650734%positive;86869069851625264644545018%positive;355815636012839616308944682713%positive;355815725828883589821336231358%positive;314605253686760173%positive;84451204733403796551629549%positive;21030279765271070659788798701%positive;355815636012839616434136013805%positive;1325516536879649315821%positive;345912134588022505755708157341%positive;4934089128945775097%positive;355815725828932003517330464190%positive;5134345645806278990606041%positive;21030279765270934362791275933%positive;355815636012888030130130246637%positive;373765840681944203042011666938%positive;5121378256853751596964825%positive;373765856398521603807373532606%positive;1325516871470486318526%positive;21030206438310456159714516910%positive;345912134588071055619607998169%positive;81942049637450665551976954%positive;373765766582526043990976216793%positive;21208264590074389577433%positive]]
  end.

Lemma cqh_h_00143 : iqh tmq_h_00143.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00143 StA 0 4 2 25 20000
                lsetq_h_00143 rsetq_h_00143 certq_h_00143 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00143); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00144 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StB)
  | StB, S1 => Some (mkTrans S0 DR StC)
  | StC, S0 => Some (mkTrans S1 DL StC)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Definition lsetq_h_00144 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S1)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S0)])]].

Definition rsetq_h_00144 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S1);(StC,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StB,S1);(StC,S1)]);(S1,[(StC,S0);(StB,S1);(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StB,S1);(StC,S1)]);(S1,[(StD,S1);(StD,S0);(StB,S1);(StC,S1)])];
   [(S1,[(StD,S1);(StD,S0);(StB,S1);(StC,S1)]);(S1,[(StC,S1);(StD,S0);(StB,S1);(StC,S1)])]].

Definition certq_h_00144 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 45 [(384842019199245203674016247230%positive,1);(345914586773754214201160892123%positive,0);(21875736092576062%positive,1);(384844437046254732549788462527%positive,1);(345914607802970400670371737023%positive,1);(5340788668563%positive,0);(20286373164956582784731%positive,0);(5278238034102935581285374%positive,1);(84377892658281315956878782%positive,1);(5872260086764530562423806%positive,1);(93956156254128913805213403%positive,0);(79235125651630403290%positive,0);(84377892586223621136374766%positive,1);(345914607803042458127119604734%positive,1);(84452066944144142385802971%positive,0);(384844437046272746811007884286%positive,1);(19311508611099950%positive,1);(384842019199227189174723861486%positive,1);(89603010155035705051%positive,0);(384844437046200689354260016575%positive,1);(1267780024859104570798%positive,1);(84452066998187337914248923%positive,0);(384841998239060192361859772123%positive,0);(75366860945106%positive,1);(84377892640266816664820718%positive,1);(384844416016984502885049171675%positive,0);(345914607803024443865900182975%positive,1);(384841998239114235557388218075%positive,0);(84451803411543394106998491%positive,0);(1433657247745151593919%positive,1);(384842019199173145979195415534%positive,1);(93955571093548030209027518%positive,1)] [384842019199245203674016247230%positive;345914586773754214201160892123%positive;21875736092576062%positive;384844437046254732549788462527%positive;345914607802970400670371737023%positive;5340788668563%positive;20286373164956582784731%positive;5278238034102935581285374%positive;84377892658281315956878782%positive;5872260086764530562423806%positive;93956156254128913805213403%positive;79235125651630403290%positive;84377892586223621136374766%positive;345914607803042458127119604734%positive;84452066944144142385802971%positive;384844437046272746811007884286%positive;19311508611099950%positive;384842019199227189174723861486%positive;89603010155035705051%positive;384844437046200689354260016575%positive;1267780024859104570798%positive;84452066998187337914248923%positive;384841998239060192361859772123%positive;75366860945106%positive;84377892640266816664820718%positive;384844416016984502885049171675%positive;345914607803024443865900182975%positive;384841998239114235557388218075%positive;84451803411543394106998491%positive;1433657247745151593919%positive;384842019199173145979195415534%positive;93955571093548030209027518%positive]]
  | StC => [HRank [(84377892640266951807319789%positive,0);(345914586773754214201160892123%positive,1);(384844437046254732549788462527%positive,0);(84377892586223756278873837%positive,0);(345914607802970400670371737023%positive,0);(5600188439699518445%positive,0);(5340788668563%positive,1);(384842019199227189309866360557%positive,0);(308984137407918829%positive,0);(20286373164956582784731%positive,1);(1267780024962035145453%positive,0);(384842019199173146114337914605%positive,0);(93956156254128913805213403%positive,1);(84451808545646969309478893%positive,0);(84452066944144142385802971%positive,1);(345914607803042458230049849325%positive,0);(93956161388232489007693805%positive,0);(89603010155035705051%positive,1);(384844437046200689354260016575%positive,0);(384844437046272746913938128877%positive,0);(84452066998187337914248923%positive,1);(384841998239060192361859772123%positive,1);(384844416016984502885049171675%positive,1);(345914607803024443865900182975%positive,0);(384841998239114235557388218075%positive,1);(84451803411543394106998491%positive,1);(1433657247745151593919%positive,0)]]
  | StD => [HRank [(384842019199245203674016247230%positive,0);(21875736092576062%positive,0);(1267780024859104570798%positive,0);(84377892586223756278873837%positive,1);(384844437046272746811007884286%positive,0);(345914607803042458127119604734%positive,0);(384842019199227189309866360557%positive,1);(5278238034102935581285374%positive,0);(19311508611099950%positive,0);(1267780024962035145453%positive,1);(5872260086764530562423806%positive,0);(5600188439699518445%positive,1);(84377892658281315956878782%positive,0);(79235125651630403290%positive,1);(84377892586223621136374766%positive,0);(84451808545646969309478893%positive,1);(84377892640266816664820718%positive,0);(345914607803042458230049849325%positive,1);(384842019199173145979195415534%positive,0);(93956161388232489007693805%positive,1);(384842019199227189174723861486%positive,0);(384844437046272746913938128877%positive,1);(384842019199173146114337914605%positive,1);(75366860945106%positive,2);(308984137407918829%positive,3);(84377892640266951807319789%positive,1);(93955571093548030209027518%positive,0)]]
  end.

Lemma cqh_h_00144 : iqh tmq_h_00144.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00144 StA 0 4 2 25 20000
                lsetq_h_00144 rsetq_h_00144 certq_h_00144 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00144); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00145 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StB)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Definition lsetq_h_00145 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StB,S0)]);(S1,[(StD,S1);(StB,S1)])];
   [(S1,[(StD,S1);(StB,S1)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StD,S1);(StB,S1)]);(S1,[(StD,S1);(StC,S1)])];
   [(S1,[(StD,S1);(StC,S1)]);(S1,[(StD,S1);(StB,S1)])]].

Definition rsetq_h_00145 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S1);(StD,S1)]);(S1,[(StC,S1);(StD,S1)])];
   [(S1,[(StC,S1);(StD,S1)]);(S1,[(StB,S1);(StD,S0)])];
   [(S1,[(StC,S1);(StD,S1)]);(S1,[(StB,S1);(StD,S1)])]].

Definition certq_h_00145 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 24 [(359689254612236030%positive,1);(75288624493535%positive,1);(19086940606298095%positive,1);(359689254612236271%positive,1);(19086940606296574%positive,1);(18412965875%positive,0);(359689259259524862%positive,1);(19086945253585406%positive,1);(359689259259525103%positive,1);(359126583110793183%positive,1);(1402838199916511%positive,1);(19086945253586927%positive,1);(5488422458026%positive,1);(323097786091829215%positive,1);(294674693919%positive,1);(1262100711561183%positive,1)] [359689254612236030%positive;18412965875%positive;359126583110793183%positive;75288624493535%positive;19086940606298095%positive;359689259259524862%positive;1402838199916511%positive;19086945253586927%positive;1262100711561183%positive;5488422458026%positive;19086945253585406%positive;323097786091829215%positive;294674693919%positive;359689259259525103%positive;359689254612236271%positive;19086940606296574%positive]]
  | StC => [HMeas MRight 24 [(75288624493535%positive,27);(19086940606298095%positive,27);(1149762033%positive,25);(4705538867005%positive,0);(359689254612236271%positive,27);(323097786091828733%positive,27);(1262100711560701%positive,27);(18412965875%positive,26);(359689259259525103%positive,27);(359126583110793183%positive,27);(1402838199916511%positive,27);(19086945253586927%positive,27);(359126583110792701%positive,27);(323097786091829215%positive,27);(294674693919%positive,27);(1262100711561183%positive,27);(1402838199916029%positive,27)] [1262100711560701%positive;18412965875%positive;359126583110793183%positive;75288624493535%positive;19086940606298095%positive;1402838199916511%positive;359126583110792701%positive;19086945253586927%positive;1262100711561183%positive;1149762033%positive;323097786091829215%positive;294674693919%positive;1402838199916029%positive;359689259259525103%positive;4705538867005%positive;359689254612236271%positive;323097786091828733%positive]]
  | StD => [HMeas MLeft 24 [(359689254612236030%positive,1);(1149762033%positive,1);(4705538867005%positive,1);(323097786091828733%positive,1);(19086940606296574%positive,1);(1262100711560701%positive,1);(359689259259524862%positive,1);(19086945253585406%positive,1);(5488422458026%positive,0);(359126583110792701%positive,1);(1402838199916029%positive,1)] [359689254612236030%positive;1262100711560701%positive;359126583110792701%positive;359689259259524862%positive;5488422458026%positive;1149762033%positive;19086945253585406%positive;1402838199916029%positive;4705538867005%positive;323097786091828733%positive;19086940606296574%positive]]
  end.

Lemma cqh_h_00145 : iqh tmq_h_00145.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00145 StA 0 2 2 25 20000
                lsetq_h_00145 rsetq_h_00145 certq_h_00145 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00145); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00146 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StB)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StD)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Definition lsetq_h_00146 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StB,S1)]);(S1,[(StC,S0)])];
   [(S1,[(StD,S1);(StB,S1)]);(S1,[(StD,S1);(StD,S0)])];
   [(S1,[(StD,S1);(StD,S0)]);(S1,[(StD,S1);(StB,S1)])]].

Definition rsetq_h_00146 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StD,S1)]);(S1,[(StD,S0)])];
   [(S1,[(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StD,S1)])]].

Definition certq_h_00146 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 28 [(4939070404094%positive,2);(21812075360679615%positive,2);(294473367359%positive,2);(79025126504427%positive,0);(348993209071826923%positive,0);(348993209069729278%positive,2);(348993206923294399%positive,2);(85203419231742%positive,2);(20230434125248191%positive,2);(1363254707746795%positive,0);(18412969971%positive,1);(22445406943179775%positive,1);(75838378735583%positive,2);(342489729327%positive,1);(87676112435167%positive,2);(359121360428988383%positive,2);(20801616018%positive,2);(359126512243307519%positive,1);(1264402060801727%positive,2);(20230436273780715%positive,0);(20230436271683070%positive,2)] [4939070404094%positive;21812075360679615%positive;294473367359%positive;79025126504427%positive;348993209071826923%positive;348993209069729278%positive;348993206923294399%positive;85203419231742%positive;20230434125248191%positive;1363254707746795%positive;18412969971%positive;22445406943179775%positive;75838378735583%positive;342489729327%positive;87676112435167%positive;359121360428988383%positive;20801616018%positive;359126512243307519%positive;1264402060801727%positive;20230436273780715%positive;20230436271683070%positive]]
  | StC => [HMeas MRight 28 [(21812075360679615%positive,30);(294473367359%positive,30);(79025126504427%positive,29);(348993209071826923%positive,29);(348993206923294399%positive,30);(20230434125248191%positive,30);(4739692491773%positive,0);(1363254707746795%positive,29);(18412969971%positive,29);(22445084820633597%positive,0);(22445406943179775%positive,30);(5479757026045%positive,0);(75836232299517%positive,0);(359121358282553341%positive,0);(75838378735583%positive,30);(342489729327%positive,30);(87676112435167%positive,30);(359121360428988383%positive,30);(359126512243307519%positive,30);(1264402060801727%positive,30);(20230436273780715%positive,29)] [21812075360679615%positive;294473367359%positive;79025126504427%positive;348993209071826923%positive;348993206923294399%positive;20230434125248191%positive;4739692491773%positive;1363254707746795%positive;18412969971%positive;22445084820633597%positive;22445406943179775%positive;5479757026045%positive;75836232299517%positive;359121358282553341%positive;75838378735583%positive;342489729327%positive;87676112435167%positive;359121360428988383%positive;359126512243307519%positive;1264402060801727%positive;20230436273780715%positive]]
  | StD => [HRank [(4939070404094%positive,0);(348993209069729278%positive,0);(85203419231742%positive,0);(4739692491773%positive,1);(22445084820633597%positive,1);(20801616018%positive,0);(5479757026045%positive,1);(20230436271683070%positive,0);(75836232299517%positive,1);(359121358282553341%positive,1)]]
  end.

Lemma cqh_h_00146 : iqh tmq_h_00146.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00146 StA 0 2 2 25 20000
                lsetq_h_00146 rsetq_h_00146 certq_h_00146 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00146); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00147 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StB)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Definition lsetq_h_00147 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StB,S1)]);(S1,[(StC,S0)])];
   [(S1,[(StD,S1);(StB,S1)]);(S1,[(StD,S1);(StC,S1)])];
   [(S1,[(StD,S1);(StC,S1)]);(S1,[(StD,S1);(StB,S1)])]].

Definition rsetq_h_00147 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StD,S1)]);(S1,[(StC,S1);(StD,S1)])];
   [(S1,[(StB,S1);(StD,S1)]);(S1,[(StD,S0)])];
   [(S1,[(StC,S1);(StD,S1)]);(S1,[(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])]].

Definition certq_h_00147 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 21 [(4939070404094%positive,1);(75838380308447%positive,1);(87677387502303%positive,1);(21437839506%positive,1);(87814759347710%positive,1);(18412969971%positive,0);(22480578430367727%positive,1);(359689259259525103%positive,1);(1264402060802031%positive,1);(20230437346473967%positive,1);(359126583110793183%positive,1);(20230436273255934%positive,1);(294674693951%positive,1);(359689258186307070%positive,1)] [87814759347710%positive;4939070404094%positive;18412969971%positive;20230437346473967%positive;359126583110793183%positive;22480578430367727%positive;294674693951%positive;359689258186307070%positive;75838380308447%positive;359689259259525103%positive;20230436273255934%positive;87677387502303%positive;1264402060802031%positive;21437839506%positive]]
  | StC => [HMeas MRight 21 [(75838380308447%positive,23);(87677387502303%positive,23);(22445411238147837%positive,23);(75839453524989%positive,0);(4739692491773%positive,0);(18412969971%positive,22);(359126584184010493%positive,23);(22480578430367727%positive,23);(359689259259525103%positive,23);(1264402060802031%positive,23);(20230437346473967%positive,23);(359126583110793183%positive,23);(342489794861%positive,23);(294674693951%positive,23)] [4739692491773%positive;18412969971%positive;359126584184010493%positive;20230437346473967%positive;359126583110793183%positive;22480578430367727%positive;294674693951%positive;75838380308447%positive;1264402060802031%positive;75839453524989%positive;342489794861%positive;359689259259525103%positive;87677387502303%positive;22445411238147837%positive]]
  | StD => [HMeas MLeft 21 [(4939070404094%positive,1);(22445411238147837%positive,1);(75839453524989%positive,1);(21437839506%positive,0);(87814759347710%positive,1);(4739692491773%positive,1);(359126584184010493%positive,1);(342489794861%positive,1);(20230436273255934%positive,1);(359689258186307070%positive,1)] [87814759347710%positive;4939070404094%positive;4739692491773%positive;359126584184010493%positive;359689258186307070%positive;75839453524989%positive;342489794861%positive;20230436273255934%positive;22445411238147837%positive;21437839506%positive]]
  end.

Lemma cqh_h_00147 : iqh tmq_h_00147.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00147 StA 0 2 2 25 20000
                lsetq_h_00147 rsetq_h_00147 certq_h_00147 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00147); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00148 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StB)
  | StB, S1 => Some (mkTrans S1 DR StC)
  | StC, S0 => Some (mkTrans S0 DL StC)
  | StC, S1 => Some (mkTrans S0 DR StD)
  | StD, S0 => Some (mkTrans S0 DR StB)
  | StD, S1 => Some (mkTrans S0 DR StB)
  end.

Definition lsetq_h_00148 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S0)]);(S1,[(StB,S1);(StB,S0)])];
   [(S0,[(StC,S1);(StB,S0)]);(S1,[(StB,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StC,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S1)]);(S0,[])];
   [(S1,[(StB,S1);(StB,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00148 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S1,[(StB,S0);(StD,S0)])];
   [(S1,[(StB,S0);(StD,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StB,S0);(StC,S1)])]].

Definition certq_h_00148 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(294338098475%positive,0);(75490401440222%positive,1);(75288487614367%positive,0);(19103432542451358%positive,1);(74622786533022%positive,1);(18396122866%positive,2);(294330627359%positive,0);(75284310061982%positive,1);(320840213705217951%positive,0);(347866205340497566%positive,1);(1358852367775390%positive,1)]]
  | StC => [HRank [(5445388899805%positive,0);(74622786531817%positive,1);(356869006479578589%positive,0);(19103432542450153%positive,1);(75288487612921%positive,2);(356869006479577565%positive,0);(347866205338399209%positive,1);(320840209410249209%positive,2);(1358852367774185%positive,1);(347866205340496361%positive,1);(320840213705216505%positive,2);(19085840287258089%positive,3);(75284312183481%positive,4);(294333775133%positive,0);(75288487614367%positive,1);(18412639697%positive,5);(294338098475%positive,6);(19103432540353001%positive,1);(75284192645625%positive,2);(18395860945%positive,3);(294330627359%positive,4);(19085840287258269%positive,0);(320840213705217951%positive,1)]]
  | StD => [HRank [(1358852367775390%positive,0);(74622786533022%positive,0);(5445388899805%positive,1);(74622786531817%positive,2);(347866205340497566%positive,0);(19103432542451358%positive,0);(356869006479578589%positive,1);(19103432542450153%positive,2);(75288487612921%positive,3);(75490401440222%positive,0);(356869006479577565%positive,1);(347866205338399209%positive,2);(320840209410249209%positive,3);(1358852367774185%positive,2);(347866205340496361%positive,2);(320840213705216505%positive,3);(19085840287258089%positive,4);(75284312183481%positive,5);(18396122866%positive,1);(18412639697%positive,6);(75284310061982%positive,0);(19085840287258269%positive,1);(19103432540353001%positive,2);(75284192645625%positive,3);(18395860945%positive,4);(294333775133%positive,2)]]
  end.

Lemma cqh_h_00148 : iqh tmq_h_00148.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00148 StA 0 2 2 25 20000
                lsetq_h_00148 rsetq_h_00148 certq_h_00148 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00148); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00149 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StB)
  | StB, S1 => Some (mkTrans S1 DR StC)
  | StC, S0 => Some (mkTrans S1 DL StC)
  | StC, S1 => Some (mkTrans S0 DR StD)
  | StD, S0 => Some (mkTrans S0 DR StB)
  | StD, S1 => Some (mkTrans S0 DR StB)
  end.

Definition lsetq_h_00149 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S0)]);(S1,[(StB,S1);(StB,S0)])];
   [(S0,[(StC,S1);(StB,S0)]);(S1,[(StB,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StC,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S1)]);(S0,[])];
   [(S1,[(StB,S1);(StB,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00149 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S1,[(StB,S0);(StD,S1)])];
   [(S1,[(StB,S0);(StD,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StB,S0);(StC,S1)])]].

Definition certq_h_00149 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(294330627359%positive,0);(75284310063006%positive,1);(75288487614367%positive,0);(19103432542451358%positive,1);(75284192647071%positive,0);(74622786533022%positive,1);(347866205220984479%positive,0);(19103432422938271%positive,0);(356869006546630558%positive,1);(75288487613343%positive,0);(18395664211%positive,0);(356869006429214623%positive,0);(347866205338400414%positive,1);(294338098479%positive,0);(75559120916958%positive,1);(18396122866%positive,2);(19085840356406942%positive,1);(74554067056286%positive,1);(356869010724181919%positive,0);(19103432540354206%positive,1);(347866205340497566%positive,1);(1358852367775390%positive,1);(294337965854%positive,1)]]
  | StC => [HRank [(5445388899805%positive,0);(74622786531817%positive,1);(356869006479578589%positive,0);(19103432542450153%positive,1);(75288487612921%positive,2);(356869006479577565%positive,0);(347866205338399209%positive,1);(356869006429213177%positive,2);(75284243011485%positive,0);(320840209460613597%positive,0);(1358852367774185%positive,1);(347866205340496361%positive,1);(356869010724180473%positive,2);(19103432473302505%positive,3);(294333775133%positive,0);(75284192647071%positive,1);(75284312183545%positive,4);(356869006479579037%positive,0);(75288487613343%positive,1);(19085840354308585%positive,1);(347866205271348893%positive,0);(4705262040377%positive,2);(4895633085917%positive,0);(74554067055081%positive,1);(320840209460614621%positive,0);(19085840356405737%positive,1);(4705530475833%positive,2);(1149741521%positive,3);(18395664211%positive,4);(19103432473302685%positive,0);(356869006429214623%positive,1);(18412640209%positive,5);(294338098479%positive,6);(19103432422938271%positive,1);(75288487614367%positive,1);(19103432540353001%positive,1);(75284192645625%positive,2);(18395860945%positive,3);(294330627359%positive,4);(356869010724181919%positive,1);(347866205220984479%positive,1)]]
  | StD => [HRank [(1358852367775390%positive,0);(74622786533022%positive,0);(5445388899805%positive,1);(74622786531817%positive,2);(347866205340497566%positive,0);(19103432542451358%positive,0);(356869006479578589%positive,1);(19103432542450153%positive,2);(75288487612921%positive,3);(356869006479577565%positive,1);(347866205338399209%positive,2);(356869006429213177%positive,3);(294337965854%positive,0);(75284243011485%positive,1);(19085840356406942%positive,0);(320840209460613597%positive,1);(1358852367774185%positive,2);(347866205340496361%positive,2);(356869010724180473%positive,3);(19103432473302505%positive,4);(75284310063006%positive,0);(75284312183545%positive,5);(347866205338400414%positive,0);(19103432540354206%positive,0);(356869006479579037%positive,1);(356869006546630558%positive,0);(19085840354308585%positive,2);(347866205271348893%positive,1);(75559120916958%positive,0);(18396122866%positive,1);(4705262040377%positive,3);(74554067056286%positive,0);(4895633085917%positive,1);(74554067055081%positive,2);(320840209460614621%positive,1);(19085840356405737%positive,2);(4705530475833%positive,3);(1149741521%positive,4);(18412640209%positive,6);(19103432540353001%positive,2);(75284192645625%positive,3);(18395860945%positive,4);(19103432473302685%positive,1);(294333775133%positive,2)]]
  end.

Lemma cqh_h_00149 : iqh tmq_h_00149.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00149 StA 0 2 2 25 20000
                lsetq_h_00149 rsetq_h_00149 certq_h_00149 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00149); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00150 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StB)
  | StB, S1 => Some (mkTrans S1 DR StC)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S0 DR StB)
  | StD, S0 => None
  | StD, S1 => None
  end.

Definition lsetq_h_00150 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S0)]);(S1,[(StB,S1);(StB,S1)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S1)]);(S0,[])];
   [(S1,[(StB,S1);(StB,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StC,S0)]);(S1,[(StB,S1);(StB,S0)])]].

Definition rsetq_h_00150 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S0)]);(S0,[])]].

Definition certq_h_00150 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(18395860722%positive,0);(75284194719390%positive,0);(294330658590%positive,0)]]
  | StC => [HRank [(294599062813%positive,0);(4705265184557%positive,0);(19099034426733277%positive,0);(75284193145321%positive,1);(1149729137%positive,1);(18399858513%positive,2)]]
  | StD => []
  end.

Lemma cqh_h_00150 : iqh tmq_h_00150.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00150 StA 0 2 2 25 20000
                lsetq_h_00150 rsetq_h_00150 certq_h_00150 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00150); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00151 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StB)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StC)
  end.

Definition lsetq_h_00151 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StC,S1)])];
   [(S0,[(StD,S1);(StD,S0)]);(S1,[(StC,S0);(StC,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00151 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StB,S0);(StD,S1)]);(S0,[(StC,S1);(StC,S0)])];
   [(S1,[(StD,S0)]);(S0,[])]].

Definition certq_h_00151 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 22 [(299941464366%positive,25);(4739944807726%positive,0);(4739690386154%positive,24);(18415853522%positive,24);(1171552402%positive,25);(356852720033167263%positive,25);(308359501599%positive,25);(294338123583%positive,25);(314511425648186090%positive,24);(1150282099%positive,23);(20208647887222687%positive,25);(19656963848656558%positive,25);(75839115875050%positive,24);(314511425648187054%positive,25);(19656963848655594%positive,24);(5445140387615%positive,25)] [308359501599%positive;294338123583%positive;19656963848656558%positive;299941464366%positive;4739944807726%positive;4739690386154%positive;75839115875050%positive;5445140387615%positive;314511425648186090%positive;18415853522%positive;1150282099%positive;1171552402%positive;356852720033167263%positive;19656963848655594%positive;314511425648187054%positive;20208647887222687%positive]]
  | StC => [HRank [(356852720033165817%positive,0);(356852720033167263%positive,0);(308359501599%positive,0);(294338123583%positive,0);(87122246201849%positive,0);(1150282099%positive,0);(20208647887222687%positive,0);(20208647887221753%positive,0);(21270079633%positive,0);(5445140387615%positive,0)]]
  | StD => [HMeas MLeft 22 [(356852720033165817%positive,1);(299941464366%positive,2);(4739944807726%positive,2);(4739690386154%positive,2);(18415853522%positive,2);(1171552402%positive,0);(87122246201849%positive,1);(314511425648186090%positive,2);(19656963848656558%positive,2);(20208647887221753%positive,1);(75839115875050%positive,2);(314511425648187054%positive,2);(21270079633%positive,1);(19656963848655594%positive,2)] [356852720033165817%positive;19656963848656558%positive;20208647887221753%positive;299941464366%positive;4739944807726%positive;4739690386154%positive;75839115875050%positive;87122246201849%positive;21270079633%positive;18415853522%positive;1171552402%positive;314511425648186090%positive;19656963848655594%positive;314511425648187054%positive]]
  end.

Lemma cqh_h_00151 : iqh tmq_h_00151.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00151 StA 0 2 2 25 20000
                lsetq_h_00151 rsetq_h_00151 certq_h_00151 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00151); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00152 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StB)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00152 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00152 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition certq_h_00152 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 35 [(20114360685811450%positive,1);(321829776116404975%positive,1);(321829775361430255%positive,1);(321829776116406010%positive,1);(314652163455309742%positive,1);(1212660372199327%positive,1);(356852788752799647%positive,1);(321829775361431290%positive,1);(5445141436191%positive,1);(4714776220603%positive,0);(321829776116406190%positive,1);(20114360685811630%positive,1);(314652164210284282%positive,1);(1172076690%positive,1);(19665759941678842%positive,1);(321829775361431470%positive,1);(314652164210283247%positive,1);(19665759941677807%positive,1);(314652163455309562%positive,1);(20114360685810415%positive,1);(314652164210284462%positive,1);(314652163455308527%positive,1);(19665759941679022%positive,1);(1212660372567967%positive,1);(4715531195323%positive,0);(356852788753168287%positive,1);(300075682094%positive,1)] [20114360685811450%positive;321829776116404975%positive;321829775361430255%positive;314652163455309742%positive;1212660372199327%positive;356852788752799647%positive;321829775361431290%positive;5445141436191%positive;321829776116406190%positive;4715531195323%positive;20114360685811630%positive;314652164210284282%positive;1172076690%positive;19665759941678842%positive;321829775361431470%positive;314652164210283247%positive;19665759941677807%positive;300075682094%positive;314652163455309562%positive;20114360685810415%positive;314652164210284462%positive;314652163455308527%positive;19665759941679022%positive;1212660372567967%positive;321829776116406010%positive;356852788753168287%positive;4714776220603%positive]]
  | StC => [HMeas MRight 35 [(321829776116404975%positive,2);(321829775361430255%positive,2);(1212660372199327%positive,2);(356852788752799647%positive,2);(5445141436191%positive,2);(4714776220603%positive,1);(21270083729%positive,2);(314652164210283247%positive,2);(87122262979065%positive,2);(19665759941677807%positive,2);(1212660372566521%positive,0);(356852788753166841%positive,2);(20114360685810415%positive,2);(314652163455308527%positive,2);(1212660372197881%positive,0);(356852788752798201%positive,2);(1212660372567967%positive,2);(4715531195323%positive,1);(356852788753168287%positive,2)] [321829776116404975%positive;321829775361430255%positive;1212660372199327%positive;356852788752799647%positive;5445141436191%positive;21270083729%positive;314652164210283247%positive;87122262979065%positive;19665759941677807%positive;1212660372566521%positive;356852788753166841%positive;20114360685810415%positive;314652163455308527%positive;1212660372197881%positive;356852788752798201%positive;1212660372567967%positive;4715531195323%positive;356852788753168287%positive;4714776220603%positive]]
  | StD => [HMeas MLeft 35 [(20114360685811450%positive,1);(321829776116406010%positive,1);(314652163455309742%positive,2);(321829775361431290%positive,1);(321829776116406190%positive,2);(20114360685811630%positive,2);(314652164210284282%positive,0);(21270083729%positive,1);(1172076690%positive,0);(19665759941678842%positive,0);(321829775361431470%positive,2);(87122262979065%positive,1);(1212660372566521%positive,2);(314652163455309562%positive,0);(356852788753166841%positive,1);(314652164210284462%positive,2);(1212660372197881%positive,2);(356852788752798201%positive,1);(19665759941679022%positive,2);(300075682094%positive,2)] [20114360685811450%positive;314652163455309742%positive;321829775361431290%positive;321829776116406190%positive;20114360685811630%positive;314652164210284282%positive;21270083729%positive;1172076690%positive;19665759941678842%positive;321829775361431470%positive;87122262979065%positive;1212660372566521%positive;314652163455309562%positive;356852788753166841%positive;314652164210284462%positive;1212660372197881%positive;356852788752798201%positive;19665759941679022%positive;321829776116406010%positive;300075682094%positive]]
  end.

Lemma cqh_h_00152 : iqh tmq_h_00152.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00152 StA 0 2 2 25 20000
                lsetq_h_00152 rsetq_h_00152 certq_h_00152 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00152); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00153 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StA)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00153 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00153 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition certq_h_00153 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 37 [(314652163455309742%positive,4);(356852788752799647%positive,4);(5445141436191%positive,4);(75791334364922%positive,2);(1212666493260527%positive,4);(356852788753168287%positive,4);(4709410501563%positive,1);(314652164210284282%positive,4);(75791334363887%positive,4);(321809154152691615%positive,4);(1212665738286842%positive,2);(19665759941678842%positive,4);(1172076690%positive,4);(1212666493261562%positive,2);(314652164210283247%positive,4);(4709410132923%positive,3);(321809154152322975%positive,4);(1212665738285807%positive,4);(19665759941677807%positive,4);(314652163455309562%positive,4);(75791334365102%positive,0);(4910418007839%positive,4);(314652164210284462%positive,4);(314652163455308527%positive,4);(1212665738287022%positive,0);(19665759941679022%positive,4);(1212666493261742%positive,0);(300075682094%positive,4)] [314652163455309742%positive;356852788752799647%positive;5445141436191%positive;75791334364922%positive;1212666493260527%positive;4709410501563%positive;314652164210284282%positive;75791334363887%positive;321809154152691615%positive;1212665738286842%positive;19665759941678842%positive;1172076690%positive;1212666493261562%positive;314652164210283247%positive;4709410132923%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;314652163455309562%positive;75791334365102%positive;4910418007839%positive;314652164210284462%positive;1212666493261742%positive;314652163455308527%positive;1212665738287022%positive;19665759941679022%positive;356852788753168287%positive;300075682094%positive]]
  | StC => [HMeas MRight 37 [(78566688125433%positive,1);(356852788752799647%positive,1);(321809154152690169%positive,1);(5445141436191%positive,1);(1212666493260527%positive,1);(321809154152321529%positive,1);(356852788753168287%positive,1);(4709410501563%positive,1);(75791334363887%positive,1);(21270083729%positive,1);(321809154152691615%positive,1);(314652164210283247%positive,1);(4709410132923%positive,0);(87122262979065%positive,1);(321809154152322975%positive,1);(1212665738285807%positive,1);(19665759941677807%positive,1);(356852788753166841%positive,1);(4910418007839%positive,1);(314652163455308527%positive,1);(356852788752798201%positive,1)] [78566688125433%positive;356852788752799647%positive;321809154152690169%positive;5445141436191%positive;1212666493260527%positive;321809154152321529%positive;4709410501563%positive;75791334363887%positive;21270083729%positive;321809154152691615%positive;314652164210283247%positive;4709410132923%positive;87122262979065%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;356852788753166841%positive;4910418007839%positive;314652163455308527%positive;356852788752798201%positive;356852788753168287%positive]]
  | StD => [HMeas MLeft 37 [(314652163455309742%positive,2);(78566688125433%positive,1);(321809154152690169%positive,1);(75791334364922%positive,2);(321809154152321529%positive,1);(314652164210284282%positive,0);(21270083729%positive,1);(1212665738286842%positive,2);(19665759941678842%positive,0);(1172076690%positive,0);(1212666493261562%positive,2);(87122262979065%positive,1);(314652163455309562%positive,0);(75791334365102%positive,2);(356852788753166841%positive,1);(314652164210284462%positive,2);(356852788752798201%positive,1);(1212665738287022%positive,2);(19665759941679022%positive,2);(1212666493261742%positive,2);(300075682094%positive,2)] [314652163455309742%positive;78566688125433%positive;321809154152690169%positive;75791334364922%positive;321809154152321529%positive;314652164210284282%positive;21270083729%positive;1212665738286842%positive;19665759941678842%positive;1172076690%positive;1212666493261562%positive;87122262979065%positive;314652163455309562%positive;75791334365102%positive;356852788753166841%positive;314652164210284462%positive;356852788752798201%positive;1212665738287022%positive;19665759941679022%positive;1212666493261742%positive;300075682094%positive]]
  end.

Lemma cqh_h_00153 : iqh tmq_h_00153.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00153 StA 23 2 2 48 20000
                lsetq_h_00153 rsetq_h_00153 certq_h_00153 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 48) 2000 tmq_h_00153); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00154 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StB)
  | StC, S0 => Some (mkTrans S1 DL StB)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00154 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S1);(StC,S1)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StB,S1)])];
   [(S1,[(StC,S1);(StC,S1)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StD,S0);(StB,S1)]);(S1,[(StC,S1);(StC,S0)])]].

Definition rsetq_h_00154 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StC,S1)]);(S0,[(StB,S1);(StD,S0)])];
   [(S0,[(StB,S1);(StD,S0)]);(S0,[(StB,S1);(StC,S1)])];
   [(S0,[(StB,S1);(StD,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StB,S1);(StD,S0)]);(S1,[(StC,S0);(StB,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S1)]);(S0,[(StB,S1);(StD,S0)])]].

Definition certq_h_00154 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 41 [(339405394645219034%positive,0);(75563231835099%positive,1);(1150007794%positive,0);(322952306689012699%positive,1);(339405395668629210%positive,0);(322947154002826203%positive,1);(18411919219%positive,1);(294338092846%positive,2);(349960706271868334%positive,2);(322947152728257499%positive,1);(76757117400991%positive,2);(1367034012596127%positive,2);(322952307963581403%positive,1);(1325802326554527%positive,2);(19649821101913518%positive,2);(19649822125323694%positive,2);(349960707295278510%positive,2);(294402055982%positive,2);(19649821101913818%positive,0);(349960706271868634%positive,0);(339405394645218734%positive,2);(75564506403803%positive,1);(19649822125323994%positive,0);(349960707295278810%positive,0);(339405395668628910%positive,2);(4927912449774%positive,2)] [339405394645219034%positive;75563231835099%positive;339405395668629210%positive;322952306689012699%positive;1150007794%positive;322947154002826203%positive;18411919219%positive;294338092846%positive;349960706271868334%positive;322947152728257499%positive;76757117400991%positive;1367034012596127%positive;1325802326554527%positive;19649821101913518%positive;19649822125323694%positive;349960707295278510%positive;294402055982%positive;19649821101913818%positive;349960706271868634%positive;339405394645218734%positive;75564506403803%positive;19649822125323994%positive;349960707295278810%positive;339405395668628910%positive;322952307963581403%positive;4927912449774%positive]]
  | StC => [HMeas MLeft 41 [(349960707295277805%positive,1);(19649822125322989%positive,1);(75563231835099%positive,1);(322952306689012699%positive,1);(322947154002826203%positive,0);(1367034012594681%positive,0);(339405394645218029%positive,1);(18411919219%positive,1);(339405395668628205%positive,1);(322952307963581885%positive,1);(322947152728257499%positive,1);(76757117400991%positive,1);(1367034012596127%positive,1);(322947154002826685%positive,1);(322952306689013181%positive,1);(322952307963581403%positive,0);(1325802326554527%positive,1);(4722701989693%positive,1);(322947152728257981%positive,1);(1325802326553081%positive,0);(75564506403803%positive,0);(349960706271867629%positive,1);(19649821101912813%positive,1)] [349960707295277805%positive;19649822125322989%positive;75563231835099%positive;322952306689012699%positive;322947154002826203%positive;1367034012594681%positive;339405394645218029%positive;18411919219%positive;339405395668628205%positive;322952307963581885%positive;322947152728257499%positive;76757117400991%positive;1367034012596127%positive;322947154002826685%positive;322952306689013181%positive;1325802326554527%positive;4722701989693%positive;322947152728257981%positive;1325802326553081%positive;75564506403803%positive;322952307963581403%positive;349960706271867629%positive;19649821101912813%positive]]
  | StD => [HMeas MLeft 41 [(349960707295277805%positive,1);(339405394645219034%positive,1);(19649822125322989%positive,1);(1150007794%positive,1);(339405395668629210%positive,1);(1367034012594681%positive,0);(339405394645218029%positive,1);(294338092846%positive,1);(349960706271868334%positive,1);(339405395668628205%positive,1);(322952307963581885%positive,1);(322947154002826685%positive,1);(322952306689013181%positive,1);(19649821101913518%positive,1);(4722701989693%positive,1);(19649822125323694%positive,1);(349960707295278510%positive,1);(322947152728257981%positive,1);(294402055982%positive,1);(1325802326553081%positive,0);(19649821101913818%positive,1);(349960706271868634%positive,1);(339405394645218734%positive,1);(19649822125323994%positive,1);(349960707295278810%positive,1);(339405395668628910%positive,1);(349960706271867629%positive,1);(4927912449774%positive,1);(19649821101912813%positive,1)] [349960707295277805%positive;339405394645219034%positive;19649822125322989%positive;339405395668629210%positive;1150007794%positive;1367034012594681%positive;339405394645218029%positive;294338092846%positive;349960706271868334%positive;339405395668628205%positive;322952307963581885%positive;322947154002826685%positive;322952306689013181%positive;19649821101913518%positive;4722701989693%positive;19649822125323694%positive;349960707295278510%positive;322947152728257981%positive;294402055982%positive;1325802326553081%positive;19649821101913818%positive;349960706271868634%positive;339405394645218734%positive;19649822125323994%positive;349960707295278810%positive;339405395668628910%positive;349960706271867629%positive;4927912449774%positive;19649821101912813%positive]]
  end.

Lemma cqh_h_00154 : iqh tmq_h_00154.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00154 StA 0 2 2 25 20000
                lsetq_h_00154 rsetq_h_00154 certq_h_00154 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00154); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00155 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StC)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => None
  | StD, S1 => None
  end.

Definition lsetq_h_00155 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])]].

Definition rsetq_h_00155 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StC,S0)]);(S1,[(StC,S1);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StC,S1);(StB,S0)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StB,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S1)]);(S1,[(StC,S1);(StA,S0)])];
   [(S1,[(StC,S1);(StC,S1)]);(S1,[(StC,S1);(StC,S0)])]].

Definition certq_h_00155 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(19620490988319214%positive,0);(76813267727066%positive,1);(4790158923550%positive,0);(1172076690%positive,1);(334415431982%positive,0);(18216609938%positive,2)]]
  | StC => [HRank [(300051826989%positive,0);(76818636436909%positive,0);(18711558289%positive,0)]]
  | StD => []
  end.

Lemma cqh_h_00155 : iqh tmq_h_00155.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00155 StA 0 2 2 25 20000
                lsetq_h_00155 rsetq_h_00155 certq_h_00155 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00155); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00156 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StC)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StD)
  | StD, S1 => Some (mkTrans S0 DL StB)
  end.

Definition lsetq_h_00156 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S1)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StB,S1)]);(S1,[(StC,S0);(StD,S1)])];
   [(S1,[(StC,S0);(StD,S1)]);(S1,[(StC,S0);(StB,S1)])]].

Definition rsetq_h_00156 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StC,S0)]);(S0,[(StD,S1);(StC,S0)])];
   [(S0,[(StD,S1);(StC,S0)]);(S1,[(StC,S1);(StB,S0)])];
   [(S0,[(StD,S1);(StC,S0)]);(S1,[(StC,S1);(StC,S0)])];
   [(S0,[(StD,S1);(StC,S0)]);(S1,[(StC,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StB,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StB,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S1)]);(S0,[])];
   [(S1,[(StC,S1);(StC,S1)]);(S0,[(StB,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S1)]);(S0,[(StD,S1);(StC,S0)])]].

Definition certq_h_00156 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(76642542777775%positive,0);(19621590499948463%positive,0);(313945453113472943%positive,0);(315053415090451182%positive,1);(313927860927427322%positive,2);(314631752381199066%positive,3);(19691959244126127%positive,0);(315071353020315567%positive,0);(314631752381200110%positive,1);(350660549400164078%positive,1);(305624553126459118%positive,1);(315071353020314362%positive,2);(76671804602287%positive,0);(1226753987934127%positive,0);(4713386702574%positive,1);(1226753987932922%positive,2);(315053415090452206%positive,1);(313945453113471738%positive,2);(350660549400163034%positive,3);(314631752381198830%positive,1);(350660549400162798%positive,1);(305624553126457838%positive,1);(315049362787758842%positive,2);(305624553126458074%positive,3);(19690838257661690%positive,4);(76646888076250%positive,5);(20926392466%positive,6);(300454480175%positive,0);(19620490988319482%positive,2);(76814391800538%positive,3);(19691959244124922%positive,2);(76671804601082%positive,2);(19621590499947258%positive,2);(85610484822746%positive,3);(19690584854590202%positive,2);(74615368544986%positive,3);(18778646674%positive,4);(313927860927428527%positive,0);(4800899487518%positive,1);(19620490988320687%positive,0);(76917336830703%positive,0);(5350655301406%positive,1);(4663460534046%positive,1);(1173649554%positive,2);(313927858780992943%positive,0);(299384932655%positive,0);(76917336798638%positive,1);(315053417236887470%positive,1);(19690838257661870%positive,1);(18711558291%positive,1);(315053415090451886%positive,1);(300458346798%positive,2)]]
  | StC => [HRank [(300056217901%positive,0);(76642542777775%positive,1);(85610484823469%positive,0);(350660549400163757%positive,0);(18216642705%positive,0);(300454480175%positive,1);(18753513617%positive,0);(314631752381199789%positive,0);(313927860927428527%positive,1);(76814391801261%positive,0);(19620490988320687%positive,1);(299401906493%positive,0);(76917336830703%positive,1);(315071353020315567%positive,1);(19664484338333613%positive,0);(314631754527635373%positive,0);(313927858780992943%positive,1);(19691959244126127%positive,1);(313945453113472943%positive,1);(1226753987934127%positive,1);(299384932655%positive,1);(19621590499948463%positive,1);(76671804602287%positive,1);(18711558291%positive,2)]]
  | StD => [HRank [(300458346798%positive,0);(85610484823469%positive,1);(19690838257661870%positive,0);(315053417236887470%positive,0);(350660549400163757%positive,1);(315053415090451182%positive,0);(313927860927427322%positive,1);(314631752381199066%positive,2);(314631752381200110%positive,0);(350660549400164078%positive,0);(305624553126459118%positive,0);(315071353020314362%positive,1);(4713386702574%positive,0);(1226753987932922%positive,1);(315053415090452206%positive,0);(313945453113471738%positive,1);(350660549400163034%positive,2);(314631752381198830%positive,0);(350660549400162798%positive,0);(305624553126457838%positive,0);(315049362787758842%positive,1);(305624553126458074%positive,2);(19690838257661690%positive,3);(76646888076250%positive,4);(20926392466%positive,5);(4800899487518%positive,0);(5350655301406%positive,0);(4663460534046%positive,0);(1173649554%positive,1);(18753513617%positive,2);(19620490988319482%positive,1);(76814391800538%positive,2);(19691959244124922%positive,1);(76671804601082%positive,1);(19621590499947258%positive,1);(85610484822746%positive,2);(19690584854590202%positive,1);(74615368544986%positive,2);(18778646674%positive,3);(76814391801261%positive,1);(76917336798638%positive,0);(18216642705%positive,2);(315053415090451886%positive,0);(314631754527635373%positive,1);(19664484338333613%positive,1);(314631752381199789%positive,1);(300056217901%positive,4);(299401906493%positive,6)]]
  end.

Lemma cqh_h_00156 : iqh tmq_h_00156.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00156 StA 0 2 2 25 20000
                lsetq_h_00156 rsetq_h_00156 certq_h_00156 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00156); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00157 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StB)
  | StC, S0 => Some (mkTrans S0 DL StB)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00157 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0);(StC,S0)]);(S0,[(StD,S1);(StB,S0);(StC,S0);(StB,S1)])];
   [(S0,[(StD,S1);(StB,S0);(StC,S0);(StB,S1)]);(S1,[(StC,S1);(StB,S0);(StC,S0);(StB,S1)])];
   [(S0,[(StD,S1);(StB,S0);(StC,S0);(StD,S1)]);(S1,[(StC,S1);(StB,S0);(StC,S0);(StB,S1)])];
   [(S0,[(StD,S1);(StB,S0);(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StB,S0);(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StB,S0);(StD,S1);(StB,S0)]);(S1,[(StC,S1);(StC,S1);(StC,S1);(StA,S0)])];
   [(S0,[(StD,S1);(StB,S0);(StD,S1);(StB,S0)]);(S1,[(StC,S1);(StC,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StC,S1);(StB,S0);(StC,S0)]);(S1,[(StD,S0);(StC,S0);(StB,S1);(StD,S0)])];
   [(S1,[(StC,S1);(StB,S0);(StC,S0);(StB,S1)]);(S1,[(StD,S0);(StC,S0);(StB,S1);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S1);(StC,S1);(StA,S0)]);(S0,[])];
   [(S1,[(StC,S1);(StC,S1);(StC,S1);(StC,S1)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S0);(StB,S1);(StD,S0)]);(S0,[(StD,S1);(StB,S0);(StD,S1);(StB,S0)])]].

Definition rsetq_h_00157 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StB,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S0)])];
   [(S0,[(StC,S0);(StB,S1);(StD,S0);(StC,S0)]);(S1,[(StB,S0);(StC,S0);(StB,S1);(StC,S1)])];
   [(S1,[(StB,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S0);(StB,S1);(StC,S1)]);(S1,[(StB,S0);(StC,S0);(StB,S1);(StD,S0)])];
   [(S1,[(StB,S0);(StC,S0);(StB,S1);(StC,S1)]);(S1,[(StB,S0);(StC,S0);(StD,S1);(StB,S0)])];
   [(S1,[(StB,S0);(StC,S0);(StB,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S0)])];
   [(S1,[(StB,S0);(StC,S0);(StD,S1);(StB,S0)]);(S1,[(StB,S0);(StD,S1);(StB,S0);(StC,S0)])];
   [(S1,[(StB,S0);(StC,S0);(StD,S1);(StB,S0)]);(S1,[(StB,S0);(StD,S1);(StB,S0);(StD,S1)])];
   [(S1,[(StB,S0);(StD,S1);(StB,S0);(StC,S0)]);(S0,[(StC,S0);(StB,S1);(StD,S0)])];
   [(S1,[(StB,S0);(StD,S1);(StB,S0);(StD,S1)]);(S0,[(StC,S0);(StB,S1);(StD,S0);(StC,S0)])]].

Definition certq_h_00157 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 65 [(5871447243027432762482591%positive,2);(355080683270510401493610446251%positive,1);(80107037844204613358%positive,2);(336511582681216535116427668442%positive,2);(336511582681108448725370584491%positive,1);(308895128872800927%positive,2);(355080683270510401493610638298%positive,2);(1339260376212736678447995550%positive,2);(75382765735795%positive,1);(4947088363607806938%positive,2);(4947080405301818330%positive,2);(344057107720320109555626408607%positive,2);(384791166519096222240246046623%positive,2);(336511582681229697370123582891%positive,1);(392412220493961277623460354718%positive,2);(75413852868563%positive,1);(22192603058791580688950077946%positive,2);(308635656770679454%positive,2);(336511582681229697370123774938%positive,2);(5006689865262763758%positive,2);(342894618922546066627495108314%positive,2);(22192603058791580688949836447%positive,2);(80107037844204220142%positive,2);(18398833138%positive,0);(20263241340220807043743%positive,2);(342894618922546066627495385758%positive,2);(18398820850%positive,0);(5871447243027226604052383%positive,2);(355080683270497239239914531802%positive,2);(1339260376212736678447718106%positive,2);(344057107720320109555626781178%positive,2);(355080683270389152848857447851%positive,1);(1266456872882022464939%positive,1);(336511582681108448725370776538%positive,2);(355080683270497239239914339755%positive,1);(83703773649129517276635039%positive,2);(355080683270389152848857639898%positive,2);(392412220493961277623460077274%positive,2);(336511582681216535116427476395%positive,1)] [5871447243027432762482591%positive;355080683270510401493610446251%positive;80107037844204613358%positive;336511582681216535116427668442%positive;336511582681108448725370584491%positive;308895128872800927%positive;355080683270510401493610638298%positive;1339260376212736678447995550%positive;75382765735795%positive;4947088363607806938%positive;4947080405301818330%positive;344057107720320109555626408607%positive;384791166519096222240246046623%positive;336511582681229697370123582891%positive;392412220493961277623460354718%positive;75413852868563%positive;22192603058791580688950077946%positive;308635656770679454%positive;336511582681229697370123774938%positive;5006689865262763758%positive;342894618922546066627495108314%positive;22192603058791580688949836447%positive;80107037844204220142%positive;18398833138%positive;20263241340220807043743%positive;342894618922546066627495385758%positive;18398820850%positive;5871447243027226604052383%positive;355080683270497239239914531802%positive;1339260376212736678447718106%positive;355080683270389152848857447851%positive;1266456872882022464939%positive;336511582681216535116427476395%positive;336511582681108448725370776538%positive;355080683270497239239914339755%positive;83703773649129517276635039%positive;355080683270389152848857639898%positive;392412220493961277623460077274%positive;344057107720320109555626781178%positive]]
  | StC => [HRank [(392412220493961277685885955497%positive,0);(342894618922546066689920986537%positive,0);(336511489639298191839269739197%positive,1);(336511582681216535116427476395%positive,0);(355080683270497239239914339755%positive,0);(5871447243027432762482591%positive,1);(355080683270510401493610446251%positive,0);(5871447243027432762112505%positive,0);(336511582681108448725370584491%positive,0);(75413852868563%positive,0);(308895128872800927%positive,1);(75382765735795%positive,0);(22192603058791580584383782825%positive,0);(342894631100855919789619915245%positive,1);(336511489639311354092965845693%positive,1);(336511582681229697370123582891%positive,0);(384791166519096222240246046623%positive,1);(344057107720320109555626408607%positive,2);(384791166519096222240245676537%positive,0);(1266452583757265059241%positive,0);(344057107720320109451060354985%positive,0);(4710098136361%positive,0);(4710101282089%positive,0);(1266456872882022464939%positive,0);(83703773649129517276635039%positive,1);(22192603058791580688949836447%positive,2);(5231485848919036900878829%positive,1);(5231485853070590534822393%positive,0);(20263241340220807043743%positive,2);(5871447243027226603682297%positive,0);(355080683270389152848857447851%positive,0);(5871447243027226604052383%positive,1);(1339260376212736740873596329%positive,0);(355080590228578895962756602557%positive,1);(366965452689201662392825%positive,0);(392412232672271130785584884205%positive,1);(19326075877521213%positive,1);(355080590228470809571699710653%positive,1);(355080590228592058216452709053%positive,1);(336511489639190105448212847293%positive,1);(19326573271645501%positive,1)]]
  | StD => [HMeas MLeft 65 [(336511489639298191839269739197%positive,4);(80107037844204613358%positive,4);(5871447243027432762112505%positive,1);(336511582681216535116427668442%positive,2);(355080683270510401493610638298%positive,2);(1339260376212736678447995550%positive,4);(342894631100855919789619915245%positive,4);(392412220493961277685885955497%positive,3);(336511489639311354092965845693%positive,4);(4947088363607806938%positive,2);(4947080405301818330%positive,2);(392412220493961277623460354718%positive,4);(384791166519096222240245676537%positive,1);(22192603058791580688950077946%positive,0);(308635656770679454%positive,4);(336511582681229697370123774938%positive,2);(5006689865262763758%positive,4);(1266452583757265059241%positive,3);(344057107720320109451060354985%positive,3);(4710098136361%positive,3);(4710101282089%positive,3);(342894618922546066627495108314%positive,2);(80107037844204220142%positive,4);(18398833138%positive,4);(5231485848919036900878829%positive,4);(5231485853070590534822393%positive,1);(342894618922546066627495385758%positive,4);(5871447243027226603682297%positive,1);(18398820850%positive,4);(355080590228578895962756602557%positive,4);(355080683270497239239914531802%positive,2);(1339260376212736678447718106%positive,2);(366965452689201662392825%positive,4);(344057107720320109555626781178%positive,0);(392412232672271130785584884205%positive,4);(342894618922546066689920986537%positive,3);(19326075877521213%positive,4);(355080590228470809571699710653%positive,4);(22192603058791580584383782825%positive,3);(355080590228592058216452709053%positive,4);(336511489639190105448212847293%positive,4);(336511582681108448725370776538%positive,2);(355080683270389152848857639898%positive,2);(392412220493961277623460077274%positive,2);(1339260376212736740873596329%positive,3);(19326573271645501%positive,4)] [336511489639298191839269739197%positive;80107037844204613358%positive;5871447243027432762112505%positive;336511582681216535116427668442%positive;355080683270510401493610638298%positive;1339260376212736678447995550%positive;342894631100855919789619915245%positive;392412220493961277685885955497%positive;336511489639311354092965845693%positive;4947088363607806938%positive;4947080405301818330%positive;392412220493961277623460354718%positive;384791166519096222240245676537%positive;22192603058791580688950077946%positive;308635656770679454%positive;336511582681229697370123774938%positive;5006689865262763758%positive;1266452583757265059241%positive;344057107720320109451060354985%positive;4710098136361%positive;4710101282089%positive;342894618922546066627495108314%positive;80107037844204220142%positive;18398833138%positive;5231485848919036900878829%positive;5231485853070590534822393%positive;342894618922546066627495385758%positive;5871447243027226603682297%positive;18398820850%positive;355080590228578895962756602557%positive;355080683270497239239914531802%positive;1339260376212736678447718106%positive;366965452689201662392825%positive;392412232672271130785584884205%positive;342894618922546066689920986537%positive;19326075877521213%positive;355080590228470809571699710653%positive;22192603058791580584383782825%positive;355080590228592058216452709053%positive;336511489639190105448212847293%positive;336511582681108448725370776538%positive;355080683270389152848857639898%positive;392412220493961277623460077274%positive;344057107720320109555626781178%positive;1339260376212736740873596329%positive;19326573271645501%positive]]
  end.

Lemma cqh_h_00157 : iqh tmq_h_00157.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00157 StA 0 4 2 25 20000
                lsetq_h_00157 rsetq_h_00157 certq_h_00157 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00157); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00158 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StC)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StB)
  | StD, S0 => None
  | StD, S1 => None
  end.

Definition lsetq_h_00158 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StB,S1);(StB,S0)]);(S1,[(StC,S0);(StC,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StC,S1)]);(S0,[(StB,S1);(StB,S0)])]].

Definition rsetq_h_00158 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StB,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StB,S1)]);(S0,[(StC,S1);(StC,S0)])]].

Definition certq_h_00158 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(314502629555099310%positive,0);(19656414092777134%positive,0);(4705584999726%positive,0);(18415849170%positive,0);(1171552402%positive,0);(75289359995626%positive,0);(4705330582250%positive,0);(294083161390%positive,0);(299933075758%positive,0);(314502629555098346%positive,0);(19656414092776170%positive,0)]]
  | StC => [HRank [(20196337809%positive,0);(19082747846161821%positive,0);(294329734941%positive,0);(1149725041%positive,0);(5170262480669%positive,0);(82724199690713%positive,0);(19082747846160857%positive,0);(291179632413%positive,0);(338838321389466073%positive,0);(338838321389467037%positive,0);(4658874118617%positive,0)]]
  | StD => []
  end.

Lemma cqh_h_00158 : iqh tmq_h_00158.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00158 StA 0 2 2 25 20000
                lsetq_h_00158 rsetq_h_00158 certq_h_00158 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00158); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00159 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StC)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StD)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => None
  end.

Definition lsetq_h_00159 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StB,S0)]);(S1,[(StC,S0);(StC,S1)])];
   [(S0,[(StB,S1);(StD,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StB,S1);(StD,S0)]);(S1,[(StC,S0);(StC,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StC,S1)]);(S0,[(StB,S1);(StD,S0)])]].

Definition rsetq_h_00159 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StB,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1)]);(S0,[(StC,S1);(StC,S0)])]].

Definition certq_h_00159 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 22 [(299933600046%positive,2);(75289361044202%positive,2);(20263446675%positive,1);(339964223443792859%positive,1);(4705584999726%positive,2);(18415849170%positive,2);(314503179311960810%positive,2);(1171585170%positive,0);(314503179311961774%positive,2);(19656448453564078%positive,2);(19082749993644507%positive,1);(4705331630826%positive,2);(82999077598171%positive,1);(19656448453563114%positive,2)] [19082749993644507%positive;75289361044202%positive;299933600046%positive;20263446675%positive;4705331630826%positive;339964223443792859%positive;82999077598171%positive;1171585170%positive;314503179311961774%positive;4705584999726%positive;18415849170%positive;314503179311960810%positive;19656448453563114%positive;19656448453564078%positive]]
  | StC => [HRank [(20263446675%positive,0);(339964223443792859%positive,0);(294463952669%positive,0);(5187442349885%positive,0);(339964223443793341%positive,0);(1149725041%positive,0);(19082749993644507%positive,0);(291179632445%positive,0);(19082749993645501%positive,0);(82999077598171%positive,0)]]
  | StD => [HMeas MRight 22 [(299933600046%positive,25);(75289361044202%positive,24);(4705584999726%positive,0);(18415849170%positive,24);(314503179311960810%positive,24);(294463952669%positive,25);(1171585170%positive,25);(314503179311961774%positive,25);(5187442349885%positive,25);(339964223443793341%positive,25);(19656448453564078%positive,25);(1149725041%positive,23);(291179632445%positive,25);(19082749993645501%positive,25);(4705331630826%positive,24);(19656448453563114%positive,24)] [294463952669%positive;75289361044202%positive;299933600046%positive;4705331630826%positive;1171585170%positive;314503179311961774%positive;291179632445%positive;4705584999726%positive;18415849170%positive;314503179311960810%positive;339964223443793341%positive;5187442349885%positive;19656448453564078%positive;19656448453563114%positive;1149725041%positive;19082749993645501%positive]]
  end.

Lemma cqh_h_00159 : iqh tmq_h_00159.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00159 StA 0 2 2 25 20000
                lsetq_h_00159 rsetq_h_00159 certq_h_00159 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00159); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00160 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DR StD)
  | StD, S1 => Some (mkTrans S1 DR StB)
  end.

Definition lsetq_h_00160 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StC,S1)]);(S1,[(StD,S1);(StB,S0)])];
   [(S0,[(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StC,S0)]);(S0,[(StD,S0)])];
   [(S1,[(StD,S1);(StB,S0)]);(S0,[(StB,S1);(StC,S1)])];
   [(S1,[(StD,S1);(StB,S0)]);(S0,[(StD,S0);(StC,S0)])]].

Definition rsetq_h_00160 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StB,S1)]);(S1,[(StC,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StD,S0)]);(S1,[(StC,S1);(StD,S1)])];
   [(S1,[(StC,S1);(StD,S1)]);(S1,[(StB,S0)])];
   [(S1,[(StC,S1);(StD,S1)]);(S1,[(StB,S0);(StB,S1)])]].

Definition certq_h_00160 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(21178773891568543%positive,0);(1194050545111967%positive,0);(87810195968939%positive,1);(19122792595%positive,2);(294339177759%positive,0);(22479960003695102%positive,0);(338860380492584351%positive,0);(359679358286615038%positive,0);(75284329452030%positive,0);(343008577850%positive,3);(19104806949279135%positive,0)]]
  | StC => [HMeas MRight 23 [(19122792595%positive,1);(75285115434989%positive,1);(359679359072597997%positive,1);(75289544620013%positive,1);(359679363501783021%positive,1);(294339177759%positive,1);(87810195968939%positive,0);(18416570353%positive,0);(338860381278566105%positive,1);(19104812164445913%positive,1);(338860385707751129%positive,1);(19104807735260889%positive,1);(338860380492584351%positive,1);(21178773891568543%positive,1);(82729585201849%positive,1);(19104806949279135%positive,1);(1194050545111967%positive,1)] [19104812164445913%positive;338860385707751129%positive;19122792595%positive;19104807735260889%positive;359679359072597997%positive;75285115434989%positive;338860381278566105%positive;75289544620013%positive;359679363501783021%positive;294339177759%positive;338860380492584351%positive;21178773891568543%positive;19104806949279135%positive;87810195968939%positive;1194050545111967%positive;18416570353%positive;82729585201849%positive]]
  | StD => [HMeas MLeft 23 [(75285115434989%positive,2);(359679359072597997%positive,2);(75289544620013%positive,2);(359679363501783021%positive,2);(18416570353%positive,2);(22479960003695102%positive,2);(338860381278566105%positive,1);(19104812164445913%positive,1);(338860385707751129%positive,1);(19104807735260889%positive,1);(82729585201849%positive,1);(359679358286615038%positive,2);(75284329452030%positive,2);(343008577850%positive,0)] [19104812164445913%positive;359679358286615038%positive;22479960003695102%positive;75284329452030%positive;338860385707751129%positive;343008577850%positive;19104807735260889%positive;359679359072597997%positive;75285115434989%positive;338860381278566105%positive;75289544620013%positive;359679363501783021%positive;18416570353%positive;82729585201849%positive]]
  end.

Lemma cqh_h_00160 : iqh tmq_h_00160.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00160 StA 0 2 2 25 20000
                lsetq_h_00160 rsetq_h_00160 certq_h_00160 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00160); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00161 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => None
  end.

Definition lsetq_h_00161 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1)]);(S0,[(StB,S1);(StB,S0)])]].

Definition rsetq_h_00161 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StB,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition certq_h_00161 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(75289427104747%positive,0);(1171552402%positive,0);(323509828876949182%positive,0);(20219364046198462%positive,0);(294083161406%positive,0);(4705589194046%positive,0);(308523010350%positive,0);(20219364046197483%positive,0);(323509828876948459%positive,0);(18416111315%positive,0)]]
  | StC => [HMeas MRight 22 [(338842719436010909%positive,2);(1149725169%positive,0);(20196337809%positive,2);(75289427104747%positive,1);(19087145892705693%positive,2);(294329736989%positive,2);(5170262480669%positive,2);(20219364046197483%positive,1);(338842719436009945%positive,2);(323509828876948459%positive,1);(82725273432537%positive,2);(18416111315%positive,1);(19087145892704729%positive,2);(4659947860441%positive,2)] [294329736989%positive;18416111315%positive;5170262480669%positive;338842719436010909%positive;19087145892705693%positive;1149725169%positive;20196337809%positive;75289427104747%positive;20219364046197483%positive;338842719436009945%positive;19087145892704729%positive;323509828876948459%positive;82725273432537%positive;4659947860441%positive]]
  | StD => [HMeas MLeft 22 [(338842719436010909%positive,25);(1149725169%positive,25);(20196337809%positive,24);(1171552402%positive,23);(19087145892705693%positive,25);(323509828876949182%positive,25);(20219364046198462%positive,25);(294083161406%positive,25);(4705589194046%positive,25);(294329736989%positive,25);(308523010350%positive,25);(5170262480669%positive,0);(338842719436009945%positive,24);(82725273432537%positive,24);(19087145892704729%positive,24);(4659947860441%positive,24)] [294329736989%positive;308523010350%positive;5170262480669%positive;338842719436010909%positive;4659947860441%positive;19087145892705693%positive;1149725169%positive;20196337809%positive;82725273432537%positive;323509828876949182%positive;338842719436009945%positive;20219364046198462%positive;19087145892704729%positive;1171552402%positive;294083161406%positive;4705589194046%positive]]
  end.

Lemma cqh_h_00161 : iqh tmq_h_00161.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00161 StA 0 2 2 25 20000
                lsetq_h_00161 rsetq_h_00161 certq_h_00161 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00161); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00162 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StD)
  | StD, S1 => Some (mkTrans S0 DR StC)
  end.

Definition lsetq_h_00162 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StB,S1);(StB,S0)]);(S1,[(StC,S0);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StD,S0);(StC,S1)]);(S0,[(StB,S1);(StB,S0)])]].

Definition rsetq_h_00162 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StD,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S1,[(StB,S0);(StD,S1)]);(S0,[(StC,S1);(StC,S0)])]].

Definition certq_h_00162 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(323509828877014702%positive,0);(1171552402%positive,0);(314511425715295210%positive,0);(356857117945492895%positive,1);(323509828809839339%positive,2);(4705589198126%positive,0);(308523010350%positive,0);(18416111570%positive,0);(20219364046197483%positive,2);(314511425648121534%positive,0);(294329736991%positive,1);(19656963848591038%positive,0);(75289359995627%positive,2);(4705330582251%positive,2)]]
  | StC => [HRank [(294329736991%positive,0);(75289359995627%positive,1);(19082747980380061%positive,2);(20196337809%positive,0);(356857117945492895%positive,0);(323509828809839339%positive,1);(338838321389498873%positive,0);(356857118079676889%positive,0);(20219364046197483%positive,1);(5170262480669%positive,2);(19082747846193657%positive,0);(338838321523685277%positive,2);(1149757809%positive,0);(4705330582251%positive,1);(291179632413%positive,2);(87123319943641%positive,0)]]
  | StD => [HMeas MLeft 26 [(19082747980380061%positive,2);(20196337809%positive,28);(323509828877014702%positive,29);(1171552402%positive,27);(338838321389498873%positive,28);(4705589198126%positive,27);(308523010350%positive,29);(356857118079676889%positive,28);(5170262480669%positive,0);(18416111570%positive,29);(19082747846193657%positive,26);(314511425715295210%positive,29);(314511425648121534%positive,29);(338838321523685277%positive,2);(1149757809%positive,2);(291179632413%positive,0);(87123319943641%positive,28);(19656963848591038%positive,29)] [338838321523685277%positive;19082747980380061%positive;308523010350%positive;356857118079676889%positive;5170262480669%positive;18416111570%positive;1149757809%positive;291179632413%positive;338838321389498873%positive;20196337809%positive;19082747846193657%positive;87123319943641%positive;323509828877014702%positive;19656963848591038%positive;1171552402%positive;314511425715295210%positive;314511425648121534%positive;4705589198126%positive]]
  end.

Lemma cqh_h_00162 : iqh tmq_h_00162.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00162 StA 0 2 2 25 20000
                lsetq_h_00162 rsetq_h_00162 certq_h_00162 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00162); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00163 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StB)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StB)
  end.

Definition lsetq_h_00163 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S1);(StB,S1)]);(S1,[(StD,S0)])];
   [(S1,[(StC,S1);(StB,S1)]);(S1,[(StD,S0);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StD,S1)]);(S1,[(StC,S1);(StB,S1)])]].

Definition rsetq_h_00163 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0)]);(S0,[])];
   [(S0,[(StD,S1);(StC,S1)]);(S1,[(StB,S1);(StD,S0)])];
   [(S1,[(StB,S1);(StD,S0)]);(S0,[(StC,S0)])];
   [(S1,[(StB,S1);(StD,S0)]);(S0,[(StD,S1);(StC,S1)])]].

Definition certq_h_00163 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 21 [(19509156578719215%positive,2);(85714520372719%positive,2);(323093594137031646%positive,2);(294725023531%positive,1);(78880271102942%positive,2);(18412705266%positive,0);(1219322151139067%positive,1);(351086679143871983%positive,2);(21942917311461115%positive,1);(20926396563%positive,2);(19509158523926267%positive,1);(75494716208094%positive,2);(351086681089079035%positive,1);(4762976777711%positive,2)] [323093594137031646%positive;351086679143871983%positive;19509156578719215%positive;85714520372719%positive;21942917311461115%positive;20926396563%positive;18412705266%positive;19509158523926267%positive;294725023531%positive;75494716208094%positive;351086681089079035%positive;78880271102942%positive;4762976777711%positive;1219322151139067%positive]]
  | StC => [HMeas MLeft 21 [(308126058813%positive,1);(19509156578719215%positive,1);(85714520372719%positive,1);(294725023531%positive,1);(20193349498533821%positive,1);(323093596082239421%positive,1);(1219322151139067%positive,1);(351086679143871983%positive,1);(4718284731069%positive,1);(21942917311461115%positive,1);(20926396563%positive,0);(19509158523926267%positive,1);(351086681089079035%positive,1);(75496661414589%positive,1);(4762976777711%positive,1)] [351086679143871983%positive;308126058813%positive;19509156578719215%positive;85714520372719%positive;4718284731069%positive;21942917311461115%positive;20926396563%positive;20193349498533821%positive;19509158523926267%positive;294725023531%positive;351086681089079035%positive;75496661414589%positive;1219322151139067%positive;4762976777711%positive;323093596082239421%positive]]
  | StD => [HRank [(308126058813%positive,0);(323093594137031646%positive,0);(78880271102942%positive,0);(75496661414589%positive,0);(4718284731069%positive,0);(18412705266%positive,1);(20193349498533821%positive,0);(323093596082239421%positive,0);(75494716208094%positive,0)]]
  end.

Lemma cqh_h_00163 : iqh tmq_h_00163.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00163 StA 0 2 2 25 20000
                lsetq_h_00163 rsetq_h_00163 certq_h_00163 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00163); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00164 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StB)
  | StC, S1 => Some (mkTrans S0 DR StB)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Definition lsetq_h_00164 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1);(StB,S1);(StB,S1)]);(S1,[(StD,S0);(StC,S1);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0);(StC,S1);(StB,S1);(StC,S0)]);(S1,[(StD,S0);(StC,S1);(StB,S1);(StB,S1)])];
   [(S1,[(StD,S0);(StC,S1);(StB,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StC,S1);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StC,S1);(StB,S1);(StB,S1)])];
   [(S1,[(StD,S0);(StC,S1);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StC,S1);(StB,S1);(StD,S0)])]].

Definition rsetq_h_00164 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StD,S0);(StC,S1);(StB,S1)]);(S1,[(StC,S0);(StC,S1);(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StD,S0);(StC,S1);(StB,S1)]);(S1,[(StD,S1);(StD,S0);(StC,S1);(StB,S1)])];
   [(S1,[(StC,S0);(StC,S1);(StB,S1);(StB,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StD,S1);(StD,S0);(StC,S1);(StB,S1)]);(S1,[(StB,S1);(StD,S0);(StC,S1);(StB,S1)])]].

Definition certq_h_00164 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(375559869038109313776762609343%positive,0);(308909645487272414%positive,0);(20207973447075781586411%positive,1);(81940044711391860618608094%positive,0);(335430800877122363595888524779%positive,1);(375559869038145342505062154206%positive,0);(1263167283376072026846%positive,0);(82016501817862571263516139%positive,1);(81940044675363063599644126%positive,0);(81892285370373764398972395%positive,1);(335430785381857341679865348062%positive,0);(375555048977669829765763423723%positive,1);(375555033344054227296918617566%positive,0);(375559884533410364421085330923%positive,1);(91689421151873515109400542%positive,0);(375559869038073284979743645375%positive,0);(375555048977633800968744459755%positive,1);(81892281587350077407936478%positive,0);(87440723780917214699%positive,1);(335430785381821312951565803199%positive,0);(375555033344018198499899653598%positive,0);(91689424934897202100436459%positive,1);(1399069536619068645055%positive,0);(82016501853891368282480107%positive,1);(5465045008808276958%positive,0);(5211939633299%positive,1);(335430785381785284154546839231%positive,0);(78945703404748348906%positive,0)]]
  | StC => [HMeas MLeft 45 [(375559869038109313776762609343%positive,1);(375555033344018198366644464605%positive,1);(20207973447075781586411%positive,0);(335430800877122363595888524779%positive,0);(82016501817862571263516139%positive,0);(5118267599209379837373437%positive,1);(81892285370373764398972395%positive,0);(375555048977669829765763423723%positive,0);(375559884533410364421085330923%positive,0);(81940044747420588917841597%positive,1);(21347832065657149%positive,1);(1263167283307241135789%positive,1);(375559869038073284979743645375%positive,1);(75365854277457%positive,1);(81940044675362930344455133%positive,1);(335430785381857341611034668029%positive,1);(375555033344054227163663428573%positive,1);(375555048977633800968744459755%positive,0);(375559869038145342436231474173%positive,1);(5730588821992094693714941%positive,1);(87440723780917214699%positive,0);(335430785381821312951565803199%positive,1);(91689424934897202100436459%positive,0);(1399069536619068645055%positive,1);(82016501853891368282480107%positive,0);(5211939633299%positive,0);(335430785381785284154546839231%positive,1);(375555033344090256025218178749%positive,1);(91688240562504597511855805%positive,1);(19306852874908957%positive,1);(81940044711391727363419101%positive,1)] [375559869038109313776762609343%positive;375555033344018198366644464605%positive;20207973447075781586411%positive;335430800877122363595888524779%positive;82016501817862571263516139%positive;5118267599209379837373437%positive;81892285370373764398972395%positive;375555048977669829765763423723%positive;375559884533410364421085330923%positive;21347832065657149%positive;81940044747420588917841597%positive;375559869038073284979743645375%positive;1263167283307241135789%positive;81940044675362930344455133%positive;75365854277457%positive;375555033344054227163663428573%positive;375555048977633800968744459755%positive;375559869038145342436231474173%positive;5730588821992094693714941%positive;87440723780917214699%positive;335430785381821312951565803199%positive;91689424934897202100436459%positive;1399069536619068645055%positive;82016501853891368282480107%positive;5211939633299%positive;335430785381785284154546839231%positive;375555033344090256025218178749%positive;91688240562504597511855805%positive;335430785381857341611034668029%positive;19306852874908957%positive;81940044711391727363419101%positive]]
  | StD => [HRank [(375555033344018198366644464605%positive,0);(375555033344054227163663428573%positive,0);(375559869038145342505062154206%positive,1);(1263167283307241135789%positive,0);(81940044711391860618608094%positive,1);(5118267599209379837373437%positive,0);(81940044675363063599644126%positive,1);(91689421151873515109400542%positive,1);(81940044747420588917841597%positive,0);(21347832065657149%positive,0);(78945703404748348906%positive,1);(75365854277457%positive,2);(81940044675362930344455133%positive,0);(335430785381857341611034668029%positive,0);(375559869038145342436231474173%positive,0);(375555033344054227296918617566%positive,1);(81940044711391727363419101%positive,0);(335430785381857341679865348062%positive,1);(5730588821992094693714941%positive,0);(81892281587350077407936478%positive,1);(308909645487272414%positive,3);(375555033344090256025218178749%positive,0);(5465045008808276958%positive,1);(91688240562504597511855805%positive,0);(19306852874908957%positive,0);(375555033344018198499899653598%positive,1);(1263167283376072026846%positive,1)]]
  end.

Lemma cqh_h_00164 : iqh tmq_h_00164.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00164 StA 0 4 2 25 20000
                lsetq_h_00164 rsetq_h_00164 certq_h_00164 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00164); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00165 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StC)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StB)
  end.

Definition lsetq_h_00165 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S1);(StB,S1)]);(S1,[(StD,S0)])];
   [(S1,[(StC,S1);(StB,S1)]);(S1,[(StD,S0);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StD,S1)]);(S1,[(StC,S1);(StB,S1)])]].

Definition rsetq_h_00165 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StC,S0)]);(S0,[])];
   [(S0,[(StD,S1);(StC,S1)]);(S1,[(StB,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S1,[(StB,S1);(StD,S0)])];
   [(S1,[(StB,S1);(StC,S1)]);(S0,[(StD,S1);(StC,S0)])];
   [(S1,[(StB,S1);(StD,S0)]);(S0,[(StD,S1);(StC,S1)])]].

Definition certq_h_00165 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 29 [(85714520372719%positive,32);(1209366082352862%positive,32);(4722579699646%positive,0);(75565380892606%positive,0);(323093594137031646%positive,32);(19691942131496699%positive,31);(315071078209648379%positive,31);(78880271102942%positive,32);(4715600376571%positive,31);(76921648575983%positive,32);(315071076264441327%positive,32);(294603323183%positive,28);(350115191901254622%positive,32);(18412715506%positive,30);(351086679143871983%positive,32);(21942917311461115%positive,31);(20926396563%positive,32);(85477340869598%positive,32);(351086681089079035%positive,31)] [85714520372719%positive;1209366082352862%positive;4722579699646%positive;75565380892606%positive;323093594137031646%positive;19691942131496699%positive;315071078209648379%positive;78880271102942%positive;4715600376571%positive;76921648575983%positive;315071076264441327%positive;294603323183%positive;350115191901254622%positive;18412715506%positive;351086679143871983%positive;21942917311461115%positive;20926396563%positive;85477340869598%positive;351086681089079035%positive]]
  | StC => [HMeas MLeft 29 [(308126058813%positive,1);(85714520372719%positive,1);(19691942131496699%positive,1);(315071078209648379%positive,1);(333895862589%positive,1);(4715600376571%positive,1);(76921648575983%positive,1);(315071076264441327%positive,1);(294603323183%positive,1);(20193349498533821%positive,1);(21882199358797757%positive,1);(323093596082239421%positive,1);(351086679143871983%positive,1);(21942917311461115%positive,1);(20926396563%positive,0);(350115193846462397%positive,1);(75585245115373%positive,1);(351086681089079035%positive,1);(1209368027558893%positive,1)] [308126058813%positive;85714520372719%positive;19691942131496699%positive;315071078209648379%positive;333895862589%positive;4715600376571%positive;76921648575983%positive;315071076264441327%positive;294603323183%positive;20193349498533821%positive;21882199358797757%positive;323093596082239421%positive;351086679143871983%positive;21942917311461115%positive;20926396563%positive;350115193846462397%positive;75585245115373%positive;351086681089079035%positive;1209368027558893%positive]]
  | StD => [HRank [(308126058813%positive,0);(1209366082352862%positive,0);(4722579699646%positive,0);(75565380892606%positive,0);(323093594137031646%positive,0);(333895862589%positive,0);(78880271102942%positive,0);(20193349498533821%positive,0);(350115191901254622%positive,0);(18412715506%positive,1);(21882199358797757%positive,0);(323093596082239421%positive,0);(350115193846462397%positive,0);(85477340869598%positive,0);(75585245115373%positive,0);(1209368027558893%positive,0)]]
  end.

Lemma cqh_h_00165 : iqh tmq_h_00165.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00165 StA 0 2 2 25 20000
                lsetq_h_00165 rsetq_h_00165 certq_h_00165 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00165); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00166 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StB)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => None
  | StD, S1 => None
  end.

Definition lsetq_h_00166 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StB,S1);(StB,S0)])]].

Definition rsetq_h_00166 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StB,S1)])];
   [(S1,[(StB,S0);(StC,S1)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1)]);(S1,[(StB,S0);(StC,S1)])]].

Definition certq_h_00166 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 68 [(1358835186225630%positive,1);(19099034376401374%positive,1);(341525528677642718%positive,1);(5307902759594%positive,0);(1334084095005150%positive,1);(19095941999948254%positive,1);(347861807174447582%positive,1);(75285048259038%positive,1);(347858715653632478%positive,1);(5211313181354%positive,1);(341528620198457822%positive,1);(1358823106630110%positive,1);(341525527822004702%positive,1);(5307949945514%positive,1);(19099035232039390%positive,1);(341528621054095838%positive,1);(1334096174600670%positive,1);(75284192621022%positive,1);(19095942855586270%positive,1);(74605604983262%positive,1);(5211265995434%positive,0);(347858714797994462%positive,1);(74593525387742%positive,1);(347861808030085598%positive,1)] [1358835186225630%positive;19099034376401374%positive;341525528677642718%positive;5307902759594%positive;19095941999948254%positive;1334084095005150%positive;347861807174447582%positive;75285048259038%positive;347858715653632478%positive;5211313181354%positive;341528620198457822%positive;1358823106630110%positive;341525527822004702%positive;5307949945514%positive;19099035232039390%positive;341528621054095838%positive;1334096174600670%positive;75284192621022%positive;19095942855586270%positive;74605604983262%positive;5211265995434%positive;347858714797994462%positive;74593525387742%positive;347861808030085598%positive]]
  | StC => [HMeas MRight 68 [(75285048260073%positive,0);(341525527822005917%positive,1);(1334084095006185%positive,1);(347858715653633513%positive,0);(341528620198458857%positive,0);(294330625821%positive,1);(74605604984477%positive,1);(19099034376402409%positive,0);(341528621054097053%positive,1);(19095941999949289%positive,0);(74593525388957%positive,1);(19095942855587485%positive,1);(347861807174448617%positive,0);(19099035232040425%positive,0);(1358835186226845%positive,1);(1358823106631145%positive,1);(347861808030086813%positive,1);(347858714797995677%positive,1);(19095942855587305%positive,0);(1334096174601885%positive,1);(75284192622057%positive,0);(75285048260253%positive,1);(1334084095006365%positive,1);(341525527822005737%positive,0);(19099034376402589%positive,1);(341525528677643933%positive,1);(75284192622237%positive,1);(341528620198459037%positive,1);(341528621054096873%positive,0);(74605604984297%positive,1);(19095941999949469%positive,1);(74593525388777%positive,1);(341525528677643753%positive,0);(347861807174448797%positive,1);(1358835186226665%positive,1);(19099035232040605%positive,1);(347861808030086633%positive,0);(1358823106631325%positive,1);(347858714797995497%positive,0);(347858715653633693%positive,1);(18395664113%positive,0);(1334096174601705%positive,1)] [75285048260073%positive;341525527822005917%positive;1334084095006185%positive;347858715653633513%positive;341528620198458857%positive;294330625821%positive;74605604984477%positive;19099034376402409%positive;341528621054097053%positive;19095941999949289%positive;74593525388957%positive;19095942855587485%positive;347861807174448617%positive;19099035232040425%positive;1358835186226845%positive;1358823106631145%positive;347861808030086813%positive;347858714797995677%positive;19095942855587305%positive;1334096174601885%positive;75284192622057%positive;75285048260253%positive;1334084095006365%positive;341525527822005737%positive;19099034376402589%positive;341525528677643933%positive;341528620198459037%positive;341528621054096873%positive;74605604984297%positive;19095941999949469%positive;74593525388777%positive;341525528677643753%positive;347861807174448797%positive;1358835186226665%positive;19099035232040605%positive;347861808030086633%positive;1358823106631325%positive;347858714797995497%positive;347858715653633693%positive;18395664113%positive;75284192622237%positive;1334096174601705%positive]]
  | StD => []
  end.

Lemma cqh_h_00166 : iqh tmq_h_00166.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00166 StA 0 2 2 25 20000
                lsetq_h_00166 rsetq_h_00166 certq_h_00166 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00166); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00167 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StB)
  | StC, S0 => Some (mkTrans S1 DL StB)
  | StC, S1 => Some (mkTrans S0 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S0 DR StC)
  end.

Definition lsetq_h_00167 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StB,S1);(StC,S0)])];
   [(S1,[(StB,S1);(StC,S0)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StC,S0)]);(S1,[(StB,S1);(StD,S0)])];
   [(S1,[(StB,S1);(StD,S0)]);(S0,[])]].

Definition rsetq_h_00167 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S0);(StC,S1)])];
   [(S1,[(StC,S0);(StC,S1)]);(S1,[(StB,S0)])];
   [(S1,[(StC,S0);(StC,S1)]);(S1,[(StB,S0);(StD,S1)])]].

Definition certq_h_00167 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(75284194776554%positive,0);(75286342260202%positive,0);(348429155176535530%positive,0);(348429157324019178%positive,0);(1394007479349983%positive,1);(85065711875562%positive,0);(21270866067%positive,1);(356865915126477535%positive,1);(348429155174904286%positive,2);(74593526018783%positive,1);(75286340628958%positive,2);(5316606989278%positive,2);(19095943073690335%positive,1);(348429157322387934%positive,2);(75284193145310%positive,2)]]
  | StC => [HMeas MRight 31 [(19099310328051193%positive,1);(348429156248123053%positive,1);(74606679356921%positive,1);(356869283455104925%positive,1);(340337068349%positive,1);(18399858417%positive,0);(19099311402317725%positive,1);(356869281307621277%positive,1);(1394007479349983%positive,1);(21270866067%positive,1);(19099309254834077%positive,1);(294330658589%positive,1);(74593526018783%positive,1);(356865915126477535%positive,1);(19095943073690335%positive,1);(1361051389982381%positive,1);(356869282380838393%positive,1);(75285266364077%positive,1);(1394020632688121%positive,1)] [19099310328051193%positive;348429156248123053%positive;74606679356921%positive;356869283455104925%positive;340337068349%positive;18399858417%positive;19099311402317725%positive;356869281307621277%positive;1394007479349983%positive;21270866067%positive;19099309254834077%positive;294330658589%positive;74593526018783%positive;356865915126477535%positive;19095943073690335%positive;1361051389982381%positive;356869282380838393%positive;75285266364077%positive;1394020632688121%positive]]
  | StD => [HMeas MRight 31 [(19099310328051193%positive,32);(348429156248123053%positive,64);(74606679356921%positive,32);(356869283455104925%positive,64);(75284194776554%positive,64);(340337068349%positive,32);(75286342260202%positive,64);(18399858417%positive,63);(19099311402317725%positive,64);(348429155176535530%positive,64);(356869281307621277%positive,64);(348429157324019178%positive,64);(348429155174904286%positive,0);(19099309254834077%positive,64);(294330658589%positive,64);(85065711875562%positive,64);(75286340628958%positive,31);(5316606989278%positive,0);(1361051389982381%positive,62);(356869282380838393%positive,32);(75285266364077%positive,64);(348429157322387934%positive,0);(1394020632688121%positive,32);(75284193145310%positive,31)] [19099310328051193%positive;348429156248123053%positive;74606679356921%positive;356869283455104925%positive;75284194776554%positive;340337068349%positive;75286342260202%positive;18399858417%positive;19099311402317725%positive;348429155176535530%positive;356869281307621277%positive;348429157324019178%positive;348429155174904286%positive;19099309254834077%positive;294330658589%positive;85065711875562%positive;75286340628958%positive;5316606989278%positive;1361051389982381%positive;356869282380838393%positive;75285266364077%positive;348429157322387934%positive;1394020632688121%positive;75284193145310%positive]]
  end.

Lemma cqh_h_00167 : iqh tmq_h_00167.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00167 StA 0 2 2 25 20000
                lsetq_h_00167 rsetq_h_00167 certq_h_00167 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00167); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00168 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StC)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00168 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0);(StD,S0);(StC,S0)]);(S1,[(StB,S1);(StC,S1);(StB,S1);(StC,S1)])];
   [(S0,[(StC,S0);(StC,S0);(StD,S0);(StC,S0)]);(S1,[(StB,S1);(StC,S1);(StC,S1);(StB,S1)])];
   [(S0,[(StC,S0);(StD,S0);(StC,S0);(StD,S0)]);(S1,[(StB,S1);(StC,S1);(StB,S1);(StC,S1)])];
   [(S0,[(StC,S0);(StD,S0);(StC,S0);(StD,S1)]);(S1,[(StB,S1);(StC,S1);(StC,S1);(StB,S1)])];
   [(S0,[(StC,S0);(StD,S1);(StB,S1);(StB,S0)]);(S1,[(StB,S1);(StB,S0);(StD,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0);(StD,S0);(StC,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StC,S1);(StB,S1);(StC,S1)]);(S0,[(StC,S0);(StD,S0);(StC,S0);(StD,S0)])];
   [(S1,[(StB,S1);(StC,S1);(StB,S1);(StC,S1)]);(S0,[(StC,S0);(StD,S0);(StC,S0);(StD,S1)])];
   [(S1,[(StB,S1);(StC,S1);(StC,S1);(StB,S1)]);(S0,[(StC,S0);(StD,S1);(StB,S1);(StB,S0)])]].

Definition rsetq_h_00168 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StC,S0);(StC,S0);(StD,S0)]);(S0,[(StD,S1);(StB,S1);(StB,S0);(StD,S1)])];
   [(S0,[(StD,S0);(StC,S0);(StD,S0);(StC,S0)]);(S1,[(StC,S1);(StB,S1);(StC,S1);(StB,S1)])];
   [(S0,[(StD,S0);(StC,S0);(StD,S1);(StB,S1)]);(S0,[(StD,S1);(StB,S1);(StC,S1);(StC,S1)])];
   [(S0,[(StD,S0);(StC,S0);(StD,S1);(StB,S1)]);(S1,[(StC,S1);(StB,S1);(StC,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S1);(StB,S0);(StD,S0)]);(S1,[(StC,S1);(StC,S1);(StB,S1);(StB,S0)])];
   [(S0,[(StD,S1);(StB,S1);(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S1);(StB,S0)])];
   [(S0,[(StD,S1);(StB,S1);(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S1);(StC,S1);(StB,S0)])];
   [(S0,[(StD,S1);(StB,S1);(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S1);(StC,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S1);(StC,S1);(StC,S1)]);(S1,[(StC,S1);(StB,S0)])];
   [(S1,[(StC,S1);(StB,S0)]);(S0,[])];
   [(S1,[(StC,S1);(StB,S1);(StB,S0);(StD,S0)]);(S0,[(StD,S0);(StC,S0);(StD,S1);(StB,S1)])];
   [(S1,[(StC,S1);(StB,S1);(StC,S1);(StB,S1)]);(S0,[(StD,S0);(StC,S0);(StC,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StB,S1);(StC,S1);(StB,S1)]);(S0,[(StD,S0);(StC,S0);(StD,S0);(StC,S0)])];
   [(S1,[(StC,S1);(StB,S1);(StC,S1);(StC,S1)]);(S0,[(StD,S0);(StC,S0);(StC,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StB,S1);(StC,S1);(StC,S1)]);(S0,[(StD,S0);(StC,S0);(StD,S0);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S1);(StB,S0)]);(S0,[])];
   [(S1,[(StC,S1);(StC,S1);(StB,S1);(StB,S0)]);(S0,[(StD,S0);(StC,S0);(StD,S1);(StB,S1)])];
   [(S1,[(StC,S1);(StC,S1);(StC,S1);(StB,S0)]);(S0,[])];
   [(S1,[(StC,S1);(StC,S1);(StC,S1);(StC,S1)]);(S0,[])]].

Definition certq_h_00168 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 84 [(1379796897956530920096915371%positive,1);(392348783772563883827695902430%positive,2);(79024287383584960238%positive,2);(343943436692783739758489873323%positive,1);(78322430830738%positive,0);(336059458839671517073607207610%positive,2);(392348783772546995466532216542%positive,2);(375634762144607517411626114782%positive,2);(5174454222250717107059167%positive,2);(353227986987496149414271232939%positive,1);(5268901551908110011333087%positive,2);(20050645371816234%positive,2);(305081278622372523%positive,1);(1343529123368092044855730091%positive,1);(342088091231097515%positive,1);(78322833483922%positive,0);(21003718841437809863208123051%positive,1);(343943436692783739758489811642%positive,2);(343943436692751370103956155307%positive,1);(375634762144532856112313396958%positive,2);(308688622592127470%positive,2);(385577060410982300821000207019%positive,1);(336059458839599459479569279674%positive,2);(21003718841470179517742164666%positive,2);(4939017961474039534%positive,2);(323403235834375458650591%positive,2);(336059350346299169055486159786%positive,2);(21003718841542237111780092602%positive,2);(385577060411014670475534248634%positive,2);(336059458839599459479569218219%positive,1);(385577060411086728069572176570%positive,2);(343943436692855797352527739578%positive,2);(385577060411014670475534187179%positive,1);(1506016239212142597346926062%positive,2);(336059350346227111461448231850%positive,2);(1312722105046901974069803706%positive,2);(375634762144590629050462428894%positive,2);(343943455582217301582536899258%positive,2);(1469257035349676362558578170%positive,2);(353227986987424091820233243322%positive,2);(22979876032446211471838%positive,2);(353227986987424091820233305003%positive,1);(79024287383584632558%positive,2);(353227986987496149414271171258%positive,2);(323403252722874061289951%positive,2);(1506009155662418292879105518%positive,2);(392348783772489222528383184606%positive,2);(336059458839567089825035238059%positive,1);(21003610348097831499621116842%positive,2);(353228005876857653644280330938%positive,2);(20050542292601130%positive,2);(385576951917642322457413200810%positive,2);(5174454205362218504419807%positive,2);(21003718841470179517742103211%positive,1);(22419083180994460826079%positive,2);(5268901535019611408693727%positive,2);(21003610348169889093659044778%positive,2);(343943436692855797352527801259%positive,1);(336059458839671517073607146155%positive,1);(385576951917714380051451128746%positive,2);(1312721045512039240377543594%positive,2);(21003718841542237111780031147%positive,1);(385577060411086728069572115115%positive,1);(353227986987391722165699586987%positive,1)] [1379796897956530920096915371%positive;343943455582217301582536899258%positive;21003718841437809863208123051%positive;353227986987391722165699586987%positive;343943436692783739758489811642%positive;343943436692751370103956155307%positive;392348783772563883827695902430%positive;353228005876857653644280330938%positive;20050542292601130%positive;375634762144532856112313396958%positive;79024287383584960238%positive;343943436692783739758489873323%positive;1469257035349676362558578170%positive;385576951917642322457413200810%positive;308688622592127470%positive;375634762144590629050462428894%positive;385577060410982300821000207019%positive;336059458839599459479569279674%positive;353227986987424091820233243322%positive;336059458839567089825035238059%positive;5174454205362218504419807%positive;21003718841470179517742103211%positive;22419083180994460826079%positive;78322430830738%positive;336059458839671517073607207610%positive;21003718841470179517742164666%positive;22979876032446211471838%positive;353227986987424091820233305003%positive;5268901535019611408693727%positive;4939017961474039534%positive;323403235834375458650591%positive;336059350346299169055486159786%positive;392348783772546995466532216542%positive;21003718841542237111780092602%positive;375634762144607517411626114782%positive;385577060411014670475534248634%positive;336059458839599459479569218219%positive;79024287383584632558%positive;21003610348169889093659044778%positive;385577060411086728069572176570%positive;343943436692855797352527739578%positive;343943436692855797352527801259%positive;5174454222250717107059167%positive;336059458839671517073607146155%positive;385576951917714380051451128746%positive;1312721045512039240377543594%positive;21003718841542237111780031147%positive;353227986987496149414271171258%positive;353227986987496149414271232939%positive;5268901551908110011333087%positive;20050645371816234%positive;385577060411014670475534187179%positive;323403252722874061289951%positive;305081278622372523%positive;1506016239212142597346926062%positive;1506009155662418292879105518%positive;1343529123368092044855730091%positive;385577060411086728069572115115%positive;336059350346227111461448231850%positive;392348783772489222528383184606%positive;1312722105046901974069803706%positive;342088091231097515%positive;78322833483922%positive;21003610348097831499621116842%positive]]
  | StC => [HRank [(1379796897956530920096915371%positive,0);(343943436692783739758489873323%positive,0);(336059458839671517073607146155%positive,0);(336059458839599459479569218219%positive,0);(5174454222250717107059167%positive,1);(353227986987496149414271232939%positive,0);(385577060411086728069572115115%positive,0);(385577060411014670475534187179%positive,0);(5268901551908110011333087%positive,1);(305081278622372523%positive,0);(1343529123368092044855730091%positive,0);(342088091231097515%positive,0);(21003718841437809863208123051%positive,0);(343943436692751370103956155307%positive,0);(385577060410982300821000207019%positive,0);(323403235834375458650591%positive,1);(78100807327327529657%positive,0);(392348783772546995466532220397%positive,0);(20212550238885268348829%positive,0);(375634762144590629050462432749%positive,0);(5268901551908107998174713%positive,0);(385538343849580175616893902573%positive,0);(5268901551908110011064221%positive,0);(385540157238309597560655961837%positive,0);(19993806675795850210205%positive,0);(353227986987424091820233305003%positive,0);(22419085146921251285917%positive,0);(21003718841542237111780031147%positive,0);(21003718841470179517742103211%positive,0);(323403252722874061289951%positive,1);(336059458839567089825035238059%positive,0);(323403252722872048131577%positive,0);(375634762144607517411626053101%positive,0);(323403252722874061021085%positive,0);(5174454205362218504419807%positive,1);(22419083180994460826079%positive,1);(5268901535019611408693727%positive,1);(20212550239055053778425%positive,0);(343943436692855797352527801259%positive,0);(87574551355161127609%positive,0);(392348783772563883827695840749%positive,0);(5174454222250715093900793%positive,0);(353227986987391722165699586987%positive,0);(5174454222250717106790301%positive,0)]]
  | StD => [HMeas MRight 84 [(392348783772563883827695902430%positive,87);(79024287383584960238%positive,87);(78322430830738%positive,87);(336059458839671517073607207610%positive,86);(392348783772546995466532216542%positive,87);(375634762144607517411626114782%positive,87);(20050645371816234%positive,1);(78322833483922%positive,87);(343943436692783739758489811642%positive,86);(375634762144532856112313396958%positive,87);(308688622592127470%positive,87);(336059458839599459479569279674%positive,86);(21003718841470179517742164666%positive,86);(4939017961474039534%positive,87);(336059350346299169055486159786%positive,0);(78100807327327529657%positive,86);(21003718841542237111780092602%positive,86);(385577060411014670475534248634%positive,86);(392348783772546995466532220397%positive,87);(20212550238885268348829%positive,83);(385577060411086728069572176570%positive,86);(343943436692855797352527739578%positive,86);(1506016239212142597346926062%positive,87);(375634762144590629050462432749%positive,87);(336059350346227111461448231850%positive,0);(1312722105046901974069803706%positive,86);(375634762144590629050462428894%positive,87);(5268901551908107998174713%positive,85);(343943455582217301582536899258%positive,86);(385538343849580175616893902573%positive,87);(5268901551908110011064221%positive,83);(1469257035349676362558578170%positive,83);(385540157238309597560655961837%positive,87);(353227986987424091820233243322%positive,86);(19993806675795850210205%positive,84);(22979876032446211471838%positive,87);(22419085146921251285917%positive,84);(79024287383584632558%positive,87);(353227986987496149414271171258%positive,86);(1506009155662418292879105518%positive,87);(392348783772489222528383184606%positive,87);(323403252722872048131577%positive,85);(21003610348097831499621116842%positive,0);(375634762144607517411626053101%positive,87);(353228005876857653644280330938%positive,86);(20050542292601130%positive,1);(323403252722874061021085%positive,83);(385576951917642322457413200810%positive,0);(21003610348169889093659044778%positive,0);(20212550239055053778425%positive,85);(87574551355161127609%positive,86);(385576951917714380051451128746%positive,0);(1312721045512039240377543594%positive,0);(392348783772563883827695840749%positive,87);(5174454222250715093900793%positive,85);(5174454222250717106790301%positive,83)] [343943455582217301582536899258%positive;375634762144607517411626053101%positive;5174454222250717106790301%positive;343943436692783739758489811642%positive;353228005876857653644280330938%positive;392348783772563883827695902430%positive;385538343849580175616893902573%positive;5268901551908110011064221%positive;20050542292601130%positive;375634762144532856112313396958%positive;79024287383584960238%positive;1469257035349676362558578170%positive;385540157238309597560655961837%positive;323403252722874061021085%positive;308688622592127470%positive;375634762144590629050462428894%positive;385576951917642322457413200810%positive;336059458839599459479569279674%positive;353227986987424091820233243322%positive;19993806675795850210205%positive;78322430830738%positive;336059458839671517073607207610%positive;21003718841470179517742164666%positive;22979876032446211471838%positive;4939017961474039534%positive;336059350346299169055486159786%positive;392348783772546995466532216542%positive;78100807327327529657%positive;21003718841542237111780092602%positive;22419085146921251285917%positive;375634762144607517411626114782%positive;385577060411014670475534248634%positive;79024287383584632558%positive;21003610348169889093659044778%positive;392348783772546995466532220397%positive;20212550238885268348829%positive;385577060411086728069572176570%positive;343943436692855797352527739578%positive;20212550239055053778425%positive;87574551355161127609%positive;385576951917714380051451128746%positive;1312721045512039240377543594%positive;353227986987496149414271171258%positive;20050645371816234%positive;392348783772563883827695840749%positive;1506016239212142597346926062%positive;1506009155662418292879105518%positive;5174454222250715093900793%positive;375634762144590629050462432749%positive;336059350346227111461448231850%positive;392348783772489222528383184606%positive;1312722105046901974069803706%positive;5268901551908107998174713%positive;78322833483922%positive;323403252722872048131577%positive;21003610348097831499621116842%positive]]
  end.

Lemma cqh_h_00168 : iqh tmq_h_00168.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00168 StA 0 4 2 25 20000
                lsetq_h_00168 rsetq_h_00168 certq_h_00168 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00168); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00169 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => None
  | StC, S1 => Some (mkTrans S0 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StD)
  | StD, S1 => Some (mkTrans S1 DR StB)
  end.

Definition lsetq_h_00169 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)])]].

Definition rsetq_h_00169 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)])]].

Definition certq_h_00169 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(5121400252161856676293087%positive,0);(19315842251812639%positive,0);(336666231129655607476438428159%positive,0);(91865338864502422595960479%positive,0);(92221282669268254699%positive,1);(22514964547406143%positive,0);(396087353015353860671596390911%positive,0);(376280314747900420265453545951%positive,0);(376280314747971008911956765151%positive,0);(396087430838708343138374033406%positive,1);(1401753406032447798975%positive,0);(81942401319767723897912991%positive,0);(376280427989074121697149714079%positive,0);(82193904084370949397801471%positive,0);(81942401249170281318489598%positive,1);(1401753827888430836734%positive,1);(82193923084213352343707646%positive,1);(81942401319758927821708798%positive,1);(79152975685779%positive,2);(96701013919746499494275583%positive,0);(376280427989003524254570290686%positive,1);(376280427989074112901073509886%positive,1);(5121400181573210173073887%positive,0);(4934250293338501630%positive,1);(336666308953010089943216070654%positive,1);(96701032919588902440181758%positive,1);(360239385426826238%positive,3)]]
  | StC => [HMeas MRight 45 [(336666308953010081147139915421%positive,1);(82193923084213487265775593%positive,0);(5121400252161856676293087%positive,1);(19315842251812639%positive,1);(4715781263345%positive,0);(376280427989074112856781348841%positive,0);(1263168066298580172445%positive,1);(336666231129655607476438428159%positive,1);(396087430838637745695794658973%positive,1);(22428061246214901252073%positive,0);(92221282669268254699%positive,0);(22514964547406143%positive,1);(396087353015353860671596390911%positive,1);(336666308953010089898672259049%positive,0);(1401753406032447798975%positive,1);(81942401319767723897912991%positive,1);(376280427989074121697149714079%positive,1);(376280314747900420265453545951%positive,1);(96701032919589037362249705%positive,0);(376280314747971008911956765151%positive,1);(78948004690632056809%positive,0);(79152975685779%positive,1);(81942401249170237026328553%positive,0);(396087430838708343093830221801%positive,0);(396087430838708334342297878173%positive,1);(91865338864502422595960479%positive,1);(81942401319758883529547753%positive,0);(82193904084370949397801471%positive,1);(336666308952939492500636696221%positive,1);(376280427989003524210278129641%positive,0);(5121400181573210173073887%positive,1);(96701013919746499494275583%positive,1)] [336666308953010081147139915421%positive;82193923084213487265775593%positive;5121400252161856676293087%positive;19315842251812639%positive;4715781263345%positive;376280427989074112856781348841%positive;1263168066298580172445%positive;336666231129655607476438428159%positive;396087430838637745695794658973%positive;22428061246214901252073%positive;92221282669268254699%positive;22514964547406143%positive;396087353015353860671596390911%positive;336666308953010089898672259049%positive;1401753406032447798975%positive;81942401319767723897912991%positive;376280427989074121697149714079%positive;376280314747900420265453545951%positive;96701032919589037362249705%positive;376280314747971008911956765151%positive;78948004690632056809%positive;79152975685779%positive;5121400181573210173073887%positive;81942401249170237026328553%positive;396087430838708343093830221801%positive;396087430838708334342297878173%positive;91865338864502422595960479%positive;81942401319758883529547753%positive;82193904084370949397801471%positive;336666308952939492500636696221%positive;376280427989003524210278129641%positive;96701013919746499494275583%positive]]
  | StD => [HRank [(336666308953010081147139915421%positive,0);(1401753827888430836734%positive,0);(82193923084213487265775593%positive,1);(4934250293338501630%positive,0);(4715781263345%positive,1);(396087430838708343138374033406%positive,0);(376280427989074112856781348841%positive,1);(1263168066298580172445%positive,0);(396087430838637745695794658973%positive,0);(360239385426826238%positive,0);(22428061246214901252073%positive,1);(376280427989003524254570290686%positive,0);(376280427989074112901073509886%positive,0);(336666308953010089898672259049%positive,1);(81942401249170281318489598%positive,0);(96701032919589037362249705%positive,1);(82193923084213352343707646%positive,0);(81942401319758927821708798%positive,0);(78948004690632056809%positive,1);(81942401249170237026328553%positive,1);(396087430838708343093830221801%positive,1);(396087430838708334342297878173%positive,0);(336666308953010089943216070654%positive,0);(81942401319758883529547753%positive,1);(336666308952939492500636696221%positive,0);(96701032919588902440181758%positive,0);(376280427989003524210278129641%positive,1)]]
  end.

Lemma cqh_h_00169 : iqh tmq_h_00169.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00169 StA 0 4 2 25 20000
                lsetq_h_00169 rsetq_h_00169 certq_h_00169 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00169); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00170 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => None
  end.

Definition lsetq_h_00170 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition rsetq_h_00170 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition certq_h_00170 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 35 [(5307768541866%positive,1);(347849918707528158%positive,2);(323514226923467755%positive,2);(1263727430424254%positive,2);(19087146765119966%positive,2);(323511134547014635%positive,2);(1263715350828734%positive,2);(19087145909481950%positive,2);(341516731731538398%positive,2);(341516732587176414%positive,2);(1263727430423531%positive,0);(1263715350828011%positive,0);(18416111347%positive,2);(5211131777706%positive,1);(323514226923468478%positive,2);(347849919563166174%positive,2);(323511134547015358%positive,2);(75289427112939%positive,2);(4705589194558%positive,2)] [5307768541866%positive;347849918707528158%positive;323514226923467755%positive;19087146765119966%positive;1263727430424254%positive;323511134547014635%positive;1263715350828734%positive;19087145909481950%positive;341516731731538398%positive;341516732587176414%positive;1263727430423531%positive;1263715350828011%positive;18416111347%positive;5211131777706%positive;323514226923468478%positive;347849919563166174%positive;323511134547015358%positive;75289427112939%positive;4705589194558%positive]]
  | StC => [HMeas MRight 35 [(341516732587177449%positive,1);(19087145909482985%positive,0);(323514226923467755%positive,1);(1149729265%positive,0);(347849919563167389%positive,2);(323511134547014635%positive,1);(294330785565%positive,2);(347849918707529373%positive,2);(341516731731539433%positive,0);(347849919563167209%positive,1);(1263727430423531%positive,2);(19087145909483165%positive,2);(19087146765121181%positive,2);(1263715350828011%positive,2);(18416111347%positive,1);(347849918707529193%positive,0);(19087146765121001%positive,1);(75289427112939%positive,1);(341516731731539613%positive,2);(341516732587177629%positive,2)] [341516732587177449%positive;19087145909482985%positive;323514226923467755%positive;1149729265%positive;347849918707529373%positive;347849919563167389%positive;323511134547014635%positive;294330785565%positive;341516731731539433%positive;347849919563167209%positive;1263727430423531%positive;19087145909483165%positive;19087146765121181%positive;1263715350828011%positive;18416111347%positive;347849918707529193%positive;19087146765121001%positive;75289427112939%positive;341516731731539613%positive;341516732587177629%positive]]
  | StD => [HMeas MLeft 35 [(5307768541866%positive,0);(341516732587177449%positive,1);(347849918707528158%positive,1);(19087145909482985%positive,1);(1149729265%positive,1);(1263727430424254%positive,1);(19087146765119966%positive,1);(347849919563167389%positive,1);(294330785565%positive,1);(347849918707529373%positive,1);(1263715350828734%positive,1);(341516731731539433%positive,1);(347849919563167209%positive,1);(19087145909481950%positive,1);(341516731731538398%positive,1);(341516732587176414%positive,1);(19087145909483165%positive,1);(19087146765121181%positive,1);(347849918707529193%positive,1);(5211131777706%positive,0);(19087146765121001%positive,1);(323514226923468478%positive,1);(347849919563166174%positive,1);(323511134547015358%positive,1);(4705589194558%positive,1);(341516731731539613%positive,1);(341516732587177629%positive,1)] [5307768541866%positive;341516732587177449%positive;347849918707528158%positive;19087145909482985%positive;1149729265%positive;1263727430424254%positive;19087146765119966%positive;347849919563167389%positive;294330785565%positive;347849918707529373%positive;1263715350828734%positive;341516731731539433%positive;347849919563167209%positive;19087145909481950%positive;341516731731538398%positive;341516732587176414%positive;19087145909483165%positive;19087146765121181%positive;347849918707529193%positive;5211131777706%positive;19087146765121001%positive;323514226923468478%positive;347849919563166174%positive;323511134547015358%positive;4705589194558%positive;341516731731539613%positive;341516732587177629%positive]]
  end.

Lemma cqh_h_00170 : iqh tmq_h_00170.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00170 StA 0 2 2 25 20000
                lsetq_h_00170 rsetq_h_00170 certq_h_00170 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00170); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00171 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S0 DR StD)
  | StD, S1 => Some (mkTrans S1 DR StB)
  end.

Definition lsetq_h_00171 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StC,S1)]);(S1,[(StD,S1);(StC,S0)])];
   [(S1,[(StB,S1);(StC,S1)]);(S1,[(StD,S1);(StC,S1)])];
   [(S1,[(StD,S1);(StC,S0)]);(S0,[(StD,S0)])];
   [(S1,[(StD,S1);(StC,S1)]);(S1,[(StB,S1);(StC,S1)])]].

Definition rsetq_h_00171 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StC,S1);(StB,S1)]);(S1,[(StC,S1);(StD,S1)])];
   [(S1,[(StC,S1);(StD,S1)]);(S1,[(StB,S0)])];
   [(S1,[(StC,S1);(StD,S1)]);(S1,[(StC,S1);(StB,S1)])]].

Definition certq_h_00171 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 26 [(294674722591%positive,3);(325846796602%positive,2);(359680738044868350%positive,3);(75285403202046%positive,3);(19104808023029231%positive,3);(4664259629999%positive,0);(341675131333441007%positive,3);(359680733749901054%positive,3);(21354695752152798%positive,3);(294406287135%positive,3);(75289698169342%positive,3);(83416779969455%positive,0);(19104812317996527%positive,3);(341675135628408303%positive,3);(87812678996734%positive,3);(21438052499%positive,1);(19104812183844574%positive,3);(341675135494256350%positive,3);(1194050545252062%positive,3)] [294674722591%positive;325846796602%positive;359680738044868350%positive;75285403202046%positive;19104808023029231%positive;4664259629999%positive;341675131333441007%positive;359680733749901054%positive;21354695752152798%positive;294406287135%positive;75289698169342%positive;83416779969455%positive;19104812317996527%positive;341675135628408303%positive;87812678996734%positive;21438052499%positive;19104812183844574%positive;341675135494256350%positive;1194050545252062%positive]]
  | StC => [HMeas MRight 26 [(294674722591%positive,1);(359680737910716397%positive,1);(19104808023029231%positive,1);(4664259629999%positive,1);(341675131333441007%positive,1);(22480045903181805%positive,1);(294406287135%positive,1);(83416779969455%positive,1);(19104812317996527%positive,1);(75289564018669%positive,1);(341675135628408303%positive,1);(21438052499%positive,1);(18416635889%positive,0);(4705381513197%positive,1)] [22480045903181805%positive;19104808023029231%positive;294674722591%positive;4705381513197%positive;294406287135%positive;4664259629999%positive;341675131333441007%positive;21438052499%positive;359680737910716397%positive;83416779969455%positive;19104812317996527%positive;75289564018669%positive;18416635889%positive;341675135628408303%positive]]
  | StD => [HMeas MLeft 26 [(325846796602%positive,0);(359680738044868350%positive,1);(359680737910716397%positive,1);(75285403202046%positive,1);(359680733749901054%positive,1);(21354695752152798%positive,1);(22480045903181805%positive,1);(75289698169342%positive,1);(75289564018669%positive,1);(87812678996734%positive,1);(19104812183844574%positive,1);(18416635889%positive,1);(341675135494256350%positive,1);(4705381513197%positive,1);(1194050545252062%positive,1)] [22480045903181805%positive;325846796602%positive;4705381513197%positive;87812678996734%positive;359680733749901054%positive;21354695752152798%positive;359680738044868350%positive;75289698169342%positive;359680737910716397%positive;19104812183844574%positive;75289564018669%positive;341675135494256350%positive;18416635889%positive;75285403202046%positive;1194050545252062%positive]]
  end.

Lemma cqh_h_00171 : iqh tmq_h_00171.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00171 StA 0 2 2 25 20000
                lsetq_h_00171 rsetq_h_00171 certq_h_00171 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00171); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00172 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DR StB)
  end.

Definition lsetq_h_00172 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StC,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StC,S0);(StC,S1);(StD,S1);(StD,S0)])]].

Definition rsetq_h_00172 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StC,S0)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)])]].

Definition certq_h_00172 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(22514964480297279%positive,0);(1401753827888430836478%positive,1);(91865338864502422587506335%positive,0);(92221278271221743594%positive,1);(76953952430227%positive,2);(360239368246957054%positive,3);(5121400252161856676293087%positive,0);(1401753406032447798959%positive,0);(82193923084213352335319038%positive,1);(19315842251812639%positive,0);(336666231129655607476438428159%positive,0);(376280314747900415867407034847%positive,0);(376280314747971008911956765151%positive,0);(396087430838708343138374033406%positive,1);(396087353015353860671596390911%positive,0);(82193904084370949389412863%positive,0);(81942401319767723897912991%positive,0);(376280427989074121697149714079%positive,0);(96701032919588902431793150%positive,1);(96701013919746499485886975%positive,0);(81942401249165883271978494%positive,1);(81942401319758927821708798%positive,1);(376280427989074112901073509886%positive,1);(5121400181568812126562783%positive,0);(4934250293338501630%positive,1);(376280427989003519856523779582%positive,1);(336666308953010089943216070654%positive,1)]]
  | StC => [HMeas MRight 45 [(336666308953010081147139915421%positive,1);(82193923084213487131557865%positive,0);(5121400252161856676293087%positive,1);(19315842251812639%positive,1);(4715781263345%positive,0);(376280427989074112856781348841%positive,0);(1263168066298580172445%positive,1);(336666231129655607476438428159%positive,1);(1401753406032447798959%positive,1);(396087353015353860671596390911%positive,1);(82193904084370949389412863%positive,1);(336666308953010089898672259049%positive,0);(376280314747900415867407034847%positive,1);(22428061246214901247977%positive,0);(81942401319767723897912991%positive,1);(376280427989074121697149714079%positive,1);(22514964480297279%positive,1);(76953952430227%positive,1);(96701032919589037228031977%positive,0);(96701013919746499485886975%positive,1);(396087430838637741297748147869%positive,1);(376280314747971008911956765151%positive,1);(81942401249165838979817449%positive,0);(78948004690632056809%positive,0);(91865338864502422587506335%positive,1);(396087430838708343093830221801%positive,0);(396087430838708334342297878173%positive,1);(81942401319758883529547753%positive,0);(336666308952939488102590185117%positive,1);(376280427989003519812231618537%positive,0);(5121400181568812126562783%positive,1)] [336666308953010081147139915421%positive;82193923084213487131557865%positive;5121400252161856676293087%positive;19315842251812639%positive;4715781263345%positive;376280427989074112856781348841%positive;1263168066298580172445%positive;336666231129655607476438428159%positive;1401753406032447798959%positive;396087353015353860671596390911%positive;82193904084370949389412863%positive;336666308953010089898672259049%positive;376280314747900415867407034847%positive;22428061246214901247977%positive;81942401319767723897912991%positive;376280427989074121697149714079%positive;22514964480297279%positive;96701032919589037228031977%positive;76953952430227%positive;96701013919746499485886975%positive;396087430838637741297748147869%positive;376280314747971008911956765151%positive;81942401249165838979817449%positive;78948004690632056809%positive;91865338864502422587506335%positive;396087430838708343093830221801%positive;396087430838708334342297878173%positive;81942401319758883529547753%positive;336666308952939488102590185117%positive;376280427989003519812231618537%positive;5121400181568812126562783%positive]]
  | StD => [HRank [(1401753827888430836478%positive,0);(336666308953010081147139915421%positive,0);(82193923084213487131557865%positive,1);(360239368246957054%positive,0);(82193923084213352335319038%positive,0);(4934250293338501630%positive,0);(4715781263345%positive,1);(396087430838708343138374033406%positive,0);(376280427989074112856781348841%positive,1);(1263168066298580172445%positive,0);(376280427989003519856523779582%positive,0);(376280427989074112901073509886%positive,0);(336666308953010089898672259049%positive,1);(22428061246214901247977%positive,1);(96701032919589037228031977%positive,1);(96701032919588902431793150%positive,0);(396087430838637741297748147869%positive,0);(81942401249165883271978494%positive,0);(81942401249165838979817449%positive,1);(81942401319758927821708798%positive,0);(78948004690632056809%positive,1);(396087430838708343093830221801%positive,1);(92221278271221743594%positive,0);(396087430838708334342297878173%positive,0);(336666308953010089943216070654%positive,0);(81942401319758883529547753%positive,1);(336666308952939488102590185117%positive,0);(376280427989003519812231618537%positive,1)]]
  end.

Lemma cqh_h_00172 : iqh tmq_h_00172.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00172 StA 0 4 2 25 20000
                lsetq_h_00172 rsetq_h_00172 certq_h_00172 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00172); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00173 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StB)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StC)
  end.

Definition lsetq_h_00173 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StB,S0);(StD,S1)]);(S0,[(StC,S1);(StC,S0)])];
   [(S1,[(StD,S0)]);(S0,[])]].

Definition rsetq_h_00173 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StC,S1)])];
   [(S0,[(StD,S1);(StD,S0)]);(S1,[(StC,S0);(StC,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition certq_h_00173 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 22 [(348404348570367662%positive,25);(4795306472170%positive,24);(5316362673966%positive,0);(19128940636886943%positive,25);(291884468543%positive,25);(1207220371%positive,23);(19641575772320490%positive,24);(306063054185387935%positive,25);(1150003442%positive,25);(20767041682%positive,24);(348404348570366698%positive,24);(85059655299818%positive,24);(19641575772321454%positive,25);(294401068846%positive,25);(4722827818271%positive,25);(295161132319%positive,25)] [348404348570367662%positive;19641575772320490%positive;306063054185387935%positive;1150003442%positive;85059655299818%positive;4795306472170%positive;19641575772321454%positive;20767041682%positive;5316362673966%positive;4722827818271%positive;294401068846%positive;348404348570366698%positive;19128940636886943%positive;295161132319%positive;291884468543%positive;1207220371%positive]]
  | StC => [HRank [(18419783505%positive,0);(19128940636886009%positive,0);(19128940636886943%positive,0);(291884468543%positive,0);(75565245092345%positive,0);(1207220371%positive,0);(306063054185387935%positive,0);(306063054185386489%positive,0);(4722827818271%positive,0);(295161132319%positive,0)]]
  | StD => [HMeas MRight 22 [(348404348570367662%positive,2);(4795306472170%positive,2);(18419783505%positive,1);(5316362673966%positive,2);(19128940636886009%positive,1);(75565245092345%positive,1);(19641575772320490%positive,2);(1150003442%positive,0);(20767041682%positive,2);(348404348570366698%positive,2);(85059655299818%positive,2);(19641575772321454%positive,2);(294401068846%positive,2);(306063054185386489%positive,1)] [348404348570367662%positive;19641575772320490%positive;1150003442%positive;85059655299818%positive;19641575772321454%positive;4795306472170%positive;18419783505%positive;5316362673966%positive;20767041682%positive;306063054185386489%positive;294401068846%positive;19128940636886009%positive;348404348570366698%positive;75565245092345%positive]]
  end.

Lemma cqh_h_00173 : iqh tmq_h_00173.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00173 StA 0 2 2 25 20000
                lsetq_h_00173 rsetq_h_00173 certq_h_00173 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00173); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00174 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S0 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00174 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition rsetq_h_00174 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition certq_h_00174 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 37 [(357411547841885946%positive,4);(351078360865895151%positive,4);(1396138856798126%positive,0);(306064359855454111%positive,4);(4670218605499%positive,1);(306064355677927327%positive,4);(76724903465711%positive,4);(357411547841884911%positive,4);(1150007538%positive,4);(351078360865896366%positive,4);(76724903466926%positive,0);(19641575789098746%positive,4);(4722827818783%positive,4);(294402117422%positive,4);(4722566723359%positive,4);(357411547841886126%positive,4);(19641575789097711%positive,4);(19641575789098926%positive,4);(1371399845172986%positive,2);(306067452231907231%positive,4);(306067448054380447%positive,4);(1396138856797946%positive,2);(1371399845171951%positive,4);(4670171419579%positive,3);(351078360865896186%positive,4);(1396138856796911%positive,4);(1371399845173166%positive,0);(76724903466746%positive,2)] [357411547841885946%positive;351078360865895151%positive;1396138856798126%positive;306064359855454111%positive;4670218605499%positive;306064355677927327%positive;76724903465711%positive;357411547841884911%positive;1150007538%positive;351078360865896366%positive;76724903466926%positive;19641575789098746%positive;4722827818783%positive;294402117422%positive;4722566723359%positive;357411547841886126%positive;19641575789097711%positive;19641575789098926%positive;1371399845172986%positive;306067452231907231%positive;306067448054380447%positive;1396138856797946%positive;1371399845171951%positive;4670171419579%positive;351078360865896186%positive;1396138856796911%positive;1371399845173166%positive;76724903466746%positive]]
  | StC => [HMeas MLeft 37 [(351078360865895151%positive,1);(306064359855454111%positive,1);(4670218605499%positive,1);(306064355677927327%positive,1);(76724903465711%positive,1);(357411547841884911%positive,1);(4722827818783%positive,1);(4722566723359%positive,1);(306067448054379001%positive,1);(18419783537%positive,1);(19641575789097711%positive,1);(306067452231905785%positive,1);(306067452231907231%positive,1);(306067448054380447%positive,1);(75561067573753%positive,1);(75565245100537%positive,1);(1371399845171951%positive,1);(4670171419579%positive,0);(306064355677925881%positive,1);(306064359855452665%positive,1);(1396138856796911%positive,1)] [351078360865895151%positive;306064359855454111%positive;4670218605499%positive;306064355677927327%positive;76724903465711%positive;357411547841884911%positive;4722827818783%positive;4722566723359%positive;306067448054379001%positive;18419783537%positive;19641575789097711%positive;306067452231905785%positive;306067452231907231%positive;306067448054380447%positive;75561067573753%positive;75565245100537%positive;1371399845171951%positive;4670171419579%positive;306064355677925881%positive;1396138856796911%positive;306064359855452665%positive]]
  | StD => [HMeas MRight 37 [(357411547841885946%positive,0);(1396138856798126%positive,2);(1150007538%positive,0);(351078360865896366%positive,2);(76724903466926%positive,2);(19641575789098746%positive,0);(294402117422%positive,2);(357411547841886126%positive,2);(306067448054379001%positive,1);(18419783537%positive,1);(306067452231905785%positive,1);(19641575789098926%positive,2);(1371399845172986%positive,2);(75561067573753%positive,1);(75565245100537%positive,1);(1396138856797946%positive,2);(306064355677925881%positive,1);(351078360865896186%positive,0);(306064359855452665%positive,1);(1371399845173166%positive,2);(76724903466746%positive,2)] [357411547841885946%positive;1396138856798126%positive;1150007538%positive;351078360865896366%positive;76724903466926%positive;19641575789098746%positive;294402117422%positive;357411547841886126%positive;306067448054379001%positive;18419783537%positive;306067452231905785%positive;19641575789098926%positive;1371399845172986%positive;75561067573753%positive;75565245100537%positive;1396138856797946%positive;306064355677925881%positive;351078360865896186%positive;306064359855452665%positive;1371399845173166%positive;76724903466746%positive]]
  end.

Lemma cqh_h_00174 : iqh tmq_h_00174.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00174 StA 0 2 2 25 20000
                lsetq_h_00174 rsetq_h_00174 certq_h_00174 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00174); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00175 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StC)
  | StC, S0 => Some (mkTrans S1 DL StB)
  | StC, S1 => Some (mkTrans S0 DR StB)
  | StD, S0 => None
  | StD, S1 => None
  end.

Definition lsetq_h_00175 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StB,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StB,S1)]);(S0,[(StC,S1);(StC,S0)])]].

Definition rsetq_h_00175 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StB,S1);(StB,S0)]);(S1,[(StC,S0);(StC,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StC,S1)]);(S0,[(StB,S1);(StB,S0)])]].

Definition certq_h_00175 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(348403798813504234%positive,0);(20766484626%positive,0);(19641026015458990%positive,0);(1150003442%positive,0);(5316220063534%positive,0);(85059521016554%positive,0);(348403798813505198%positive,0);(299698261806%positive,0);(19641026015458026%positive,0);(4795172188906%positive,0);(294401003310%positive,0)]]
  | StC => [HRank [(19058571758490073%positive,0);(290810726685%positive,0);(4722443899353%positive,0);(19058571758491037%positive,0);(75563097608665%positive,0);(304937152131060185%positive,0);(4722693600541%positive,0);(18411394897%positive,0);(304937152131061149%positive,0);(1135917201%positive,0);(295152743709%positive,0)]]
  | StD => []
  end.

Lemma cqh_h_00175 : iqh tmq_h_00175.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00175 StA 0 2 2 25 20000
                lsetq_h_00175 rsetq_h_00175 certq_h_00175 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00175); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00176 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StC)
  | StC, S0 => Some (mkTrans S1 DL StB)
  | StC, S1 => Some (mkTrans S0 DR StD)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => None
  end.

Definition lsetq_h_00176 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StB,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1)]);(S0,[(StC,S1);(StC,S0)])]].

Definition rsetq_h_00176 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StB,S0)]);(S1,[(StC,S0);(StC,S1)])];
   [(S0,[(StB,S1);(StD,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StB,S1);(StD,S0)]);(S1,[(StC,S0);(StC,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StC,S1)]);(S0,[(StB,S1);(StD,S0)])]].

Definition certq_h_00176 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 22 [(18411919187%positive,1);(20766484626%positive,2);(322951550774760411%positive,1);(348412594906592942%positive,2);(294401007406%positive,2);(5316220063534%positive,2);(1150003698%positive,0);(19649822108545770%positive,2);(4797319672554%positive,2);(348412594906591978%positive,2);(85061668500202%positive,2);(20184471665332699%positive,1);(75563231826907%positive,1);(19649822108546734%positive,2)] [18411919187%positive;294401007406%positive;5316220063534%positive;19649822108546734%positive;348412594906591978%positive;20766484626%positive;322951550774760411%positive;348412594906592942%positive;1150003698%positive;85061668500202%positive;19649822108545770%positive;75563231826907%positive;20184471665332699%positive;4797319672554%positive]]
  | StC => [HRank [(18411919187%positive,0);(322951550774760411%positive,0);(20184471665333693%positive,0);(4722701989181%positive,0);(307990595869%positive,0);(322951550774760893%positive,0);(20184471665332699%positive,0);(1135917201%positive,0);(295152743741%positive,0);(75563231826907%positive,0)]]
  | StD => [HMeas MLeft 22 [(20766484626%positive,24);(348412594906592942%positive,25);(20184471665333693%positive,25);(294401007406%positive,25);(5316220063534%positive,0);(4722701989181%positive,25);(1150003698%positive,25);(307990595869%positive,25);(19649822108545770%positive,24);(4797319672554%positive,24);(348412594906591978%positive,24);(85061668500202%positive,24);(322951550774760893%positive,25);(1135917201%positive,23);(295152743741%positive,25);(19649822108546734%positive,25)] [294401007406%positive;5316220063534%positive;19649822108546734%positive;348412594906591978%positive;4722701989181%positive;20766484626%positive;1135917201%positive;295152743741%positive;348412594906592942%positive;1150003698%positive;307990595869%positive;85061668500202%positive;19649822108545770%positive;322951550774760893%positive;20184471665333693%positive;4797319672554%positive]]
  end.

Lemma cqh_h_00176 : iqh tmq_h_00176.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00176 StA 0 2 2 25 20000
                lsetq_h_00176 rsetq_h_00176 certq_h_00176 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00176); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00177 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S0 DR StC)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DL StB)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Definition lsetq_h_00177 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StD,S1);(StB,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StC,S0)]);(S1,[(StD,S1);(StB,S0)])];
   [(S1,[(StD,S1);(StC,S0)]);(S1,[(StD,S1);(StD,S0)])];
   [(S1,[(StD,S1);(StD,S0)]);(S1,[(StD,S1);(StC,S0)])]].

Definition rsetq_h_00177 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0);(StC,S1)]);(S1,[(StD,S0)])];
   [(S1,[(StC,S0);(StC,S1)]);(S1,[(StD,S0);(StB,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1)]);(S1,[(StC,S0);(StC,S1)])]].

Definition certq_h_00177 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 31 [(348420908974528490%positive,64);(79004724885467%positive,32);(348420910046246575%positive,64);(339980784986748351%positive,64);(348420911119463422%positive,0);(5316481159678%positive,0);(20225209295959487%positive,64);(324230940959%positive,32);(18400387059%positive,63);(339980783913531355%positive,32);(1361019176744623%positive,62);(75836233275370%positive,64);(1328049934039003%positive,32);(20225211443443135%positive,64);(75834083243006%positive,31);(294473269055%positive,64);(75834085791722%positive,64);(20225210370226139%positive,32);(348420911122012138%positive,64);(75835157509807%positive,64);(339980782839264703%positive,64);(348420908971979774%positive,0);(85063698544618%positive,64);(75836230726654%positive,31)] [348420908974528490%positive;79004724885467%positive;348420910046246575%positive;339980784986748351%positive;5316481159678%positive;348420911119463422%positive;20225209295959487%positive;324230940959%positive;18400387059%positive;339980783913531355%positive;1361019176744623%positive;75836233275370%positive;1328049934039003%positive;20225211443443135%positive;75834083243006%positive;75834085791722%positive;20225210370226139%positive;348420911122012138%positive;75835157509807%positive;75836230726654%positive;339980782839264703%positive;348420908971979774%positive;85063698544618%positive;294473269055%positive]]
  | StC => [HMeas MRight 31 [(79004724885467%positive,1);(348420910046246575%positive,1);(1328071140438781%positive,1);(339980784986748351%positive,1);(20230639208887037%positive,1);(20225209295959487%positive,1);(324230940959%positive,1);(18400387059%positive,0);(20264757393%positive,1);(339980783913531355%positive,1);(1361019176744623%positive,1);(79025931285245%positive,1);(1328049934039003%positive,1);(20225211443443135%positive,1);(294473269055%positive,1);(20225210370226139%positive,1);(75835157509807%positive,1);(339986212752192253%positive,1);(339980782839264703%positive,1)] [79004724885467%positive;348420910046246575%positive;1328071140438781%positive;339980784986748351%positive;20230639208887037%positive;20225209295959487%positive;324230940959%positive;18400387059%positive;20264757393%positive;339980783913531355%positive;1361019176744623%positive;79025931285245%positive;1328049934039003%positive;20225211443443135%positive;20225210370226139%positive;75835157509807%positive;339986212752192253%positive;339980782839264703%positive;294473269055%positive]]
  | StD => [HRank [(348420908974528490%positive,0);(1328071140438781%positive,1);(75836233275370%positive,0);(20230639208887037%positive,1);(348420911122012138%positive,0);(339986212752192253%positive,1);(348420911119463422%positive,2);(85063698544618%positive,0);(20264757393%positive,1);(5316481159678%positive,2);(75834085791722%positive,0);(79025931285245%positive,1);(75834083243006%positive,2);(348420908971979774%positive,2);(75836230726654%positive,2)]]
  end.

Lemma cqh_h_00177 : iqh tmq_h_00177.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00177 StA 0 2 2 25 20000
                lsetq_h_00177 rsetq_h_00177 certq_h_00177 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00177); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00178 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StC)
  | StC, S1 => Some (mkTrans S0 DR StB)
  | StD, S0 => Some (mkTrans S0 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Definition lsetq_h_00178 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StC,S0)]);(S0,[(StC,S1);(StB,S0)])];
   [(S0,[(StB,S1);(StC,S0)]);(S0,[(StC,S1);(StD,S1);(StC,S0);(StD,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[])];
   [(S0,[(StC,S1);(StB,S0)]);(S0,[(StC,S1);(StD,S1);(StC,S0)])];
   [(S0,[(StC,S1);(StB,S0);(StB,S1);(StC,S0)]);(S0,[(StC,S1);(StD,S1);(StC,S0);(StB,S1)])];
   [(S0,[(StC,S1);(StB,S0);(StB,S1);(StC,S0)]);(S0,[(StC,S1);(StD,S1);(StC,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StD,S1);(StC,S0)]);(S1,[(StB,S0);(StB,S1);(StC,S0);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S1);(StC,S0);(StB,S1)]);(S1,[(StB,S0);(StB,S1);(StC,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StD,S1);(StC,S0);(StC,S1)]);(S1,[(StB,S0);(StB,S1);(StC,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StD,S1);(StC,S0);(StD,S0)]);(S1,[(StB,S0);(StB,S1);(StC,S0);(StB,S1)])];
   [(S1,[(StB,S0);(StB,S1);(StC,S0);(StB,S1)]);(S0,[(StC,S1);(StD,S1);(StC,S0);(StC,S1)])];
   [(S1,[(StB,S0);(StB,S1);(StC,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0);(StB,S1);(StC,S0);(StC,S1)]);(S0,[(StC,S1);(StB,S0);(StB,S1);(StC,S0)])];
   [(S1,[(StB,S0);(StB,S1);(StC,S0);(StD,S0)]);(S0,[(StC,S1);(StD,S1);(StC,S0);(StB,S1)])]].

Definition rsetq_h_00178 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S1);(StC,S0)]);(S1,[(StC,S0);(StD,S0)])];
   [(S1,[(StC,S0);(StC,S1);(StB,S0)]);(S1,[(StC,S0);(StB,S1);(StC,S0)])];
   [(S1,[(StC,S0);(StD,S0)]);(S1,[(StC,S0)])]].

Definition certq_h_00178 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(19343619611161886%positive,0);(4952178358031405999%positive,0);(20993960123068977697036414366%positive,0);(84274313153160050205732842%positive,1);(20603539159868790091183%positive,0);(21574244516483999735255248286%positive,0);(86271561595546834700578794%positive,1);(1287721396421231858394%positive,2);(329656626557858062981886%positive,0);(21062392954429179384298%positive,2);(314385060445770458%positive,3);(4722445086010%positive,4);(1208976379833658%positive,3);(86271561526444762277735166%positive,0);(18400389362%positive,1);(79234853734565493502%positive,0);(1149987282%positive,5);(18395862739%positive,6);(4711243224787%positive,6);(1206628021792047%positive,0);(308896773578748670%positive,0);(5391972595402800303513263%positive,0)]]
  | StC => [HRank [(5274513970327011487570649%positive,0);(4952178358031405999%positive,1);(1380344992368678975332412121%positive,0);(1380344992350664576822930137%positive,0);(20603539159868790091183%positive,1);(21574224174337133948454824665%positive,0);(21574224174319119549945342681%positive,0);(5391972595402800303513263%positive,1);(1348389010450560774877413037%positive,2);(18395862739%positive,0);(4710499677485%positive,1);(20603543468646059027885%positive,2);(1268185145258632624857%positive,0);(86271561595546737566744237%positive,2);(4711243224787%positive,0);(19306008888735021%positive,1);(1206628021792047%positive,1);(4952177727051355053%positive,2);(75379737460561%positive,0)]]
  | StD => [HRank [(4710499677485%positive,0);(19343619611161886%positive,1);(4952177727051355053%positive,0);(329656626557858062981886%positive,1);(1380344992368678975332412121%positive,2);(1348389010450560774877413037%positive,0);(20993960123068977697036414366%positive,1);(84274313153160050205732842%positive,2);(86271561595546737566744237%positive,0);(21574244516483999735255248286%positive,1);(86271561595546834700578794%positive,2);(1287721396421231858394%positive,3);(20603543468646059027885%positive,0);(86271561526444762277735166%positive,1);(21574224174319119549945342681%positive,2);(21062392954429179384298%positive,3);(314385060445770458%positive,4);(4722445086010%positive,5);(18400389362%positive,2);(75379737460561%positive,3);(308896773578748670%positive,4);(1268185145258632624857%positive,5);(1208976379833658%positive,4);(19306008888735021%positive,0);(79234853734565493502%positive,1);(1149987282%positive,6);(5274513970327011487570649%positive,2);(21574224174337133948454824665%positive,2);(1380344992350664576822930137%positive,2)]]
  end.

Lemma cqh_h_00178 : iqh tmq_h_00178.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00178 StA 0 4 2 25 20000
                lsetq_h_00178 rsetq_h_00178 certq_h_00178 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00178); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00179 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StC)
  | StC, S1 => Some (mkTrans S0 DR StB)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00179 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StD,S0)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StB,S0)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StD,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StD,S1);(StD,S1)])];
   [(S0,[(StC,S1);(StD,S1)]);(S0,[(StB,S1);(StD,S0)])];
   [(S1,[(StD,S1);(StD,S0)]);(S0,[(StB,S1);(StD,S0)])];
   [(S1,[(StD,S1);(StD,S1)]);(S0,[])];
   [(S1,[(StD,S1);(StD,S1)]);(S0,[(StB,S1);(StD,S0)])]].

Definition rsetq_h_00179 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StB,S1)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StD,S0);(StB,S1)])]].

Definition certq_h_00179 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(348983860924511934%positive,0);(1328051010926270%positive,0);(339981059716282046%positive,0);(78988621903550%positive,0);(1363218203145918%positive,0);(5187699251199%positive,1);(1363218203145195%positive,2);(20221088126465726%positive,0);(339981059781220351%positive,1);(348983860924511211%positive,2);(339981064160105435%positive,3);(20221088124368574%positive,0);(339981059781219327%positive,1);(348983860922414059%positive,2);(339981059865138139%positive,3);(78988621902827%positive,2);(20221088124367851%positive,2);(4722853016862%positive,0);(4722584581406%positive,0);(1150265586%positive,1);(20221088191404011%positive,4);(75836082311899%positive,5);(18421028563%positive,6);(294463864638%positive,0);(75836147291583%positive,1);(20221088126465003%positive,2);(5325138204671%positive,1);(1328051010925547%positive,2);(75840526177243%positive,3);(75836231209947%positive,3);(18404253395%positive,4);(75561269384190%positive,0);(18403991538%positive,1);(294468054335%positive,2);(348988259035960319%positive,1);(339981059714184171%positive,2);(339981059714184638%positive,0);(348983860989449919%positive,1);(348988259035961343%positive,1);(339981059716281323%positive,2);(75836080256446%positive,0);(20221088191403711%positive,1);(20221092570288619%positive,3);(20221088275321323%positive,3);(75836146275035%positive,4);(18395862739%positive,5);(348983860922414782%positive,0);(339981059781219775%positive,1)]]
  | StC => [HRank [(5187699251199%positive,0);(1363218203145195%positive,1);(339981059781220351%positive,0);(348983860924511211%positive,1);(339981064160105435%positive,2);(339981059781219327%positive,0);(348983860922414059%positive,1);(339981059865138139%positive,2);(78988621902827%positive,1);(20221088124367851%positive,1);(20221088191404011%positive,3);(75836082311899%positive,4);(18421028563%positive,5);(294463993133%positive,6);(75836147291583%positive,0);(20221088126465003%positive,1);(5325138204671%positive,0);(1328051010925547%positive,1);(75840526177243%positive,2);(75836231209947%positive,2);(18404253395%positive,3);(294468054335%positive,0);(348988259035960319%positive,0);(339981059714184171%positive,1);(20221088191403711%positive,0);(348983860989449919%positive,0);(339981064160105917%positive,1);(339981059865138621%positive,1);(348988259035961343%positive,0);(339981059716281323%positive,1);(20221092570288619%positive,2);(20221088275321323%positive,2);(75836146275035%positive,3);(18395862739%positive,4);(294467990829%positive,5);(18404581201%positive,0);(339981059781219775%positive,0);(348983865368336061%positive,1);(20221092570289853%positive,1);(75840526177725%positive,1);(75836231210429%positive,1);(20221088275322557%positive,1);(294473299261%positive,4);(348983861073368765%positive,1)]]
  | StD => [HRank [(339981064160105917%positive,0);(348983860924511934%positive,1);(20221092570289853%positive,0);(348983865368336061%positive,0);(1328051010926270%positive,1);(339981059716282046%positive,1);(75836231210429%positive,0);(20221088124368574%positive,1);(294463993133%positive,0);(294467990829%positive,0);(4722853016862%positive,1);(4722584581406%positive,1);(1150265586%positive,2);(339981059865138621%positive,0);(20221088275322557%positive,0);(348983861073368765%positive,0);(339981059714184638%positive,1);(18404581201%positive,3);(75561269384190%positive,1);(18403991538%positive,2);(75840526177725%positive,0);(294473299261%positive,0);(75836080256446%positive,1);(78988621903550%positive,1);(294463864638%positive,4);(20221088126465726%positive,1);(1363218203145918%positive,1);(348983860922414782%positive,1)]]
  end.

Lemma cqh_h_00179 : iqh tmq_h_00179.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00179 StA 0 2 2 25 20000
                lsetq_h_00179 rsetq_h_00179 certq_h_00179 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00179); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00180 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StB)
  | StC, S0 => Some (mkTrans S0 DL StB)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => None
  | StD, S1 => None
  end.

Definition lsetq_h_00180 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StB,S1)])];
   [(S1,[(StB,S0);(StC,S1)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1)]);(S1,[(StB,S0);(StC,S1)])]].

Definition rsetq_h_00180 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StB,S1);(StB,S0)])]].

Definition certq_h_00180 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 68 [(305056725095895518%positive,1);(4714392777386%positive,1);(1207992430055902%positive,1);(75499211911646%positive,1);(312234336247411166%positive,1);(312234337002017246%positive,1);(19514645747659230%positive,1);(1207991675449822%positive,1);(19066045003157982%positive,1);(1207991675081182%positive,1);(305056724340920798%positive,1);(19514645747290590%positive,1);(305056725096264158%positive,1);(4714392408746%positive,0);(74476738376158%positive,1);(1207992430424542%positive,1);(305056724341289438%positive,1);(312234336247042526%positive,1);(4713637802666%positive,1);(312234337002385886%positive,1);(76229085032926%positive,1);(75499211543006%positive,1);(19066045003526622%positive,1);(4713637434026%positive,0)] [305056725095895518%positive;75499211911646%positive;4714392777386%positive;1207992430055902%positive;312234336247411166%positive;312234337002017246%positive;19514645747659230%positive;1207991675449822%positive;19066045003157982%positive;305056724340920798%positive;1207991675081182%positive;19514645747290590%positive;305056725096264158%positive;1207992430424542%positive;4714392408746%positive;74476738376158%positive;312234336247042526%positive;4713637802666%positive;312234337002385886%positive;76229085032926%positive;75499211543006%positive;19066045003526622%positive;4713637434026%positive;305056724341289438%positive]]
  | StC => [HMeas MLeft 68 [(312234336247412201%positive,0);(76229085034141%positive,1);(305056725096265193%positive,0);(305056724341290653%positive,1);(19066045003527837%positive,1);(74476738377193%positive,0);(312234337002386921%positive,0);(75499211544041%positive,1);(18182797457%positive,0);(1207991675082217%positive,1);(305056725095896733%positive,1);(1207992430425577%positive,1);(312234336247043561%positive,0);(19514645747291625%positive,0);(1207991675451037%positive,1);(75499211912861%positive,1);(312234337002018461%positive,1);(312234336247412381%positive,1);(305056724340922013%positive,1);(290924759325%positive,1);(76229085033961%positive,0);(19514645747660445%positive,1);(19066045003527657%positive,0);(305056724341290473%positive,0);(74476738377373%positive,1);(305056725096265373%positive,1);(1207992430057117%positive,1);(19066045003159197%positive,1);(305056725095896553%positive,0);(75499211544221%positive,1);(1207992430056937%positive,1);(19514645747660265%positive,0);(1207991675082397%positive,1);(1207992430425757%positive,1);(75499211912681%positive,1);(1207991675450857%positive,1);(312234337002018281%positive,0);(19514645747291805%positive,1);(312234336247043741%positive,1);(305056724340921833%positive,0);(19066045003159017%positive,0);(312234337002387101%positive,1)] [312234336247412201%positive;76229085034141%positive;305056725096265193%positive;305056724341290653%positive;19066045003527837%positive;74476738377193%positive;312234337002386921%positive;75499211544041%positive;18182797457%positive;1207991675082217%positive;305056725095896733%positive;1207992430425577%positive;312234336247043561%positive;19514645747291625%positive;1207991675451037%positive;75499211912861%positive;312234337002018461%positive;312234336247412381%positive;305056724340922013%positive;290924759325%positive;76229085033961%positive;19514645747660445%positive;19066045003527657%positive;305056725096265373%positive;305056724341290473%positive;74476738377373%positive;1207992430057117%positive;19066045003159197%positive;305056725095896553%positive;75499211544221%positive;1207992430056937%positive;19514645747660265%positive;1207991675082397%positive;1207992430425757%positive;75499211912681%positive;1207991675450857%positive;312234337002018281%positive;19514645747291805%positive;312234336247043741%positive;305056724340921833%positive;19066045003159017%positive;312234337002387101%positive]]
  | StD => []
  end.

Lemma cqh_h_00180 : iqh tmq_h_00180.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00180 StA 0 2 2 25 20000
                lsetq_h_00180 rsetq_h_00180 certq_h_00180 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00180); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00181 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StC)
  | StC, S1 => Some (mkTrans S0 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Definition lsetq_h_00181 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)])]].

Definition rsetq_h_00181 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00181 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(96506244151734932528823967%positive,0);(395289576045616243870191315455%positive,0);(395289576045508157479134423551%positive,0);(1272356869486641675967%positive,0);(86815892754912382467697151%positive,0);(356478221541895532295539301886%positive,1);(356478221541895532089555020255%positive,0);(395284740351525128597623269855%positive,0);(395289576045616244011751088126%positive,1);(5439425987881799326886367%positive,0);(86815892718883795727810207%positive,0);(6031566472647875933759967%positive,0);(5752220401271370238%positive,1);(79524556147012878315%positive,1);(75385173311315%positive,2);(309059144859841534%positive,3);(395284740351525128803607551486%positive,1);(86815892646826132970577918%positive,1);(86815892646825991410805247%positive,0);(87030815806108789221268990%positive,1);(22469610942466335%positive,0);(395289576045508157620694196222%positive,1);(19316196576851263%positive,0);(1272356869692626299902%positive,1);(96505063562366014931246590%positive,1);(395289576045580215283451559583%positive,0);(86815892754912524027469822%positive,1)]]
  | StC => [HMeas MLeft 45 [(356478221541823474632781987485%positive,1);(5485676198033%positive,0);(395289551557455399771264122857%positive,0);(92035520718772838377%positive,0);(96506244151734932528823967%positive,1);(86890067004746519077322729%positive,0);(395289576045616243870191315455%positive,1);(395289576045508157479134423551%positive,1);(1472550408361321037469%positive,1);(1272356869486641675967%positive,1);(20364736985982012145641%positive,0);(395284740351453071140850237085%positive,1);(5439425987881799326886367%positive,1);(356478221541895532089555020255%positive,1);(356478197192193354998930857961%positive,0);(86815892718883795727810207%positive,1);(79524556147012878315%positive,0);(86890067112832910134214633%positive,0);(6031566472647875933759967%positive,1);(395284740351525128597623269855%positive,1);(395284716001822951506999107561%positive,0);(87030809861357281091903465%positive,0);(22469610942466335%positive,1);(356478221541931561023838879389%positive,1);(19316196576851263%positive,1);(395289551557563486162321014761%positive,0);(395289576045580215283451559583%positive,1);(395284740351561157531907128989%positive,1);(75385173311315%positive,1);(96505057617614506801881065%positive,0);(86815892646825991410805247%positive,1);(86815892754912382467697151%positive,1)] [356478221541823474632781987485%positive;5485676198033%positive;395289551557455399771264122857%positive;92035520718772838377%positive;96506244151734932528823967%positive;86890067004746519077322729%positive;395289576045616243870191315455%positive;395289576045508157479134423551%positive;1472550408361321037469%positive;1272356869486641675967%positive;20364736985982012145641%positive;356478197192193354998930857961%positive;395284740351453071140850237085%positive;5439425987881799326886367%positive;356478221541895532089555020255%positive;86815892718883795727810207%positive;79524556147012878315%positive;86890067112832910134214633%positive;6031566472647875933759967%positive;395284740351525128597623269855%positive;395284716001822951506999107561%positive;87030809861357281091903465%positive;22469610942466335%positive;356478221541931561023838879389%positive;19316196576851263%positive;395289551557563486162321014761%positive;395289576045580215283451559583%positive;395284740351561157531907128989%positive;75385173311315%positive;96505057617614506801881065%positive;86815892646825991410805247%positive;86815892754912382467697151%positive]]
  | StD => [HRank [(356478221541823474632781987485%positive,0);(5752220401271370238%positive,0);(5485676198033%positive,1);(356478221541895532295539301886%positive,0);(395284740351525128803607551486%positive,0);(395289551557455399771264122857%positive,1);(87030815806108789221268990%positive,0);(96505063562366014931246590%positive,0);(92035520718772838377%positive,1);(1272356869692626299902%positive,0);(86890067004746519077322729%positive,1);(1472550408361321037469%positive,0);(309059144859841534%positive,0);(20364736985982012145641%positive,1);(395289576045616244011751088126%positive,0);(395284740351453071140850237085%positive,0);(86815892754912524027469822%positive,0);(356478197192193354998930857961%positive,1);(86890067112832910134214633%positive,1);(86815892646826132970577918%positive,0);(395284716001822951506999107561%positive,1);(87030809861357281091903465%positive,1);(356478221541931561023838879389%positive,0);(395289576045508157620694196222%positive,0);(395289551557563486162321014761%positive,1);(395284740351561157531907128989%positive,0);(96505057617614506801881065%positive,1)]]
  end.

Lemma cqh_h_00181 : iqh tmq_h_00181.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00181 StA 0 4 2 25 20000
                lsetq_h_00181 rsetq_h_00181 certq_h_00181 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00181); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00182 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StB)
  | StC, S1 => Some (mkTrans S0 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Definition lsetq_h_00182 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)])]].

Definition rsetq_h_00182 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00182 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(96506244151734932528823967%positive,0);(395289576045616243870191315455%positive,0);(395289576045508157479134423551%positive,0);(86815892754912382467697151%positive,0);(356478221541895532295539301886%positive,1);(1272356869486641675967%positive,0);(356478221541895532089555020255%positive,0);(395284740351525128597623269855%positive,0);(395289576045616244011751088126%positive,1);(5439425987881799326886367%positive,0);(86815892718883795727810207%positive,0);(6031566472647875933759967%positive,0);(5752220401271370238%positive,1);(79524556147012878315%positive,1);(75385173311315%positive,2);(309059144859841534%positive,3);(395284740351525128803607551486%positive,1);(86815892646826132970577918%positive,1);(86815892646825991410805247%positive,0);(87030815806108789221268990%positive,1);(1272356869486641610431%positive,0);(86797003180894654389723134%positive,1);(22469610942466335%positive,0);(395289576045508157620694196222%positive,1);(19316196576851263%positive,0);(1272356869692626299902%positive,1);(96505063562366014931246590%positive,1);(395289576045580215283451559583%positive,0);(86815892754912524027469822%positive,1)]]
  | StC => [HMeas MLeft 47 [(356478221541823474632781987485%positive,1);(5485676198033%positive,0);(395289551557455399771264122857%positive,0);(92035520718772838377%positive,0);(96506244151734932528823967%positive,1);(86890067004746519077322729%positive,0);(395289576045616243870191315455%positive,1);(395289576045508157479134423551%positive,1);(1472550408361321037469%positive,1);(20364736985982012145641%positive,0);(1272356869486641675967%positive,1);(395284740351453071140850237085%positive,1);(5439425987881799326886367%positive,1);(356478221541895532089555020255%positive,1);(356478197192193354998930857961%positive,0);(86815892718883795727810207%positive,1);(79524556147012878315%positive,0);(86890067112832910134214633%positive,0);(6031566472647875933759967%positive,1);(395284740351525128597623269855%positive,1);(395284716001822951506999107561%positive,0);(22469610942466335%positive,1);(87030809861357281091903465%positive,0);(356478221541931561023838879389%positive,1);(19316196576851263%positive,1);(395289551557563486162321014761%positive,0);(1272356869486641610431%positive,1);(395289576045580215283451559583%positive,1);(395284740351561157531907128989%positive,1);(75385173311315%positive,1);(96505057617614506801881065%positive,0);(86815892646825991410805247%positive,1);(86815892754912382467697151%positive,1)] [356478221541823474632781987485%positive;5485676198033%positive;395289551557455399771264122857%positive;92035520718772838377%positive;96506244151734932528823967%positive;86890067004746519077322729%positive;395289576045616243870191315455%positive;395289576045508157479134423551%positive;1472550408361321037469%positive;1272356869486641675967%positive;20364736985982012145641%positive;356478197192193354998930857961%positive;5439425987881799326886367%positive;395284740351453071140850237085%positive;356478221541895532089555020255%positive;86815892718883795727810207%positive;79524556147012878315%positive;86890067112832910134214633%positive;6031566472647875933759967%positive;395284740351525128597623269855%positive;395284716001822951506999107561%positive;22469610942466335%positive;87030809861357281091903465%positive;356478221541931561023838879389%positive;19316196576851263%positive;395289551557563486162321014761%positive;1272356869486641610431%positive;395289576045580215283451559583%positive;395284740351561157531907128989%positive;75385173311315%positive;96505057617614506801881065%positive;86815892646825991410805247%positive;86815892754912382467697151%positive]]
  | StD => [HRank [(356478221541823474632781987485%positive,0);(5752220401271370238%positive,0);(5485676198033%positive,1);(356478221541895532295539301886%positive,0);(395284740351525128803607551486%positive,0);(395289551557455399771264122857%positive,1);(87030815806108789221268990%positive,0);(96505063562366014931246590%positive,0);(92035520718772838377%positive,1);(1272356869692626299902%positive,0);(86890067004746519077322729%positive,1);(1472550408361321037469%positive,0);(309059144859841534%positive,0);(20364736985982012145641%positive,1);(395289576045616244011751088126%positive,0);(395284740351453071140850237085%positive,0);(86815892754912524027469822%positive,0);(356478197192193354998930857961%positive,1);(86890067112832910134214633%positive,1);(86815892646826132970577918%positive,0);(395284716001822951506999107561%positive,1);(86797003180894654389723134%positive,0);(87030809861357281091903465%positive,1);(356478221541931561023838879389%positive,0);(395289576045508157620694196222%positive,0);(395289551557563486162321014761%positive,1);(395284740351561157531907128989%positive,0);(96505057617614506801881065%positive,1)]]
  end.

Lemma cqh_h_00182 : iqh tmq_h_00182.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00182 StA 0 4 2 25 20000
                lsetq_h_00182 rsetq_h_00182 certq_h_00182 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00182); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00183 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => Some (mkTrans S0 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Definition lsetq_h_00183 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StC,S1);(StB,S1)]);(S1,[(StC,S1);(StD,S1)])];
   [(S1,[(StC,S1);(StD,S1)]);(S1,[(StB,S0)])];
   [(S1,[(StC,S1);(StD,S1)]);(S1,[(StC,S1);(StB,S1)])]].

Definition rsetq_h_00183 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StC,S1)]);(S1,[(StD,S1);(StC,S0)])];
   [(S1,[(StB,S1);(StC,S1)]);(S1,[(StD,S1);(StC,S1)])];
   [(S1,[(StD,S1);(StC,S0)]);(S0,[(StD,S0)])];
   [(S1,[(StD,S1);(StC,S1)]);(S1,[(StB,S1);(StC,S1)])]].

Definition certq_h_00183 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 26 [(334969145631%positive,3);(85752101270014%positive,3);(75771740648190%positive,3);(18421095795%positive,1);(315211813752894959%positive,3);(19700738091349487%positive,3);(20068258241541854%positive,3);(1254265871890142%positive,3);(351240610771858927%positive,3);(21952537905034735%positive,3);(4735331431343%positive,0);(315211815899330302%positive,3);(75769594213295%positive,0);(351240612918294270%positive,3);(350115260620830430%positive,3);(300609407263%positive,3);(294603454266%positive,2);(76956008247806%positive,3);(21882203520595678%positive,3)] [334969145631%positive;85752101270014%positive;75771740648190%positive;18421095795%positive;315211813752894959%positive;19700738091349487%positive;20068258241541854%positive;1254265871890142%positive;351240610771858927%positive;21952537905034735%positive;4735331431343%positive;315211815899330302%positive;75769594213295%positive;351240612918294270%positive;350115260620830430%positive;300609407263%positive;294603454266%positive;76956008247806%positive;21882203520595678%positive]]
  | StC => [HMeas MLeft 26 [(334969145631%positive,1);(85477357582317%positive,1);(18421095795%positive,1);(315211813752894959%positive,1);(19700738091349487%positive,1);(350115262767265773%positive,1);(351240610771858927%positive,1);(21952537905034735%positive,1);(20867184785%positive,0);(4899476142061%positive,1);(4735331431343%positive,1);(75769594213295%positive,1);(20068260387977197%positive,1);(300609407263%positive,1)] [334969145631%positive;75769594213295%positive;85477357582317%positive;4899476142061%positive;20068260387977197%positive;350115262767265773%positive;4735331431343%positive;351240610771858927%positive;300609407263%positive;21952537905034735%positive;18421095795%positive;315211813752894959%positive;19700738091349487%positive;20867184785%positive]]
  | StD => [HMeas MRight 26 [(85477357582317%positive,1);(85752101270014%positive,1);(75771740648190%positive,1);(20068258241541854%positive,1);(1254265871890142%positive,1);(350115262767265773%positive,1);(20867184785%positive,1);(4899476142061%positive,1);(315211815899330302%positive,1);(20068260387977197%positive,1);(351240612918294270%positive,1);(350115260620830430%positive,1);(294603454266%positive,0);(76956008247806%positive,1);(21882203520595678%positive,1)] [85477357582317%positive;4899476142061%positive;20068258241541854%positive;20068260387977197%positive;351240612918294270%positive;85752101270014%positive;1254265871890142%positive;350115262767265773%positive;350115260620830430%positive;315211815899330302%positive;294603454266%positive;75771740648190%positive;76956008247806%positive;21882203520595678%positive;20867184785%positive]]
  end.

Lemma cqh_h_00183 : iqh tmq_h_00183.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00183 StA 0 2 2 25 20000
                lsetq_h_00183 rsetq_h_00183 certq_h_00183 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00183); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00184 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S0 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00184 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition rsetq_h_00184 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition certq_h_00184 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 35 [(5453667406779%positive,0);(351078360865895151%positive,1);(357411547841885946%positive,1);(306064359855454111%positive,1);(357411548697523962%positive,1);(1195563884074911%positive,1);(357411547841884911%positive,1);(1150007538%positive,1);(351078360865896366%positive,1);(19641575789098746%positive,1);(351078361721533167%positive,1);(351078361721534382%positive,1);(19641576644736762%positive,1);(4722827818783%positive,1);(294402117422%positive,1);(19641576644735727%positive,1);(357411547841886126%positive,1);(19641575789097711%positive,1);(357411548697522927%positive,1);(357411548697524142%positive,1);(19641575789098926%positive,1);(306067452231907231%positive,1);(19641576644736942%positive,1);(1195575963670431%positive,1);(5357030642619%positive,0);(351078360865896186%positive,1);(351078361721534202%positive,1)] [5453667406779%positive;351078360865895151%positive;357411547841885946%positive;306064359855454111%positive;357411548697523962%positive;1195563884074911%positive;357411547841884911%positive;1150007538%positive;351078360865896366%positive;19641575789098746%positive;351078361721533167%positive;351078361721534382%positive;19641576644736762%positive;4722827818783%positive;294402117422%positive;19641576644735727%positive;357411547841886126%positive;19641575789097711%positive;357411548697522927%positive;357411548697524142%positive;19641575789098926%positive;306067452231907231%positive;19641576644736942%positive;1195575963670431%positive;5357030642619%positive;351078360865896186%positive;351078361721534202%positive]]
  | StC => [HMeas MLeft 35 [(5453667406779%positive,1);(351078360865895151%positive,2);(306064359855454111%positive,2);(1195563884074911%positive,2);(357411547841884911%positive,2);(351078361721533167%positive,2);(4722827818783%positive,2);(19641576644735727%positive,2);(18419783537%positive,2);(19641575789097711%positive,2);(306067452231905785%positive,2);(1195575963668985%positive,0);(357411548697522927%positive,2);(306067452231907231%positive,2);(75565245100537%positive,2);(1195575963670431%positive,2);(5357030642619%positive,1);(1195563884073465%positive,0);(306064359855452665%positive,2)] [5453667406779%positive;351078360865895151%positive;306064359855454111%positive;1195563884074911%positive;357411547841884911%positive;351078361721533167%positive;4722827818783%positive;19641576644735727%positive;18419783537%positive;19641575789097711%positive;306067452231905785%positive;357411548697522927%positive;1195575963668985%positive;306067452231907231%positive;75565245100537%positive;1195575963670431%positive;5357030642619%positive;1195563884073465%positive;306064359855452665%positive]]
  | StD => [HMeas MRight 35 [(357411547841885946%positive,0);(357411548697523962%positive,1);(1150007538%positive,0);(351078360865896366%positive,2);(19641575789098746%positive,0);(351078361721534382%positive,2);(19641576644736762%positive,1);(294402117422%positive,2);(357411547841886126%positive,2);(18419783537%positive,1);(306067452231905785%positive,1);(1195575963668985%positive,2);(357411548697524142%positive,2);(19641575789098926%positive,2);(19641576644736942%positive,2);(75565245100537%positive,1);(1195563884073465%positive,2);(306064359855452665%positive,1);(351078360865896186%positive,0);(351078361721534202%positive,1)] [357411547841885946%positive;357411548697523962%positive;1150007538%positive;351078360865896366%positive;19641575789098746%positive;351078361721534382%positive;19641576644736762%positive;294402117422%positive;357411547841886126%positive;18419783537%positive;306067452231905785%positive;1195575963668985%positive;357411548697524142%positive;19641575789098926%positive;19641576644736942%positive;75565245100537%positive;1195563884073465%positive;306064359855452665%positive;351078360865896186%positive;351078361721534202%positive]]
  end.

Lemma cqh_h_00184 : iqh tmq_h_00184.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00184 StA 13 2 2 38 20000
                lsetq_h_00184 rsetq_h_00184 certq_h_00184 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 38) 2000 tmq_h_00184); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00185 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StB)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StA)
  end.

Definition lsetq_h_00185 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition rsetq_h_00185 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition certq_h_00185 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 37 [(1334049735266782%positive,1);(323514222544615102%positive,1);(347849918707528158%positive,1);(75285048259563%positive,1);(323514226923467755%positive,1);(323511130168161982%positive,1);(4705315516222%positive,1);(323511134547014635%positive,1);(1358788746891742%positive,1);(323514222544614379%positive,1);(4936435274410%positive,1);(19087145909481950%positive,1);(323511130168161259%positive,1);(341516731731538398%positive,1);(4936388088490%positive,0);(18416111347%positive,1);(74559165649374%positive,1);(323514226923468478%positive,1);(323511134547015358%positive,1);(75289427112939%positive,1);(4705589194558%positive,1)] [347849918707528158%positive;1334049735266782%positive;323514222544615102%positive;323514226923467755%positive;75285048259563%positive;323511130168161982%positive;323511134547014635%positive;4705315516222%positive;1358788746891742%positive;323514222544614379%positive;4936435274410%positive;19087145909481950%positive;323511130168161259%positive;341516731731538398%positive;4936388088490%positive;18416111347%positive;74559165649374%positive;323514226923468478%positive;323511134547015358%positive;75289427112939%positive;4705589194558%positive]]
  | StC => [HMeas MRight 37 [(19087145909482985%positive,0);(75285048259563%positive,1);(323514226923467755%positive,1);(1149729265%positive,0);(347849918707529373%positive,2);(294330785565%positive,2);(323511134547014635%positive,1);(74559165650589%positive,2);(1334049735267997%positive,2);(341516731731539433%positive,0);(323514222544614379%positive,1);(1358788746892777%positive,2);(323511130168161259%positive,1);(19087145909483165%positive,2);(18416111347%positive,1);(347849918707529193%positive,0);(74559165650409%positive,2);(75289427112939%positive,1);(1334049735267817%positive,2);(341516731731539613%positive,2);(1358788746892957%positive,2)] [19087145909482985%positive;75285048259563%positive;323514226923467755%positive;1149729265%positive;347849918707529373%positive;294330785565%positive;323511134547014635%positive;74559165650589%positive;1334049735267997%positive;341516731731539433%positive;323514222544614379%positive;1358788746892777%positive;323511130168161259%positive;19087145909483165%positive;18416111347%positive;347849918707529193%positive;74559165650409%positive;75289427112939%positive;1334049735267817%positive;341516731731539613%positive;1358788746892957%positive]]
  | StD => [HMeas MLeft 37 [(1334049735266782%positive,4);(19087145909482985%positive,4);(323514222544615102%positive,4);(347849918707528158%positive,4);(1149729265%positive,4);(323511130168161982%positive,4);(347849918707529373%positive,4);(294330785565%positive,4);(4705315516222%positive,4);(74559165650589%positive,0);(1334049735267997%positive,0);(341516731731539433%positive,4);(1358788746891742%positive,4);(4936435274410%positive,1);(1358788746892777%positive,2);(19087145909481950%positive,4);(341516731731538398%positive,4);(4936388088490%positive,3);(19087145909483165%positive,4);(347849918707529193%positive,4);(74559165649374%positive,4);(323514226923468478%positive,4);(74559165650409%positive,2);(323511134547015358%positive,4);(1334049735267817%positive,2);(4705589194558%positive,4);(341516731731539613%positive,4);(1358788746892957%positive,0)] [347849918707528158%positive;19087145909482985%positive;323514222544615102%positive;1334049735266782%positive;1149729265%positive;323511130168161982%positive;347849918707529373%positive;294330785565%positive;4705315516222%positive;74559165650589%positive;1334049735267997%positive;341516731731539433%positive;1358788746891742%positive;4936435274410%positive;19087145909481950%positive;1358788746892777%positive;341516731731538398%positive;4936388088490%positive;19087145909483165%positive;347849918707529193%positive;74559165649374%positive;323514226923468478%positive;74559165650409%positive;323511134547015358%positive;1334049735267817%positive;4705589194558%positive;341516731731539613%positive;1358788746892957%positive]]
  end.

Lemma cqh_h_00185 : iqh tmq_h_00185.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00185 StA 8 2 2 33 20000
                lsetq_h_00185 rsetq_h_00185 certq_h_00185 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 33) 2000 tmq_h_00185); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00186 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StB)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00186 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition rsetq_h_00186 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition certq_h_00186 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 37 [(347849918707528158%positive,1);(323514222544615102%positive,1);(1334049735266782%positive,1);(75285048259563%positive,1);(323514226923467755%positive,1);(323511130168161982%positive,1);(4705315516222%positive,1);(323511134547014635%positive,1);(1358788746891742%positive,1);(323514222544614379%positive,1);(4936435274410%positive,1);(19087145909481950%positive,1);(323511130168161259%positive,1);(341516731731538398%positive,1);(4936388088490%positive,0);(18416111347%positive,1);(74559165649374%positive,1);(323514226923468478%positive,1);(75289427112939%positive,1);(323511134547015358%positive,1);(4705589194558%positive,1)] [1334049735266782%positive;347849918707528158%positive;323514222544615102%positive;323514226923467755%positive;75285048259563%positive;323511130168161982%positive;323511134547014635%positive;4705315516222%positive;1358788746891742%positive;323514222544614379%positive;4936435274410%positive;19087145909481950%positive;323511130168161259%positive;341516731731538398%positive;4936388088490%positive;18416111347%positive;74559165649374%positive;323514226923468478%positive;75289427112939%positive;323511134547015358%positive;4705589194558%positive]]
  | StC => [HMeas MRight 37 [(19087145909482985%positive,0);(75285048259563%positive,1);(323514226923467755%positive,1);(1149729265%positive,0);(347849918707529373%positive,2);(294330785565%positive,2);(323511134547014635%positive,1);(74559165650589%positive,2);(1334049735267997%positive,2);(341516731731539433%positive,0);(323514222544614379%positive,1);(1358788746892777%positive,2);(323511130168161259%positive,1);(19087145909483165%positive,2);(18416111347%positive,1);(347849918707529193%positive,0);(74559165650409%positive,2);(75289427112939%positive,1);(1334049735267817%positive,2);(341516731731539613%positive,2);(1358788746892957%positive,2)] [19087145909482985%positive;75285048259563%positive;323514226923467755%positive;1149729265%positive;347849918707529373%positive;294330785565%positive;323511134547014635%positive;74559165650589%positive;1334049735267997%positive;341516731731539433%positive;323514222544614379%positive;1358788746892777%positive;323511130168161259%positive;19087145909483165%positive;18416111347%positive;347849918707529193%positive;74559165650409%positive;75289427112939%positive;1334049735267817%positive;341516731731539613%positive;1358788746892957%positive]]
  | StD => [HMeas MLeft 37 [(347849918707528158%positive,4);(19087145909482985%positive,4);(323514222544615102%positive,4);(1334049735266782%positive,4);(1149729265%positive,4);(323511130168161982%positive,4);(347849918707529373%positive,4);(294330785565%positive,4);(4705315516222%positive,4);(74559165650589%positive,0);(1334049735267997%positive,0);(341516731731539433%positive,4);(1358788746891742%positive,4);(4936435274410%positive,1);(1358788746892777%positive,2);(19087145909481950%positive,4);(341516731731538398%positive,4);(4936388088490%positive,3);(19087145909483165%positive,4);(347849918707529193%positive,4);(74559165649374%positive,4);(323514226923468478%positive,4);(74559165650409%positive,2);(323511134547015358%positive,4);(1334049735267817%positive,2);(4705589194558%positive,4);(341516731731539613%positive,4);(1358788746892957%positive,0)] [1334049735266782%positive;19087145909482985%positive;323514222544615102%positive;347849918707528158%positive;1149729265%positive;323511130168161982%positive;347849918707529373%positive;294330785565%positive;4705315516222%positive;74559165650589%positive;1334049735267997%positive;341516731731539433%positive;1358788746891742%positive;4936435274410%positive;19087145909481950%positive;1358788746892777%positive;341516731731538398%positive;4936388088490%positive;19087145909483165%positive;347849918707529193%positive;74559165649374%positive;323514226923468478%positive;74559165650409%positive;323511134547015358%positive;1334049735267817%positive;4705589194558%positive;341516731731539613%positive;1358788746892957%positive]]
  end.

Lemma cqh_h_00186 : iqh tmq_h_00186.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00186 StA 8 2 2 33 20000
                lsetq_h_00186 rsetq_h_00186 certq_h_00186 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 33) 2000 tmq_h_00186); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00187 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StB)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StB)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S0 DL StA)
  end.

Definition lsetq_h_00187 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition rsetq_h_00187 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[(StD,S1);(StB,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition certq_h_00187 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 48 [(306045391451673054%positive,1);(312234334099559403%positive,1);(305057203230143146%positive,1);(19067385031905758%positive,1);(348966818560669374%positive,1);(305078164816613854%positive,1);(1207992429007326%positive,1);(76229085033451%positive,1);(85196976747499%positive,1);(4764317814590%positive,1);(5324811046718%positive,1);(4711490319018%positive,1);(312234334099928766%positive,1);(306045392206647774%positive,1);(312234334099560126%positive,1);(305057203229774506%positive,0);(1207991674032606%positive,1);(312234334099928043%positive,1);(20800043155%positive,1);(348966818560668651%positive,1);(305078165571588574%positive,1);(19127836696596958%positive,1);(348966818560300734%positive,1);(348966818560300011%positive,1);(4711489950378%positive,0);(75499210494430%positive,1)] [306045391451673054%positive;312234334099559403%positive;305057203230143146%positive;19067385031905758%positive;348966818560669374%positive;305078164816613854%positive;1207992429007326%positive;76229085033451%positive;85196976747499%positive;4764317814590%positive;5324811046718%positive;4711490319018%positive;312234334099928766%positive;306045392206647774%positive;305057203229774506%positive;1207991674032606%positive;312234334099928043%positive;20800043155%positive;348966818560668651%positive;305078165571588574%positive;19127836696596958%positive;312234334099560126%positive;348966818560300734%positive;348966818560300011%positive;4711489950378%positive;75499210494430%positive]]
  | StC => [HMeas MLeft 48 [(1136457873%positive,0);(75499210495645%positive,2);(1207991674033821%positive,2);(1207992429008361%positive,2);(19067385031906793%positive,0);(305078165571589789%positive,2);(312234334099559403%positive,1);(19127836696598173%positive,2);(290945206557%positive,2);(306045392206648809%positive,2);(76229085033451%positive,1);(85196976747499%positive,1);(306045391451674269%positive,2);(306045391451674089%positive,2);(75499210495465%positive,2);(1207991674033641%positive,2);(19067385031906973%positive,2);(305078165571589609%positive,0);(305078164816615069%positive,2);(312234334099928043%positive,1);(20800043155%positive,1);(348966818560668651%positive,1);(19127836696597993%positive,2);(305078164816614889%positive,0);(306045392206648989%positive,2);(1207992429008541%positive,2);(348966818560300011%positive,1)] [1136457873%positive;75499210495645%positive;1207991674033821%positive;1207992429008361%positive;305078165571589789%positive;19067385031906793%positive;312234334099559403%positive;19127836696598173%positive;290945206557%positive;306045392206648809%positive;76229085033451%positive;85196976747499%positive;306045391451674269%positive;306045391451674089%positive;75499210495465%positive;1207991674033641%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;312234334099928043%positive;20800043155%positive;348966818560668651%positive;19127836696597993%positive;305078164816614889%positive;306045392206648989%positive;1207992429008541%positive;348966818560300011%positive]]
  | StD => [HMeas MRight 48 [(306045391451673054%positive,4);(1136457873%positive,4);(75499210495645%positive,0);(1207991674033821%positive,0);(1207992429008361%positive,2);(19067385031906793%positive,4);(305078165571589789%positive,4);(305057203230143146%positive,1);(19067385031905758%positive,4);(348966818560669374%positive,4);(19127836696598173%positive,0);(305078164816613854%positive,4);(290945206557%positive,4);(1207992429007326%positive,4);(306045392206648809%positive,2);(306045391451674269%positive,0);(4764317814590%positive,4);(5324811046718%positive,4);(4711490319018%positive,1);(312234334099928766%positive,4);(306045392206647774%positive,4);(306045391451674089%positive,2);(312234334099560126%positive,4);(75499210495465%positive,2);(1207991674033641%positive,2);(19067385031906973%positive,4);(305078165571589609%positive,4);(305057203229774506%positive,3);(305078164816615069%positive,4);(1207991674032606%positive,4);(19127836696597993%positive,2);(305078164816614889%positive,4);(306045392206648989%positive,0);(305078165571588574%positive,4);(1207992429008541%positive,0);(19127836696596958%positive,4);(348966818560300734%positive,4);(4711489950378%positive,3);(75499210494430%positive,4)] [306045391451673054%positive;1136457873%positive;75499210495645%positive;1207991674033821%positive;1207992429008361%positive;305078165571589789%positive;19067385031906793%positive;305057203230143146%positive;19067385031905758%positive;348966818560669374%positive;19127836696598173%positive;305078164816613854%positive;290945206557%positive;1207992429007326%positive;306045392206648809%positive;306045391451674269%positive;4764317814590%positive;5324811046718%positive;4711490319018%positive;348966818560300734%positive;312234334099928766%positive;306045392206647774%positive;306045391451674089%positive;75499210495465%positive;1207991674033641%positive;19067385031906973%positive;305078165571589609%positive;305057203229774506%positive;305078164816615069%positive;1207991674032606%positive;19127836696597993%positive;305078164816614889%positive;306045392206648989%positive;305078165571588574%positive;1207992429008541%positive;312234334099560126%positive;19127836696596958%positive;4711489950378%positive;75499210494430%positive]]
  end.

Lemma cqh_h_00187 : iqh tmq_h_00187.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00187 StA 13 2 2 38 20000
                lsetq_h_00187 rsetq_h_00187 certq_h_00187 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 38) 2000 tmq_h_00187); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00188 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StB)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StB)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S0 DR StA)
  end.

Definition lsetq_h_00188 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition rsetq_h_00188 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition certq_h_00188 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 37 [(19503865160225246%positive,1);(312234334099559403%positive,1);(75492551357098%positive,1);(19067385031905758%positive,1);(348966818560669374%positive,1);(305078164816613854%positive,1);(76229085033451%positive,1);(85196976747499%positive,1);(4764317814590%positive,1);(5324811046718%positive,1);(1218991303381470%positive,1);(312234334099928766%positive,1);(75492550988458%positive,0);(312234334099928043%positive,1);(19503865915199966%positive,1);(20800043155%positive,1);(348966818560668651%positive,1);(305078165571588574%positive,1);(312234334099560126%positive,1);(348966818560300734%positive,1);(348966818560300011%positive,1)] [19503865160225246%positive;312234334099559403%positive;75492551357098%positive;19067385031905758%positive;348966818560669374%positive;305078164816613854%positive;76229085033451%positive;85196976747499%positive;4764317814590%positive;1218991303381470%positive;5324811046718%positive;312234334099928766%positive;75492550988458%positive;312234334099928043%positive;19503865915199966%positive;20800043155%positive;348966818560668651%positive;305078165571588574%positive;312234334099560126%positive;348966818560300734%positive;348966818560300011%positive]]
  | StC => [HMeas MLeft 37 [(19503865160226281%positive,2);(1218991303382505%positive,2);(19503865915201181%positive,2);(1136457873%positive,0);(19067385031906793%positive,0);(305078165571589789%positive,2);(312234334099559403%positive,1);(290945206557%positive,2);(76229085033451%positive,1);(85196976747499%positive,1);(1218991303382685%positive,2);(19503865160226461%positive,2);(19503865915201001%positive,2);(19067385031906973%positive,2);(305078165571589609%positive,0);(305078164816615069%positive,2);(312234334099928043%positive,1);(20800043155%positive,1);(348966818560668651%positive,1);(305078164816614889%positive,0);(348966818560300011%positive,1)] [19503865160226281%positive;1218991303382505%positive;19503865915201181%positive;1136457873%positive;305078165571589789%positive;19067385031906793%positive;312234334099559403%positive;290945206557%positive;76229085033451%positive;85196976747499%positive;1218991303382685%positive;19503865160226461%positive;19503865915201001%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;312234334099928043%positive;20800043155%positive;348966818560668651%positive;305078164816614889%positive;348966818560300011%positive]]
  | StD => [HMeas MRight 37 [(19503865160226281%positive,2);(1218991303382505%positive,2);(19503865915201181%positive,0);(1136457873%positive,4);(19503865160225246%positive,4);(19067385031906793%positive,4);(305078165571589789%positive,4);(75492551357098%positive,1);(19067385031905758%positive,4);(348966818560669374%positive,4);(305078164816613854%positive,4);(290945206557%positive,4);(4764317814590%positive,4);(5324811046718%positive,4);(1218991303381470%positive,4);(1218991303382685%positive,0);(19503865160226461%positive,0);(19503865915201001%positive,2);(312234334099928766%positive,4);(19067385031906973%positive,4);(305078165571589609%positive,4);(75492550988458%positive,3);(305078164816615069%positive,4);(19503865915199966%positive,4);(305078164816614889%positive,4);(305078165571588574%positive,4);(312234334099560126%positive,4);(348966818560300734%positive,4)] [19503865160226281%positive;1218991303382505%positive;19503865915201181%positive;1136457873%positive;19503865160225246%positive;305078165571589789%positive;19067385031906793%positive;75492551357098%positive;19067385031905758%positive;348966818560669374%positive;305078164816613854%positive;290945206557%positive;4764317814590%positive;1218991303381470%positive;5324811046718%positive;1218991303382685%positive;19503865160226461%positive;19503865915201001%positive;312234334099928766%positive;19067385031906973%positive;305078165571589609%positive;75492550988458%positive;305078164816615069%positive;19503865915199966%positive;305078164816614889%positive;305078165571588574%positive;312234334099560126%positive;348966818560300734%positive]]
  end.

Lemma cqh_h_00188 : iqh tmq_h_00188.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00188 StA 5 2 2 30 20000
                lsetq_h_00188 rsetq_h_00188 certq_h_00188 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 30) 2000 tmq_h_00188); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00189 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StB)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StB)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S1 DR StA)
  end.

Definition lsetq_h_00189 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition rsetq_h_00189 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition certq_h_00189 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 37 [(19503865160225246%positive,1);(312234334099559403%positive,1);(75492551357098%positive,1);(19067385031905758%positive,1);(348966818560669374%positive,1);(305078164816613854%positive,1);(76229085033451%positive,1);(85196976747499%positive,1);(4764317814590%positive,1);(5324811046718%positive,1);(1218991303381470%positive,1);(312234334099928766%positive,1);(75492550988458%positive,0);(312234334099928043%positive,1);(19503865915199966%positive,1);(20800043155%positive,1);(348966818560668651%positive,1);(305078165571588574%positive,1);(312234334099560126%positive,1);(348966818560300734%positive,1);(348966818560300011%positive,1)] [19503865160225246%positive;312234334099559403%positive;75492551357098%positive;19067385031905758%positive;348966818560669374%positive;305078164816613854%positive;76229085033451%positive;85196976747499%positive;4764317814590%positive;1218991303381470%positive;5324811046718%positive;312234334099928766%positive;75492550988458%positive;312234334099928043%positive;19503865915199966%positive;20800043155%positive;348966818560668651%positive;305078165571588574%positive;312234334099560126%positive;348966818560300734%positive;348966818560300011%positive]]
  | StC => [HMeas MLeft 37 [(19503865160226281%positive,2);(1218991303382505%positive,2);(19503865915201181%positive,2);(1136457873%positive,0);(19067385031906793%positive,0);(305078165571589789%positive,2);(312234334099559403%positive,1);(290945206557%positive,2);(76229085033451%positive,1);(85196976747499%positive,1);(1218991303382685%positive,2);(19503865160226461%positive,2);(19503865915201001%positive,2);(19067385031906973%positive,2);(305078165571589609%positive,0);(305078164816615069%positive,2);(312234334099928043%positive,1);(20800043155%positive,1);(348966818560668651%positive,1);(305078164816614889%positive,0);(348966818560300011%positive,1)] [19503865160226281%positive;1218991303382505%positive;19503865915201181%positive;1136457873%positive;305078165571589789%positive;19067385031906793%positive;312234334099559403%positive;290945206557%positive;76229085033451%positive;85196976747499%positive;1218991303382685%positive;19503865160226461%positive;19503865915201001%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;312234334099928043%positive;20800043155%positive;348966818560668651%positive;305078164816614889%positive;348966818560300011%positive]]
  | StD => [HMeas MRight 37 [(19503865160226281%positive,2);(1218991303382505%positive,2);(19503865915201181%positive,0);(1136457873%positive,4);(19503865160225246%positive,4);(19067385031906793%positive,4);(305078165571589789%positive,4);(75492551357098%positive,1);(19067385031905758%positive,4);(348966818560669374%positive,4);(305078164816613854%positive,4);(290945206557%positive,4);(4764317814590%positive,4);(5324811046718%positive,4);(1218991303381470%positive,4);(1218991303382685%positive,0);(19503865160226461%positive,0);(19503865915201001%positive,2);(312234334099928766%positive,4);(19067385031906973%positive,4);(305078165571589609%positive,4);(75492550988458%positive,3);(305078164816615069%positive,4);(19503865915199966%positive,4);(305078164816614889%positive,4);(305078165571588574%positive,4);(312234334099560126%positive,4);(348966818560300734%positive,4)] [19503865160226281%positive;1218991303382505%positive;19503865915201181%positive;1136457873%positive;19503865160225246%positive;305078165571589789%positive;19067385031906793%positive;75492551357098%positive;19067385031905758%positive;348966818560669374%positive;305078164816613854%positive;290945206557%positive;4764317814590%positive;1218991303381470%positive;5324811046718%positive;1218991303382685%positive;19503865160226461%positive;19503865915201001%positive;312234334099928766%positive;19067385031906973%positive;305078165571589609%positive;75492550988458%positive;305078164816615069%positive;19503865915199966%positive;305078164816614889%positive;305078165571588574%positive;312234334099560126%positive;348966818560300734%positive]]
  end.

Lemma cqh_h_00189 : iqh tmq_h_00189.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00189 StA 5 2 2 30 20000
                lsetq_h_00189 rsetq_h_00189 certq_h_00189 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 30) 2000 tmq_h_00189); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00190 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StC)
  | StB, S0 => Some (mkTrans S0 DL StB)
  | StB, S1 => Some (mkTrans S1 DL StA)
  | StC, S0 => Some (mkTrans S1 DR StC)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00190 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StA,S1);(StC,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StA,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StA,S1);(StC,S1)]);(S1,[(StD,S1);(StD,S0);(StA,S1);(StC,S1)])];
   [(S1,[(StD,S1);(StD,S0);(StA,S1);(StC,S1)]);(S1,[(StC,S1);(StD,S0);(StA,S1);(StC,S1)])]].

Definition rsetq_h_00190 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S1)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S0)])]].

Definition certq_h_00190 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MRight 45 [(94114347458316807332875246%positive,1);(355781880472656385225673600191%positive,1);(94114365579957415850536651%positive,0);(355781880472726142641386220735%positive,1);(4714582220659%positive,0);(355781880472726138173009424075%positive,0);(385492441415505511823252581567%positive,1);(385492441415575269238965202111%positive,1);(86814564498004942135754443%positive,0);(385492441415575264770588405451%positive,0);(89754431268238864074%positive,0);(86814564567762357848374987%positive,0);(1272371321632298626239%positive,1);(395395886322957545211619101694%positive,1);(19310927726116670%positive,1);(1472964459370625821870%positive,1);(86860810662269640802299595%positive,0);(23567434718627486805707%positive,0);(76800402860178%positive,1);(96532212607500522863389886%positive,1);(355781806246486750149932927982%positive,1);(395395942840392375561539284158%positive,1);(395395886323027302627331722238%positive,1);(385492367189335876747511909358%positive,1);(5425909790084498250451966%positive,1);(395395942840322622473400221387%positive,0);(21912704833980718%positive,1);(86814564567758030274817214%positive,1);(395395942840392379889112841931%positive,0);(86860792540629032284638190%positive,1);(79523207322745126603%positive,0);(5425909859841913963072510%positive,1)] [94114347458316807332875246%positive;355781880472656385225673600191%positive;94114365579957415850536651%positive;355781880472726142641386220735%positive;4714582220659%positive;355781880472726138173009424075%positive;385492441415505511823252581567%positive;385492441415575269238965202111%positive;86814564498004942135754443%positive;385492441415575264770588405451%positive;89754431268238864074%positive;86814564567762357848374987%positive;1272371321632298626239%positive;395395886322957545211619101694%positive;19310927726116670%positive;1472964459370625821870%positive;86860810662269640802299595%positive;23567434718627486805707%positive;76800402860178%positive;96532212607500522863389886%positive;395395942840392375561539284158%positive;355781806246486750149932927982%positive;395395886323027302627331722238%positive;385492367189335876747511909358%positive;5425909790084498250451966%positive;395395942840322622473400221387%positive;21912704833980718%positive;86814564567758030274817214%positive;395395942840392379889112841931%positive;86860792540629032284638190%positive;79523207322745126603%positive;5425909859841913963072510%positive]]
  | StB => []
  | StC => [HRank [(1472964669914217892588%positive,0);(355781880472656385225673600191%positive,0);(94114365579957415850536651%positive,1);(355781880472726142641386220735%positive,0);(385492441415575264840926936812%positive,0);(4970200457946330092%positive,0);(4714582220659%positive,1);(395395942840322622543864578028%positive,0);(395395942840392379959577198572%positive,0);(355781880472726138173009424075%positive,1);(385492441415505511823252581567%positive,0);(385492441415575269238965202111%positive,0);(86860810662269507893247724%positive,0);(86814564498004942135754443%positive,1);(385492441415575264770588405451%positive,1);(355781880472726138243347955436%positive,0);(86814564567762357848374987%positive,1);(94114365579957282941484780%positive,0);(1272371321632298626239%positive,0);(86860810662269640802299595%positive,1);(350603247141556972%positive,0);(23567434718627486805707%positive,1);(86814564498005012600111084%positive,0);(86814564567762428312731628%positive,0);(395395942840322622473400221387%positive,1);(395395942840392379889112841931%positive,1);(79523207322745126603%positive,1)]]
  | StD => [HRank [(21912704833980718%positive,0);(1472964669914217892588%positive,1);(94114347458316807332875246%positive,0);(395395886322957545211619101694%positive,0);(395395886323027302627331722238%positive,0);(385492441415575264840926936812%positive,1);(96532212607500522863389886%positive,0);(89754431268238864074%positive,1);(395395942840322622543864578028%positive,1);(1472964459370625821870%positive,0);(94114365579957282941484780%positive,1);(385492367189335876747511909358%positive,0);(395395942840392379959577198572%positive,1);(19310927726116670%positive,0);(76800402860178%positive,2);(86860792540629032284638190%positive,0);(86814564498005012600111084%positive,1);(355781806246486750149932927982%positive,0);(395395942840392375561539284158%positive,0);(355781880472726138243347955436%positive,1);(86814564567762428312731628%positive,1);(5425909790084498250451966%positive,0);(350603247141556972%positive,3);(5425909859841913963072510%positive,0);(4970200457946330092%positive,1);(86860810662269507893247724%positive,1);(86814564567758030274817214%positive,0)]]
  end.

Lemma cqh_h_00190 : iqh tmq_h_00190.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00190 StB 4 4 2 29 20000
                lsetq_h_00190 rsetq_h_00190 certq_h_00190 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00190); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00191 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StC)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StC)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00191 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StA,S1);(StC,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StA,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StA,S1);(StC,S1)]);(S1,[(StD,S1);(StD,S0);(StA,S1);(StC,S1)])];
   [(S1,[(StD,S1);(StD,S0);(StA,S1);(StC,S1)]);(S1,[(StC,S1);(StD,S0);(StA,S1);(StC,S1)])]].

Definition rsetq_h_00191 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S1)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S0)])]].

Definition certq_h_00191 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MRight 45 [(94114347458316807332875246%positive,1);(355781880472656385225673600191%positive,1);(94114365579957415850536651%positive,0);(355781880472726142641386220735%positive,1);(4714582220659%positive,0);(355781880472726138173009424075%positive,0);(385492441415505511823252581567%positive,1);(385492441415575269238965202111%positive,1);(86814564498004942135754443%positive,0);(385492441415575264770588405451%positive,0);(89754431268238864074%positive,0);(86814564567762357848374987%positive,0);(1272371321632298626239%positive,1);(395395886322957545211619101694%positive,1);(19310927726116670%positive,1);(1472964459370625821870%positive,1);(86860810662269640802299595%positive,0);(23567434718627486805707%positive,0);(76800402860178%positive,1);(96532212607500522863389886%positive,1);(355781806246486750149932927982%positive,1);(395395942840392375561539284158%positive,1);(395395886323027302627331722238%positive,1);(385492367189335876747511909358%positive,1);(5425909790084498250451966%positive,1);(395395942840322622473400221387%positive,0);(21912704833980718%positive,1);(86814564567758030274817214%positive,1);(395395942840392379889112841931%positive,0);(86860792540629032284638190%positive,1);(79523207322745126603%positive,0);(5425909859841913963072510%positive,1)] [94114347458316807332875246%positive;355781880472656385225673600191%positive;94114365579957415850536651%positive;355781880472726142641386220735%positive;4714582220659%positive;355781880472726138173009424075%positive;385492441415505511823252581567%positive;385492441415575269238965202111%positive;86814564498004942135754443%positive;385492441415575264770588405451%positive;89754431268238864074%positive;86814564567762357848374987%positive;1272371321632298626239%positive;395395886322957545211619101694%positive;19310927726116670%positive;1472964459370625821870%positive;86860810662269640802299595%positive;23567434718627486805707%positive;76800402860178%positive;96532212607500522863389886%positive;395395942840392375561539284158%positive;355781806246486750149932927982%positive;395395886323027302627331722238%positive;385492367189335876747511909358%positive;5425909790084498250451966%positive;395395942840322622473400221387%positive;21912704833980718%positive;86814564567758030274817214%positive;395395942840392379889112841931%positive;86860792540629032284638190%positive;79523207322745126603%positive;5425909859841913963072510%positive]]
  | StB => []
  | StC => [HRank [(1472964669914217892588%positive,0);(355781880472656385225673600191%positive,0);(94114365579957415850536651%positive,1);(355781880472726142641386220735%positive,0);(385492441415575264840926936812%positive,0);(4970200457946330092%positive,0);(4714582220659%positive,1);(395395942840322622543864578028%positive,0);(395395942840392379959577198572%positive,0);(355781880472726138173009424075%positive,1);(385492441415505511823252581567%positive,0);(385492441415575269238965202111%positive,0);(86860810662269507893247724%positive,0);(86814564498004942135754443%positive,1);(385492441415575264770588405451%positive,1);(355781880472726138243347955436%positive,0);(86814564567762357848374987%positive,1);(94114365579957282941484780%positive,0);(1272371321632298626239%positive,0);(86860810662269640802299595%positive,1);(350603247141556972%positive,0);(23567434718627486805707%positive,1);(86814564498005012600111084%positive,0);(86814564567762428312731628%positive,0);(395395942840322622473400221387%positive,1);(395395942840392379889112841931%positive,1);(79523207322745126603%positive,1)]]
  | StD => [HRank [(21912704833980718%positive,0);(1472964669914217892588%positive,1);(94114347458316807332875246%positive,0);(395395886322957545211619101694%positive,0);(395395886323027302627331722238%positive,0);(385492441415575264840926936812%positive,1);(96532212607500522863389886%positive,0);(89754431268238864074%positive,1);(395395942840322622543864578028%positive,1);(1472964459370625821870%positive,0);(94114365579957282941484780%positive,1);(385492367189335876747511909358%positive,0);(395395942840392379959577198572%positive,1);(19310927726116670%positive,0);(76800402860178%positive,2);(86860792540629032284638190%positive,0);(86814564498005012600111084%positive,1);(355781806246486750149932927982%positive,0);(395395942840392375561539284158%positive,0);(355781880472726138243347955436%positive,1);(86814564567762428312731628%positive,1);(5425909790084498250451966%positive,0);(350603247141556972%positive,3);(5425909859841913963072510%positive,0);(4970200457946330092%positive,1);(86860810662269507893247724%positive,1);(86814564567758030274817214%positive,0)]]
  end.

Lemma cqh_h_00191 : iqh tmq_h_00191.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00191 StB 1 4 2 26 20000
                lsetq_h_00191 rsetq_h_00191 certq_h_00191 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00191); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00192 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StC)
  | StB, S0 => Some (mkTrans S1 DL StA)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StC)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00192 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StA,S1);(StC,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StA,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StA,S1);(StC,S1)]);(S1,[(StD,S1);(StD,S0);(StA,S1);(StC,S1)])];
   [(S1,[(StD,S1);(StD,S0);(StA,S1);(StC,S1)]);(S1,[(StC,S1);(StD,S0);(StA,S1);(StC,S1)])]].

Definition rsetq_h_00192 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S1)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S0)])]].

Definition certq_h_00192 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MRight 45 [(94114347458316807332875246%positive,1);(355781880472656385225673600191%positive,1);(94114365579957415850536651%positive,0);(355781880472726142641386220735%positive,1);(4714582220659%positive,0);(355781880472726138173009424075%positive,0);(385492441415505511823252581567%positive,1);(385492441415575269238965202111%positive,1);(86814564498004942135754443%positive,0);(385492441415575264770588405451%positive,0);(89754431268238864074%positive,0);(86814564567762357848374987%positive,0);(1272371321632298626239%positive,1);(395395886322957545211619101694%positive,1);(19310927726116670%positive,1);(1472964459370625821870%positive,1);(86860810662269640802299595%positive,0);(23567434718627486805707%positive,0);(76800402860178%positive,1);(96532212607500522863389886%positive,1);(355781806246486750149932927982%positive,1);(395395942840392375561539284158%positive,1);(395395886323027302627331722238%positive,1);(385492367189335876747511909358%positive,1);(5425909790084498250451966%positive,1);(395395942840322622473400221387%positive,0);(21912704833980718%positive,1);(86814564567758030274817214%positive,1);(395395942840392379889112841931%positive,0);(86860792540629032284638190%positive,1);(79523207322745126603%positive,0);(5425909859841913963072510%positive,1)] [94114347458316807332875246%positive;355781880472656385225673600191%positive;94114365579957415850536651%positive;355781880472726142641386220735%positive;4714582220659%positive;355781880472726138173009424075%positive;385492441415505511823252581567%positive;385492441415575269238965202111%positive;86814564498004942135754443%positive;385492441415575264770588405451%positive;89754431268238864074%positive;86814564567762357848374987%positive;1272371321632298626239%positive;395395886322957545211619101694%positive;19310927726116670%positive;1472964459370625821870%positive;86860810662269640802299595%positive;23567434718627486805707%positive;76800402860178%positive;96532212607500522863389886%positive;395395942840392375561539284158%positive;355781806246486750149932927982%positive;395395886323027302627331722238%positive;385492367189335876747511909358%positive;5425909790084498250451966%positive;395395942840322622473400221387%positive;21912704833980718%positive;86814564567758030274817214%positive;395395942840392379889112841931%positive;86860792540629032284638190%positive;79523207322745126603%positive;5425909859841913963072510%positive]]
  | StB => []
  | StC => [HRank [(1472964669914217892588%positive,0);(355781880472656385225673600191%positive,0);(94114365579957415850536651%positive,1);(355781880472726142641386220735%positive,0);(385492441415575264840926936812%positive,0);(4970200457946330092%positive,0);(4714582220659%positive,1);(395395942840322622543864578028%positive,0);(395395942840392379959577198572%positive,0);(355781880472726138173009424075%positive,1);(385492441415505511823252581567%positive,0);(385492441415575269238965202111%positive,0);(86860810662269507893247724%positive,0);(86814564498004942135754443%positive,1);(385492441415575264770588405451%positive,1);(355781880472726138243347955436%positive,0);(86814564567762357848374987%positive,1);(94114365579957282941484780%positive,0);(1272371321632298626239%positive,0);(86860810662269640802299595%positive,1);(350603247141556972%positive,0);(23567434718627486805707%positive,1);(86814564498005012600111084%positive,0);(86814564567762428312731628%positive,0);(395395942840322622473400221387%positive,1);(395395942840392379889112841931%positive,1);(79523207322745126603%positive,1)]]
  | StD => [HRank [(21912704833980718%positive,0);(1472964669914217892588%positive,1);(94114347458316807332875246%positive,0);(395395886322957545211619101694%positive,0);(395395886323027302627331722238%positive,0);(385492441415575264840926936812%positive,1);(96532212607500522863389886%positive,0);(89754431268238864074%positive,1);(395395942840322622543864578028%positive,1);(1472964459370625821870%positive,0);(94114365579957282941484780%positive,1);(385492367189335876747511909358%positive,0);(395395942840392379959577198572%positive,1);(19310927726116670%positive,0);(76800402860178%positive,2);(86860792540629032284638190%positive,0);(86814564498005012600111084%positive,1);(355781806246486750149932927982%positive,0);(395395942840392375561539284158%positive,0);(355781880472726138243347955436%positive,1);(86814564567762428312731628%positive,1);(5425909790084498250451966%positive,0);(350603247141556972%positive,3);(5425909859841913963072510%positive,0);(4970200457946330092%positive,1);(86860810662269507893247724%positive,1);(86814564567758030274817214%positive,0)]]
  end.

Lemma cqh_h_00192 : iqh tmq_h_00192.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00192 StB 1 4 2 26 20000
                lsetq_h_00192 rsetq_h_00192 certq_h_00192 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00192); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00193 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StC)
  | StB, S0 => Some (mkTrans S1 DL StA)
  | StB, S1 => Some (mkTrans S0 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StC)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00193 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S1);(StC,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StB,S1);(StC,S1)]);(S1,[(StC,S0);(StB,S1);(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StB,S1);(StC,S1)]);(S1,[(StD,S1);(StD,S0);(StB,S1);(StC,S1)])];
   [(S1,[(StD,S1);(StD,S0);(StB,S1);(StC,S1)]);(S1,[(StC,S1);(StD,S0);(StB,S1);(StC,S1)])]].

Definition rsetq_h_00193 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S1)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S0)])]].

Definition certq_h_00193 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 45 [(395434628540408145892022414782%positive,1);(94123810330937555797929691%positive,0);(76808992811154%positive,1);(23569740566034747076315%positive,0);(1272372447534352952767%positive,1);(5425914401840887569505278%positive,1);(385531127115520226622573047231%positive,1);(385531127115591039569448332735%positive,1);(4714649329523%positive,0);(89763438484673474266%positive,0);(395434628540337337304932941531%positive,0);(395434628540408150251808227035%positive,0);(5425914472653834444790782%positive,1);(395434571953867782681404038142%positive,1);(86814638285051640077876955%positive,0);(19311202604547902%positive,1);(385531127115591035133283790555%positive,0);(86814638355864586953162459%positive,0);(355820491877327230204005243886%positive,1);(395434571953796969734528752638%positive,1);(1473108574575881547182%positive,1);(86870237274720671616130030%positive,1);(21914904931240238%positive,1);(86870255413249780749692635%positive,0);(96541657358480660797517246%positive,1);(86814638355860227167350206%positive,1);(385531052820176356801584225262%positive,1);(94123792192408446664367086%positive,1);(355820566172671100024994065855%positive,1);(355820566172741908535704809179%positive,0);(355820566172741912971869351359%positive,1);(79523277693636787931%positive,0)] [395434628540408145892022414782%positive;94123810330937555797929691%positive;76808992811154%positive;23569740566034747076315%positive;1272372447534352952767%positive;5425914401840887569505278%positive;385531127115520226622573047231%positive;385531127115591039569448332735%positive;4714649329523%positive;89763438484673474266%positive;395434628540337337304932941531%positive;395434628540408150251808227035%positive;5425914472653834444790782%positive;395434571953867782681404038142%positive;86814638285051640077876955%positive;19311202604547902%positive;385531127115591035133283790555%positive;86814638355864586953162459%positive;355820491877327230204005243886%positive;395434571953796969734528752638%positive;1473108574575881547182%positive;86870237274720671616130030%positive;21914904931240238%positive;86870255413249780749692635%positive;96541657358480660797517246%positive;86814638355860227167350206%positive;385531052820176356801584225262%positive;94123792192408446664367086%positive;355820566172671100024994065855%positive;355820566172741908535704809179%positive;355820566172741912971869351359%positive;79523277693636787931%positive]]
  | StC => [HRank [(385531127115591035171410132717%positive,0);(86814638285051678330044397%positive,0);(395434628540408150290060394477%positive,0);(94123810330937420875677421%positive,0);(1473108785377171659501%positive,0);(94123810330937555797929691%positive,1);(350638431580754669%positive,0);(23569740566034747076315%positive,1);(86814638355864625205329901%positive,0);(1272372447534352952767%positive,0);(395434628540337337343185108973%positive,0);(385531127115520226622573047231%positive,0);(385531127115591039569448332735%positive,0);(4970204856001229805%positive,0);(4714649329523%positive,1);(395434628540337337304932941531%positive,1);(395434628540408150251808227035%positive,1);(86870255413249645827440365%positive,0);(86814638285051640077876955%positive,1);(385531127115591035133283790555%positive,1);(355820566172741908573831151341%positive,0);(86814638355864586953162459%positive,1);(86870255413249780749692635%positive,1);(355820566172671100024994065855%positive,0);(355820566172741908535704809179%positive,1);(355820566172741912971869351359%positive,0);(79523277693636787931%positive,1)]]
  | StD => [HRank [(395434571953867782681404038142%positive,0);(395434571953796969734528752638%positive,0);(385531127115591035171410132717%positive,1);(395434628540408145892022414782%positive,0);(86870237274720671616130030%positive,0);(86814638285051678330044397%positive,1);(385531052820176356801584225262%positive,0);(395434628540408150290060394477%positive,1);(1473108574575881547182%positive,0);(94123810330937420875677421%positive,1);(96541657358480660797517246%positive,0);(89763438484673474266%positive,1);(76808992811154%positive,2);(355820491877327230204005243886%positive,0);(86814638355864625205329901%positive,1);(5425914401840887569505278%positive,0);(94123792192408446664367086%positive,0);(395434628540337337343185108973%positive,1);(5425914472653834444790782%positive,0);(19311202604547902%positive,0);(21914904931240238%positive,0);(355820566172741908573831151341%positive,1);(350638431580754669%positive,3);(86870255413249645827440365%positive,1);(86814638355860227167350206%positive,0);(1473108785377171659501%positive,1);(4970204856001229805%positive,1)]]
  end.

Lemma cqh_h_00193 : iqh tmq_h_00193.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00193 StA 2 4 2 27 20000
                lsetq_h_00193 rsetq_h_00193 certq_h_00193 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 27) 2000 tmq_h_00193); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00194 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StC)
  | StB, S0 => Some (mkTrans S1 DL StB)
  | StB, S1 => Some (mkTrans S0 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StC)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00194 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StA,S1);(StC,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StA,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StA,S1);(StC,S1)]);(S1,[(StD,S1);(StD,S0);(StA,S1);(StC,S1)])];
   [(S1,[(StD,S1);(StD,S0);(StA,S1);(StC,S1)]);(S1,[(StC,S1);(StD,S0);(StA,S1);(StC,S1)])]].

Definition rsetq_h_00194 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S1)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S0)])]].

Definition certq_h_00194 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MRight 45 [(94114347458316807332875246%positive,1);(355781880472656385225673600191%positive,1);(94114365579957415850536651%positive,0);(355781880472726142641386220735%positive,1);(4714582220659%positive,0);(355781880472726138173009424075%positive,0);(385492441415505511823252581567%positive,1);(385492441415575269238965202111%positive,1);(86814564498004942135754443%positive,0);(385492441415575264770588405451%positive,0);(89754431268238864074%positive,0);(86814564567762357848374987%positive,0);(1272371321632298626239%positive,1);(395395886322957545211619101694%positive,1);(19310927726116670%positive,1);(1472964459370625821870%positive,1);(86860810662269640802299595%positive,0);(23567434718627486805707%positive,0);(76800402860178%positive,1);(96532212607500522863389886%positive,1);(355781806246486750149932927982%positive,1);(395395942840392375561539284158%positive,1);(395395886323027302627331722238%positive,1);(385492367189335876747511909358%positive,1);(5425909790084498250451966%positive,1);(395395942840322622473400221387%positive,0);(21912704833980718%positive,1);(86814564567758030274817214%positive,1);(395395942840392379889112841931%positive,0);(86860792540629032284638190%positive,1);(79523207322745126603%positive,0);(5425909859841913963072510%positive,1)] [94114347458316807332875246%positive;355781880472656385225673600191%positive;94114365579957415850536651%positive;355781880472726142641386220735%positive;4714582220659%positive;355781880472726138173009424075%positive;385492441415505511823252581567%positive;385492441415575269238965202111%positive;86814564498004942135754443%positive;385492441415575264770588405451%positive;89754431268238864074%positive;86814564567762357848374987%positive;1272371321632298626239%positive;395395886322957545211619101694%positive;19310927726116670%positive;1472964459370625821870%positive;86860810662269640802299595%positive;23567434718627486805707%positive;76800402860178%positive;96532212607500522863389886%positive;395395942840392375561539284158%positive;355781806246486750149932927982%positive;395395886323027302627331722238%positive;385492367189335876747511909358%positive;5425909790084498250451966%positive;395395942840322622473400221387%positive;21912704833980718%positive;86814564567758030274817214%positive;395395942840392379889112841931%positive;86860792540629032284638190%positive;79523207322745126603%positive;5425909859841913963072510%positive]]
  | StB => []
  | StC => [HRank [(1472964669914217892588%positive,0);(355781880472656385225673600191%positive,0);(94114365579957415850536651%positive,1);(355781880472726142641386220735%positive,0);(385492441415575264840926936812%positive,0);(4970200457946330092%positive,0);(4714582220659%positive,1);(395395942840322622543864578028%positive,0);(395395942840392379959577198572%positive,0);(355781880472726138173009424075%positive,1);(385492441415505511823252581567%positive,0);(385492441415575269238965202111%positive,0);(86860810662269507893247724%positive,0);(86814564498004942135754443%positive,1);(385492441415575264770588405451%positive,1);(355781880472726138243347955436%positive,0);(86814564567762357848374987%positive,1);(94114365579957282941484780%positive,0);(1272371321632298626239%positive,0);(86860810662269640802299595%positive,1);(350603247141556972%positive,0);(23567434718627486805707%positive,1);(86814564498005012600111084%positive,0);(86814564567762428312731628%positive,0);(395395942840322622473400221387%positive,1);(395395942840392379889112841931%positive,1);(79523207322745126603%positive,1)]]
  | StD => [HRank [(21912704833980718%positive,0);(1472964669914217892588%positive,1);(94114347458316807332875246%positive,0);(395395886322957545211619101694%positive,0);(395395886323027302627331722238%positive,0);(385492441415575264840926936812%positive,1);(96532212607500522863389886%positive,0);(89754431268238864074%positive,1);(395395942840322622543864578028%positive,1);(1472964459370625821870%positive,0);(94114365579957282941484780%positive,1);(385492367189335876747511909358%positive,0);(395395942840392379959577198572%positive,1);(19310927726116670%positive,0);(76800402860178%positive,2);(86860792540629032284638190%positive,0);(86814564498005012600111084%positive,1);(355781806246486750149932927982%positive,0);(395395942840392375561539284158%positive,0);(355781880472726138243347955436%positive,1);(86814564567762428312731628%positive,1);(5425909790084498250451966%positive,0);(350603247141556972%positive,3);(5425909859841913963072510%positive,0);(4970200457946330092%positive,1);(86860810662269507893247724%positive,1);(86814564567758030274817214%positive,0)]]
  end.

Lemma cqh_h_00194 : iqh tmq_h_00194.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00194 StB 2 4 2 27 20000
                lsetq_h_00194 rsetq_h_00194 certq_h_00194 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 27) 2000 tmq_h_00194); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00195 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StC)
  | StB, S0 => Some (mkTrans S1 DL StB)
  | StB, S1 => Some (mkTrans S0 DR StC)
  | StC, S0 => Some (mkTrans S1 DR StC)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00195 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StA,S1);(StC,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StA,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StA,S1);(StC,S1)]);(S1,[(StD,S1);(StD,S0);(StA,S1);(StC,S1)])];
   [(S1,[(StD,S1);(StD,S0);(StA,S1);(StC,S1)]);(S1,[(StC,S1);(StD,S0);(StA,S1);(StC,S1)])]].

Definition rsetq_h_00195 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S1)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S0)])]].

Definition certq_h_00195 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MRight 45 [(94114347458316807332875246%positive,1);(355781880472656385225673600191%positive,1);(94114365579957415850536651%positive,0);(355781880472726142641386220735%positive,1);(4714582220659%positive,0);(355781880472726138173009424075%positive,0);(385492441415505511823252581567%positive,1);(385492441415575269238965202111%positive,1);(86814564498004942135754443%positive,0);(385492441415575264770588405451%positive,0);(89754431268238864074%positive,0);(86814564567762357848374987%positive,0);(1272371321632298626239%positive,1);(395395886322957545211619101694%positive,1);(19310927726116670%positive,1);(1472964459370625821870%positive,1);(86860810662269640802299595%positive,0);(23567434718627486805707%positive,0);(76800402860178%positive,1);(96532212607500522863389886%positive,1);(355781806246486750149932927982%positive,1);(395395942840392375561539284158%positive,1);(395395886323027302627331722238%positive,1);(385492367189335876747511909358%positive,1);(5425909790084498250451966%positive,1);(395395942840322622473400221387%positive,0);(21912704833980718%positive,1);(86814564567758030274817214%positive,1);(395395942840392379889112841931%positive,0);(86860792540629032284638190%positive,1);(79523207322745126603%positive,0);(5425909859841913963072510%positive,1)] [94114347458316807332875246%positive;355781880472656385225673600191%positive;94114365579957415850536651%positive;355781880472726142641386220735%positive;4714582220659%positive;355781880472726138173009424075%positive;385492441415505511823252581567%positive;385492441415575269238965202111%positive;86814564498004942135754443%positive;385492441415575264770588405451%positive;89754431268238864074%positive;86814564567762357848374987%positive;1272371321632298626239%positive;395395886322957545211619101694%positive;19310927726116670%positive;1472964459370625821870%positive;86860810662269640802299595%positive;23567434718627486805707%positive;76800402860178%positive;96532212607500522863389886%positive;395395942840392375561539284158%positive;355781806246486750149932927982%positive;395395886323027302627331722238%positive;385492367189335876747511909358%positive;5425909790084498250451966%positive;395395942840322622473400221387%positive;21912704833980718%positive;86814564567758030274817214%positive;395395942840392379889112841931%positive;86860792540629032284638190%positive;79523207322745126603%positive;5425909859841913963072510%positive]]
  | StB => []
  | StC => [HRank [(1472964669914217892588%positive,0);(355781880472656385225673600191%positive,0);(94114365579957415850536651%positive,1);(355781880472726142641386220735%positive,0);(385492441415575264840926936812%positive,0);(4970200457946330092%positive,0);(4714582220659%positive,1);(395395942840322622543864578028%positive,0);(395395942840392379959577198572%positive,0);(355781880472726138173009424075%positive,1);(385492441415505511823252581567%positive,0);(385492441415575269238965202111%positive,0);(86860810662269507893247724%positive,0);(86814564498004942135754443%positive,1);(385492441415575264770588405451%positive,1);(355781880472726138243347955436%positive,0);(86814564567762357848374987%positive,1);(94114365579957282941484780%positive,0);(1272371321632298626239%positive,0);(86860810662269640802299595%positive,1);(350603247141556972%positive,0);(23567434718627486805707%positive,1);(86814564498005012600111084%positive,0);(86814564567762428312731628%positive,0);(395395942840322622473400221387%positive,1);(395395942840392379889112841931%positive,1);(79523207322745126603%positive,1)]]
  | StD => [HRank [(21912704833980718%positive,0);(1472964669914217892588%positive,1);(94114347458316807332875246%positive,0);(395395886322957545211619101694%positive,0);(395395886323027302627331722238%positive,0);(385492441415575264840926936812%positive,1);(96532212607500522863389886%positive,0);(89754431268238864074%positive,1);(395395942840322622543864578028%positive,1);(1472964459370625821870%positive,0);(94114365579957282941484780%positive,1);(385492367189335876747511909358%positive,0);(395395942840392379959577198572%positive,1);(19310927726116670%positive,0);(76800402860178%positive,2);(86860792540629032284638190%positive,0);(86814564498005012600111084%positive,1);(355781806246486750149932927982%positive,0);(395395942840392375561539284158%positive,0);(355781880472726138243347955436%positive,1);(86814564567762428312731628%positive,1);(5425909790084498250451966%positive,0);(350603247141556972%positive,3);(5425909859841913963072510%positive,0);(4970200457946330092%positive,1);(86860810662269507893247724%positive,1);(86814564567758030274817214%positive,0)]]
  end.

Lemma cqh_h_00195 : iqh tmq_h_00195.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00195 StB 2 4 2 27 20000
                lsetq_h_00195 rsetq_h_00195 certq_h_00195 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 27) 2000 tmq_h_00195); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00196 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StC)
  | StB, S0 => Some (mkTrans S1 DL StB)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S1 DR StC)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00196 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StA,S1);(StC,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StA,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StA,S1);(StC,S1)]);(S1,[(StD,S1);(StD,S0);(StA,S1);(StC,S1)])];
   [(S1,[(StD,S1);(StD,S0);(StA,S1);(StC,S1)]);(S1,[(StC,S1);(StD,S0);(StA,S1);(StC,S1)])]].

Definition rsetq_h_00196 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S1)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S0)])]].

Definition certq_h_00196 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MRight 45 [(94114347458316807332875246%positive,1);(355781880472656385225673600191%positive,1);(94114365579957415850536651%positive,0);(355781880472726142641386220735%positive,1);(4714582220659%positive,0);(355781880472726138173009424075%positive,0);(385492441415505511823252581567%positive,1);(385492441415575269238965202111%positive,1);(86814564498004942135754443%positive,0);(385492441415575264770588405451%positive,0);(89754431268238864074%positive,0);(86814564567762357848374987%positive,0);(1272371321632298626239%positive,1);(395395886322957545211619101694%positive,1);(19310927726116670%positive,1);(1472964459370625821870%positive,1);(86860810662269640802299595%positive,0);(23567434718627486805707%positive,0);(76800402860178%positive,1);(96532212607500522863389886%positive,1);(355781806246486750149932927982%positive,1);(395395942840392375561539284158%positive,1);(395395886323027302627331722238%positive,1);(385492367189335876747511909358%positive,1);(5425909790084498250451966%positive,1);(395395942840322622473400221387%positive,0);(21912704833980718%positive,1);(86814564567758030274817214%positive,1);(395395942840392379889112841931%positive,0);(86860792540629032284638190%positive,1);(79523207322745126603%positive,0);(5425909859841913963072510%positive,1)] [94114347458316807332875246%positive;355781880472656385225673600191%positive;94114365579957415850536651%positive;355781880472726142641386220735%positive;4714582220659%positive;355781880472726138173009424075%positive;385492441415505511823252581567%positive;385492441415575269238965202111%positive;86814564498004942135754443%positive;385492441415575264770588405451%positive;89754431268238864074%positive;86814564567762357848374987%positive;1272371321632298626239%positive;395395886322957545211619101694%positive;19310927726116670%positive;1472964459370625821870%positive;86860810662269640802299595%positive;23567434718627486805707%positive;76800402860178%positive;96532212607500522863389886%positive;395395942840392375561539284158%positive;355781806246486750149932927982%positive;395395886323027302627331722238%positive;385492367189335876747511909358%positive;5425909790084498250451966%positive;395395942840322622473400221387%positive;21912704833980718%positive;86814564567758030274817214%positive;395395942840392379889112841931%positive;86860792540629032284638190%positive;79523207322745126603%positive;5425909859841913963072510%positive]]
  | StB => []
  | StC => [HRank [(1472964669914217892588%positive,0);(355781880472656385225673600191%positive,0);(94114365579957415850536651%positive,1);(355781880472726142641386220735%positive,0);(385492441415575264840926936812%positive,0);(4970200457946330092%positive,0);(4714582220659%positive,1);(395395942840322622543864578028%positive,0);(395395942840392379959577198572%positive,0);(355781880472726138173009424075%positive,1);(385492441415505511823252581567%positive,0);(385492441415575269238965202111%positive,0);(86860810662269507893247724%positive,0);(86814564498004942135754443%positive,1);(385492441415575264770588405451%positive,1);(355781880472726138243347955436%positive,0);(86814564567762357848374987%positive,1);(94114365579957282941484780%positive,0);(1272371321632298626239%positive,0);(86860810662269640802299595%positive,1);(86814564498005012600111084%positive,0);(350603247141556972%positive,0);(23567434718627486805707%positive,1);(86814564567762428312731628%positive,0);(395395942840322622473400221387%positive,1);(395395942840392379889112841931%positive,1);(79523207322745126603%positive,1)]]
  | StD => [HRank [(21912704833980718%positive,0);(1472964669914217892588%positive,1);(94114347458316807332875246%positive,0);(395395886322957545211619101694%positive,0);(395395886323027302627331722238%positive,0);(385492441415575264840926936812%positive,1);(96532212607500522863389886%positive,0);(89754431268238864074%positive,1);(395395942840322622543864578028%positive,1);(1472964459370625821870%positive,0);(94114365579957282941484780%positive,1);(385492367189335876747511909358%positive,0);(395395942840392379959577198572%positive,1);(19310927726116670%positive,0);(86860792540629032284638190%positive,0);(86814564498005012600111084%positive,1);(76800402860178%positive,2);(355781806246486750149932927982%positive,0);(395395942840392375561539284158%positive,0);(355781880472726138243347955436%positive,1);(86814564567762428312731628%positive,1);(5425909790084498250451966%positive,0);(350603247141556972%positive,3);(5425909859841913963072510%positive,0);(4970200457946330092%positive,1);(86860810662269507893247724%positive,1);(86814564567758030274817214%positive,0)]]
  end.

Lemma cqh_h_00196 : iqh tmq_h_00196.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00196 StB 2 4 2 27 20000
                lsetq_h_00196 rsetq_h_00196 certq_h_00196 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 27) 2000 tmq_h_00196); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00197 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StC)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StA)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00197 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00197 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S1,[(StB,S0);(StD,S1)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition certq_h_00197 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 48 [(314652163455309742%positive,4);(356852788752799647%positive,4);(314652158089589691%positive,1);(5445141436191%positive,4);(356856299567175418%positive,2);(22303518401484538%positive,2);(75791334364922%positive,2);(314652158089221051%positive,3);(356856299567174383%positive,4);(1212666493260527%positive,4);(4709410501563%positive,1);(356852788753168287%positive,4);(314652164210284282%positive,4);(22303518401483503%positive,4);(75791334363887%positive,4);(321809154152691615%positive,4);(1212665738286842%positive,2);(19665759941678842%positive,4);(1172076690%positive,4);(1212666493261562%positive,2);(356856298812200698%positive,2);(314652164210283247%positive,4);(4709410132923%positive,3);(356856299567175598%positive,0);(321809154152322975%positive,4);(356856298812199663%positive,4);(19665759941677807%positive,4);(1212665738285807%positive,4);(22303518401484718%positive,0);(75791334365102%positive,0);(314652163455309562%positive,4);(4910418007839%positive,4);(314652164210284462%positive,4);(314652163455308527%positive,4);(356856298812200878%positive,0);(1212665738287022%positive,0);(19665759941679022%positive,4);(1212666493261742%positive,0);(300075682094%positive,4)] [314652163455309742%positive;356852788752799647%positive;314652158089589691%positive;5445141436191%positive;356856299567175418%positive;22303518401484538%positive;75791334364922%positive;314652158089221051%positive;356856299567174383%positive;1212666493260527%positive;4709410501563%positive;314652164210284282%positive;22303518401483503%positive;75791334363887%positive;321809154152691615%positive;1212665738286842%positive;19665759941678842%positive;1172076690%positive;1212666493261562%positive;356856298812200698%positive;314652164210283247%positive;4709410132923%positive;356856299567175598%positive;321809154152322975%positive;356856298812199663%positive;19665759941677807%positive;1212665738285807%positive;22303518401484718%positive;75791334365102%positive;314652163455309562%positive;4910418007839%positive;314652164210284462%positive;1212666493261742%positive;314652163455308527%positive;356856298812200878%positive;1212665738287022%positive;19665759941679022%positive;356852788753168287%positive;300075682094%positive]]
  | StC => [HMeas MRight 48 [(78566688125433%positive,1);(356852788752799647%positive,1);(314652158089589691%positive,1);(321809154152690169%positive,1);(5445141436191%positive,1);(314652158089221051%positive,0);(356856299567174383%positive,1);(1212666493260527%positive,1);(321809154152321529%positive,1);(4709410501563%positive,1);(356852788753168287%positive,1);(22303518401483503%positive,1);(75791334363887%positive,1);(21270083729%positive,1);(321809154152691615%positive,1);(314652164210283247%positive,1);(4709410132923%positive,0);(87122262979065%positive,1);(321809154152322975%positive,1);(356856298812199663%positive,1);(19665759941677807%positive,1);(1212665738285807%positive,1);(356852788753166841%positive,1);(4910418007839%positive,1);(314652163455308527%positive,1);(356852788752798201%positive,1)] [78566688125433%positive;356852788752799647%positive;314652158089589691%positive;321809154152690169%positive;5445141436191%positive;314652158089221051%positive;356856299567174383%positive;1212666493260527%positive;321809154152321529%positive;4709410501563%positive;22303518401483503%positive;75791334363887%positive;21270083729%positive;321809154152691615%positive;314652164210283247%positive;4709410132923%positive;87122262979065%positive;321809154152322975%positive;356856298812199663%positive;19665759941677807%positive;1212665738285807%positive;356852788753166841%positive;4910418007839%positive;314652163455308527%positive;356852788752798201%positive;356852788753168287%positive]]
  | StD => [HMeas MLeft 48 [(314652163455309742%positive,2);(78566688125433%positive,1);(321809154152690169%positive,1);(356856299567175418%positive,2);(22303518401484538%positive,2);(75791334364922%positive,2);(321809154152321529%positive,1);(314652164210284282%positive,0);(21270083729%positive,1);(1212665738286842%positive,2);(19665759941678842%positive,0);(1172076690%positive,0);(1212666493261562%positive,2);(356856298812200698%positive,2);(87122262979065%positive,1);(356856299567175598%positive,2);(22303518401484718%positive,2);(75791334365102%positive,2);(314652163455309562%positive,0);(356852788753166841%positive,1);(314652164210284462%positive,2);(356856298812200878%positive,2);(1212665738287022%positive,2);(19665759941679022%positive,2);(356852788752798201%positive,1);(1212666493261742%positive,2);(300075682094%positive,2)] [314652163455309742%positive;78566688125433%positive;321809154152690169%positive;356856299567175418%positive;22303518401484538%positive;75791334364922%positive;321809154152321529%positive;314652164210284282%positive;21270083729%positive;1212665738286842%positive;19665759941678842%positive;1172076690%positive;1212666493261562%positive;356856298812200698%positive;87122262979065%positive;356856299567175598%positive;22303518401484718%positive;75791334365102%positive;314652163455309562%positive;356852788753166841%positive;314652164210284462%positive;356856298812200878%positive;1212665738287022%positive;19665759941679022%positive;356852788752798201%positive;1212666493261742%positive;300075682094%positive]]
  end.

Lemma cqh_h_00197 : iqh tmq_h_00197.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00197 StA 23 2 2 48 20000
                lsetq_h_00197 rsetq_h_00197 certq_h_00197 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 48) 2000 tmq_h_00197); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00198 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StC)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StA)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00198 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00198 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S1,[(StB,S1);(StB,S1)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition certq_h_00198 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 48 [(21318355982997242%positive,2);(341093700871377647%positive,4);(314652163455309742%positive,4);(21318355982996207%positive,4);(356852788752799647%positive,4);(341093700116403962%positive,2);(5445141436191%positive,4);(341093700871378862%positive,0);(75791334364922%positive,2);(21318355982997422%positive,0);(341093700116402927%positive,4);(1212666493260527%positive,4);(314644461508195259%positive,1);(4709410501563%positive,1);(314652164210284282%positive,4);(75791334363887%positive,4);(321809154152691615%positive,4);(1212665738286842%positive,2);(19665759941678842%positive,4);(1172076690%positive,4);(1212666493261562%positive,2);(341093700116404142%positive,0);(314652164210283247%positive,4);(314644461507826619%positive,3);(4709410132923%positive,3);(321809154152322975%positive,4);(1212665738285807%positive,4);(19665759941677807%positive,4);(314652163455309562%positive,4);(75791334365102%positive,0);(4910418007839%positive,4);(314652164210284462%positive,4);(1212666493261742%positive,0);(314652163455308527%positive,4);(1212665738287022%positive,0);(19665759941679022%positive,4);(341093700871378682%positive,2);(356852788753168287%positive,4);(300075682094%positive,4)] [21318355982997242%positive;341093700871377647%positive;314652163455309742%positive;21318355982996207%positive;356852788752799647%positive;341093700116403962%positive;5445141436191%positive;341093700871378862%positive;75791334364922%positive;21318355982997422%positive;341093700116402927%positive;1212666493260527%positive;314644461508195259%positive;4709410501563%positive;356852788753168287%positive;314652164210284282%positive;75791334363887%positive;321809154152691615%positive;1212665738286842%positive;19665759941678842%positive;1172076690%positive;1212666493261562%positive;341093700116404142%positive;314652164210283247%positive;314644461507826619%positive;4709410132923%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;314652163455309562%positive;75791334365102%positive;4910418007839%positive;314652164210284462%positive;314652163455308527%positive;1212665738287022%positive;19665759941679022%positive;341093700871378682%positive;1212666493261742%positive;300075682094%positive]]
  | StC => [HMeas MRight 48 [(341093700871377647%positive,1);(78566688125433%positive,1);(21318355982996207%positive,1);(356852788752799647%positive,1);(321809154152690169%positive,1);(5445141436191%positive,1);(341093700116402927%positive,1);(1212666493260527%positive,1);(314644461508195259%positive,1);(4709410501563%positive,1);(321809154152321529%positive,1);(75791334363887%positive,1);(21270083729%positive,1);(321809154152691615%positive,1);(314652164210283247%positive,1);(314644461507826619%positive,0);(4709410132923%positive,0);(87122262979065%positive,1);(321809154152322975%positive,1);(1212665738285807%positive,1);(19665759941677807%positive,1);(356852788753166841%positive,1);(4910418007839%positive,1);(314652163455308527%positive,1);(356852788752798201%positive,1);(356852788753168287%positive,1)] [341093700871377647%positive;78566688125433%positive;21318355982996207%positive;356852788752799647%positive;321809154152690169%positive;5445141436191%positive;341093700116402927%positive;1212666493260527%positive;314644461508195259%positive;4709410501563%positive;321809154152321529%positive;75791334363887%positive;21270083729%positive;321809154152691615%positive;314652164210283247%positive;314644461507826619%positive;4709410132923%positive;87122262979065%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;356852788753166841%positive;4910418007839%positive;314652163455308527%positive;356852788752798201%positive;356852788753168287%positive]]
  | StD => [HMeas MLeft 48 [(21318355982997242%positive,2);(314652163455309742%positive,2);(78566688125433%positive,1);(341093700116403962%positive,2);(321809154152690169%positive,1);(341093700871378862%positive,2);(75791334364922%positive,2);(21318355982997422%positive,2);(321809154152321529%positive,1);(314652164210284282%positive,0);(21270083729%positive,1);(1212665738286842%positive,2);(19665759941678842%positive,0);(1172076690%positive,0);(1212666493261562%positive,2);(341093700116404142%positive,2);(87122262979065%positive,1);(314652163455309562%positive,0);(75791334365102%positive,2);(356852788753166841%positive,1);(314652164210284462%positive,2);(1212666493261742%positive,2);(1212665738287022%positive,2);(19665759941679022%positive,2);(356852788752798201%positive,1);(341093700871378682%positive,2);(300075682094%positive,2)] [21318355982997242%positive;314652163455309742%positive;78566688125433%positive;321809154152690169%positive;341093700116403962%positive;341093700871378862%positive;75791334364922%positive;21318355982997422%positive;321809154152321529%positive;314652164210284282%positive;21270083729%positive;1212665738286842%positive;19665759941678842%positive;1172076690%positive;1212666493261562%positive;341093700116404142%positive;87122262979065%positive;314652163455309562%positive;75791334365102%positive;356852788753166841%positive;314652164210284462%positive;1212665738287022%positive;19665759941679022%positive;356852788752798201%positive;341093700871378682%positive;1212666493261742%positive;300075682094%positive]]
  end.

Lemma cqh_h_00198 : iqh tmq_h_00198.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00198 StA 25 2 2 50 20000
                lsetq_h_00198 rsetq_h_00198 certq_h_00198 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 50) 2000 tmq_h_00198); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00199 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StC)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00199 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00199 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S1,[(StB,S0);(StD,S1)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition certq_h_00199 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 48 [(314652163455309742%positive,4);(356852788752799647%positive,4);(314652158089589691%positive,1);(5445141436191%positive,4);(356856299567175418%positive,2);(22303518401484538%positive,2);(75791334364922%positive,2);(314652158089221051%positive,3);(356856299567174383%positive,4);(1212666493260527%positive,4);(4709410501563%positive,1);(356852788753168287%positive,4);(314652164210284282%positive,4);(22303518401483503%positive,4);(75791334363887%positive,4);(321809154152691615%positive,4);(1212665738286842%positive,2);(1172076690%positive,4);(19665759941678842%positive,4);(1212666493261562%positive,2);(356856298812200698%positive,2);(314652164210283247%positive,4);(4709410132923%positive,3);(356856299567175598%positive,0);(321809154152322975%positive,4);(356856298812199663%positive,4);(1212665738285807%positive,4);(19665759941677807%positive,4);(22303518401484718%positive,0);(75791334365102%positive,0);(314652163455309562%positive,4);(4910418007839%positive,4);(314652164210284462%positive,4);(314652163455308527%positive,4);(356856298812200878%positive,0);(1212665738287022%positive,0);(19665759941679022%positive,4);(1212666493261742%positive,0);(300075682094%positive,4)] [314652163455309742%positive;356852788752799647%positive;314652158089589691%positive;5445141436191%positive;356856299567175418%positive;22303518401484538%positive;75791334364922%positive;314652158089221051%positive;356856299567174383%positive;1212666493260527%positive;4709410501563%positive;314652164210284282%positive;22303518401483503%positive;75791334363887%positive;321809154152691615%positive;1212665738286842%positive;1172076690%positive;19665759941678842%positive;1212666493261562%positive;356856298812200698%positive;314652164210283247%positive;4709410132923%positive;356856299567175598%positive;321809154152322975%positive;356856298812199663%positive;1212665738285807%positive;19665759941677807%positive;22303518401484718%positive;75791334365102%positive;314652163455309562%positive;4910418007839%positive;314652164210284462%positive;1212666493261742%positive;314652163455308527%positive;356856298812200878%positive;1212665738287022%positive;19665759941679022%positive;356852788753168287%positive;300075682094%positive]]
  | StC => [HMeas MRight 48 [(78566688125433%positive,1);(356852788752799647%positive,1);(314652158089589691%positive,1);(321809154152690169%positive,1);(5445141436191%positive,1);(314652158089221051%positive,0);(356856299567174383%positive,1);(1212666493260527%positive,1);(321809154152321529%positive,1);(4709410501563%positive,1);(356852788753168287%positive,1);(22303518401483503%positive,1);(75791334363887%positive,1);(21270083729%positive,1);(321809154152691615%positive,1);(314652164210283247%positive,1);(4709410132923%positive,0);(87122262979065%positive,1);(321809154152322975%positive,1);(356856298812199663%positive,1);(1212665738285807%positive,1);(19665759941677807%positive,1);(356852788753166841%positive,1);(4910418007839%positive,1);(314652163455308527%positive,1);(356852788752798201%positive,1)] [78566688125433%positive;356852788752799647%positive;314652158089589691%positive;321809154152690169%positive;5445141436191%positive;314652158089221051%positive;356856299567174383%positive;1212666493260527%positive;321809154152321529%positive;4709410501563%positive;22303518401483503%positive;75791334363887%positive;21270083729%positive;321809154152691615%positive;314652164210283247%positive;4709410132923%positive;87122262979065%positive;321809154152322975%positive;356856298812199663%positive;1212665738285807%positive;19665759941677807%positive;356852788753166841%positive;4910418007839%positive;314652163455308527%positive;356852788752798201%positive;356852788753168287%positive]]
  | StD => [HMeas MLeft 48 [(314652163455309742%positive,2);(78566688125433%positive,1);(321809154152690169%positive,1);(356856299567175418%positive,2);(22303518401484538%positive,2);(75791334364922%positive,2);(321809154152321529%positive,1);(314652164210284282%positive,0);(21270083729%positive,1);(1212665738286842%positive,2);(1172076690%positive,0);(19665759941678842%positive,0);(1212666493261562%positive,2);(356856298812200698%positive,2);(87122262979065%positive,1);(356856299567175598%positive,2);(22303518401484718%positive,2);(75791334365102%positive,2);(314652163455309562%positive,0);(356852788753166841%positive,1);(314652164210284462%positive,2);(356856298812200878%positive,2);(1212665738287022%positive,2);(19665759941679022%positive,2);(356852788752798201%positive,1);(1212666493261742%positive,2);(300075682094%positive,2)] [314652163455309742%positive;78566688125433%positive;321809154152690169%positive;356856299567175418%positive;22303518401484538%positive;75791334364922%positive;321809154152321529%positive;314652164210284282%positive;21270083729%positive;1212665738286842%positive;1172076690%positive;19665759941678842%positive;1212666493261562%positive;356856298812200698%positive;87122262979065%positive;356856299567175598%positive;22303518401484718%positive;75791334365102%positive;314652163455309562%positive;356852788753166841%positive;314652164210284462%positive;356856298812200878%positive;1212665738287022%positive;19665759941679022%positive;356852788752798201%positive;1212666493261742%positive;300075682094%positive]]
  end.

Lemma cqh_h_00199 : iqh tmq_h_00199.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00199 StA 23 2 2 48 20000
                lsetq_h_00199 rsetq_h_00199 certq_h_00199 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 48) 2000 tmq_h_00199); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition nghw_01 : list TM :=
  [tmq_h_00100;
   tmq_h_00101;
   tmq_h_00102;
   tmq_h_00103;
   tmq_h_00104;
   tmq_h_00105;
   tmq_h_00106;
   tmq_h_00107;
   tmq_h_00108;
   tmq_h_00109;
   tmq_h_00110;
   tmq_h_00111;
   tmq_h_00112;
   tmq_h_00113;
   tmq_h_00114;
   tmq_h_00115;
   tmq_h_00116;
   tmq_h_00117;
   tmq_h_00118;
   tmq_h_00119;
   tmq_h_00120;
   tmq_h_00121;
   tmq_h_00122;
   tmq_h_00123;
   tmq_h_00124;
   tmq_h_00125;
   tmq_h_00126;
   tmq_h_00127;
   tmq_h_00128;
   tmq_h_00129;
   tmq_h_00130;
   tmq_h_00131;
   tmq_h_00132;
   tmq_h_00133;
   tmq_h_00134;
   tmq_h_00135;
   tmq_h_00136;
   tmq_h_00137;
   tmq_h_00138;
   tmq_h_00139;
   tmq_h_00140;
   tmq_h_00141;
   tmq_h_00142;
   tmq_h_00143;
   tmq_h_00144;
   tmq_h_00145;
   tmq_h_00146;
   tmq_h_00147;
   tmq_h_00148;
   tmq_h_00149;
   tmq_h_00150;
   tmq_h_00151;
   tmq_h_00152;
   tmq_h_00153;
   tmq_h_00154;
   tmq_h_00155;
   tmq_h_00156;
   tmq_h_00157;
   tmq_h_00158;
   tmq_h_00159;
   tmq_h_00160;
   tmq_h_00161;
   tmq_h_00162;
   tmq_h_00163;
   tmq_h_00164;
   tmq_h_00165;
   tmq_h_00166;
   tmq_h_00167;
   tmq_h_00168;
   tmq_h_00169;
   tmq_h_00170;
   tmq_h_00171;
   tmq_h_00172;
   tmq_h_00173;
   tmq_h_00174;
   tmq_h_00175;
   tmq_h_00176;
   tmq_h_00177;
   tmq_h_00178;
   tmq_h_00179;
   tmq_h_00180;
   tmq_h_00181;
   tmq_h_00182;
   tmq_h_00183;
   tmq_h_00184;
   tmq_h_00185;
   tmq_h_00186;
   tmq_h_00187;
   tmq_h_00188;
   tmq_h_00189;
   tmq_h_00190;
   tmq_h_00191;
   tmq_h_00192;
   tmq_h_00193;
   tmq_h_00194;
   tmq_h_00195;
   tmq_h_00196;
   tmq_h_00197;
   tmq_h_00198;
   tmq_h_00199].

Lemma nghw_01_all : Forall iqh nghw_01.

Proof. unfold nghw_01. exact (Forall_cons _ cqh_h_00100 (Forall_cons _ cqh_h_00101 (Forall_cons _ cqh_h_00102 (Forall_cons _ cqh_h_00103 (Forall_cons _ cqh_h_00104 (Forall_cons _ cqh_h_00105 (Forall_cons _ cqh_h_00106 (Forall_cons _ cqh_h_00107 (Forall_cons _ cqh_h_00108 (Forall_cons _ cqh_h_00109 (Forall_cons _ cqh_h_00110 (Forall_cons _ cqh_h_00111 (Forall_cons _ cqh_h_00112 (Forall_cons _ cqh_h_00113 (Forall_cons _ cqh_h_00114 (Forall_cons _ cqh_h_00115 (Forall_cons _ cqh_h_00116 (Forall_cons _ cqh_h_00117 (Forall_cons _ cqh_h_00118 (Forall_cons _ cqh_h_00119 (Forall_cons _ cqh_h_00120 (Forall_cons _ cqh_h_00121 (Forall_cons _ cqh_h_00122 (Forall_cons _ cqh_h_00123 (Forall_cons _ cqh_h_00124 (Forall_cons _ cqh_h_00125 (Forall_cons _ cqh_h_00126 (Forall_cons _ cqh_h_00127 (Forall_cons _ cqh_h_00128 (Forall_cons _ cqh_h_00129 (Forall_cons _ cqh_h_00130 (Forall_cons _ cqh_h_00131 (Forall_cons _ cqh_h_00132 (Forall_cons _ cqh_h_00133 (Forall_cons _ cqh_h_00134 (Forall_cons _ cqh_h_00135 (Forall_cons _ cqh_h_00136 (Forall_cons _ cqh_h_00137 (Forall_cons _ cqh_h_00138 (Forall_cons _ cqh_h_00139 (Forall_cons _ cqh_h_00140 (Forall_cons _ cqh_h_00141 (Forall_cons _ cqh_h_00142 (Forall_cons _ cqh_h_00143 (Forall_cons _ cqh_h_00144 (Forall_cons _ cqh_h_00145 (Forall_cons _ cqh_h_00146 (Forall_cons _ cqh_h_00147 (Forall_cons _ cqh_h_00148 (Forall_cons _ cqh_h_00149 (Forall_cons _ cqh_h_00150 (Forall_cons _ cqh_h_00151 (Forall_cons _ cqh_h_00152 (Forall_cons _ cqh_h_00153 (Forall_cons _ cqh_h_00154 (Forall_cons _ cqh_h_00155 (Forall_cons _ cqh_h_00156 (Forall_cons _ cqh_h_00157 (Forall_cons _ cqh_h_00158 (Forall_cons _ cqh_h_00159 (Forall_cons _ cqh_h_00160 (Forall_cons _ cqh_h_00161 (Forall_cons _ cqh_h_00162 (Forall_cons _ cqh_h_00163 (Forall_cons _ cqh_h_00164 (Forall_cons _ cqh_h_00165 (Forall_cons _ cqh_h_00166 (Forall_cons _ cqh_h_00167 (Forall_cons _ cqh_h_00168 (Forall_cons _ cqh_h_00169 (Forall_cons _ cqh_h_00170 (Forall_cons _ cqh_h_00171 (Forall_cons _ cqh_h_00172 (Forall_cons _ cqh_h_00173 (Forall_cons _ cqh_h_00174 (Forall_cons _ cqh_h_00175 (Forall_cons _ cqh_h_00176 (Forall_cons _ cqh_h_00177 (Forall_cons _ cqh_h_00178 (Forall_cons _ cqh_h_00179 (Forall_cons _ cqh_h_00180 (Forall_cons _ cqh_h_00181 (Forall_cons _ cqh_h_00182 (Forall_cons _ cqh_h_00183 (Forall_cons _ cqh_h_00184 (Forall_cons _ cqh_h_00185 (Forall_cons _ cqh_h_00186 (Forall_cons _ cqh_h_00187 (Forall_cons _ cqh_h_00188 (Forall_cons _ cqh_h_00189 (Forall_cons _ cqh_h_00190 (Forall_cons _ cqh_h_00191 (Forall_cons _ cqh_h_00192 (Forall_cons _ cqh_h_00193 (Forall_cons _ cqh_h_00194 (Forall_cons _ cqh_h_00195 (Forall_cons _ cqh_h_00196 (Forall_cons _ cqh_h_00197 (Forall_cons _ cqh_h_00198 (Forall_cons _ cqh_h_00199 (Forall_nil iqh))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))). Qed.
