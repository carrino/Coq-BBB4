(* UNTRUSTED-generated R_QH tier; the Coq kernel re-checks via vm_compute. *)
From Coq Require Import List ZArith Lia.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import NGram NGramHist NGramHistWrap.
From BBB4.Census Require Import TNF_QH.
Import ListNotations.

Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.


Definition tmq_h_00400 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => Some (mkTrans S0 DL StB)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S0 DR StA)
  end.

Definition lsetq_h_00400 : hgset :=
  [[(S0,[]);(S0,[])]].

Definition rsetq_h_00400 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StA,S1);(StA,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StA,S1);(StA,S0)]);(S1,[(StC,S0);(StB,S1)])];
   [(S1,[(StA,S1);(StA,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S1,[(StA,S1);(StD,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StA,S1);(StD,S0)]);(S1,[(StD,S0);(StD,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0);(StD,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StC,S0);(StB,S1)]);(S1,[(StB,S0);(StD,S1)])];
   [(S1,[(StC,S0);(StD,S1)]);(S1,[(StA,S1);(StD,S0)])];
   [(S1,[(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0)]);(S1,[(StD,S0);(StB,S1)])];
   [(S1,[(StD,S0);(StB,S1)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StA,S1);(StA,S0)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S0);(StB,S1)])];
   [(S1,[(StD,S0);(StD,S1)]);(S1,[(StD,S0);(StB,S1)])]].

Definition certq_h_00400 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => []
  | StC => []
  | StD => []
  end.

Lemma cqh_h_00400 : iqh tmq_h_00400.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00400 StA 1161 2 2 1186 20000
                lsetq_h_00400 rsetq_h_00400 certq_h_00400 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 1186) 2000 tmq_h_00400); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00401 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StA)
  end.

Definition lsetq_h_00401 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition rsetq_h_00401 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition certq_h_00401 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 37 [(347849918707528158%positive,1);(323514222544615102%positive,1);(1334049735266782%positive,1);(75285048259563%positive,1);(323514226923467755%positive,1);(323511130168161982%positive,1);(4705315516222%positive,1);(323511134547014635%positive,1);(1358788746891742%positive,1);(323514222544614379%positive,1);(4936435274410%positive,1);(19087145909481950%positive,1);(323511130168161259%positive,1);(341516731731538398%positive,1);(4936388088490%positive,0);(18416111347%positive,1);(74559165649374%positive,1);(323514226923468478%positive,1);(323511134547015358%positive,1);(75289427112939%positive,1);(4705589194558%positive,1)] [1334049735266782%positive;347849918707528158%positive;323514222544615102%positive;323514226923467755%positive;75285048259563%positive;323511130168161982%positive;323511134547014635%positive;4705315516222%positive;1358788746891742%positive;323514222544614379%positive;4936435274410%positive;19087145909481950%positive;323511130168161259%positive;341516731731538398%positive;4936388088490%positive;18416111347%positive;74559165649374%positive;323514226923468478%positive;323511134547015358%positive;75289427112939%positive;4705589194558%positive]]
  | StC => [HMeas MRight 37 [(19087145909482985%positive,0);(75285048259563%positive,1);(323514226923467755%positive,1);(1149729265%positive,0);(347849918707529373%positive,2);(294330785565%positive,2);(323511134547014635%positive,1);(74559165650589%positive,2);(1334049735267997%positive,2);(341516731731539433%positive,0);(323514222544614379%positive,1);(1358788746892777%positive,2);(323511130168161259%positive,1);(19087145909483165%positive,2);(18416111347%positive,1);(347849918707529193%positive,0);(74559165650409%positive,2);(75289427112939%positive,1);(1334049735267817%positive,2);(341516731731539613%positive,2);(1358788746892957%positive,2)] [19087145909482985%positive;75285048259563%positive;323514226923467755%positive;1149729265%positive;347849918707529373%positive;294330785565%positive;323511134547014635%positive;74559165650589%positive;1334049735267997%positive;341516731731539433%positive;323514222544614379%positive;1358788746892777%positive;323511130168161259%positive;19087145909483165%positive;18416111347%positive;347849918707529193%positive;74559165650409%positive;75289427112939%positive;1334049735267817%positive;341516731731539613%positive;1358788746892957%positive]]
  | StD => [HMeas MLeft 37 [(347849918707528158%positive,4);(19087145909482985%positive,4);(323514222544615102%positive,4);(1334049735266782%positive,4);(1149729265%positive,4);(323511130168161982%positive,4);(347849918707529373%positive,4);(294330785565%positive,4);(4705315516222%positive,4);(74559165650589%positive,0);(1334049735267997%positive,0);(341516731731539433%positive,4);(1358788746891742%positive,4);(4936435274410%positive,1);(1358788746892777%positive,2);(19087145909481950%positive,4);(341516731731538398%positive,4);(4936388088490%positive,3);(19087145909483165%positive,4);(347849918707529193%positive,4);(74559165649374%positive,4);(323514226923468478%positive,4);(74559165650409%positive,2);(323511134547015358%positive,4);(1334049735267817%positive,2);(4705589194558%positive,4);(341516731731539613%positive,4);(1358788746892957%positive,0)] [1334049735266782%positive;19087145909482985%positive;323514222544615102%positive;347849918707528158%positive;1149729265%positive;323511130168161982%positive;347849918707529373%positive;294330785565%positive;4705315516222%positive;74559165650589%positive;1334049735267997%positive;341516731731539433%positive;1358788746891742%positive;4936435274410%positive;19087145909481950%positive;1358788746892777%positive;341516731731538398%positive;4936388088490%positive;19087145909483165%positive;347849918707529193%positive;74559165649374%positive;323514226923468478%positive;74559165650409%positive;323511134547015358%positive;1334049735267817%positive;4705589194558%positive;341516731731539613%positive;1358788746892957%positive]]
  end.

Lemma cqh_h_00401 : iqh tmq_h_00401.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00401 StA 8 2 2 33 20000
                lsetq_h_00401 rsetq_h_00401 certq_h_00401 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 33) 2000 tmq_h_00401); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00402 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StA)
  | StC, S1 => Some (mkTrans S0 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Definition lsetq_h_00402 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)])]].

Definition rsetq_h_00402 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00402 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(96506244151734932528823967%positive,0);(395289576045616243870191315455%positive,0);(395289576045508157479134423551%positive,0);(1272356869486641675967%positive,0);(86815892754912382467697151%positive,0);(356478221541895532295539301886%positive,1);(356478221541895532089555020255%positive,0);(395284740351525128597623269855%positive,0);(395289576045616244011751088126%positive,1);(5439425987881799326886367%positive,0);(86815892718883795727810207%positive,0);(6031566472647875933759967%positive,0);(5752220401271370238%positive,1);(79524556147012878315%positive,1);(75385173311315%positive,2);(309059144859841534%positive,3);(395284740351525128803607551486%positive,1);(86815892646826132970577918%positive,1);(86815892646825991410805247%positive,0);(87030815806108789221268990%positive,1);(22469610942466335%positive,0);(395289576045508157620694196222%positive,1);(19316196576851263%positive,0);(1272356869692626299902%positive,1);(96505063562366014931246590%positive,1);(395289576045580215283451559583%positive,0);(86815892754912524027469822%positive,1)]]
  | StC => [HMeas MLeft 45 [(356478221541823474632781987485%positive,1);(5485676198033%positive,0);(395289551557455399771264122857%positive,0);(92035520718772838377%positive,0);(96506244151734932528823967%positive,1);(86890067004746519077322729%positive,0);(395289576045616243870191315455%positive,1);(395289576045508157479134423551%positive,1);(1472550408361321037469%positive,1);(1272356869486641675967%positive,1);(20364736985982012145641%positive,0);(395284740351453071140850237085%positive,1);(5439425987881799326886367%positive,1);(356478221541895532089555020255%positive,1);(356478197192193354998930857961%positive,0);(86815892718883795727810207%positive,1);(79524556147012878315%positive,0);(86890067112832910134214633%positive,0);(6031566472647875933759967%positive,1);(395284740351525128597623269855%positive,1);(395284716001822951506999107561%positive,0);(87030809861357281091903465%positive,0);(22469610942466335%positive,1);(356478221541931561023838879389%positive,1);(19316196576851263%positive,1);(395289551557563486162321014761%positive,0);(395289576045580215283451559583%positive,1);(395284740351561157531907128989%positive,1);(75385173311315%positive,1);(96505057617614506801881065%positive,0);(86815892646825991410805247%positive,1);(86815892754912382467697151%positive,1)] [356478221541823474632781987485%positive;5485676198033%positive;395289551557455399771264122857%positive;92035520718772838377%positive;96506244151734932528823967%positive;86890067004746519077322729%positive;395289576045616243870191315455%positive;395289576045508157479134423551%positive;1472550408361321037469%positive;1272356869486641675967%positive;20364736985982012145641%positive;356478197192193354998930857961%positive;395284740351453071140850237085%positive;5439425987881799326886367%positive;356478221541895532089555020255%positive;86815892718883795727810207%positive;79524556147012878315%positive;86890067112832910134214633%positive;6031566472647875933759967%positive;395284740351525128597623269855%positive;395284716001822951506999107561%positive;87030809861357281091903465%positive;22469610942466335%positive;356478221541931561023838879389%positive;19316196576851263%positive;395289551557563486162321014761%positive;395289576045580215283451559583%positive;395284740351561157531907128989%positive;75385173311315%positive;96505057617614506801881065%positive;86815892646825991410805247%positive;86815892754912382467697151%positive]]
  | StD => [HRank [(356478221541823474632781987485%positive,0);(5752220401271370238%positive,0);(5485676198033%positive,1);(356478221541895532295539301886%positive,0);(395284740351525128803607551486%positive,0);(395289551557455399771264122857%positive,1);(87030815806108789221268990%positive,0);(96505063562366014931246590%positive,0);(92035520718772838377%positive,1);(1272356869692626299902%positive,0);(86890067004746519077322729%positive,1);(1472550408361321037469%positive,0);(309059144859841534%positive,0);(20364736985982012145641%positive,1);(395289576045616244011751088126%positive,0);(395284740351453071140850237085%positive,0);(86815892754912524027469822%positive,0);(356478197192193354998930857961%positive,1);(86890067112832910134214633%positive,1);(86815892646826132970577918%positive,0);(395284716001822951506999107561%positive,1);(87030809861357281091903465%positive,1);(356478221541931561023838879389%positive,0);(395289576045508157620694196222%positive,0);(395289551557563486162321014761%positive,1);(395284740351561157531907128989%positive,0);(96505057617614506801881065%positive,1)]]
  end.

Lemma cqh_h_00402 : iqh tmq_h_00402.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00402 StA 3 4 2 28 20000
                lsetq_h_00402 rsetq_h_00402 certq_h_00402 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00402); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00403 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StB)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S0 DL StA)
  end.

Definition lsetq_h_00403 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition rsetq_h_00403 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S1,[(StA,S1);(StA,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StA,S1);(StA,S0)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition certq_h_00403 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 48 [(18468129719931358%positive,1);(312234334099559403%positive,1);(295490079825023454%positive,1);(19067385031905758%positive,1);(348966818560669374%positive,1);(305078164816613854%positive,1);(1207992429007326%positive,1);(76229085033451%positive,1);(85196976747499%positive,1);(4764317814590%positive,1);(5324811046718%positive,1);(306037211687506602%positive,0);(4711490319018%positive,1);(295490080579998174%positive,1);(312234334099928766%positive,1);(1207991674032606%positive,1);(312234334099928043%positive,1);(20800043155%positive,1);(348966818560668651%positive,1);(305078165571588574%positive,1);(312234334099560126%positive,1);(348966818560300734%positive,1);(348966818560300011%positive,1);(4711489950378%positive,0);(306037211687875242%positive,1);(75499210494430%positive,1)] [18468129719931358%positive;295490079825023454%positive;312234334099559403%positive;19067385031905758%positive;348966818560669374%positive;305078164816613854%positive;1207992429007326%positive;76229085033451%positive;85196976747499%positive;4764317814590%positive;5324811046718%positive;306037211687506602%positive;4711490319018%positive;295490080579998174%positive;312234334099928766%positive;1207991674032606%positive;312234334099928043%positive;20800043155%positive;348966818560668651%positive;305078165571588574%positive;312234334099560126%positive;348966818560300734%positive;348966818560300011%positive;4711489950378%positive;306037211687875242%positive;75499210494430%positive]]
  | StC => [HMeas MLeft 48 [(1136457873%positive,0);(295490080579999389%positive,2);(75499210495645%positive,2);(1207991674033821%positive,2);(1207992429008361%positive,2);(19067385031906793%positive,0);(305078165571589789%positive,2);(312234334099559403%positive,1);(295490079825024669%positive,2);(290945206557%positive,2);(76229085033451%positive,1);(85196976747499%positive,1);(18468129719932573%positive,2);(295490080579999209%positive,2);(75499210495465%positive,2);(1207991674033641%positive,2);(19067385031906973%positive,2);(305078165571589609%positive,0);(305078164816615069%positive,2);(295490079825024489%positive,2);(18468129719932393%positive,2);(312234334099928043%positive,1);(20800043155%positive,1);(348966818560668651%positive,1);(305078164816614889%positive,0);(1207992429008541%positive,2);(348966818560300011%positive,1)] [295490080579999389%positive;1136457873%positive;75499210495645%positive;1207991674033821%positive;1207992429008361%positive;305078165571589789%positive;19067385031906793%positive;312234334099559403%positive;295490079825024669%positive;290945206557%positive;76229085033451%positive;85196976747499%positive;18468129719932573%positive;295490080579999209%positive;75499210495465%positive;1207991674033641%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;295490079825024489%positive;18468129719932393%positive;312234334099928043%positive;20800043155%positive;348966818560668651%positive;305078164816614889%positive;1207992429008541%positive;348966818560300011%positive]]
  | StD => [HMeas MRight 48 [(1136457873%positive,4);(295490080579999389%positive,0);(75499210495645%positive,0);(1207991674033821%positive,0);(1207992429008361%positive,2);(18468129719931358%positive,4);(19067385031906793%positive,4);(305078165571589789%positive,4);(295490079825023454%positive,4);(19067385031905758%positive,4);(348966818560669374%positive,4);(295490079825024669%positive,0);(305078164816613854%positive,4);(290945206557%positive,4);(1207992429007326%positive,4);(4764317814590%positive,4);(5324811046718%positive,4);(306037211687506602%positive,3);(4711490319018%positive,1);(295490080579998174%positive,4);(18468129719932573%positive,0);(295490080579999209%positive,2);(312234334099928766%positive,4);(75499210495465%positive,2);(1207991674033641%positive,2);(19067385031906973%positive,4);(305078165571589609%positive,4);(305078164816615069%positive,4);(1207991674032606%positive,4);(295490079825024489%positive,2);(18468129719932393%positive,2);(305078164816614889%positive,4);(305078165571588574%positive,4);(1207992429008541%positive,0);(312234334099560126%positive,4);(348966818560300734%positive,4);(4711489950378%positive,3);(306037211687875242%positive,1);(75499210494430%positive,4)] [295490080579999389%positive;1136457873%positive;75499210495645%positive;1207991674033821%positive;1207992429008361%positive;18468129719931358%positive;305078165571589789%positive;19067385031906793%positive;295490079825023454%positive;19067385031905758%positive;348966818560669374%positive;295490079825024669%positive;305078164816613854%positive;290945206557%positive;1207992429007326%positive;4764317814590%positive;5324811046718%positive;306037211687506602%positive;4711490319018%positive;295490080579998174%positive;18468129719932573%positive;295490080579999209%positive;312234334099928766%positive;75499210495465%positive;1207991674033641%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;1207991674032606%positive;295490079825024489%positive;18468129719932393%positive;305078164816614889%positive;305078165571588574%positive;1207992429008541%positive;312234334099560126%positive;348966818560300734%positive;4711489950378%positive;306037211687875242%positive;75499210494430%positive]]
  end.

Lemma cqh_h_00403 : iqh tmq_h_00403.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00403 StA 13 2 2 38 20000
                lsetq_h_00403 rsetq_h_00403 certq_h_00403 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 38) 2000 tmq_h_00403); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00404 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StB)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S0 DR StA)
  end.

Definition lsetq_h_00404 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition rsetq_h_00404 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S1,[(StA,S1);(StB,S1)])];
   [(S1,[(StA,S1);(StB,S1)]);(S0,[(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition certq_h_00404 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 37 [(19517675628614314%positive,0);(21282879487037918%positive,1);(312234334099559403%positive,1);(340526076098728414%positive,1);(19067385031905758%positive,1);(348966818560669374%positive,1);(305078164816613854%positive,1);(76229085033451%positive,1);(85196976747499%positive,1);(4764317814590%positive,1);(5324811046718%positive,1);(340526076853703134%positive,1);(312234334099928766%positive,1);(19517675628982954%positive,1);(312234334099928043%positive,1);(20800043155%positive,1);(348966818560668651%positive,1);(305078165571588574%positive,1);(312234334099560126%positive,1);(348966818560300734%positive,1);(348966818560300011%positive,1)] [19517675628614314%positive;21282879487037918%positive;312234334099559403%positive;340526076098728414%positive;19067385031905758%positive;348966818560669374%positive;305078164816613854%positive;76229085033451%positive;85196976747499%positive;4764317814590%positive;5324811046718%positive;340526076853703134%positive;312234334099928766%positive;19517675628982954%positive;312234334099928043%positive;20800043155%positive;348966818560668651%positive;305078165571588574%positive;312234334099560126%positive;348966818560300734%positive;348966818560300011%positive]]
  | StC => [HMeas MLeft 37 [(1136457873%positive,0);(21282879487038953%positive,2);(340526076853704349%positive,2);(19067385031906793%positive,0);(312234334099559403%positive,1);(305078165571589789%positive,2);(290945206557%positive,2);(76229085033451%positive,1);(85196976747499%positive,1);(340526076098729629%positive,2);(21282879487039133%positive,2);(340526076853704169%positive,2);(19067385031906973%positive,2);(305078165571589609%positive,0);(305078164816615069%positive,2);(312234334099928043%positive,1);(340526076098729449%positive,2);(20800043155%positive,1);(348966818560668651%positive,1);(305078164816614889%positive,0);(348966818560300011%positive,1)] [1136457873%positive;21282879487038953%positive;340526076853704349%positive;305078165571589789%positive;19067385031906793%positive;312234334099559403%positive;290945206557%positive;76229085033451%positive;85196976747499%positive;340526076098729629%positive;21282879487039133%positive;340526076853704169%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;312234334099928043%positive;340526076098729449%positive;20800043155%positive;348966818560668651%positive;305078164816614889%positive;348966818560300011%positive]]
  | StD => [HMeas MRight 37 [(19517675628614314%positive,3);(1136457873%positive,4);(21282879487038953%positive,2);(340526076853704349%positive,0);(19067385031906793%positive,4);(21282879487037918%positive,4);(305078165571589789%positive,4);(340526076098728414%positive,4);(19067385031905758%positive,4);(348966818560669374%positive,4);(305078164816613854%positive,4);(290945206557%positive,4);(4764317814590%positive,4);(5324811046718%positive,4);(340526076853703134%positive,4);(312234334099928766%positive,4);(19517675628982954%positive,1);(340526076098729629%positive,0);(21282879487039133%positive,0);(340526076853704169%positive,2);(19067385031906973%positive,4);(305078165571589609%positive,4);(305078164816615069%positive,4);(340526076098729449%positive,2);(305078164816614889%positive,4);(305078165571588574%positive,4);(312234334099560126%positive,4);(348966818560300734%positive,4)] [19517675628614314%positive;1136457873%positive;21282879487038953%positive;340526076853704349%positive;305078165571589789%positive;19067385031906793%positive;21282879487037918%positive;340526076098728414%positive;19067385031905758%positive;348966818560669374%positive;305078164816613854%positive;290945206557%positive;4764317814590%positive;5324811046718%positive;340526076853703134%positive;312234334099928766%positive;19517675628982954%positive;340526076098729629%positive;21282879487039133%positive;340526076853704169%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;340526076098729449%positive;305078164816614889%positive;305078165571588574%positive;312234334099560126%positive;348966818560300734%positive]]
  end.

Lemma cqh_h_00404 : iqh tmq_h_00404.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00404 StA 5 2 2 30 20000
                lsetq_h_00404 rsetq_h_00404 certq_h_00404 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 30) 2000 tmq_h_00404); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00405 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StB)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S1 DR StA)
  end.

Definition lsetq_h_00405 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition rsetq_h_00405 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition certq_h_00405 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 37 [(312234334099559403%positive,1);(19067385031905758%positive,1);(348966818560669374%positive,1);(305078164816613854%positive,1);(1207992429007326%positive,1);(76229085033451%positive,1);(85196976747499%positive,1);(4764317814590%positive,1);(5324811046718%positive,1);(4711490319018%positive,1);(312234334099928766%positive,1);(1207991674032606%positive,1);(312234334099928043%positive,1);(20800043155%positive,1);(348966818560668651%positive,1);(305078165571588574%positive,1);(312234334099560126%positive,1);(348966818560300734%positive,1);(348966818560300011%positive,1);(4711489950378%positive,0);(75499210494430%positive,1)] [312234334099559403%positive;19067385031905758%positive;348966818560669374%positive;305078164816613854%positive;1207992429007326%positive;76229085033451%positive;85196976747499%positive;4764317814590%positive;5324811046718%positive;4711490319018%positive;312234334099928766%positive;1207991674032606%positive;312234334099928043%positive;20800043155%positive;348966818560668651%positive;305078165571588574%positive;312234334099560126%positive;348966818560300734%positive;348966818560300011%positive;4711489950378%positive;75499210494430%positive]]
  | StC => [HMeas MLeft 37 [(1136457873%positive,0);(75499210495645%positive,2);(1207991674033821%positive,2);(1207992429008361%positive,2);(19067385031906793%positive,0);(305078165571589789%positive,2);(312234334099559403%positive,1);(290945206557%positive,2);(76229085033451%positive,1);(85196976747499%positive,1);(75499210495465%positive,2);(1207991674033641%positive,2);(19067385031906973%positive,2);(305078165571589609%positive,0);(305078164816615069%positive,2);(312234334099928043%positive,1);(20800043155%positive,1);(348966818560668651%positive,1);(305078164816614889%positive,0);(1207992429008541%positive,2);(348966818560300011%positive,1)] [1136457873%positive;75499210495645%positive;1207991674033821%positive;1207992429008361%positive;305078165571589789%positive;19067385031906793%positive;312234334099559403%positive;290945206557%positive;76229085033451%positive;85196976747499%positive;75499210495465%positive;1207991674033641%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;312234334099928043%positive;20800043155%positive;348966818560668651%positive;305078164816614889%positive;1207992429008541%positive;348966818560300011%positive]]
  | StD => [HMeas MRight 37 [(1136457873%positive,4);(75499210495645%positive,0);(1207991674033821%positive,0);(1207992429008361%positive,2);(19067385031906793%positive,4);(305078165571589789%positive,4);(19067385031905758%positive,4);(348966818560669374%positive,4);(305078164816613854%positive,4);(290945206557%positive,4);(1207992429007326%positive,4);(4764317814590%positive,4);(5324811046718%positive,4);(4711490319018%positive,1);(312234334099928766%positive,4);(75499210495465%positive,2);(1207991674033641%positive,2);(19067385031906973%positive,4);(305078165571589609%positive,4);(305078164816615069%positive,4);(1207991674032606%positive,4);(305078164816614889%positive,4);(305078165571588574%positive,4);(1207992429008541%positive,0);(312234334099560126%positive,4);(348966818560300734%positive,4);(4711489950378%positive,3);(75499210494430%positive,4)] [1136457873%positive;75499210495645%positive;1207991674033821%positive;1207992429008361%positive;305078165571589789%positive;19067385031906793%positive;19067385031905758%positive;348966818560669374%positive;305078164816613854%positive;290945206557%positive;1207992429007326%positive;4764317814590%positive;5324811046718%positive;4711490319018%positive;312234334099928766%positive;75499210495465%positive;1207991674033641%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;1207991674032606%positive;305078164816614889%positive;305078165571588574%positive;1207992429008541%positive;312234334099560126%positive;348966818560300734%positive;4711489950378%positive;75499210494430%positive]]
  end.

Lemma cqh_h_00405 : iqh tmq_h_00405.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00405 StA 5 2 2 30 20000
                lsetq_h_00405 rsetq_h_00405 certq_h_00405 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 30) 2000 tmq_h_00405); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00406 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S0 DL StA)
  end.

Definition lsetq_h_00406 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition rsetq_h_00406 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S1,[(StA,S1);(StA,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StC,S0)])];
   [(S1,[(StA,S1);(StA,S0)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition certq_h_00406 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 35 [(295490077678957547%positive,0);(312255777477710302%positive,2);(295490077678589630%positive,2);(19067385031905758%positive,2);(348966818560669374%positive,2);(305078164816613854%positive,2);(85196976747499%positive,2);(5324811046718%positive,2);(312255776722735582%positive,2);(295490077678588907%positive,0);(295490077678958270%positive,2);(306037214588916394%positive,1);(19515985776038366%positive,2);(20800043155%positive,2);(348966818560668651%positive,2);(306037213833941674%positive,1);(305078165571588574%positive,2);(348966818560300734%positive,2);(348966818560300011%positive,2)] [295490077678957547%positive;312255777477710302%positive;295490077678589630%positive;19067385031905758%positive;348966818560669374%positive;305078164816613854%positive;85196976747499%positive;5324811046718%positive;312255776722735582%positive;295490077678588907%positive;295490077678958270%positive;306037214588916394%positive;19515985776038366%positive;20800043155%positive;348966818560668651%positive;306037213833941674%positive;305078165571588574%positive;348966818560300734%positive;348966818560300011%positive]]
  | StC => [HMeas MLeft 35 [(1136457873%positive,0);(295490077678957547%positive,2);(19067385031906793%positive,0);(305078165571589789%positive,2);(312255776722736617%positive,1);(19515985776039401%positive,1);(312255777477711517%positive,2);(290945206557%positive,2);(85196976747499%positive,1);(295490077678588907%positive,2);(19067385031906973%positive,2);(305078165571589609%positive,0);(305078164816615069%positive,2);(20800043155%positive,1);(348966818560668651%positive,1);(312255776722736797%positive,2);(19515985776039581%positive,2);(312255777477711337%positive,1);(305078164816614889%positive,0);(348966818560300011%positive,1)] [1136457873%positive;295490077678957547%positive;305078165571589789%positive;19067385031906793%positive;312255776722736617%positive;19515985776039401%positive;312255777477711517%positive;290945206557%positive;85196976747499%positive;295490077678588907%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;20800043155%positive;348966818560668651%positive;312255776722736797%positive;19515985776039581%positive;312255777477711337%positive;305078164816614889%positive;348966818560300011%positive]]
  | StD => [HMeas MRight 35 [(1136457873%positive,1);(312255777477710302%positive,1);(295490077678589630%positive,1);(19067385031906793%positive,1);(305078165571589789%positive,1);(19067385031905758%positive,1);(348966818560669374%positive,1);(312255776722736617%positive,1);(305078164816613854%positive,1);(19515985776039401%positive,1);(312255777477711517%positive,1);(290945206557%positive,1);(5324811046718%positive,1);(312255776722735582%positive,1);(295490077678958270%positive,1);(306037214588916394%positive,0);(19067385031906973%positive,1);(305078165571589609%positive,1);(305078164816615069%positive,1);(19515985776038366%positive,1);(306037213833941674%positive,0);(312255776722736797%positive,1);(19515985776039581%positive,1);(312255777477711337%positive,1);(305078164816614889%positive,1);(305078165571588574%positive,1);(348966818560300734%positive,1)] [1136457873%positive;312255777477710302%positive;295490077678589630%positive;305078165571589789%positive;19067385031906793%positive;19067385031905758%positive;348966818560669374%positive;312255776722736617%positive;305078164816613854%positive;19515985776039401%positive;312255777477711517%positive;290945206557%positive;5324811046718%positive;312255776722735582%positive;295490077678958270%positive;306037214588916394%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;19515985776038366%positive;306037213833941674%positive;312255776722736797%positive;19515985776039581%positive;312255777477711337%positive;305078164816614889%positive;305078165571588574%positive;348966818560300734%positive]]
  end.

Lemma cqh_h_00406 : iqh tmq_h_00406.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00406 StA 4 2 2 29 20000
                lsetq_h_00406 rsetq_h_00406 certq_h_00406 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00406); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00407 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00407 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition rsetq_h_00407 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S1,[(StA,S1);(StA,S0)])];
   [(S1,[(StA,S1);(StA,S0)]);(S1,[(StD,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StD,S1);(StB,S0)]);(S0,[(StC,S0)])]].

Definition certq_h_00407 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 35 [(295490077678957547%positive,0);(312255777477710302%positive,2);(295490077678589630%positive,2);(19067385031905758%positive,2);(348966818560669374%positive,2);(305078164816613854%positive,2);(85196976747499%positive,2);(5324811046718%positive,2);(312255776722735582%positive,2);(295490077678588907%positive,0);(295490077678958270%positive,2);(306177952077271722%positive,1);(19515985776038366%positive,2);(20800043155%positive,2);(348966818560668651%positive,2);(306177951322297002%positive,1);(305078165571588574%positive,2);(348966818560300734%positive,2);(348966818560300011%positive,2)] [295490077678957547%positive;312255777477710302%positive;295490077678589630%positive;19067385031905758%positive;348966818560669374%positive;305078164816613854%positive;85196976747499%positive;5324811046718%positive;312255776722735582%positive;295490077678588907%positive;295490077678958270%positive;306177952077271722%positive;19515985776038366%positive;20800043155%positive;348966818560668651%positive;306177951322297002%positive;305078165571588574%positive;348966818560300734%positive;348966818560300011%positive]]
  | StC => [HMeas MLeft 35 [(1136457873%positive,0);(295490077678957547%positive,2);(19067385031906793%positive,0);(305078165571589789%positive,2);(312255776722736617%positive,1);(19515985776039401%positive,1);(312255777477711517%positive,2);(290945206557%positive,2);(85196976747499%positive,1);(295490077678588907%positive,2);(19067385031906973%positive,2);(305078165571589609%positive,0);(305078164816615069%positive,2);(20800043155%positive,1);(348966818560668651%positive,1);(312255776722736797%positive,2);(19515985776039581%positive,2);(312255777477711337%positive,1);(305078164816614889%positive,0);(348966818560300011%positive,1)] [1136457873%positive;295490077678957547%positive;305078165571589789%positive;19067385031906793%positive;312255776722736617%positive;19515985776039401%positive;312255777477711517%positive;290945206557%positive;85196976747499%positive;295490077678588907%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;20800043155%positive;348966818560668651%positive;312255776722736797%positive;19515985776039581%positive;312255777477711337%positive;305078164816614889%positive;348966818560300011%positive]]
  | StD => [HMeas MRight 35 [(1136457873%positive,1);(312255777477710302%positive,1);(295490077678589630%positive,1);(19067385031906793%positive,1);(305078165571589789%positive,1);(19067385031905758%positive,1);(348966818560669374%positive,1);(312255776722736617%positive,1);(305078164816613854%positive,1);(19515985776039401%positive,1);(312255777477711517%positive,1);(290945206557%positive,1);(5324811046718%positive,1);(312255776722735582%positive,1);(295490077678958270%positive,1);(306177952077271722%positive,0);(19067385031906973%positive,1);(305078165571589609%positive,1);(305078164816615069%positive,1);(19515985776038366%positive,1);(306177951322297002%positive,0);(312255776722736797%positive,1);(19515985776039581%positive,1);(312255777477711337%positive,1);(305078164816614889%positive,1);(305078165571588574%positive,1);(348966818560300734%positive,1)] [1136457873%positive;312255777477710302%positive;295490077678589630%positive;305078165571589789%positive;19067385031906793%positive;19067385031905758%positive;348966818560669374%positive;312255776722736617%positive;305078164816613854%positive;19515985776039401%positive;312255777477711517%positive;290945206557%positive;5324811046718%positive;312255776722735582%positive;295490077678958270%positive;306177952077271722%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;19515985776038366%positive;306177951322297002%positive;312255776722736797%positive;19515985776039581%positive;312255777477711337%positive;305078164816614889%positive;305078165571588574%positive;348966818560300734%positive]]
  end.

Lemma cqh_h_00407 : iqh tmq_h_00407.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00407 StA 4 2 2 29 20000
                lsetq_h_00407 rsetq_h_00407 certq_h_00407 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00407); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00408 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => None
  | StC, S1 => Some (mkTrans S1 DL StA)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00408 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00408 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00408 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(87021360228470714673450968%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(22432227475556623%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;87021360228470714673450968%positive;1470091438291843874188%positive;19316178314849599%positive;356439534661271177744046610639%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;22432227475556623%positive;6021494531243055068469455%positive;394624665599546797399408639372%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(1470091438291843874188%positive,0);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00408 : iqh tmq_h_00408.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00408 StC 2 4 2 27 20000
                lsetq_h_00408 rsetq_h_00408 certq_h_00408 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 27) 2000 tmq_h_00408); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00409 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00409 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00409 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00409 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(87021360228470714673450968%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(86815818841760494756813055%positive,1);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(96343901961465753030938584%positive,0);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(22432227475556623%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;87021360228470714673450968%positive;1470091438291843874188%positive;19316178314849599%positive;356439534661271177744046610639%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;86815818841760494756813055%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;96343901961465753030938584%positive;22432227475556623%positive;6021494531243055068469455%positive;394624665599546797399408639372%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(1470091438291843874188%positive,0);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00409 : iqh tmq_h_00409.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00409 StC 3 4 2 28 20000
                lsetq_h_00409 rsetq_h_00409 certq_h_00409 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00409); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00410 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StA)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00410 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00410 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00410 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(87021360228470714673450968%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(22432227475556623%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;87021360228470714673450968%positive;1470091438291843874188%positive;19316178314849599%positive;356439534661271177744046610639%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;22432227475556623%positive;6021494531243055068469455%positive;394624665599546797399408639372%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(1470091438291843874188%positive,0);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00410 : iqh tmq_h_00410.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00410 StC 4 4 2 29 20000
                lsetq_h_00410 rsetq_h_00410 certq_h_00410 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00410); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00411 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00411 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00411 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00411 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(87021360228470714673450968%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(86815818841760494756813055%positive,1);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(96343901961465753030938584%positive,0);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(22432227475556623%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;87021360228470714673450968%positive;1470091438291843874188%positive;19316178314849599%positive;356439534661271177744046610639%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;86815818841760494756813055%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;96343901961465753030938584%positive;22432227475556623%positive;6021494531243055068469455%positive;394624665599546797399408639372%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(1470091438291843874188%positive,0);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00411 : iqh tmq_h_00411.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00411 StC 3 4 2 28 20000
                lsetq_h_00411 rsetq_h_00411 certq_h_00411 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00411); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00412 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00412 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00412 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00412 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(87021360228470714673450968%positive,0);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(22432227475556623%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;87021360228470714673450968%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;394624665599546797399408639372%positive;6021494531243055068469455%positive;22432227475556623%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1470091438291843874188%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00412 : iqh tmq_h_00412.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00412 StC 3 4 2 28 20000
                lsetq_h_00412 rsetq_h_00412 certq_h_00412 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00412); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00413 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => Some (mkTrans S0 DL StB)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00413 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00413 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S0)]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0);(StB,S0)])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0);(StC,S1);(StA,S0)])];
   [(S1,[(StD,S0);(StC,S1);(StA,S0)]);(S0,[(StB,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00413 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(1305413045085364543550651791%positive,0);(20198752243211272896475%positive,1);(19298586137193755%positive,2);(1262016530043810933757%positive,3);(394624665599618854856315885775%positive,0);(356439534661271177744046610639%positive,0);(394631919140629427119174553597%positive,1);(20377426775253696563025271039%positive,0);(20377426775379797352591644927%positive,0);(1305413045139407492427012351%positive,0);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(5082354206907288127798719%positive,0);(20377426775379797496164618237%positive,1);(86815818913818335446826383%positive,0);(1272392823585272610779%positive,1);(1206161630953171%positive,2);(4944941644824124413%positive,3);(1305413045013306702860638463%positive,0);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(20198698199912973335999%positive,0);(1305413045013306846433611773%positive,1);(20377426775253696706598244349%positive,1);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(1305413045139407635999985661%positive,1);(86815818841760638329786365%positive,1);(309058853037593023%positive,0);(78876033131515547327%positive,0);(5082354206907528337939453%positive,1);(394631919140701484816291659151%positive,0);(20198698200153183476733%positive,1);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 72 [(96345683383942257474600335%positive,1);(81317674608928835040034776%positive,0);(1305486112566582809967263704%positive,0);(1305486112692683599533637592%positive,0);(20377426775253696563025271039%positive,1);(394624622434237722616174530520%positive,0);(87021360228470714673450968%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(1272392823585272610779%positive,0);(356439491495890045503905255384%positive,0);(323186469610832568631256%positive,0);(86815818967861284323186943%positive,1);(20377499842806972670131896280%positive,0);(20377499842933073459698270168%positive,0);(19298586137193755%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(20377426775379797352591644927%positive,1);(1305413045139407492427012351%positive,1);(356439534661325221076705738124%positive,1);(86815818841760494756813055%positive,1);(394624665599618854856315885775%positive,1);(1305413045085364543550651791%positive,1);(96343901961465753030938584%positive,0);(5082354206907288127798719%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(22432227475556623%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(20198698199912973335999%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(1305413045013306702860638463%positive,1);(309058853037593023%positive,1);(1206161630953171%positive,1);(394624665599672898188975013260%positive,1);(78876033131515547327%positive,1);(1272338780286973377983%positive,1);(20198752243211272896475%positive,0);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;81317674608928835040034776%positive;1305486112566582809967263704%positive;1305486112692683599533637592%positive;20377426775253696563025271039%positive;394624622434237722616174530520%positive;87021360228470714673450968%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;1272392823585272610779%positive;356439491495890045503905255384%positive;323186469610832568631256%positive;86815818967861284323186943%positive;20377499842806972670131896280%positive;20377499842933073459698270168%positive;19298586137193755%positive;5438835672930865171126479%positive;20364718896816569303000%positive;1305413045139407492427012351%positive;356439534661325221076705738124%positive;86815818841760494756813055%positive;394624665599618854856315885775%positive;1305413045085364543550651791%positive;96343901961465753030938584%positive;5082354206907288127798719%positive;394624665599546797399408639372%positive;75385102008019%positive;22432227475556623%positive;5476515575952%positive;6021494531243055068469455%positive;20198698199912973335999%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;78876033131515547327%positive;1305413045013306702860638463%positive;309058853037593023%positive;1206161630953171%positive;86888886395036601863438296%positive;394624665599672898188975013260%positive;20198752243211272896475%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;20377426775379797352591644927%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1262016530043810933757%positive,0);(81317674608928835040034776%positive,1);(20198698200153183476733%positive,0);(1305486112566582809967263704%positive,1);(1305486112692683599533637592%positive,1);(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(20377426775379797496164618237%positive,0);(4944941644824124413%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(20377426775253696706598244349%positive,0);(1305413045013306846433611773%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(1470091438291843874188%positive,0);(1305413045139407635999985661%positive,0);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(323186469610832568631256%positive,1);(5082354206907528337939453%positive,0);(20377499842806972670131896280%positive,1);(20377499842933073459698270168%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00413 : iqh tmq_h_00413.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00413 StC 4 4 2 29 20000
                lsetq_h_00413 rsetq_h_00413 certq_h_00413 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00413); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00414 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00414 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00414 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0);(StB,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00414 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(1305413045139407492427012351%positive,0);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818913818335446826383%positive,0);(1272392823585272610779%positive,1);(1206161630953171%positive,2);(4944941644824124413%positive,3);(1305413045013306702860638463%positive,0);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(20198698199912973335999%positive,0);(1305413045139407635999985661%positive,1);(86815818841760638329786365%positive,1);(309058853037593023%positive,0);(394631919140701484816291659151%positive,0);(20198698200153183476733%positive,1);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1);(1305413045013306846433611773%positive,1)]]
  | StB => [HMeas MLeft 58 [(96345683383942257474600335%positive,1);(1305486112566582809967263704%positive,0);(1305486112692683599533637592%positive,0);(394624622434237722616174530520%positive,0);(87021360228470714673450968%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(1272392823585272610779%positive,0);(356439491495890045503905255384%positive,0);(323186469610832568631256%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(1305413045139407492427012351%positive,1);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(22432227475556623%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(20198698199912973335999%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(86888886395036601863438296%positive,0);(309058853037593023%positive,1);(1206161630953171%positive,1);(1305413045013306702860638463%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;1305486112566582809967263704%positive;1305486112692683599533637592%positive;394624622434237722616174530520%positive;87021360228470714673450968%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;1272392823585272610779%positive;356439491495890045503905255384%positive;323186469610832568631256%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;1305413045139407492427012351%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;394624665599546797399408639372%positive;75385102008019%positive;22432227475556623%positive;5476515575952%positive;6021494531243055068469455%positive;394631919140755527765167954175%positive;20198698199912973335999%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;309058853037593023%positive;1305413045013306702860638463%positive;1206161630953171%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(20198698200153183476733%positive,0);(1305486112566582809967263704%positive,1);(1305486112692683599533637592%positive,1);(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(4944941644824124413%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1305413045013306846433611773%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(1470091438291843874188%positive,0);(1305413045139407635999985661%positive,0);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(323186469610832568631256%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(86888886395036601863438296%positive,1);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00414 : iqh tmq_h_00414.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00414 StC 3 4 2 28 20000
                lsetq_h_00414 rsetq_h_00414 certq_h_00414 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00414); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00415 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => Some (mkTrans S0 DR StB)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00415 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00415 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00415 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(87021360228470714673450968%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(22432227475556623%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;87021360228470714673450968%positive;1470091438291843874188%positive;19316178314849599%positive;356439534661271177744046610639%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;22432227475556623%positive;6021494531243055068469455%positive;394624665599546797399408639372%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(1470091438291843874188%positive,0);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00415 : iqh tmq_h_00415.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00415 StC 4 4 2 29 20000
                lsetq_h_00415 rsetq_h_00415 certq_h_00415 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00415); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00416 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00416 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00416 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00416 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(87021360228470714673450968%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(22432227475556623%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;87021360228470714673450968%positive;1470091438291843874188%positive;19316178314849599%positive;356439534661271177744046610639%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;22432227475556623%positive;6021494531243055068469455%positive;394624665599546797399408639372%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(1470091438291843874188%positive,0);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00416 : iqh tmq_h_00416.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00416 StC 3 4 2 28 20000
                lsetq_h_00416 rsetq_h_00416 certq_h_00416 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00416); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00417 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StB)
  | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00417 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00417 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00417 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(87021360228470714673450968%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(86815818841760494756813055%positive,1);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(96343901961465753030938584%positive,0);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(22432227475556623%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;87021360228470714673450968%positive;1470091438291843874188%positive;19316178314849599%positive;356439534661271177744046610639%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;86815818841760494756813055%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;96343901961465753030938584%positive;22432227475556623%positive;6021494531243055068469455%positive;394624665599546797399408639372%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(1470091438291843874188%positive,0);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00417 : iqh tmq_h_00417.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00417 StC 3 4 2 28 20000
                lsetq_h_00417 rsetq_h_00417 certq_h_00417 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00417); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00418 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00418 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00418 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00418 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(87021360228470714673450968%positive,0);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(22432227475556623%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;87021360228470714673450968%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;394624665599546797399408639372%positive;6021494531243055068469455%positive;22432227475556623%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1470091438291843874188%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00418 : iqh tmq_h_00418.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00418 StC 3 4 2 28 20000
                lsetq_h_00418 rsetq_h_00418 certq_h_00418 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00418); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00419 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00419 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00419 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00419 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(394631919140629426975601580287%positive,0);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818913818335446826383%positive,0);(1272392823585272610779%positive,1);(1206161630953171%positive,2);(4944941644824124413%positive,3);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(309058853037593023%positive,0);(20198698200153183476733%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 52 [(96345683383942257474600335%positive,1);(1305486112566582809967263704%positive,1);(394631919140629426975601580287%positive,1);(394624622434237722616174530520%positive,0);(1272392823585272610779%positive,0);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(19316178314849599%positive,1);(87021360228470714673450968%positive,0);(356439491495890045503905255384%positive,0);(323186469610832568631256%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(22432227475556623%positive,1);(394624665599546797399408639372%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(75385102008019%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(309058853037593023%positive,1);(1206161630953171%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;1305486112566582809967263704%positive;394624622434237722616174530520%positive;1272392823585272610779%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;19316178314849599%positive;87021360228470714673450968%positive;356439491495890045503905255384%positive;323186469610832568631256%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;22432227475556623%positive;394624665599546797399408639372%positive;5476515575952%positive;6021494531243055068469455%positive;75385102008019%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;309058853037593023%positive;1206161630953171%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(20198698200153183476733%positive,0);(1305486112566582809967263704%positive,1);(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(4944941644824124413%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1470091438291843874188%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(323186469610832568631256%positive,1);(394624665599618855096525622525%positive,0);(309058852801508349%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00419 : iqh tmq_h_00419.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00419 StC 4 4 2 29 20000
                lsetq_h_00419 rsetq_h_00419 certq_h_00419 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00419); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00420 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S0 DL StC)
  | StC, S1 => Some (mkTrans S1 DL StA)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00420 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00420 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0);(StC,S0)])];
   [(S1,[(StD,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00420 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(309058853037593279%positive,0);(20272485176448021683197%positive,1);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(1344098671367075626017609983%positive,0);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818913818335446826383%positive,0);(1272392823585272676315%positive,1);(1344098671240974836451236095%positive,0);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(1206161631477459%positive,2);(4944941644824128509%positive,3);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(20272485176207811542463%positive,0);(1344098671367075769590583293%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(1344098671240974980024209405%positive,1);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 58 [(96345683383942257474600335%positive,1);(309058853037593279%positive,1);(1272392823585272676315%positive,0);(394624622434237722616174530520%positive,0);(87021360228470714673450968%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(1206161631477459%positive,1);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(1344098671240974836451236095%positive,1);(96343901961465753030938584%positive,0);(86815818841760494756813055%positive,1);(1344098671367075626017609983%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(22432227475556623%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(324367061231549979934680%positive,0);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(356439534661199120287139364236%positive,1);(20272485176207811542463%positive,1);(1344171738920351733124235224%positive,0);(394624665599672898188975013260%positive,1);(1344171738794250943557861336%positive,0);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;309058853037593279%positive;1272392823585272676315%positive;394624622434237722616174530520%positive;87021360228470714673450968%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;1206161631477459%positive;1344098671240974836451236095%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;1344098671367075626017609983%positive;394624665599546797399408639372%positive;75385102008019%positive;22432227475556623%positive;5476515575952%positive;6021494531243055068469455%positive;394631919140755527765167954175%positive;324367061231549979934680%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;1344171738920351733124235224%positive;20272485176207811542463%positive;394624665599672898188975013260%positive;1344171738794250943557861336%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(20272485176448021683197%positive,0);(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1344098671240974980024209405%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(1470091438291843874188%positive,0);(1344098671367075769590583293%positive,0);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(4944941644824128509%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(324367061231549979934680%positive,1);(356439534661199120287139364236%positive,0);(1344171738920351733124235224%positive,1);(394624665599672898188975013260%positive,0);(1344171738794250943557861336%positive,1);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00420 : iqh tmq_h_00420.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00420 StC 4 4 2 29 20000
                lsetq_h_00420 rsetq_h_00420 certq_h_00420 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00420); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00421 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00421 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00421 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00421 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(87021360228470714673450968%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(86815818841760494756813055%positive,1);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(96343901961465753030938584%positive,0);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(22432227475556623%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;87021360228470714673450968%positive;1470091438291843874188%positive;19316178314849599%positive;356439534661271177744046610639%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;86815818841760494756813055%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;96343901961465753030938584%positive;22432227475556623%positive;6021494531243055068469455%positive;394624665599546797399408639372%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(1470091438291843874188%positive,0);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00421 : iqh tmq_h_00421.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00421 StC 5 4 2 30 20000
                lsetq_h_00421 rsetq_h_00421 certq_h_00421 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 30) 2000 tmq_h_00421); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00422 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StB)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00422 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00422 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00422 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(87021360228470714673450968%positive,0);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(22432227475556623%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;87021360228470714673450968%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;394624665599546797399408639372%positive;6021494531243055068469455%positive;22432227475556623%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1470091438291843874188%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00422 : iqh tmq_h_00422.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00422 StC 4 4 2 29 20000
                lsetq_h_00422 rsetq_h_00422 certq_h_00422 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00422); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00423 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StB)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00423 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00423 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00423 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(87021360228470714673450968%positive,0);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(22432227475556623%positive,1);(6021494531243055068469455%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(5476515575952%positive,0);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;87021360228470714673450968%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;394624665599546797399408639372%positive;6021494531243055068469455%positive;22432227475556623%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1470091438291843874188%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00423 : iqh tmq_h_00423.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00423 StC 4 4 2 29 20000
                lsetq_h_00423 rsetq_h_00423 certq_h_00423 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00423); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00424 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StC)
  | StC, S1 => Some (mkTrans S0 DR StB)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00424 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00424 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00424 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(87021360228470714673450968%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(86815818841760494756813055%positive,1);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(96343901961465753030938584%positive,0);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(22432227475556623%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;87021360228470714673450968%positive;1470091438291843874188%positive;19316178314849599%positive;356439534661271177744046610639%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;86815818841760494756813055%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;96343901961465753030938584%positive;22432227475556623%positive;6021494531243055068469455%positive;394624665599546797399408639372%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(1470091438291843874188%positive,0);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00424 : iqh tmq_h_00424.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00424 StC 4 4 2 29 20000
                lsetq_h_00424 rsetq_h_00424 certq_h_00424 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00424); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00425 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StC)
  | StC, S1 => Some (mkTrans S1 DL StA)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00425 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00425 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00425 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(87021360228470714673450968%positive,0);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(22432227475556623%positive,1);(6021494531243055068469455%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(5476515575952%positive,0);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;87021360228470714673450968%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;394624665599546797399408639372%positive;6021494531243055068469455%positive;22432227475556623%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1470091438291843874188%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00425 : iqh tmq_h_00425.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00425 StC 4 4 2 29 20000
                lsetq_h_00425 rsetq_h_00425 certq_h_00425 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00425); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00426 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StC)
  | StC, S1 => Some (mkTrans S1 DR StA)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00426 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00426 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00426 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(87021360228470714673450968%positive,0);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(22432227475556623%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;87021360228470714673450968%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;394624665599546797399408639372%positive;6021494531243055068469455%positive;22432227475556623%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1470091438291843874188%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00426 : iqh tmq_h_00426.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00426 StC 4 4 2 29 20000
                lsetq_h_00426 rsetq_h_00426 certq_h_00426 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00426); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00427 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => None
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00427 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00427 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00427 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(87021360228470714673450968%positive,0);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(22432227475556623%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;87021360228470714673450968%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;394624665599546797399408639372%positive;6021494531243055068469455%positive;22432227475556623%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1470091438291843874188%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00427 : iqh tmq_h_00427.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00427 StC 2 4 2 27 20000
                lsetq_h_00427 rsetq_h_00427 certq_h_00427 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 27) 2000 tmq_h_00427); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00428 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => None
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00428 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00428 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00428 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(87021360228470714673450968%positive,0);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(22432227475556623%positive,1);(6021494531243055068469455%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(5476515575952%positive,0);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;87021360228470714673450968%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;394624665599546797399408639372%positive;6021494531243055068469455%positive;22432227475556623%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1470091438291843874188%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00428 : iqh tmq_h_00428.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00428 StC 2 4 2 27 20000
                lsetq_h_00428 rsetq_h_00428 certq_h_00428 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 27) 2000 tmq_h_00428); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00429 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StA)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00429 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00429 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S1,[(StA,S1);(StC,S1)])];
   [(S1,[(StA,S1);(StC,S1)]);(S1,[(StB,S0);(StD,S1)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition certq_h_00429 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 48 [(349537950172698542%positive,0);(21846121564329902%positive,0);(314652163455309742%positive,4);(349537949417722607%positive,4);(356852788752799647%positive,4);(5445141436191%positive,4);(349537949417723822%positive,0);(75791334364922%positive,2);(1212666493260527%positive,4);(356852788753168287%positive,4);(4709410501563%positive,1);(314652164210284282%positive,4);(75791334363887%positive,4);(321809154152691615%positive,4);(1212665738286842%positive,2);(19665759941678842%positive,4);(1172076690%positive,4);(1212666493261562%positive,2);(314652164210283247%positive,4);(4709410132923%positive,3);(356869831183397819%positive,1);(321809154152322975%positive,4);(1212665738285807%positive,4);(19665759941677807%positive,4);(349537949417723642%positive,2);(349537950172698362%positive,2);(314652163455309562%positive,4);(75791334365102%positive,0);(21846121564329722%positive,2);(4910418007839%positive,4);(356869831183029179%positive,3);(314652164210284462%positive,4);(349537950172697327%positive,4);(314652163455308527%positive,4);(1212665738287022%positive,0);(21846121564328687%positive,4);(19665759941679022%positive,4);(1212666493261742%positive,0);(300075682094%positive,4)] [349537950172698542%positive;349537949417722607%positive;314652163455309742%positive;21846121564329902%positive;356852788752799647%positive;5445141436191%positive;349537949417723822%positive;75791334364922%positive;1212666493260527%positive;4709410501563%positive;314652164210284282%positive;75791334363887%positive;321809154152691615%positive;1212665738286842%positive;19665759941678842%positive;1172076690%positive;1212666493261562%positive;314652164210283247%positive;4709410132923%positive;356869831183397819%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;349537949417723642%positive;349537950172698362%positive;314652163455309562%positive;75791334365102%positive;21846121564329722%positive;4910418007839%positive;356869831183029179%positive;314652164210284462%positive;349537950172697327%positive;1212666493261742%positive;314652163455308527%positive;1212665738287022%positive;21846121564328687%positive;19665759941679022%positive;356852788753168287%positive;300075682094%positive]]
  | StC => [HMeas MRight 48 [(78566688125433%positive,1);(349537949417722607%positive,1);(356852788752799647%positive,1);(321809154152690169%positive,1);(5445141436191%positive,1);(321809154152321529%positive,1);(1212666493260527%positive,1);(356852788753168287%positive,1);(4709410501563%positive,1);(75791334363887%positive,1);(21270083729%positive,1);(321809154152691615%positive,1);(314652164210283247%positive,1);(4709410132923%positive,0);(356869831183397819%positive,1);(87122262979065%positive,1);(321809154152322975%positive,1);(1212665738285807%positive,1);(19665759941677807%positive,1);(4910418007839%positive,1);(356852788753166841%positive,1);(356869831183029179%positive,0);(349537950172697327%positive,1);(314652163455308527%positive,1);(21846121564328687%positive,1);(356852788752798201%positive,1)] [349537949417722607%positive;78566688125433%positive;356852788752799647%positive;321809154152690169%positive;5445141436191%positive;321809154152321529%positive;1212666493260527%positive;4709410501563%positive;75791334363887%positive;21270083729%positive;321809154152691615%positive;314652164210283247%positive;4709410132923%positive;356869831183397819%positive;87122262979065%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;356852788753166841%positive;4910418007839%positive;356869831183029179%positive;349537950172697327%positive;314652163455308527%positive;21846121564328687%positive;356852788752798201%positive;356852788753168287%positive]]
  | StD => [HMeas MLeft 48 [(349537950172698542%positive,2);(21846121564329902%positive,2);(314652163455309742%positive,2);(78566688125433%positive,1);(321809154152690169%positive,1);(349537949417723822%positive,2);(75791334364922%positive,2);(321809154152321529%positive,1);(314652164210284282%positive,0);(21270083729%positive,1);(1212665738286842%positive,2);(19665759941678842%positive,0);(1172076690%positive,0);(1212666493261562%positive,2);(87122262979065%positive,1);(349537949417723642%positive,2);(349537950172698362%positive,2);(314652163455309562%positive,0);(75791334365102%positive,2);(21846121564329722%positive,2);(356852788753166841%positive,1);(314652164210284462%positive,2);(1212665738287022%positive,2);(19665759941679022%positive,2);(356852788752798201%positive,1);(1212666493261742%positive,2);(300075682094%positive,2)] [349537950172698542%positive;21846121564329902%positive;314652163455309742%positive;78566688125433%positive;321809154152690169%positive;349537949417723822%positive;75791334364922%positive;321809154152321529%positive;314652164210284282%positive;21270083729%positive;1212665738286842%positive;19665759941678842%positive;1172076690%positive;1212666493261562%positive;87122262979065%positive;349537950172698362%positive;314652163455309562%positive;75791334365102%positive;21846121564329722%positive;356852788753166841%positive;314652164210284462%positive;1212666493261742%positive;1212665738287022%positive;19665759941679022%positive;356852788752798201%positive;349537949417723642%positive;300075682094%positive]]
  end.

Lemma cqh_h_00429 : iqh tmq_h_00429.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00429 StA 23 2 2 48 20000
                lsetq_h_00429 rsetq_h_00429 certq_h_00429 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 48) 2000 tmq_h_00429); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00430 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => None
  | StC, S1 => Some (mkTrans S0 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00430 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00430 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00430 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(87021360228470714673450968%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(86815818841760494756813055%positive,1);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(96343901961465753030938584%positive,0);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(22432227475556623%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;87021360228470714673450968%positive;1470091438291843874188%positive;19316178314849599%positive;356439534661271177744046610639%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;86815818841760494756813055%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;96343901961465753030938584%positive;22432227475556623%positive;6021494531243055068469455%positive;394624665599546797399408639372%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(1470091438291843874188%positive,0);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00430 : iqh tmq_h_00430.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00430 StC 2 4 2 27 20000
                lsetq_h_00430 rsetq_h_00430 certq_h_00430 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 27) 2000 tmq_h_00430); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00431 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => None
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00431 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00431 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00431 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(87021360228470714673450968%positive,0);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(22432227475556623%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;87021360228470714673450968%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;394624665599546797399408639372%positive;6021494531243055068469455%positive;22432227475556623%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1470091438291843874188%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00431 : iqh tmq_h_00431.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00431 StC 2 4 2 27 20000
                lsetq_h_00431 rsetq_h_00431 certq_h_00431 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 27) 2000 tmq_h_00431); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00432 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S0 DL StB)
  | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00432 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00432 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00432 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(87021360228470714673450968%positive,0);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(22432227475556623%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;87021360228470714673450968%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;394624665599546797399408639372%positive;6021494531243055068469455%positive;22432227475556623%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1470091438291843874188%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00432 : iqh tmq_h_00432.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00432 StC 4 4 2 29 20000
                lsetq_h_00432 rsetq_h_00432 certq_h_00432 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00432); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00433 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StA)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00433 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00433 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00433 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(87021360228470714673450968%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(22432227475556623%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;87021360228470714673450968%positive;1470091438291843874188%positive;19316178314849599%positive;356439534661271177744046610639%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;22432227475556623%positive;6021494531243055068469455%positive;394624665599546797399408639372%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(1470091438291843874188%positive,0);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00433 : iqh tmq_h_00433.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00433 StC 3 4 2 28 20000
                lsetq_h_00433 rsetq_h_00433 certq_h_00433 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00433); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00434 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00434 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00434 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00434 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(87021360228470714673450968%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(86815818841760494756813055%positive,1);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(96343901961465753030938584%positive,0);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(22432227475556623%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;87021360228470714673450968%positive;1470091438291843874188%positive;19316178314849599%positive;356439534661271177744046610639%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;86815818841760494756813055%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;96343901961465753030938584%positive;22432227475556623%positive;6021494531243055068469455%positive;394624665599546797399408639372%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(1470091438291843874188%positive,0);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00434 : iqh tmq_h_00434.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00434 StC 5 4 2 30 20000
                lsetq_h_00434 rsetq_h_00434 certq_h_00434 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 30) 2000 tmq_h_00434); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00435 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00435 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00435 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00435 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(87021360228470714673450968%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(86815818841760494756813055%positive,1);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(96343901961465753030938584%positive,0);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(22432227475556623%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;87021360228470714673450968%positive;1470091438291843874188%positive;19316178314849599%positive;356439534661271177744046610639%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;86815818841760494756813055%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;96343901961465753030938584%positive;22432227475556623%positive;6021494531243055068469455%positive;394624665599546797399408639372%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(1470091438291843874188%positive,0);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00435 : iqh tmq_h_00435.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00435 StC 3 4 2 28 20000
                lsetq_h_00435 rsetq_h_00435 certq_h_00435 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00435); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00436 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00436 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00436 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00436 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(87021360228470714673450968%positive,0);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(22432227475556623%positive,1);(6021494531243055068469455%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(5476515575952%positive,0);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;87021360228470714673450968%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;394624665599546797399408639372%positive;6021494531243055068469455%positive;22432227475556623%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1470091438291843874188%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00436 : iqh tmq_h_00436.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00436 StC 4 4 2 29 20000
                lsetq_h_00436 rsetq_h_00436 certq_h_00436 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00436); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00437 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00437 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00437 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00437 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(87021360228470714673450968%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(22432227475556623%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;87021360228470714673450968%positive;1470091438291843874188%positive;19316178314849599%positive;356439534661271177744046610639%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;22432227475556623%positive;6021494531243055068469455%positive;394624665599546797399408639372%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(1470091438291843874188%positive,0);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00437 : iqh tmq_h_00437.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00437 StC 4 4 2 29 20000
                lsetq_h_00437 rsetq_h_00437 certq_h_00437 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00437); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00438 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00438 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00438 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00438 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(87021360228470714673450968%positive,0);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(22432227475556623%positive,1);(6021494531243055068469455%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(5476515575952%positive,0);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;87021360228470714673450968%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;394624665599546797399408639372%positive;6021494531243055068469455%positive;22432227475556623%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1470091438291843874188%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00438 : iqh tmq_h_00438.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00438 StC 3 4 2 28 20000
                lsetq_h_00438 rsetq_h_00438 certq_h_00438 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00438); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00439 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00439 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00439 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00439 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(87021360228470714673450968%positive,0);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(22432227475556623%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;87021360228470714673450968%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;394624665599546797399408639372%positive;6021494531243055068469455%positive;22432227475556623%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1470091438291843874188%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00439 : iqh tmq_h_00439.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00439 StC 4 4 2 29 20000
                lsetq_h_00439 rsetq_h_00439 certq_h_00439 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00439); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00440 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StA)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00440 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00440 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00440 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(87021360228470714673450968%positive,0);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(22432227475556623%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;87021360228470714673450968%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;394624665599546797399408639372%positive;6021494531243055068469455%positive;22432227475556623%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1470091438291843874188%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00440 : iqh tmq_h_00440.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00440 StC 3 4 2 28 20000
                lsetq_h_00440 rsetq_h_00440 certq_h_00440 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00440); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00441 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00441 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StC,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StC,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00441 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00441 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(96345683383942326194077071%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 51 [(96345683383942257474600335%positive,1);(394631875767758452606609981400%positive,0);(394624622434237722616174530520%positive,0);(86888886431065398882402264%positive,0);(19316178314849599%positive,1);(87021360228470714673450968%positive,0);(1470091438291844005260%positive,1);(356439534661271177744046610639%positive,1);(1470091438291843874188%positive,1);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(22432227475556623%positive,1);(6021494531243055068469455%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(5476515575952%positive,0);(96345683383942326194077071%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599582826196427603340%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(356439534661235149084158328204%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394631875767758452606609981400%positive;86888886431065398882402264%positive;394624622434237722616174530520%positive;19316178314849599%positive;87021360228470714673450968%positive;1470091438291844005260%positive;356439534661271177744046610639%positive;1470091438291843874188%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;6021494531243055068469455%positive;22432227475556623%positive;394624665599546797399408639372%positive;75385102008019%positive;5476515575952%positive;96345683383942326194077071%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599582826196427603340%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;356439534661235149084158328204%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(394624665599618855096525622525%positive,0);(394631875767758452606609981400%positive,1);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(86888886431065398882402264%positive,1);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(1470091438291844005260%positive,0);(1470091438291843874188%positive,0);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599582826196427603340%positive,0);(394624665599672898188975013260%positive,0);(356439534661235149084158328204%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00441 : iqh tmq_h_00441.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00441 StC 4 4 2 29 20000
                lsetq_h_00441 rsetq_h_00441 certq_h_00441 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00441); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00442 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StC)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00442 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00442 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00442 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(87021360228470714673450968%positive,0);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(22432227475556623%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;87021360228470714673450968%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;394624665599546797399408639372%positive;6021494531243055068469455%positive;22432227475556623%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1470091438291843874188%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00442 : iqh tmq_h_00442.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00442 StC 5 4 2 30 20000
                lsetq_h_00442 rsetq_h_00442 certq_h_00442 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 30) 2000 tmq_h_00442); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00443 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00443 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00443 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00443 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(87021360228470714673450968%positive,0);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(22432227475556623%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;87021360228470714673450968%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;394624665599546797399408639372%positive;6021494531243055068469455%positive;22432227475556623%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1470091438291843874188%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00443 : iqh tmq_h_00443.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00443 StC 3 4 2 28 20000
                lsetq_h_00443 rsetq_h_00443 certq_h_00443 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00443); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00444 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StA)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00444 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00444 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S1,[(StA,S1);(StA,S0)])];
   [(S1,[(StA,S1);(StA,S0)]);(S1,[(StB,S1);(StB,S1)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition certq_h_00444 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 48 [(314652163455309742%positive,4);(356852788752799647%positive,4);(341080844208165819%positive,3);(5445141436191%positive,4);(295494754644252410%positive,2);(75791334364922%positive,2);(18468421843801850%positive,2);(295494754644251375%positive,4);(1212666493260527%positive,4);(356852788753168287%positive,4);(4709410501563%positive,1);(314652164210284282%positive,4);(75791334363887%positive,4);(321809154152691615%positive,4);(1212665738286842%positive,2);(19665759941678842%positive,4);(1172076690%positive,4);(18468421843800815%positive,4);(295494753889277690%positive,2);(1212666493261562%positive,2);(314652164210283247%positive,4);(4709410132923%positive,3);(295494754644252590%positive,0);(321809154152322975%positive,4);(1212665738285807%positive,4);(19665759941677807%positive,4);(18468421843802030%positive,0);(295494753889276655%positive,4);(314652163455309562%positive,4);(75791334365102%positive,0);(4910418007839%positive,4);(341080844208534459%positive,1);(314652164210284462%positive,4);(314652163455308527%positive,4);(1212665738287022%positive,0);(19665759941679022%positive,4);(295494753889277870%positive,0);(1212666493261742%positive,0);(300075682094%positive,4)] [314652163455309742%positive;356852788752799647%positive;5445141436191%positive;295494754644252410%positive;75791334364922%positive;18468421843801850%positive;295494754644251375%positive;1212666493260527%positive;4709410501563%positive;314652164210284282%positive;75791334363887%positive;321809154152691615%positive;1212665738286842%positive;19665759941678842%positive;1172076690%positive;18468421843800815%positive;295494753889277690%positive;1212666493261562%positive;314652164210283247%positive;4709410132923%positive;295494754644252590%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;300075682094%positive;18468421843802030%positive;295494753889276655%positive;314652163455309562%positive;75791334365102%positive;4910418007839%positive;341080844208534459%positive;314652164210284462%positive;1212666493261742%positive;314652163455308527%positive;1212665738287022%positive;19665759941679022%positive;295494753889277870%positive;356852788753168287%positive;341080844208165819%positive]]
  | StC => [HMeas MRight 48 [(78566688125433%positive,1);(356852788752799647%positive,1);(341080844208165819%positive,0);(321809154152690169%positive,1);(5445141436191%positive,1);(295494754644251375%positive,1);(321809154152321529%positive,1);(1212666493260527%positive,1);(356852788753168287%positive,1);(4709410501563%positive,1);(75791334363887%positive,1);(21270083729%positive,1);(321809154152691615%positive,1);(18468421843800815%positive,1);(314652164210283247%positive,1);(4709410132923%positive,0);(87122262979065%positive,1);(321809154152322975%positive,1);(1212665738285807%positive,1);(19665759941677807%positive,1);(295494753889276655%positive,1);(356852788753166841%positive,1);(4910418007839%positive,1);(341080844208534459%positive,1);(314652163455308527%positive,1);(356852788752798201%positive,1)] [78566688125433%positive;356852788752799647%positive;321809154152690169%positive;5445141436191%positive;295494754644251375%positive;321809154152321529%positive;1212666493260527%positive;4709410501563%positive;75791334363887%positive;21270083729%positive;321809154152691615%positive;18468421843800815%positive;314652164210283247%positive;4709410132923%positive;87122262979065%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;295494753889276655%positive;356852788753166841%positive;4910418007839%positive;341080844208534459%positive;314652163455308527%positive;356852788752798201%positive;356852788753168287%positive;341080844208165819%positive]]
  | StD => [HMeas MLeft 48 [(314652163455309742%positive,2);(78566688125433%positive,1);(321809154152690169%positive,1);(295494754644252410%positive,2);(75791334364922%positive,2);(18468421843801850%positive,2);(321809154152321529%positive,1);(314652164210284282%positive,0);(21270083729%positive,1);(1212665738286842%positive,2);(19665759941678842%positive,0);(1172076690%positive,0);(295494753889277690%positive,2);(1212666493261562%positive,2);(295494754644252590%positive,2);(87122262979065%positive,1);(18468421843802030%positive,2);(314652163455309562%positive,0);(75791334365102%positive,2);(356852788753166841%positive,1);(314652164210284462%positive,2);(1212665738287022%positive,2);(19665759941679022%positive,2);(356852788752798201%positive,1);(295494753889277870%positive,2);(1212666493261742%positive,2);(300075682094%positive,2)] [314652163455309742%positive;78566688125433%positive;321809154152690169%positive;295494754644252410%positive;75791334364922%positive;18468421843801850%positive;321809154152321529%positive;314652164210284282%positive;21270083729%positive;1212665738286842%positive;19665759941678842%positive;1172076690%positive;295494753889277690%positive;1212666493261562%positive;295494754644252590%positive;87122262979065%positive;18468421843802030%positive;314652163455309562%positive;75791334365102%positive;356852788753166841%positive;314652164210284462%positive;1212665738287022%positive;19665759941679022%positive;356852788752798201%positive;295494753889277870%positive;1212666493261742%positive;300075682094%positive]]
  end.

Lemma cqh_h_00444 : iqh tmq_h_00444.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00444 StA 25 2 2 50 20000
                lsetq_h_00444 rsetq_h_00444 certq_h_00444 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 50) 2000 tmq_h_00444); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00445 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => None
  | StD, S1 => Some (mkTrans S0 DL StB)
  end.

Definition lsetq_h_00445 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00445 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00445 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951769851369%positive,4);(74507626043037%positive,0);(347836724567896542%positive,4);(1333998195660445%positive,0);(347836724567897757%positive,4);(4524118413994%positive,1);(296492628957918862%positive,4);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 37 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(75289225785576%positive,1);(296489532403937512%positive,1);(347836724567896542%positive,1);(4524118413994%positive,1);(296492628957918862%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;75289225785576%positive;296489532403937512%positive;347836724567896542%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(75289225785576%positive,1);(296489532403937512%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;75289225785576%positive;296489532403937512%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00445 : iqh tmq_h_00445.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00445 StD 8 2 2 33 20000
                lsetq_h_00445 rsetq_h_00445 certq_h_00445 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 33) 2000 tmq_h_00445); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00446 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => None
  | StD, S1 => Some (mkTrans S0 DR StB)
  end.

Definition lsetq_h_00446 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00446 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00446 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 50 [(4524071228074%positive,3);(296492624780808874%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,4);(341503538445506205%positive,0);(1158174314156714%positive,1);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(19073952623449577%positive,2);(4524118413994%positive,1);(1358737207284190%positive,4);(347836725421494750%positive,4);(1149728881%positive,4);(347836725421495965%positive,0);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(341503538445506025%positive,2);(74507626041822%positive,4);(294330779421%positive,4);(19073952623448542%positive,4);(341503538445504990%positive,4);(19073952623449757%positive,0);(1333998195660265%positive,2);(296489532404355754%positive,3);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(1158162234561194%positive,3);(347836725421495785%positive,2);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;296492624780808874%positive;1358737207285225%positive;19073951769851369%positive;341503538445506205%positive;1158174314156714%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;19073952623449577%positive;4524118413994%positive;1358737207284190%positive;347836725421494750%positive;1149728881%positive;347836725421495965%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;341503538445506025%positive;74507626041822%positive;294330779421%positive;19073952623448542%positive;341503538445504990%positive;19073952623449757%positive;1333998195660265%positive;296489532404355754%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;1158162234561194%positive;347836725421495785%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 50 [(4524071228074%positive,0);(296492624780808874%positive,1);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(1158174314156714%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(347836725421494750%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(19073952623448542%positive,1);(341503538445504990%positive,1);(296489532404355754%positive,0);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(1158162234561194%positive,0);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296492624780808874%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;1158174314156714%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492628957917416%positive;347836725421494750%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;19073952623448542%positive;341503538445504990%positive;296489532404355754%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;1158162234561194%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 50 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(341503538445506205%positive,2);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(19073952623449577%positive,2);(296492628957917416%positive,1);(18415324912%positive,1);(1149728881%positive,0);(347836725421495965%positive,2);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(341503538445506025%positive,2);(294330779421%positive,2);(19073952623449757%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(347836725421495785%positive,2);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;341503538445506205%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;19073952623449577%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;347836725421495965%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;341503538445506025%positive;294330779421%positive;19073952623449757%positive;1333998195660265%positive;347836724567897577%positive;347836725421495785%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00446 : iqh tmq_h_00446.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00446 StD 8 2 2 33 20000
                lsetq_h_00446 rsetq_h_00446 certq_h_00446 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 33) 2000 tmq_h_00446); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00447 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => None
  | StD, S1 => Some (mkTrans S0 DR StC)
  end.

Definition lsetq_h_00447 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00447 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00447 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 50 [(4524071228074%positive,3);(296492624780808874%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,4);(341503538445506205%positive,0);(1158174314156714%positive,1);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(19073952623449577%positive,2);(4524118413994%positive,1);(1358737207284190%positive,4);(1149728881%positive,4);(347836725421494750%positive,4);(347836725421495965%positive,0);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(341503538445506025%positive,2);(74507626041822%positive,4);(294330779421%positive,4);(19073952623448542%positive,4);(341503538445504990%positive,4);(19073952623449757%positive,0);(1333998195660265%positive,2);(296489532404355754%positive,3);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(1158162234561194%positive,3);(347836725421495785%positive,2);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;296492624780808874%positive;1358737207285225%positive;19073951769851369%positive;341503538445506205%positive;1158174314156714%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;19073952623449577%positive;4524118413994%positive;1358737207284190%positive;1149728881%positive;347836725421494750%positive;347836725421495965%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;341503538445506025%positive;74507626041822%positive;294330779421%positive;19073952623448542%positive;341503538445504990%positive;19073952623449757%positive;1333998195660265%positive;296489532404355754%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;1158162234561194%positive;347836725421495785%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 50 [(4524071228074%positive,0);(296492624780808874%positive,1);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(1158174314156714%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(347836725421494750%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(19073952623448542%positive,1);(341503538445504990%positive,1);(296489532404355754%positive,0);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(1158162234561194%positive,0);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296492624780808874%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;1158174314156714%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492628957917416%positive;347836725421494750%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;19073952623448542%positive;341503538445504990%positive;296489532404355754%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;1158162234561194%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 50 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(341503538445506205%positive,2);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(19073952623449577%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(347836725421495965%positive,2);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(341503538445506025%positive,2);(294330779421%positive,2);(19073952623449757%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(347836725421495785%positive,2);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;341503538445506205%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;19073952623449577%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;347836725421495965%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;341503538445506025%positive;294330779421%positive;19073952623449757%positive;1333998195660265%positive;347836724567897577%positive;347836725421495785%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00447 : iqh tmq_h_00447.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00447 StD 8 2 2 33 20000
                lsetq_h_00447 rsetq_h_00447 certq_h_00447 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 33) 2000 tmq_h_00447); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00448 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => None
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00448 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00448 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00448 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951769851369%positive,4);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(4524118413994%positive,1);(296492628957918862%positive,4);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 37 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(4524118413994%positive,1);(296492628957918862%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00448 : iqh tmq_h_00448.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00448 StD 8 2 2 33 20000
                lsetq_h_00448 rsetq_h_00448 certq_h_00448 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 33) 2000 tmq_h_00448); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00449 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StB)
  | StD, S1 => Some (mkTrans S0 DR StA)
  end.

Definition lsetq_h_00449 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00449 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00449 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951769851369%positive,4);(74507626043037%positive,0);(347836724567896542%positive,4);(1333998195660445%positive,0);(347836724567897757%positive,4);(4524118413994%positive,1);(296492628957918862%positive,4);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 37 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(75289225785576%positive,1);(296489532403937512%positive,1);(347836724567896542%positive,1);(4524118413994%positive,1);(296492628957918862%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;75289225785576%positive;296489532403937512%positive;347836724567896542%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(75289225785576%positive,1);(296489532403937512%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;75289225785576%positive;296489532403937512%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00449 : iqh tmq_h_00449.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00449 StD 10 2 2 35 20000
                lsetq_h_00449 rsetq_h_00449 certq_h_00449 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 35) 2000 tmq_h_00449); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00450 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StB)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00450 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00450 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00450 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 50 [(4524071228074%positive,3);(296492624780808874%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,4);(341503538445506205%positive,0);(1158174314156714%positive,1);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(19073952623449577%positive,2);(4524118413994%positive,1);(1358737207284190%positive,4);(1149728881%positive,4);(347836725421494750%positive,4);(347836725421495965%positive,0);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(341503538445506025%positive,2);(74507626041822%positive,4);(294330779421%positive,4);(19073952623448542%positive,4);(341503538445504990%positive,4);(19073952623449757%positive,0);(1333998195660265%positive,2);(296489532404355754%positive,3);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(1158162234561194%positive,3);(347836725421495785%positive,2);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;296492624780808874%positive;1358737207285225%positive;19073951769851369%positive;341503538445506205%positive;1158174314156714%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;19073952623449577%positive;4524118413994%positive;1358737207284190%positive;1149728881%positive;347836725421494750%positive;347836725421495965%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;341503538445506025%positive;74507626041822%positive;294330779421%positive;19073952623448542%positive;341503538445504990%positive;19073952623449757%positive;1333998195660265%positive;296489532404355754%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;1158162234561194%positive;347836725421495785%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 50 [(4524071228074%positive,0);(296492624780808874%positive,1);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(1158174314156714%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(347836725421494750%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(19073952623448542%positive,1);(341503538445504990%positive,1);(296489532404355754%positive,0);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(1158162234561194%positive,0);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296492624780808874%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;1158174314156714%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492628957917416%positive;347836725421494750%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;19073952623448542%positive;341503538445504990%positive;296489532404355754%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;1158162234561194%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 50 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(341503538445506205%positive,2);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(19073952623449577%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(347836725421495965%positive,2);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(341503538445506025%positive,2);(294330779421%positive,2);(19073952623449757%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(347836725421495785%positive,2);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;341503538445506205%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;19073952623449577%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;347836725421495965%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;341503538445506025%positive;294330779421%positive;19073952623449757%positive;1333998195660265%positive;347836724567897577%positive;347836725421495785%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00450 : iqh tmq_h_00450.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00450 StD 10 2 2 35 20000
                lsetq_h_00450 rsetq_h_00450 certq_h_00450 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 35) 2000 tmq_h_00450); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00451 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00451 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00451 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00451 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951769851369%positive,4);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(4524118413994%positive,1);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(341503537591907997%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 37 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(75285048258792%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(1358737207285225%positive,2);(296492624780390632%positive,1);(19073951769851369%positive,0);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(75285048258792%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(1358737207285405%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(341503537591907997%positive,2)] [296489536581464296%positive;1358737207285225%positive;19073951769851369%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;74507626042857%positive;341503537591907817%positive;341503537591907997%positive;1358737207285405%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;75285048258792%positive]]
  | StD => []
  end.

Lemma cqh_h_00451 : iqh tmq_h_00451.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00451 StD 9 2 2 34 20000
                lsetq_h_00451 rsetq_h_00451 certq_h_00451 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00451); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00452 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00452 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[(StD,S1);(StB,S1)])];
   [(S0,[(StD,S1);(StB,S1)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00452 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00452 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 48 [(4524071228074%positive,3);(296489532406092458%positive,3);(1358737207285225%positive,2);(19073956180219369%positive,2);(19073951769851369%positive,4);(347836728978265757%positive,0);(19073956180218334%positive,4);(74507626043037%positive,0);(347836724567896542%positive,4);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(4524118413994%positive,1);(1358737207284190%positive,4);(296492624782545578%positive,1);(1149728881%positive,4);(341503542002275817%positive,2);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(19073956180219549%positive,0);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(341503542002274782%positive,4);(74507626041822%positive,4);(294330779421%positive,4);(347836728978265577%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,4);(341503542002275997%positive,0);(4705576611598%positive,4);(341503537591906782%positive,4);(347836728978264542%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;296489532406092458%positive;1358737207285225%positive;19073951769851369%positive;347836728978265757%positive;19073956180218334%positive;347836724567896542%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492624782545578%positive;1149728881%positive;341503542002275817%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073956180219549%positive;19073951769850334%positive;1358737207285405%positive;341503542002274782%positive;74507626041822%positive;294330779421%positive;347836728978265577%positive;1333998195660265%positive;347836724567897577%positive;341503542002275997%positive;4705576611598%positive;341503537591906782%positive;347836728978264542%positive;296492624780392078%positive;296489536581465742%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;19073956180219369%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 48 [(4524071228074%positive,0);(296489536581464296%positive,1);(296489532406092458%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(19073956180218334%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(296492624782545578%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(341503542002274782%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(347836728978264542%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296489532406092458%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;19073956180218334%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492628957917416%positive;296492624782545578%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;341503542002274782%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;347836728978264542%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 48 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073956180219369%positive,2);(19073951769851369%positive,0);(347836728978265757%positive,2);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(341503542002275817%positive,2);(74507626042857%positive,2);(341503537591907817%positive,0);(19073956180219549%positive,2);(341503537591907997%positive,2);(1358737207285405%positive,2);(294330779421%positive,2);(347836728978265577%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(341503542002275997%positive,2);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;19073951769851369%positive;347836728978265757%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;341503542002275817%positive;75285048258792%positive;74507626042857%positive;19073956180219549%positive;341503537591907817%positive;1358737207285405%positive;294330779421%positive;347836728978265577%positive;1333998195660265%positive;347836724567897577%positive;341503542002275997%positive;19073951769851549%positive;341503537591907997%positive;19073956180219369%positive]]
  | StD => []
  end.

Lemma cqh_h_00452 : iqh tmq_h_00452.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00452 StD 10 2 2 35 20000
                lsetq_h_00452 rsetq_h_00452 certq_h_00452 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 35) 2000 tmq_h_00452); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00453 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Definition lsetq_h_00453 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00453 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00453 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951769851369%positive,4);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(4524118413994%positive,1);(296492628957918862%positive,4);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 37 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(4524118413994%positive,1);(296492628957918862%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00453 : iqh tmq_h_00453.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00453 StD 10 2 2 35 20000
                lsetq_h_00453 rsetq_h_00453 certq_h_00453 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 35) 2000 tmq_h_00453); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00454 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DR StB)
  | StD, S1 => Some (mkTrans S0 DR StA)
  end.

Definition lsetq_h_00454 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00454 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00454 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 50 [(4524071228074%positive,3);(296492624780808874%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,4);(341503538445506205%positive,0);(1158174314156714%positive,1);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(19073952623449577%positive,2);(4524118413994%positive,1);(1358737207284190%positive,4);(347836725421494750%positive,4);(1149728881%positive,4);(347836725421495965%positive,0);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(341503538445506025%positive,2);(74507626041822%positive,4);(294330779421%positive,4);(19073952623448542%positive,4);(341503538445504990%positive,4);(19073952623449757%positive,0);(1333998195660265%positive,2);(296489532404355754%positive,3);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(1158162234561194%positive,3);(347836725421495785%positive,2);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;296492624780808874%positive;1358737207285225%positive;19073951769851369%positive;341503538445506205%positive;1158174314156714%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;19073952623449577%positive;4524118413994%positive;1358737207284190%positive;347836725421494750%positive;1149728881%positive;347836725421495965%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;341503538445506025%positive;74507626041822%positive;294330779421%positive;19073952623448542%positive;341503538445504990%positive;19073952623449757%positive;1333998195660265%positive;296489532404355754%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;1158162234561194%positive;347836725421495785%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 50 [(4524071228074%positive,0);(296492624780808874%positive,1);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(1158174314156714%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(347836725421494750%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(19073952623448542%positive,1);(341503538445504990%positive,1);(296489532404355754%positive,0);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(1158162234561194%positive,0);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296492624780808874%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;1158174314156714%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492628957917416%positive;347836725421494750%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;19073952623448542%positive;341503538445504990%positive;296489532404355754%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;1158162234561194%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 50 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(341503538445506205%positive,2);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(19073952623449577%positive,2);(296492628957917416%positive,1);(18415324912%positive,1);(1149728881%positive,0);(347836725421495965%positive,2);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(341503538445506025%positive,2);(294330779421%positive,2);(19073952623449757%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(347836725421495785%positive,2);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;341503538445506205%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;19073952623449577%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;347836725421495965%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;341503538445506025%positive;294330779421%positive;19073952623449757%positive;1333998195660265%positive;347836724567897577%positive;347836725421495785%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00454 : iqh tmq_h_00454.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00454 StD 10 2 2 35 20000
                lsetq_h_00454 rsetq_h_00454 certq_h_00454 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 35) 2000 tmq_h_00454); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00455 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DR StB)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00455 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[(StD,S1);(StA,S1)])];
   [(S0,[(StD,S1);(StA,S1)]);(S0,[(StD,S1);(StB,S1)])];
   [(S0,[(StD,S1);(StB,S1)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00455 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00455 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 48 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073955106477545%positive,2);(19073951769851369%positive,4);(347836727904523933%positive,0);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(4524118413994%positive,1);(1358737207284190%positive,4);(1149728881%positive,4);(341503540928533993%positive,2);(4705315516174%positive,4);(296492628338791082%positive,1);(74507626042857%positive,2);(19073955106476510%positive,4);(341503537591907817%positive,4);(341503540928532958%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(296489535962337962%positive,3);(19073955106477725%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(347836727904523753%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,4);(347836727904522718%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(341503540928534173%positive,0);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073955106477545%positive;19073951769851369%positive;347836727904523933%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;1149728881%positive;341503540928533993%positive;4705315516174%positive;296492628338791082%positive;74507626042857%positive;19073955106476510%positive;341503537591907817%positive;341503540928532958%positive;19073951769850334%positive;1358737207285405%positive;296489535962337962%positive;19073955106477725%positive;74507626041822%positive;294330779421%positive;347836727904523753%positive;1333998195660265%positive;347836724567897577%positive;347836727904522718%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;341503540928534173%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 48 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(296492628338791082%positive,1);(19073955106476510%positive,1);(341503540928532958%positive,1);(19073951769850334%positive,1);(296489535962337962%positive,0);(74507626041822%positive,1);(347836727904522718%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;296492628338791082%positive;19073955106476510%positive;341503540928532958%positive;19073951769850334%positive;296489535962337962%positive;74507626041822%positive;347836727904522718%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 48 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073955106477545%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836727904523933%positive,2);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(341503540928533993%positive,2);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(19073955106477725%positive,2);(294330779421%positive,2);(347836727904523753%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(341503540928534173%positive,2);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;19073955106477545%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;347836727904523933%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;341503540928533993%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;19073955106477725%positive;294330779421%positive;347836727904523753%positive;1333998195660265%positive;347836724567897577%positive;341503540928534173%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00455 : iqh tmq_h_00455.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00455 StD 10 2 2 35 20000
                lsetq_h_00455 rsetq_h_00455 certq_h_00455 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 35) 2000 tmq_h_00455); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00456 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DR StB)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Definition lsetq_h_00456 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S1,[(StD,S1);(StA,S1)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])];
   [(S1,[(StD,S1);(StA,S1)]);(S1,[(StD,S1);(StB,S1)])];
   [(S1,[(StD,S1);(StB,S1)]);(S0,[(StC,S0);(StC,S0)])]].

Definition rsetq_h_00456 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00456 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 48 [(4524071228074%positive,3);(19073955123254941%positive,0);(1358737207285225%positive,2);(19073951769851369%positive,4);(74507626043037%positive,0);(347836724567896542%positive,4);(347836727921300969%positive,2);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(4524118413994%positive,1);(347836727921299934%positive,4);(1358737207284190%positive,4);(1149728881%positive,4);(341503540945311389%positive,0);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(19073955123254761%positive,2);(74507626041822%positive,4);(294330779421%positive,4);(19073955123253726%positive,4);(347836727921301149%positive,0);(1333998195660265%positive,2);(347836724567897577%positive,4);(296489535979123370%positive,3);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(341503540945311209%positive,2);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(341503540945310174%positive,4);(1333998195659230%positive,4);(296492628355576490%positive,1)] [4524071228074%positive;19073955123254941%positive;1358737207285225%positive;19073951769851369%positive;347836724567896542%positive;347836727921300969%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;4524118413994%positive;347836727921299934%positive;1358737207284190%positive;1149728881%positive;341503540945311389%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;19073955123254761%positive;74507626041822%positive;294330779421%positive;19073955123253726%positive;347836727921301149%positive;1333998195660265%positive;347836724567897577%positive;296489535979123370%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;341503540945311209%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;341503540945310174%positive;1333998195659230%positive;296492628355576490%positive]]
  | StB => [HMeas MLeft 48 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(347836727921299934%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(19073955123253726%positive,1);(296489535979123370%positive,0);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(341503540945310174%positive,1);(1333998195659230%positive,1);(296492628355576490%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;347836727921299934%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;19073955123253726%positive;296489535979123370%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;341503540945310174%positive;1333998195659230%positive;296492628355576490%positive]]
  | StC => [HMeas MRight 48 [(19073955123254941%positive,2);(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(347836727921300969%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(341503540945311389%positive,2);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(19073955123254761%positive,2);(294330779421%positive,2);(347836727921301149%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(341503540945311209%positive,2);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;19073955123254941%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;347836727921300969%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;341503540945311389%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;19073955123254761%positive;294330779421%positive;347836727921301149%positive;1333998195660265%positive;347836724567897577%positive;341503540945311209%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00456 : iqh tmq_h_00456.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00456 StD 10 2 2 35 20000
                lsetq_h_00456 rsetq_h_00456 certq_h_00456 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 35) 2000 tmq_h_00456); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00457 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00457 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[(StD,S0);(StC,S0)])];
   [(S0,[(StD,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00457 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00457 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(1158162234593962%positive,3);(19073951769851369%positive,4);(341503538512614889%positive,2);(347836724567896542%positive,4);(19073952690557406%positive,4);(347836724567897757%positive,4);(296492628957918862%positive,4);(341503538512613854%positive,4);(1158174314189482%positive,1);(1149728881%positive,4);(19073952690558621%positive,0);(4705315516174%positive,4);(347836725488604649%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(294330779421%positive,4);(341503538512615069%positive,0);(347836724567897577%positive,4);(19073952690558441%positive,2);(4705576611598%positive,4);(341503537591906782%positive,4);(347836725488603614%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(347836725488604829%positive,0)] [1158162234593962%positive;19073951769851369%positive;341503538512614889%positive;347836724567896542%positive;19073952690557406%positive;347836724567897757%positive;296492628957918862%positive;341503538512613854%positive;1158174314189482%positive;1149728881%positive;19073952690558621%positive;4705315516174%positive;347836725488604649%positive;341503537591907817%positive;19073951769850334%positive;294330779421%positive;341503538512615069%positive;347836724567897577%positive;19073952690558441%positive;4705576611598%positive;341503537591906782%positive;347836725488603614%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;347836725488604829%positive]]
  | StB => [HMeas MLeft 37 [(296489536581464296%positive,1);(1158162234593962%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(19073952690557406%positive,1);(296492628957918862%positive,1);(341503538512613854%positive,1);(296492628957917416%positive,1);(1158174314189482%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(347836725488603614%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1)] [296489536581464296%positive;1158162234593962%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;19073952690557406%positive;296492628957918862%positive;341503538512613854%positive;296492628957917416%positive;1158174314189482%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;4705576611598%positive;341503537591906782%positive;347836725488603614%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(19073951769851369%positive,0);(296492624780390632%positive,1);(341503538512614889%positive,2);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567897757%positive,2);(296492628957917416%positive,1);(18415324912%positive,1);(1149728881%positive,0);(19073952690558621%positive,2);(347836725488604649%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(294330779421%positive,2);(341503538512615069%positive,2);(347836724567897577%positive,0);(19073952690558441%positive,2);(19073951769851549%positive,2);(75285048258792%positive,1);(347836725488604829%positive,2)] [296489536581464296%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;341503538512614889%positive;75289225785576%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;19073952690558621%positive;75285048258792%positive;347836725488604649%positive;341503537591907817%positive;294330779421%positive;341503538512615069%positive;347836724567897577%positive;19073952690558441%positive;19073951769851549%positive;341503537591907997%positive;347836725488604829%positive]]
  | StD => []
  end.

Lemma cqh_h_00457 : iqh tmq_h_00457.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00457 StD 9 2 2 34 20000
                lsetq_h_00457 rsetq_h_00457 certq_h_00457 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00457); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00458 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DR StC)
  | StD, S1 => Some (mkTrans S0 DR StA)
  end.

Definition lsetq_h_00458 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00458 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00458 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 50 [(4524071228074%positive,3);(296492624780808874%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,4);(341503538445506205%positive,0);(1158174314156714%positive,1);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(19073952623449577%positive,2);(4524118413994%positive,1);(1358737207284190%positive,4);(1149728881%positive,4);(347836725421494750%positive,4);(347836725421495965%positive,0);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(341503538445506025%positive,2);(74507626041822%positive,4);(294330779421%positive,4);(19073952623448542%positive,4);(341503538445504990%positive,4);(19073952623449757%positive,0);(1333998195660265%positive,2);(296489532404355754%positive,3);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(1158162234561194%positive,3);(347836725421495785%positive,2);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;296492624780808874%positive;1358737207285225%positive;19073951769851369%positive;341503538445506205%positive;1158174314156714%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;19073952623449577%positive;4524118413994%positive;1358737207284190%positive;1149728881%positive;347836725421494750%positive;347836725421495965%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;341503538445506025%positive;74507626041822%positive;294330779421%positive;19073952623448542%positive;341503538445504990%positive;19073952623449757%positive;1333998195660265%positive;296489532404355754%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;1158162234561194%positive;347836725421495785%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 50 [(4524071228074%positive,0);(296492624780808874%positive,1);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(1158174314156714%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(347836725421494750%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(19073952623448542%positive,1);(341503538445504990%positive,1);(296489532404355754%positive,0);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(1158162234561194%positive,0);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296492624780808874%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;1158174314156714%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492628957917416%positive;347836725421494750%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;19073952623448542%positive;341503538445504990%positive;296489532404355754%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;1158162234561194%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 50 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(341503538445506205%positive,2);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(19073952623449577%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(347836725421495965%positive,2);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(341503538445506025%positive,2);(294330779421%positive,2);(19073952623449757%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(347836725421495785%positive,2);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;341503538445506205%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;19073952623449577%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;347836725421495965%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;341503538445506025%positive;294330779421%positive;19073952623449757%positive;1333998195660265%positive;347836724567897577%positive;347836725421495785%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00458 : iqh tmq_h_00458.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00458 StD 10 2 2 35 20000
                lsetq_h_00458 rsetq_h_00458 certq_h_00458 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 35) 2000 tmq_h_00458); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00459 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DR StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00459 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[(StD,S0)])];
   [(S0,[(StD,S0)]);(S0,[(StD,S1);(StA,S1)])];
   [(S0,[(StD,S1);(StA,S1)]);(S0,[(StD,S1);(StB,S1)])];
   [(S0,[(StD,S1);(StB,S1)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00459 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00459 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 48 [(4524071228074%positive,3);(1358737207285225%positive,2);(1192122104763881%positive,2);(19073951769851369%positive,4);(347836724567896542%positive,4);(74507626043037%positive,0);(21739795404641949%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(4524118413994%positive,1);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(21343971218642409%positive,2);(341503537591907817%positive,4);(1192122104762846%positive,4);(341503537591907997%positive,4);(21343971218641374%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(1192122104764061%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(18530789204021930%positive,1);(21739795404641769%positive,2);(18530595930493610%positive,3);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(21739795404640734%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(21343971218642589%positive,0);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;1192122104763881%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;21739795404641949%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;21343971218642409%positive;341503537591907817%positive;1192122104762846%positive;21343971218641374%positive;19073951769850334%positive;1358737207285405%positive;1192122104764061%positive;74507626041822%positive;294330779421%positive;18530789204021930%positive;21739795404641769%positive;18530595930493610%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;21739795404640734%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;21343971218642589%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 48 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(1192122104762846%positive,1);(21343971218641374%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(18530789204021930%positive,1);(18530595930493610%positive,0);(4705576611598%positive,1);(21739795404640734%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;1192122104762846%positive;21343971218641374%positive;19073951769850334%positive;74507626041822%positive;18530789204021930%positive;18530595930493610%positive;4705576611598%positive;21739795404640734%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 48 [(296489536581464296%positive,1);(1358737207285225%positive,2);(1192122104763881%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(21739795404641949%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(21343971218642409%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(1192122104764061%positive,2);(294330779421%positive,2);(21739795404641769%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(21343971218642589%positive,2);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;1192122104763881%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;21739795404641949%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;21343971218642409%positive;341503537591907817%positive;1358737207285405%positive;1192122104764061%positive;294330779421%positive;21739795404641769%positive;1333998195660265%positive;347836724567897577%positive;21343971218642589%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00459 : iqh tmq_h_00459.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00459 StD 10 2 2 35 20000
                lsetq_h_00459 rsetq_h_00459 certq_h_00459 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 35) 2000 tmq_h_00459); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00460 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DR StC)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Definition lsetq_h_00460 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[(StD,S0)])];
   [(S0,[(StD,S0)]);(S1,[(StD,S1);(StA,S1)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])];
   [(S1,[(StD,S1);(StA,S1)]);(S1,[(StD,S1);(StB,S1)])];
   [(S1,[(StD,S1);(StB,S1)]);(S0,[(StC,S0);(StC,S0)])]].

Definition rsetq_h_00460 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00460 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 48 [(4524071228074%positive,3);(1358737207285225%positive,2);(1192122104763881%positive,2);(19073951769851369%positive,4);(347836724567896542%positive,4);(74507626043037%positive,0);(21739795404641949%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(4524118413994%positive,1);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(21343971218642409%positive,2);(341503537591907817%positive,4);(1192122104762846%positive,4);(18530789205070506%positive,1);(21343971218641374%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(341503537591907997%positive,4);(18530595931542186%positive,3);(1192122104764061%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(21739795404641769%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(21739795404640734%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(21343971218642589%positive,0);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;1192122104763881%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;21739795404641949%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;21343971218642409%positive;341503537591907817%positive;1192122104762846%positive;18530789205070506%positive;21343971218641374%positive;19073951769850334%positive;1358737207285405%positive;18530595931542186%positive;1192122104764061%positive;74507626041822%positive;294330779421%positive;21739795404641769%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;21739795404640734%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;21343971218642589%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 48 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(1192122104762846%positive,1);(18530789205070506%positive,1);(21343971218641374%positive,1);(19073951769850334%positive,1);(18530595931542186%positive,0);(74507626041822%positive,1);(4705576611598%positive,1);(21739795404640734%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;1192122104762846%positive;18530789205070506%positive;21343971218641374%positive;19073951769850334%positive;18530595931542186%positive;74507626041822%positive;4705576611598%positive;21739795404640734%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 48 [(296489536581464296%positive,1);(1358737207285225%positive,2);(1192122104763881%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(21739795404641949%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(21343971218642409%positive,2);(341503537591907817%positive,0);(1358737207285405%positive,2);(341503537591907997%positive,2);(1192122104764061%positive,2);(294330779421%positive,2);(21739795404641769%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(21343971218642589%positive,2);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;1192122104763881%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;21739795404641949%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;21343971218642409%positive;341503537591907817%positive;1358737207285405%positive;1192122104764061%positive;294330779421%positive;21739795404641769%positive;1333998195660265%positive;347836724567897577%positive;21343971218642589%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00460 : iqh tmq_h_00460.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00460 StD 10 2 2 35 20000
                lsetq_h_00460 rsetq_h_00460 certq_h_00460 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 35) 2000 tmq_h_00460); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00461 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00461 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00461 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00461 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951769851369%positive,4);(74507626043037%positive,0);(347836724567896542%positive,4);(1333998195660445%positive,0);(347836724567897757%positive,4);(4524118413994%positive,1);(296492628957918862%positive,4);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 37 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(75289225785576%positive,1);(296489532403937512%positive,1);(347836724567896542%positive,1);(4524118413994%positive,1);(296492628957918862%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;75289225785576%positive;296489532403937512%positive;347836724567896542%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(75289225785576%positive,1);(296489532403937512%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;75289225785576%positive;296489532403937512%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00461 : iqh tmq_h_00461.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00461 StD 9 2 2 34 20000
                lsetq_h_00461 rsetq_h_00461 certq_h_00461 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00461); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00462 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00462 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[(StD,S1);(StB,S1)])];
   [(S0,[(StD,S1);(StB,S1)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00462 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00462 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 48 [(4524071228074%positive,3);(296489532406092458%positive,3);(1358737207285225%positive,2);(19073956180219369%positive,2);(19073951769851369%positive,4);(347836728978265757%positive,0);(19073956180218334%positive,4);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(4524118413994%positive,1);(296492628957918862%positive,4);(1358737207284190%positive,4);(296492624782545578%positive,1);(1149728881%positive,4);(341503542002275817%positive,2);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(19073956180219549%positive,0);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(341503542002274782%positive,4);(74507626041822%positive,4);(347836728978265577%positive,2);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(341503542002275997%positive,0);(4705576611598%positive,4);(341503537591906782%positive,4);(347836728978264542%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;296489532406092458%positive;1358737207285225%positive;19073951769851369%positive;347836728978265757%positive;19073956180218334%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;296492624782545578%positive;1149728881%positive;341503542002275817%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073956180219549%positive;19073951769850334%positive;1358737207285405%positive;341503542002274782%positive;74507626041822%positive;347836728978265577%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;341503542002275997%positive;4705576611598%positive;341503537591906782%positive;347836728978264542%positive;296492624780392078%positive;296489536581465742%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;19073956180219369%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 48 [(4524071228074%positive,0);(296489536581464296%positive,1);(296489532406092458%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(19073956180218334%positive,1);(347836724567896542%positive,1);(4524118413994%positive,1);(296492628957918862%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(296492624782545578%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(341503542002274782%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(347836728978264542%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296489532406092458%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;19073956180218334%positive;347836724567896542%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;296492628957917416%positive;296492624782545578%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;341503542002274782%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;347836728978264542%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 48 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073956180219369%positive,2);(19073951769851369%positive,0);(347836728978265757%positive,2);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(341503542002275817%positive,2);(74507626042857%positive,2);(341503537591907817%positive,0);(19073956180219549%positive,2);(341503537591907997%positive,2);(1358737207285405%positive,2);(347836728978265577%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(341503542002275997%positive,2);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;19073951769851369%positive;347836728978265757%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;341503542002275817%positive;75285048258792%positive;74507626042857%positive;19073956180219549%positive;341503537591907817%positive;1358737207285405%positive;347836728978265577%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;341503542002275997%positive;19073951769851549%positive;341503537591907997%positive;19073956180219369%positive]]
  | StD => []
  end.

Lemma cqh_h_00462 : iqh tmq_h_00462.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00462 StD 10 2 2 35 20000
                lsetq_h_00462 rsetq_h_00462 certq_h_00462 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 35) 2000 tmq_h_00462); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00463 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Definition lsetq_h_00463 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00463 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00463 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951769851369%positive,4);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(4524118413994%positive,1);(296492628957918862%positive,4);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 37 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(4524118413994%positive,1);(296492628957918862%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00463 : iqh tmq_h_00463.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00463 StD 10 2 2 35 20000
                lsetq_h_00463 rsetq_h_00463 certq_h_00463 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 35) 2000 tmq_h_00463); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00464 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StA)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00464 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00464 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00464 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951769851369%positive,4);(74507626043037%positive,0);(347836724567896542%positive,4);(1333998195660445%positive,0);(347836724567897757%positive,4);(4524118413994%positive,1);(296492628957918862%positive,4);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 37 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(4524118413994%positive,1);(296492628957918862%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00464 : iqh tmq_h_00464.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00464 StD 9 2 2 34 20000
                lsetq_h_00464 rsetq_h_00464 certq_h_00464 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00464); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00465 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StA)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00465 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[(StD,S1);(StB,S1)])];
   [(S0,[(StD,S1);(StB,S1)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00465 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00465 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 48 [(4524071228074%positive,3);(296489532406092458%positive,3);(1358737207285225%positive,2);(19073956180219369%positive,2);(19073951769851369%positive,4);(347836728978265757%positive,0);(19073956180218334%positive,4);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(4524118413994%positive,1);(1358737207284190%positive,4);(296492624782545578%positive,1);(1149728881%positive,4);(341503542002275817%positive,2);(4705315516174%positive,4);(74507626042857%positive,2);(19073956180219549%positive,0);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(341503542002274782%positive,4);(74507626041822%positive,4);(347836728978265577%positive,2);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(341503542002275997%positive,0);(4705576611598%positive,4);(341503537591906782%positive,4);(347836728978264542%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;296489532406092458%positive;1358737207285225%positive;19073951769851369%positive;347836728978265757%positive;19073956180218334%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492624782545578%positive;1149728881%positive;341503542002275817%positive;4705315516174%positive;74507626042857%positive;19073956180219549%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;341503542002274782%positive;74507626041822%positive;347836728978265577%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;341503542002275997%positive;4705576611598%positive;341503537591906782%positive;347836728978264542%positive;296492624780392078%positive;296489536581465742%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;19073956180219369%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 48 [(4524071228074%positive,0);(296489536581464296%positive,1);(296489532406092458%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(19073956180218334%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(296492624782545578%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(341503542002274782%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(347836728978264542%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296489532406092458%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;19073956180218334%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492628957917416%positive;296492624782545578%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;341503542002274782%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;347836728978264542%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 48 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073956180219369%positive,2);(19073951769851369%positive,0);(347836728978265757%positive,2);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(341503542002275817%positive,2);(74507626042857%positive,2);(19073956180219549%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(347836728978265577%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(341503542002275997%positive,2);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;19073951769851369%positive;347836728978265757%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;341503542002275817%positive;75285048258792%positive;74507626042857%positive;19073956180219549%positive;341503537591907817%positive;1358737207285405%positive;347836728978265577%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;341503542002275997%positive;19073951769851549%positive;341503537591907997%positive;19073956180219369%positive]]
  | StD => []
  end.

Lemma cqh_h_00465 : iqh tmq_h_00465.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00465 StD 10 2 2 35 20000
                lsetq_h_00465 rsetq_h_00465 certq_h_00465 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 35) 2000 tmq_h_00465); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00466 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StA)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Definition lsetq_h_00466 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00466 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00466 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951769851369%positive,4);(74507626043037%positive,0);(347836724567896542%positive,4);(1333998195660445%positive,0);(347836724567897757%positive,4);(4524118413994%positive,1);(296492628957918862%positive,4);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 37 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(4524118413994%positive,1);(296492628957918862%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00466 : iqh tmq_h_00466.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00466 StD 10 2 2 35 20000
                lsetq_h_00466 rsetq_h_00466 certq_h_00466 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 35) 2000 tmq_h_00466); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00467 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00467 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S1,[(StD,S0);(StC,S0)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S0)]);(S0,[])]].

Definition rsetq_h_00467 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00467 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(347836725505382045%positive,0);(19073951769851369%positive,4);(347836724567896542%positive,4);(341503538529392105%positive,2);(347836724567897757%positive,4);(296492628957918862%positive,4);(1149728881%positive,4);(1158162234602154%positive,3);(19073952707334622%positive,4);(19073952707335837%positive,0);(4705315516174%positive,4);(341503537591907817%positive,4);(341503537591907997%positive,4);(347836725505381865%positive,2);(19073951769850334%positive,4);(1158174314197674%positive,1);(294330779421%positive,4);(341503538529391070%positive,4);(341503538529392285%positive,0);(347836724567897577%positive,4);(4705576611598%positive,4);(19073952707335657%positive,2);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(347836725505380830%positive,4);(296489536581465742%positive,4)] [347836725505382045%positive;19073951769851369%positive;347836724567896542%positive;341503538529392105%positive;347836724567897757%positive;296492628957918862%positive;1149728881%positive;19073952707334622%positive;1158162234602154%positive;19073952707335837%positive;4705315516174%positive;341503537591907817%positive;347836725505381865%positive;19073951769850334%positive;1158174314197674%positive;294330779421%positive;341503538529391070%positive;341503538529392285%positive;347836724567897577%positive;4705576611598%positive;19073952707335657%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;347836725505380830%positive;341503537591907997%positive;296489536581465742%positive]]
  | StB => [HMeas MLeft 37 [(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(1158162234602154%positive,0);(19073952707334622%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(1158174314197674%positive,1);(341503538529391070%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(347836725505380830%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1)] [296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;296492628957918862%positive;296492628957917416%positive;19073952707334622%positive;18415324912%positive;1158162234602154%positive;4705315516174%positive;19073951769850334%positive;1158174314197674%positive;341503538529391070%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;347836725505380830%positive;75285048258792%positive;296489536581465742%positive]]
  | StC => [HMeas MRight 37 [(347836725505382045%positive,2);(296489536581464296%positive,1);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(341503538529392105%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(19073952707335837%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(347836725505381865%positive,2);(294330779421%positive,2);(341503538529392285%positive,2);(347836724567897577%positive,0);(19073952707335657%positive,2);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;347836725505382045%positive;19073951769851369%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;341503538529392105%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;19073952707335837%positive;341503537591907817%positive;347836725505381865%positive;294330779421%positive;341503538529392285%positive;347836724567897577%positive;19073952707335657%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00467 : iqh tmq_h_00467.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00467 StD 9 2 2 34 20000
                lsetq_h_00467 rsetq_h_00467 certq_h_00467 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00467); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00468 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S0 DR StA)
  end.

Definition lsetq_h_00468 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00468 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00468 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951769851369%positive,4);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(4524118413994%positive,1);(296492628957918862%positive,4);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 37 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(4524118413994%positive,1);(296492628957918862%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00468 : iqh tmq_h_00468.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00468 StD 10 2 2 35 20000
                lsetq_h_00468 rsetq_h_00468 certq_h_00468 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 35) 2000 tmq_h_00468); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00469 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00469 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S1,[(StD,S0)])];
   [(S0,[(StD,S1);(StA,S1)]);(S0,[(StD,S1);(StB,S1)])];
   [(S0,[(StD,S1);(StB,S1)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])];
   [(S1,[(StD,S0)]);(S0,[(StD,S1);(StA,S1)])]].

Definition rsetq_h_00469 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00469 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 48 [(4524071228074%positive,3);(21739795421418985%positive,2);(1358737207285225%positive,2);(19073951769851369%positive,4);(21739795421417950%positive,4);(74507626043037%positive,0);(347836724567896542%positive,4);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(21343971235419805%positive,0);(1358737207284190%positive,4);(4524118413994%positive,1);(1149728881%positive,4);(18530595930501802%positive,3);(1192122121541097%positive,2);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(1192122121540062%positive,4);(21739795421419165%positive,0);(18530789204030122%positive,1);(74507626041822%positive,4);(294330779421%positive,4);(21343971235419625%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(21343971235418590%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(1192122121541277%positive,0);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;21739795421418985%positive;1358737207285225%positive;19073951769851369%positive;21739795421417950%positive;347836724567896542%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;21343971235419805%positive;1358737207284190%positive;4524118413994%positive;1149728881%positive;18530595930501802%positive;1192122121541097%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;1192122121540062%positive;21739795421419165%positive;18530789204030122%positive;74507626041822%positive;294330779421%positive;21343971235419625%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;21343971235418590%positive;296489532403938958%positive;19073951769851549%positive;1192122121541277%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 48 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(21739795421417950%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(1358737207284190%positive,1);(4524118413994%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(18530595930501802%positive,0);(4705315516174%positive,1);(19073951769850334%positive,1);(1192122121540062%positive,1);(18530789204030122%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(21343971235418590%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;21739795421417950%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;18530595930501802%positive;4705315516174%positive;19073951769850334%positive;1192122121540062%positive;18530789204030122%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;21343971235418590%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 48 [(21739795421418985%positive,2);(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(21343971235419805%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(1192122121541097%positive,2);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(21739795421419165%positive,2);(294330779421%positive,2);(21343971235419625%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(1192122121541277%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;21739795421418985%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;21343971235419805%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;1192122121541097%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;21739795421419165%positive;294330779421%positive;21343971235419625%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;1192122121541277%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00469 : iqh tmq_h_00469.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00469 StD 10 2 2 35 20000
                lsetq_h_00469 rsetq_h_00469 certq_h_00469 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 35) 2000 tmq_h_00469); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00470 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Definition lsetq_h_00470 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00470 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00470 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951769851369%positive,4);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(4524118413994%positive,1);(296492628957918862%positive,4);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 37 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(4524118413994%positive,1);(296492628957918862%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00470 : iqh tmq_h_00470.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00470 StD 9 2 2 34 20000
                lsetq_h_00470 rsetq_h_00470 certq_h_00470 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00470); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00471 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Definition lsetq_h_00471 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])];
   [(S1,[(StD,S0)]);(S1,[(StD,S1);(StA,S1)])];
   [(S1,[(StD,S1);(StA,S1)]);(S1,[(StD,S1);(StB,S1)])];
   [(S1,[(StD,S1);(StB,S1)]);(S0,[(StC,S0);(StC,S0)])]].

Definition rsetq_h_00471 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00471 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 48 [(4524071228074%positive,3);(21739795421418985%positive,2);(1358737207285225%positive,2);(19073951769851369%positive,4);(21739795421417950%positive,4);(74507626043037%positive,0);(347836724567896542%positive,4);(1333998195660445%positive,0);(347836724567897757%positive,4);(296492628957918862%positive,4);(4524118413994%positive,1);(21343971235419805%positive,0);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(1192122121541097%positive,2);(74507626042857%positive,2);(341503537591907817%positive,4);(18530595931550378%positive,3);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(1192122121540062%positive,4);(21739795421419165%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(21343971235419625%positive,2);(18530789205078698%positive,1);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(21343971235418590%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(1192122121541277%positive,0);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;21739795421418985%positive;1358737207285225%positive;19073951769851369%positive;21739795421417950%positive;347836724567896542%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957918862%positive;4524118413994%positive;21343971235419805%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;1192122121541097%positive;74507626042857%positive;341503537591907817%positive;18530595931550378%positive;19073951769850334%positive;1358737207285405%positive;1192122121540062%positive;21739795421419165%positive;74507626041822%positive;294330779421%positive;21343971235419625%positive;18530789205078698%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;21343971235418590%positive;296489532403938958%positive;19073951769851549%positive;1192122121541277%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 48 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(21739795421417950%positive,1);(347836724567896542%positive,1);(296492628957918862%positive,1);(4524118413994%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(18530595931550378%positive,0);(19073951769850334%positive,1);(1192122121540062%positive,1);(74507626041822%positive,1);(18530789205078698%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(21343971235418590%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;21739795421417950%positive;347836724567896542%positive;296492628957918862%positive;4524118413994%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;18530595931550378%positive;19073951769850334%positive;1192122121540062%positive;74507626041822%positive;18530789205078698%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;21343971235418590%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 48 [(21739795421418985%positive,2);(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(21343971235419805%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(1192122121541097%positive,2);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(21739795421419165%positive,2);(294330779421%positive,2);(21343971235419625%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(1192122121541277%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;21739795421418985%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;21343971235419805%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;1192122121541097%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;21739795421419165%positive;294330779421%positive;21343971235419625%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;1192122121541277%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00471 : iqh tmq_h_00471.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00471 StD 10 2 2 35 20000
                lsetq_h_00471 rsetq_h_00471 certq_h_00471 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 35) 2000 tmq_h_00471); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00472 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00472 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00472 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition certq_h_00472 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 37 [(314652163455309742%positive,4);(356852788752799647%positive,4);(5445141436191%positive,4);(75791334364922%positive,2);(1212666493260527%positive,4);(4709410501563%positive,1);(356852788753168287%positive,4);(314652164210284282%positive,4);(75791334363887%positive,4);(321809154152691615%positive,4);(1212665738286842%positive,2);(1172076690%positive,4);(19665759941678842%positive,4);(1212666493261562%positive,2);(314652164210283247%positive,4);(4709410132923%positive,3);(321809154152322975%positive,4);(1212665738285807%positive,4);(19665759941677807%positive,4);(314652163455309562%positive,4);(75791334365102%positive,0);(4910418007839%positive,4);(314652164210284462%positive,4);(314652163455308527%positive,4);(1212665738287022%positive,0);(19665759941679022%positive,4);(1212666493261742%positive,0);(300075682094%positive,4)] [314652163455309742%positive;356852788752799647%positive;5445141436191%positive;75791334364922%positive;1212666493260527%positive;4709410501563%positive;314652164210284282%positive;75791334363887%positive;321809154152691615%positive;1212665738286842%positive;1172076690%positive;19665759941678842%positive;1212666493261562%positive;314652164210283247%positive;4709410132923%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;314652163455309562%positive;75791334365102%positive;4910418007839%positive;314652164210284462%positive;1212666493261742%positive;314652163455308527%positive;1212665738287022%positive;19665759941679022%positive;356852788753168287%positive;300075682094%positive]]
  | StC => [HMeas MRight 37 [(78566688125433%positive,1);(356852788752799647%positive,1);(321809154152690169%positive,1);(5445141436191%positive,1);(1212666493260527%positive,1);(321809154152321529%positive,1);(4709410501563%positive,1);(356852788753168287%positive,1);(75791334363887%positive,1);(21270083729%positive,1);(321809154152691615%positive,1);(314652164210283247%positive,1);(4709410132923%positive,0);(87122262979065%positive,1);(321809154152322975%positive,1);(1212665738285807%positive,1);(19665759941677807%positive,1);(356852788753166841%positive,1);(4910418007839%positive,1);(314652163455308527%positive,1);(356852788752798201%positive,1)] [78566688125433%positive;356852788752799647%positive;321809154152690169%positive;5445141436191%positive;1212666493260527%positive;321809154152321529%positive;4709410501563%positive;75791334363887%positive;21270083729%positive;321809154152691615%positive;314652164210283247%positive;4709410132923%positive;87122262979065%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;356852788753166841%positive;4910418007839%positive;314652163455308527%positive;356852788752798201%positive;356852788753168287%positive]]
  | StD => [HMeas MLeft 37 [(314652163455309742%positive,2);(78566688125433%positive,1);(321809154152690169%positive,1);(75791334364922%positive,2);(321809154152321529%positive,1);(314652164210284282%positive,0);(21270083729%positive,1);(1212665738286842%positive,2);(1172076690%positive,0);(19665759941678842%positive,0);(1212666493261562%positive,2);(87122262979065%positive,1);(314652163455309562%positive,0);(75791334365102%positive,2);(356852788753166841%positive,1);(314652164210284462%positive,2);(1212665738287022%positive,2);(19665759941679022%positive,2);(356852788752798201%positive,1);(1212666493261742%positive,2);(300075682094%positive,2)] [314652163455309742%positive;78566688125433%positive;321809154152690169%positive;75791334364922%positive;321809154152321529%positive;314652164210284282%positive;21270083729%positive;1212665738286842%positive;1172076690%positive;19665759941678842%positive;1212666493261562%positive;87122262979065%positive;314652163455309562%positive;75791334365102%positive;356852788753166841%positive;314652164210284462%positive;1212665738287022%positive;19665759941679022%positive;356852788752798201%positive;1212666493261742%positive;300075682094%positive]]
  end.

Lemma cqh_h_00472 : iqh tmq_h_00472.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00472 StA 23 2 2 48 20000
                lsetq_h_00472 rsetq_h_00472 certq_h_00472 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 48) 2000 tmq_h_00472); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00473 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StA)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S0 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00473 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition rsetq_h_00473 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition certq_h_00473 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 35 [(5453667406779%positive,0);(351078360865895151%positive,1);(357411547841885946%positive,1);(306064359855454111%positive,1);(357411548697523962%positive,1);(1195563884074911%positive,1);(357411547841884911%positive,1);(1150007538%positive,1);(351078360865896366%positive,1);(19641575789098746%positive,1);(351078361721533167%positive,1);(351078361721534382%positive,1);(19641576644736762%positive,1);(4722827818783%positive,1);(294402117422%positive,1);(19641576644735727%positive,1);(357411547841886126%positive,1);(19641575789097711%positive,1);(357411548697522927%positive,1);(357411548697524142%positive,1);(19641575789098926%positive,1);(306067452231907231%positive,1);(19641576644736942%positive,1);(1195575963670431%positive,1);(5357030642619%positive,0);(351078360865896186%positive,1);(351078361721534202%positive,1)] [5453667406779%positive;351078360865895151%positive;357411547841885946%positive;306064359855454111%positive;357411548697523962%positive;1195563884074911%positive;357411547841884911%positive;1150007538%positive;351078360865896366%positive;19641575789098746%positive;351078361721533167%positive;351078361721534382%positive;19641576644736762%positive;4722827818783%positive;294402117422%positive;19641576644735727%positive;357411547841886126%positive;19641575789097711%positive;357411548697522927%positive;357411548697524142%positive;19641575789098926%positive;306067452231907231%positive;19641576644736942%positive;1195575963670431%positive;5357030642619%positive;351078360865896186%positive;351078361721534202%positive]]
  | StC => [HMeas MLeft 35 [(5453667406779%positive,1);(351078360865895151%positive,2);(306064359855454111%positive,2);(1195563884074911%positive,2);(357411547841884911%positive,2);(351078361721533167%positive,2);(4722827818783%positive,2);(19641576644735727%positive,2);(18419783537%positive,2);(19641575789097711%positive,2);(306067452231905785%positive,2);(1195575963668985%positive,0);(357411548697522927%positive,2);(306067452231907231%positive,2);(75565245100537%positive,2);(1195575963670431%positive,2);(5357030642619%positive,1);(1195563884073465%positive,0);(306064359855452665%positive,2)] [5453667406779%positive;351078360865895151%positive;306064359855454111%positive;1195563884074911%positive;357411547841884911%positive;351078361721533167%positive;4722827818783%positive;19641576644735727%positive;18419783537%positive;19641575789097711%positive;306067452231905785%positive;357411548697522927%positive;1195575963668985%positive;306067452231907231%positive;75565245100537%positive;1195575963670431%positive;5357030642619%positive;1195563884073465%positive;306064359855452665%positive]]
  | StD => [HMeas MRight 35 [(357411547841885946%positive,0);(357411548697523962%positive,1);(1150007538%positive,0);(351078360865896366%positive,2);(19641575789098746%positive,0);(351078361721534382%positive,2);(19641576644736762%positive,1);(294402117422%positive,2);(357411547841886126%positive,2);(18419783537%positive,1);(306067452231905785%positive,1);(1195575963668985%positive,2);(357411548697524142%positive,2);(19641575789098926%positive,2);(19641576644736942%positive,2);(75565245100537%positive,1);(1195563884073465%positive,2);(306064359855452665%positive,1);(351078360865896186%positive,0);(351078361721534202%positive,1)] [357411547841885946%positive;357411548697523962%positive;1150007538%positive;351078360865896366%positive;19641575789098746%positive;351078361721534382%positive;19641576644736762%positive;294402117422%positive;357411547841886126%positive;18419783537%positive;306067452231905785%positive;1195575963668985%positive;357411548697524142%positive;19641575789098926%positive;19641576644736942%positive;75565245100537%positive;1195563884073465%positive;306064359855452665%positive;351078360865896186%positive;351078361721534202%positive]]
  end.

Lemma cqh_h_00473 : iqh tmq_h_00473.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00473 StA 13 2 2 38 20000
                lsetq_h_00473 rsetq_h_00473 certq_h_00473 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 38) 2000 tmq_h_00473); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00474 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S0 DL StB)
  | StC, S1 => None
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00474 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00474 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00474 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(87021360228470714673450968%positive,0);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(22432227475556623%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;87021360228470714673450968%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;394624665599546797399408639372%positive;6021494531243055068469455%positive;22432227475556623%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1470091438291843874188%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00474 : iqh tmq_h_00474.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00474 StC 2 4 2 27 20000
                lsetq_h_00474 rsetq_h_00474 certq_h_00474 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 27) 2000 tmq_h_00474); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00475 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S0 DL StC)
  | StC, S1 => Some (mkTrans S0 DL StD)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00475 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00475 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0);(StC,S0)])];
   [(S1,[(StD,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00475 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(309058853037593279%positive,0);(20272485176448021683197%positive,1);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(1344098671367075626017609983%positive,0);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818913818335446826383%positive,0);(1272392823585272676315%positive,1);(1344098671240974836451236095%positive,0);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(1206161631477459%positive,2);(4944941644824128509%positive,3);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(20272485176207811542463%positive,0);(1344098671367075769590583293%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(1344098671240974980024209405%positive,1);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 58 [(96345683383942257474600335%positive,1);(309058853037593279%positive,1);(1272392823585272676315%positive,0);(394624622434237722616174530520%positive,0);(87021360228470714673450968%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(1344098671240974836451236095%positive,1);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(1206161631477459%positive,1);(96343901961465753030938584%positive,0);(86815818841760494756813055%positive,1);(1344098671367075626017609983%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(22432227475556623%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(324367061231549979934680%positive,0);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(356439534661199120287139364236%positive,1);(20272485176207811542463%positive,1);(1344171738920351733124235224%positive,0);(394624665599672898188975013260%positive,1);(1344171738794250943557861336%positive,0);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;309058853037593279%positive;1272392823585272676315%positive;394624622434237722616174530520%positive;87021360228470714673450968%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;1344098671240974836451236095%positive;1206161631477459%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;1344098671367075626017609983%positive;394624665599546797399408639372%positive;75385102008019%positive;22432227475556623%positive;5476515575952%positive;6021494531243055068469455%positive;394631919140755527765167954175%positive;324367061231549979934680%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;1344171738920351733124235224%positive;20272485176207811542463%positive;394624665599672898188975013260%positive;1344171738794250943557861336%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(20272485176448021683197%positive,0);(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1344098671240974980024209405%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(1470091438291843874188%positive,0);(1344098671367075769590583293%positive,0);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(4944941644824128509%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(324367061231549979934680%positive,1);(356439534661199120287139364236%positive,0);(1344171738920351733124235224%positive,1);(394624665599672898188975013260%positive,0);(1344171738794250943557861336%positive,1);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00475 : iqh tmq_h_00475.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00475 StC 3 4 2 28 20000
                lsetq_h_00475 rsetq_h_00475 certq_h_00475 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00475); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00476 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S0 DL StC)
  | StC, S1 => Some (mkTrans S0 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00476 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00476 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00476 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(87021360228470714673450968%positive,0);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(22432227475556623%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;87021360228470714673450968%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;394624665599546797399408639372%positive;6021494531243055068469455%positive;22432227475556623%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1470091438291843874188%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00476 : iqh tmq_h_00476.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00476 StC 3 4 2 28 20000
                lsetq_h_00476 rsetq_h_00476 certq_h_00476 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00476); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00477 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S0 DL StC)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00477 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00477 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00477 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(87021360228470714673450968%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(86815818841760494756813055%positive,1);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(96343901961465753030938584%positive,0);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(22432227475556623%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;87021360228470714673450968%positive;1470091438291843874188%positive;19316178314849599%positive;356439534661271177744046610639%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;86815818841760494756813055%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;96343901961465753030938584%positive;22432227475556623%positive;6021494531243055068469455%positive;394624665599546797399408639372%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(1470091438291843874188%positive,0);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00477 : iqh tmq_h_00477.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00477 StC 3 4 2 28 20000
                lsetq_h_00477 rsetq_h_00477 certq_h_00477 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00477); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00478 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => None
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00478 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00478 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00478 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(87021360228470714673450968%positive,0);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(22432227475556623%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;87021360228470714673450968%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;394624665599546797399408639372%positive;6021494531243055068469455%positive;22432227475556623%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1470091438291843874188%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00478 : iqh tmq_h_00478.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00478 StC 2 4 2 27 20000
                lsetq_h_00478 rsetq_h_00478 certq_h_00478 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 27) 2000 tmq_h_00478); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00479 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StC)
  | StC, S1 => Some (mkTrans S0 DR StA)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00479 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00479 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00479 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(1272338780286973443519%positive,0);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 46 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(87021360228470714673450968%positive,0);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(1272338780286973443519%positive,1);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(22432227475556623%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;87021360228470714673450968%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;1272338780286973443519%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;394624665599546797399408639372%positive;22432227475556623%positive;75385102008019%positive;5476515575952%positive;6021494531243055068469455%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1470091438291843874188%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00479 : iqh tmq_h_00479.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00479 StC 3 4 2 28 20000
                lsetq_h_00479 rsetq_h_00479 certq_h_00479 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00479); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00480 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StC)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00480 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00480 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00480 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 45 [(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(87021360228470714673450968%positive,0);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(22432227475556623%positive,1);(6021494531243055068469455%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(5476515575952%positive,0);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [96345683383942257474600335%positive;394624622434237722616174530520%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;87021360228470714673450968%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;394624665599546797399408639372%positive;6021494531243055068469455%positive;22432227475556623%positive;75385102008019%positive;5476515575952%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1470091438291843874188%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00480 : iqh tmq_h_00480.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00480 StC 3 4 2 28 20000
                lsetq_h_00480 rsetq_h_00480 certq_h_00480 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00480); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00481 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StC)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00481 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StA,S0);(StB,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00481 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StA,S1);(StA,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00481 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(1272338780286973640127%positive,0);(96345683383942257474600335%positive,0);(19316178314849599%positive,0);(1272338780527183518717%positive,1);(356439534661271177744046610639%positive,0);(394624665599618854856315885775%positive,0);(394631919140629427119174553597%positive,1);(86815818967861284323186943%positive,0);(356439534661271177984256347389%positive,1);(86815818841760494756813055%positive,0);(87021370766893842720722173%positive,1);(86815818913818335446826383%positive,0);(79524551474079547355%positive,1);(75385102008019%positive,2);(309058852801508349%positive,3);(5438835672930865171126479%positive,0);(394631919140755527765167954175%positive,0);(394624665599618855096525622525%positive,1);(394631919140629426975601580287%positive,0);(96343912499888881078209789%positive,1);(1272338780286973377983%positive,0);(86815818967861427896160253%positive,1);(22432227475556623%positive,0);(6021494531243055068469455%positive,0);(86815818841760638329786365%positive,1);(394631919140701484816291659151%positive,0);(394631919140755527908740927485%positive,1);(5742650233742455037%positive,1)]]
  | StB => [HMeas MLeft 46 [(1272338780286973640127%positive,1);(96345683383942257474600335%positive,1);(394624622434237722616174530520%positive,0);(19316178314849599%positive,1);(1470091438291843874188%positive,1);(356439534661271177744046610639%positive,1);(87021360228470714673450968%positive,0);(356439491495890045503905255384%positive,0);(86815818967861284323186943%positive,1);(5438835672930865171126479%positive,1);(20364718896816569303000%positive,0);(356439534661325221076705738124%positive,1);(394624665599618854856315885775%positive,1);(86815818841760494756813055%positive,1);(96343901961465753030938584%positive,0);(22432227475556623%positive,1);(394624665599546797399408639372%positive,1);(75385102008019%positive,1);(5476515575952%positive,0);(6021494531243055068469455%positive,1);(394631919140755527765167954175%positive,1);(356439534661199120287139364236%positive,1);(79524551474079547355%positive,0);(86815818913818335446826383%positive,1);(394624665599672898188975013260%positive,1);(1272338780286973377983%positive,1);(394631875767722423809591017432%positive,0);(394631875767848524599157391320%positive,0);(394631919140701484816291659151%positive,1);(91882393641337425880%positive,0);(394631919140629426975601580287%positive,1);(86888886395036601863438296%positive,0);(86888886521137391429812184%positive,0)] [1272338780286973640127%positive;96345683383942257474600335%positive;394624622434237722616174530520%positive;19316178314849599%positive;1470091438291843874188%positive;356439534661271177744046610639%positive;87021360228470714673450968%positive;356439491495890045503905255384%positive;86815818967861284323186943%positive;5438835672930865171126479%positive;20364718896816569303000%positive;356439534661325221076705738124%positive;394624665599618854856315885775%positive;86815818841760494756813055%positive;96343901961465753030938584%positive;394624665599546797399408639372%positive;22432227475556623%positive;75385102008019%positive;5476515575952%positive;6021494531243055068469455%positive;394631919140755527765167954175%positive;356439534661199120287139364236%positive;79524551474079547355%positive;86815818913818335446826383%positive;394624665599672898188975013260%positive;1272338780286973377983%positive;394631875767722423809591017432%positive;394631875767848524599157391320%positive;394631919140701484816291659151%positive;91882393641337425880%positive;394631919140629426975601580287%positive;86888886395036601863438296%positive;86888886521137391429812184%positive]]
  | StC => []
  | StD => [HRank [(1272338780527183518717%positive,0);(394631919140629427119174553597%positive,0);(356439534661271177984256347389%positive,0);(87021370766893842720722173%positive,0);(394631919140755527908740927485%positive,0);(394624622434237722616174530520%positive,1);(1470091438291843874188%positive,0);(86815818841760638329786365%positive,0);(87021360228470714673450968%positive,1);(86815818967861427896160253%positive,0);(356439491495890045503905255384%positive,1);(309058852801508349%positive,0);(394624665599618855096525622525%positive,0);(20364718896816569303000%positive,1);(96343912499888881078209789%positive,0);(356439534661325221076705738124%positive,0);(96343901961465753030938584%positive,1);(394624665599546797399408639372%positive,0);(5742650233742455037%positive,0);(5476515575952%positive,1);(356439534661199120287139364236%positive,0);(394624665599672898188975013260%positive,0);(394631875767722423809591017432%positive,1);(394631875767848524599157391320%positive,1);(91882393641337425880%positive,1);(86888886395036601863438296%positive,1);(86888886521137391429812184%positive,1)]]
  end.

Lemma cqh_h_00481 : iqh tmq_h_00481.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00481 StC 3 4 2 28 20000
                lsetq_h_00481 rsetq_h_00481 certq_h_00481 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00481); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00482 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StB)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S0 DL StA)
  end.

Definition lsetq_h_00482 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition rsetq_h_00482 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition certq_h_00482 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 50 [(4711489950378%positive,0);(312234334099559403%positive,1);(19067385031905758%positive,1);(348966818560669374%positive,1);(19066264045441502%positive,1);(305078164816613854%positive,1);(1207992429007326%positive,1);(305060229033185758%positive,1);(76229085033451%positive,1);(312234334099927722%positive,1);(348966818560668330%positive,1);(85196976747499%positive,1);(4764317814590%positive,1);(5324811046718%positive,1);(4711490319018%positive,1);(312234334099928766%positive,1);(1207991674032606%positive,1);(312234334099928043%positive,1);(20800043155%positive,1);(348966818560668651%positive,1);(312234334099559082%positive,0);(348966818560299690%positive,0);(305078165571588574%positive,1);(312234334099560126%positive,1);(348966818560300734%positive,1);(348966818560300011%positive,1);(305060229788160478%positive,1);(75499210494430%positive,1)] [312234334099559403%positive;19067385031905758%positive;348966818560669374%positive;19066264045441502%positive;305078164816613854%positive;305060229788160478%positive;1207992429007326%positive;305060229033185758%positive;76229085033451%positive;312234334099927722%positive;348966818560668330%positive;85196976747499%positive;4764317814590%positive;5324811046718%positive;4711490319018%positive;312234334099928766%positive;1207991674032606%positive;312234334099928043%positive;20800043155%positive;348966818560668651%positive;312234334099559082%positive;348966818560299690%positive;305078165571588574%positive;312234334099560126%positive;348966818560300734%positive;348966818560300011%positive;4711489950378%positive;75499210494430%positive]]
  | StC => [HMeas MLeft 50 [(1136457873%positive,0);(75499210495645%positive,2);(1207991674033821%positive,2);(1207992429008361%positive,2);(305060229033186793%positive,2);(305060229788161693%positive,2);(19067385031906793%positive,0);(305078165571589789%positive,2);(312234334099559403%positive,1);(19066264045442537%positive,2);(290945206557%positive,2);(76229085033451%positive,1);(85196976747499%positive,1);(75499210495465%positive,2);(1207991674033641%positive,2);(19067385031906973%positive,2);(305078165571589609%positive,0);(19066264045442717%positive,2);(305060229788161513%positive,2);(312234334099928043%positive,1);(305078164816615069%positive,2);(305060229033186973%positive,2);(20800043155%positive,1);(348966818560668651%positive,1);(305078164816614889%positive,0);(1207992429008541%positive,2);(348966818560300011%positive,1)] [1136457873%positive;75499210495645%positive;1207991674033821%positive;1207992429008361%positive;305060229788161693%positive;305078165571589789%positive;19067385031906793%positive;312234334099559403%positive;19066264045442537%positive;290945206557%positive;76229085033451%positive;85196976747499%positive;75499210495465%positive;1207991674033641%positive;19067385031906973%positive;305078165571589609%positive;19066264045442717%positive;305060229788161513%positive;312234334099928043%positive;305078164816615069%positive;305060229033186973%positive;20800043155%positive;348966818560668651%positive;305078164816614889%positive;1207992429008541%positive;348966818560300011%positive;305060229033186793%positive]]
  | StD => [HMeas MRight 50 [(1136457873%positive,4);(75499210495645%positive,0);(1207991674033821%positive,0);(4711489950378%positive,3);(1207992429008361%positive,2);(305060229033186793%positive,2);(305060229788161693%positive,0);(19067385031906793%positive,4);(305078165571589789%positive,4);(19066264045442537%positive,2);(19067385031905758%positive,4);(348966818560669374%positive,4);(19066264045441502%positive,4);(305078164816613854%positive,4);(290945206557%positive,4);(1207992429007326%positive,4);(305060229033185758%positive,4);(312234334099927722%positive,1);(348966818560668330%positive,1);(4764317814590%positive,4);(5324811046718%positive,4);(4711490319018%positive,1);(312234334099928766%positive,4);(75499210495465%positive,2);(1207991674033641%positive,2);(19067385031906973%positive,4);(305078165571589609%positive,4);(19066264045442717%positive,0);(305060229788161513%positive,2);(1207991674032606%positive,4);(305078164816615069%positive,4);(305060229033186973%positive,0);(312234334099559082%positive,3);(348966818560299690%positive,3);(305078164816614889%positive,4);(305078165571588574%positive,4);(1207992429008541%positive,0);(312234334099560126%positive,4);(348966818560300734%positive,4);(305060229788160478%positive,4);(75499210494430%positive,4)] [1136457873%positive;75499210495645%positive;1207991674033821%positive;4711489950378%positive;1207992429008361%positive;305060229788161693%positive;305078165571589789%positive;19067385031906793%positive;19066264045442537%positive;19067385031905758%positive;348966818560669374%positive;19066264045441502%positive;305078164816613854%positive;290945206557%positive;305060229788160478%positive;1207992429007326%positive;305060229033185758%positive;312234334099927722%positive;348966818560668330%positive;4764317814590%positive;5324811046718%positive;4711490319018%positive;312234334099928766%positive;75499210495465%positive;1207991674033641%positive;19067385031906973%positive;305078165571589609%positive;19066264045442717%positive;305060229788161513%positive;1207991674032606%positive;305078164816615069%positive;305060229033186973%positive;312234334099559082%positive;348966818560299690%positive;305078164816614889%positive;305078165571588574%positive;1207992429008541%positive;312234334099560126%positive;348966818560300734%positive;305060229033186793%positive;75499210494430%positive]]
  end.

Lemma cqh_h_00482 : iqh tmq_h_00482.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00482 StA 13 2 2 38 20000
                lsetq_h_00482 rsetq_h_00482 certq_h_00482 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 38) 2000 tmq_h_00482); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00483 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StB)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S0 DR StA)
  end.

Definition lsetq_h_00483 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition rsetq_h_00483 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition certq_h_00483 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 37 [(312234334099559403%positive,1);(19067385031905758%positive,1);(348966818560669374%positive,1);(305078164816613854%positive,1);(1207992429007326%positive,1);(76229085033451%positive,1);(85196976747499%positive,1);(4764317814590%positive,1);(5324811046718%positive,1);(4711490319018%positive,1);(312234334099928766%positive,1);(1207991674032606%positive,1);(312234334099928043%positive,1);(20800043155%positive,1);(348966818560668651%positive,1);(305078165571588574%positive,1);(312234334099560126%positive,1);(348966818560300734%positive,1);(348966818560300011%positive,1);(4711489950378%positive,0);(75499210494430%positive,1)] [312234334099559403%positive;19067385031905758%positive;348966818560669374%positive;305078164816613854%positive;1207992429007326%positive;76229085033451%positive;85196976747499%positive;4764317814590%positive;5324811046718%positive;4711490319018%positive;312234334099928766%positive;1207991674032606%positive;312234334099928043%positive;20800043155%positive;348966818560668651%positive;305078165571588574%positive;312234334099560126%positive;348966818560300734%positive;348966818560300011%positive;4711489950378%positive;75499210494430%positive]]
  | StC => [HMeas MLeft 37 [(1136457873%positive,0);(75499210495645%positive,2);(1207991674033821%positive,2);(1207992429008361%positive,2);(19067385031906793%positive,0);(305078165571589789%positive,2);(312234334099559403%positive,1);(290945206557%positive,2);(76229085033451%positive,1);(85196976747499%positive,1);(75499210495465%positive,2);(1207991674033641%positive,2);(19067385031906973%positive,2);(305078165571589609%positive,0);(305078164816615069%positive,2);(312234334099928043%positive,1);(20800043155%positive,1);(348966818560668651%positive,1);(305078164816614889%positive,0);(1207992429008541%positive,2);(348966818560300011%positive,1)] [1136457873%positive;75499210495645%positive;1207991674033821%positive;1207992429008361%positive;305078165571589789%positive;19067385031906793%positive;312234334099559403%positive;290945206557%positive;76229085033451%positive;85196976747499%positive;75499210495465%positive;1207991674033641%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;312234334099928043%positive;20800043155%positive;348966818560668651%positive;305078164816614889%positive;1207992429008541%positive;348966818560300011%positive]]
  | StD => [HMeas MRight 37 [(1136457873%positive,4);(75499210495645%positive,0);(1207991674033821%positive,0);(1207992429008361%positive,2);(19067385031906793%positive,4);(305078165571589789%positive,4);(19067385031905758%positive,4);(348966818560669374%positive,4);(305078164816613854%positive,4);(290945206557%positive,4);(1207992429007326%positive,4);(4764317814590%positive,4);(5324811046718%positive,4);(4711490319018%positive,1);(312234334099928766%positive,4);(75499210495465%positive,2);(1207991674033641%positive,2);(19067385031906973%positive,4);(305078165571589609%positive,4);(305078164816615069%positive,4);(1207991674032606%positive,4);(305078164816614889%positive,4);(305078165571588574%positive,4);(1207992429008541%positive,0);(312234334099560126%positive,4);(348966818560300734%positive,4);(4711489950378%positive,3);(75499210494430%positive,4)] [1136457873%positive;75499210495645%positive;1207991674033821%positive;1207992429008361%positive;305078165571589789%positive;19067385031906793%positive;19067385031905758%positive;348966818560669374%positive;305078164816613854%positive;290945206557%positive;1207992429007326%positive;4764317814590%positive;5324811046718%positive;4711490319018%positive;312234334099928766%positive;75499210495465%positive;1207991674033641%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;1207991674032606%positive;305078164816614889%positive;305078165571588574%positive;1207992429008541%positive;312234334099560126%positive;348966818560300734%positive;4711489950378%positive;75499210494430%positive]]
  end.

Lemma cqh_h_00483 : iqh tmq_h_00483.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00483 StA 5 2 2 30 20000
                lsetq_h_00483 rsetq_h_00483 certq_h_00483 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 30) 2000 tmq_h_00483); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00484 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00484 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition rsetq_h_00484 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition certq_h_00484 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 35 [(1207989527598782%positive,2);(1207989527598059%positive,0);(312255777477710302%positive,2);(19067385031905758%positive,2);(348966818560669374%positive,2);(305078164816613854%positive,2);(4713636385450%positive,1);(85196976747499%positive,2);(1207989527967422%positive,2);(5324811046718%positive,2);(312255776722735582%positive,2);(19515985776038366%positive,2);(20800043155%positive,2);(348966818560668651%positive,2);(4714391360170%positive,1);(305078165571588574%positive,2);(1207989527966699%positive,0);(348966818560300734%positive,2);(348966818560300011%positive,2)] [1207989527598782%positive;1207989527598059%positive;312255777477710302%positive;19067385031905758%positive;348966818560669374%positive;305078164816613854%positive;4713636385450%positive;85196976747499%positive;1207989527967422%positive;5324811046718%positive;312255776722735582%positive;19515985776038366%positive;20800043155%positive;348966818560668651%positive;4714391360170%positive;305078165571588574%positive;1207989527966699%positive;348966818560300734%positive;348966818560300011%positive]]
  | StC => [HMeas MLeft 35 [(1136457873%positive,0);(1207989527598059%positive,2);(19067385031906793%positive,0);(305078165571589789%positive,2);(312255776722736617%positive,1);(312255777477711517%positive,2);(19515985776039401%positive,1);(290945206557%positive,2);(85196976747499%positive,1);(19067385031906973%positive,2);(305078165571589609%positive,0);(305078164816615069%positive,2);(20800043155%positive,1);(348966818560668651%positive,1);(312255776722736797%positive,2);(19515985776039581%positive,2);(305078164816614889%positive,0);(312255777477711337%positive,1);(1207989527966699%positive,2);(348966818560300011%positive,1)] [1136457873%positive;1207989527598059%positive;305078165571589789%positive;19067385031906793%positive;312255776722736617%positive;312255777477711517%positive;19515985776039401%positive;290945206557%positive;85196976747499%positive;348966818560300011%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;20800043155%positive;348966818560668651%positive;312255776722736797%positive;19515985776039581%positive;305078164816614889%positive;312255777477711337%positive;1207989527966699%positive]]
  | StD => [HMeas MRight 35 [(1136457873%positive,1);(1207989527598782%positive,1);(312255777477710302%positive,1);(19067385031906793%positive,1);(305078165571589789%positive,1);(19067385031905758%positive,1);(348966818560669374%positive,1);(312255776722736617%positive,1);(312255777477711517%positive,1);(305078164816613854%positive,1);(4713636385450%positive,0);(19515985776039401%positive,1);(290945206557%positive,1);(1207989527967422%positive,1);(5324811046718%positive,1);(312255776722735582%positive,1);(19067385031906973%positive,1);(305078165571589609%positive,1);(305078164816615069%positive,1);(19515985776038366%positive,1);(4714391360170%positive,0);(312255776722736797%positive,1);(19515985776039581%positive,1);(305078164816614889%positive,1);(312255777477711337%positive,1);(305078165571588574%positive,1);(348966818560300734%positive,1)] [1136457873%positive;1207989527598782%positive;312255777477710302%positive;305078165571589789%positive;19067385031906793%positive;19067385031905758%positive;348966818560669374%positive;312255776722736617%positive;312255777477711517%positive;305078164816613854%positive;4713636385450%positive;19515985776039401%positive;290945206557%positive;1207989527967422%positive;5324811046718%positive;312255776722735582%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;19515985776038366%positive;4714391360170%positive;312255776722736797%positive;19515985776039581%positive;305078164816614889%positive;312255777477711337%positive;305078165571588574%positive;348966818560300734%positive]]
  end.

Lemma cqh_h_00484 : iqh tmq_h_00484.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00484 StA 4 2 2 29 20000
                lsetq_h_00484 rsetq_h_00484 certq_h_00484 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00484); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00485 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => Some (mkTrans S0 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Definition lsetq_h_00485 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)])]].

Definition rsetq_h_00485 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00485 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(96506244151734932528823967%positive,0);(395289576045616243870191315455%positive,0);(395289576045508157479134423551%positive,0);(86815892754912382467697151%positive,0);(356478221541895532295539301886%positive,1);(1272356869486641675967%positive,0);(356478221541895532089555020255%positive,0);(395284740351525128597623269855%positive,0);(395289576045616244011751088126%positive,1);(5439425987881799326886367%positive,0);(86815892718883795727810207%positive,0);(6031566472647875933759967%positive,0);(5752220401271370238%positive,1);(79524556147012878315%positive,1);(75385173311315%positive,2);(309059144859841534%positive,3);(395284740351525128803607551486%positive,1);(86815892646826132970577918%positive,1);(86815892646825991410805247%positive,0);(87030815806108789221268990%positive,1);(22469610942466335%positive,0);(395289576045508157620694196222%positive,1);(19316196576851263%positive,0);(1272356869692626299902%positive,1);(96505063562366014931246590%positive,1);(395289576045580215283451559583%positive,0);(86815892754912524027469822%positive,1)]]
  | StC => [HMeas MLeft 45 [(356478221541823474632781987485%positive,1);(5485676198033%positive,0);(395289551557455399771264122857%positive,0);(92035520718772838377%positive,0);(96506244151734932528823967%positive,1);(86890067004746519077322729%positive,0);(395289576045616243870191315455%positive,1);(395289576045508157479134423551%positive,1);(1472550408361321037469%positive,1);(20364736985982012145641%positive,0);(1272356869486641675967%positive,1);(5439425987881799326886367%positive,1);(395284740351453071140850237085%positive,1);(356478221541895532089555020255%positive,1);(356478197192193354998930857961%positive,0);(86815892718883795727810207%positive,1);(79524556147012878315%positive,0);(86890067112832910134214633%positive,0);(6031566472647875933759967%positive,1);(395284740351525128597623269855%positive,1);(395284716001822951506999107561%positive,0);(22469610942466335%positive,1);(87030809861357281091903465%positive,0);(356478221541931561023838879389%positive,1);(19316196576851263%positive,1);(395289551557563486162321014761%positive,0);(395289576045580215283451559583%positive,1);(395284740351561157531907128989%positive,1);(75385173311315%positive,1);(96505057617614506801881065%positive,0);(86815892646825991410805247%positive,1);(86815892754912382467697151%positive,1)] [356478221541823474632781987485%positive;5485676198033%positive;395289551557455399771264122857%positive;92035520718772838377%positive;96506244151734932528823967%positive;86890067004746519077322729%positive;395289576045616243870191315455%positive;395289576045508157479134423551%positive;1472550408361321037469%positive;1272356869486641675967%positive;20364736985982012145641%positive;356478197192193354998930857961%positive;395284740351453071140850237085%positive;5439425987881799326886367%positive;356478221541895532089555020255%positive;86815892718883795727810207%positive;79524556147012878315%positive;86890067112832910134214633%positive;6031566472647875933759967%positive;395284740351525128597623269855%positive;395284716001822951506999107561%positive;22469610942466335%positive;87030809861357281091903465%positive;356478221541931561023838879389%positive;19316196576851263%positive;395289551557563486162321014761%positive;395289576045580215283451559583%positive;395284740351561157531907128989%positive;75385173311315%positive;96505057617614506801881065%positive;86815892646825991410805247%positive;86815892754912382467697151%positive]]
  | StD => [HRank [(356478221541823474632781987485%positive,0);(5752220401271370238%positive,0);(5485676198033%positive,1);(356478221541895532295539301886%positive,0);(395284740351525128803607551486%positive,0);(395289551557455399771264122857%positive,1);(87030815806108789221268990%positive,0);(96505063562366014931246590%positive,0);(92035520718772838377%positive,1);(1272356869692626299902%positive,0);(86890067004746519077322729%positive,1);(1472550408361321037469%positive,0);(309059144859841534%positive,0);(20364736985982012145641%positive,1);(395289576045616244011751088126%positive,0);(395284740351453071140850237085%positive,0);(86815892754912524027469822%positive,0);(356478197192193354998930857961%positive,1);(86890067112832910134214633%positive,1);(86815892646826132970577918%positive,0);(395284716001822951506999107561%positive,1);(87030809861357281091903465%positive,1);(356478221541931561023838879389%positive,0);(395289576045508157620694196222%positive,0);(395289551557563486162321014761%positive,1);(395284740351561157531907128989%positive,0);(96505057617614506801881065%positive,1)]]
  end.

Lemma cqh_h_00485 : iqh tmq_h_00485.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00485 StA 3 4 2 28 20000
                lsetq_h_00485 rsetq_h_00485 certq_h_00485 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00485); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00486 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StA)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StA)
  end.

Definition lsetq_h_00486 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition rsetq_h_00486 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition certq_h_00486 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 37 [(347849918707528158%positive,1);(323514222544615102%positive,1);(1334049735266782%positive,1);(75285048259563%positive,1);(323514226923467755%positive,1);(323511130168161982%positive,1);(4705315516222%positive,1);(323511134547014635%positive,1);(1358788746891742%positive,1);(323514222544614379%positive,1);(4936435274410%positive,1);(19087145909481950%positive,1);(323511130168161259%positive,1);(341516731731538398%positive,1);(4936388088490%positive,0);(18416111347%positive,1);(74559165649374%positive,1);(323514226923468478%positive,1);(323511134547015358%positive,1);(75289427112939%positive,1);(4705589194558%positive,1)] [1334049735266782%positive;347849918707528158%positive;323514222544615102%positive;323514226923467755%positive;75285048259563%positive;323511130168161982%positive;323511134547014635%positive;4705315516222%positive;1358788746891742%positive;323514222544614379%positive;4936435274410%positive;19087145909481950%positive;323511130168161259%positive;341516731731538398%positive;4936388088490%positive;18416111347%positive;74559165649374%positive;323514226923468478%positive;323511134547015358%positive;75289427112939%positive;4705589194558%positive]]
  | StC => [HMeas MRight 37 [(19087145909482985%positive,0);(75285048259563%positive,1);(323514226923467755%positive,1);(1149729265%positive,0);(347849918707529373%positive,2);(294330785565%positive,2);(323511134547014635%positive,1);(74559165650589%positive,2);(1334049735267997%positive,2);(341516731731539433%positive,0);(323514222544614379%positive,1);(1358788746892777%positive,2);(323511130168161259%positive,1);(19087145909483165%positive,2);(18416111347%positive,1);(347849918707529193%positive,0);(74559165650409%positive,2);(75289427112939%positive,1);(1334049735267817%positive,2);(341516731731539613%positive,2);(1358788746892957%positive,2)] [19087145909482985%positive;75285048259563%positive;323514226923467755%positive;1149729265%positive;347849918707529373%positive;294330785565%positive;323511134547014635%positive;74559165650589%positive;1334049735267997%positive;341516731731539433%positive;323514222544614379%positive;1358788746892777%positive;323511130168161259%positive;19087145909483165%positive;18416111347%positive;347849918707529193%positive;74559165650409%positive;75289427112939%positive;1334049735267817%positive;341516731731539613%positive;1358788746892957%positive]]
  | StD => [HMeas MLeft 37 [(347849918707528158%positive,4);(19087145909482985%positive,4);(323514222544615102%positive,4);(1334049735266782%positive,4);(1149729265%positive,4);(323511130168161982%positive,4);(347849918707529373%positive,4);(294330785565%positive,4);(4705315516222%positive,4);(74559165650589%positive,0);(1334049735267997%positive,0);(341516731731539433%positive,4);(1358788746891742%positive,4);(4936435274410%positive,1);(1358788746892777%positive,2);(19087145909481950%positive,4);(341516731731538398%positive,4);(4936388088490%positive,3);(19087145909483165%positive,4);(347849918707529193%positive,4);(74559165649374%positive,4);(323514226923468478%positive,4);(74559165650409%positive,2);(323511134547015358%positive,4);(1334049735267817%positive,2);(4705589194558%positive,4);(341516731731539613%positive,4);(1358788746892957%positive,0)] [1334049735266782%positive;19087145909482985%positive;323514222544615102%positive;347849918707528158%positive;1149729265%positive;323511130168161982%positive;347849918707529373%positive;294330785565%positive;4705315516222%positive;74559165650589%positive;1334049735267997%positive;341516731731539433%positive;1358788746891742%positive;4936435274410%positive;19087145909481950%positive;1358788746892777%positive;341516731731538398%positive;4936388088490%positive;19087145909483165%positive;347849918707529193%positive;74559165649374%positive;323514226923468478%positive;74559165650409%positive;323511134547015358%positive;1334049735267817%positive;4705589194558%positive;341516731731539613%positive;1358788746892957%positive]]
  end.

Lemma cqh_h_00486 : iqh tmq_h_00486.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00486 StA 9 2 2 34 20000
                lsetq_h_00486 rsetq_h_00486 certq_h_00486 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00486); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00487 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StA)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StA)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S0 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00487 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition rsetq_h_00487 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition certq_h_00487 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 35 [(5453667406779%positive,0);(351078360865895151%positive,1);(357411547841885946%positive,1);(306064359855454111%positive,1);(357411548697523962%positive,1);(1195563884074911%positive,1);(357411547841884911%positive,1);(1150007538%positive,1);(351078360865896366%positive,1);(19641575789098746%positive,1);(351078361721533167%positive,1);(351078361721534382%positive,1);(19641576644736762%positive,1);(4722827818783%positive,1);(294402117422%positive,1);(19641576644735727%positive,1);(357411547841886126%positive,1);(19641575789097711%positive,1);(357411548697522927%positive,1);(357411548697524142%positive,1);(19641575789098926%positive,1);(306067452231907231%positive,1);(19641576644736942%positive,1);(1195575963670431%positive,1);(5357030642619%positive,0);(351078360865896186%positive,1);(351078361721534202%positive,1)] [5453667406779%positive;351078360865895151%positive;357411547841885946%positive;306064359855454111%positive;357411548697523962%positive;1195563884074911%positive;357411547841884911%positive;1150007538%positive;351078360865896366%positive;19641575789098746%positive;351078361721533167%positive;351078361721534382%positive;19641576644736762%positive;4722827818783%positive;294402117422%positive;19641576644735727%positive;357411547841886126%positive;19641575789097711%positive;357411548697522927%positive;357411548697524142%positive;19641575789098926%positive;306067452231907231%positive;19641576644736942%positive;1195575963670431%positive;5357030642619%positive;351078360865896186%positive;351078361721534202%positive]]
  | StC => [HMeas MLeft 35 [(5453667406779%positive,1);(351078360865895151%positive,2);(306064359855454111%positive,2);(1195563884074911%positive,2);(357411547841884911%positive,2);(351078361721533167%positive,2);(4722827818783%positive,2);(19641576644735727%positive,2);(18419783537%positive,2);(19641575789097711%positive,2);(306067452231905785%positive,2);(1195575963668985%positive,0);(357411548697522927%positive,2);(306067452231907231%positive,2);(75565245100537%positive,2);(1195575963670431%positive,2);(5357030642619%positive,1);(1195563884073465%positive,0);(306064359855452665%positive,2)] [5453667406779%positive;351078360865895151%positive;306064359855454111%positive;1195563884074911%positive;357411547841884911%positive;351078361721533167%positive;4722827818783%positive;19641576644735727%positive;18419783537%positive;19641575789097711%positive;306067452231905785%positive;357411548697522927%positive;1195575963668985%positive;306067452231907231%positive;75565245100537%positive;1195575963670431%positive;5357030642619%positive;1195563884073465%positive;306064359855452665%positive]]
  | StD => [HMeas MRight 35 [(357411547841885946%positive,0);(357411548697523962%positive,1);(1150007538%positive,0);(351078360865896366%positive,2);(19641575789098746%positive,0);(351078361721534382%positive,2);(19641576644736762%positive,1);(294402117422%positive,2);(357411547841886126%positive,2);(18419783537%positive,1);(306067452231905785%positive,1);(1195575963668985%positive,2);(357411548697524142%positive,2);(19641575789098926%positive,2);(19641576644736942%positive,2);(75565245100537%positive,1);(1195563884073465%positive,2);(306064359855452665%positive,1);(351078360865896186%positive,0);(351078361721534202%positive,1)] [357411547841885946%positive;357411548697523962%positive;1150007538%positive;351078360865896366%positive;19641575789098746%positive;351078361721534382%positive;19641576644736762%positive;294402117422%positive;357411547841886126%positive;18419783537%positive;306067452231905785%positive;1195575963668985%positive;357411548697524142%positive;19641575789098926%positive;19641576644736942%positive;75565245100537%positive;1195563884073465%positive;306064359855452665%positive;351078360865896186%positive;351078361721534202%positive]]
  end.

Lemma cqh_h_00487 : iqh tmq_h_00487.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00487 StA 15 2 2 40 20000
                lsetq_h_00487 rsetq_h_00487 certq_h_00487 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 40) 2000 tmq_h_00487); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00488 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StB)
  | StB, S0 => Some (mkTrans S1 DL StA)
  | StB, S1 => Some (mkTrans S0 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StC)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00488 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S1);(StC,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StB,S1);(StC,S1)]);(S1,[(StC,S0);(StB,S1);(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StB,S1);(StC,S1)]);(S1,[(StD,S1);(StD,S0);(StB,S1);(StC,S1)])];
   [(S1,[(StD,S1);(StD,S0);(StB,S1);(StC,S1)]);(S1,[(StC,S1);(StD,S0);(StB,S1);(StC,S1)])]].

Definition rsetq_h_00488 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S1)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S0)])]].

Definition certq_h_00488 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 45 [(395434628540408145892022414782%positive,1);(94123810330937555797929691%positive,0);(76808992811154%positive,1);(23569740566034747076315%positive,0);(1272372447534352952767%positive,1);(5425914401840887569505278%positive,1);(385531127115520226622573047231%positive,1);(385531127115591039569448332735%positive,1);(4714649329523%positive,0);(89763438484673474266%positive,0);(395434628540337337304932941531%positive,0);(395434628540408150251808227035%positive,0);(5425914472653834444790782%positive,1);(395434571953867782681404038142%positive,1);(86814638285051640077876955%positive,0);(19311202604547902%positive,1);(385531127115591035133283790555%positive,0);(86814638355864586953162459%positive,0);(355820491877327230204005243886%positive,1);(395434571953796969734528752638%positive,1);(1473108574575881547182%positive,1);(86870237274720671616130030%positive,1);(21914904931240238%positive,1);(86870255413249780749692635%positive,0);(96541657358480660797517246%positive,1);(86814638355860227167350206%positive,1);(385531052820176356801584225262%positive,1);(94123792192408446664367086%positive,1);(355820566172671100024994065855%positive,1);(355820566172741908535704809179%positive,0);(355820566172741912971869351359%positive,1);(79523277693636787931%positive,0)] [395434628540408145892022414782%positive;94123810330937555797929691%positive;76808992811154%positive;23569740566034747076315%positive;1272372447534352952767%positive;5425914401840887569505278%positive;385531127115520226622573047231%positive;385531127115591039569448332735%positive;4714649329523%positive;89763438484673474266%positive;395434628540337337304932941531%positive;395434628540408150251808227035%positive;5425914472653834444790782%positive;395434571953867782681404038142%positive;86814638285051640077876955%positive;19311202604547902%positive;385531127115591035133283790555%positive;86814638355864586953162459%positive;355820491877327230204005243886%positive;395434571953796969734528752638%positive;1473108574575881547182%positive;86870237274720671616130030%positive;21914904931240238%positive;86870255413249780749692635%positive;96541657358480660797517246%positive;86814638355860227167350206%positive;385531052820176356801584225262%positive;94123792192408446664367086%positive;355820566172671100024994065855%positive;355820566172741908535704809179%positive;355820566172741912971869351359%positive;79523277693636787931%positive]]
  | StC => [HRank [(385531127115591035171410132717%positive,0);(86814638285051678330044397%positive,0);(395434628540408150290060394477%positive,0);(94123810330937420875677421%positive,0);(1473108785377171659501%positive,0);(94123810330937555797929691%positive,1);(350638431580754669%positive,0);(23569740566034747076315%positive,1);(86814638355864625205329901%positive,0);(1272372447534352952767%positive,0);(395434628540337337343185108973%positive,0);(385531127115520226622573047231%positive,0);(385531127115591039569448332735%positive,0);(4970204856001229805%positive,0);(4714649329523%positive,1);(395434628540337337304932941531%positive,1);(395434628540408150251808227035%positive,1);(86870255413249645827440365%positive,0);(86814638285051640077876955%positive,1);(385531127115591035133283790555%positive,1);(355820566172741908573831151341%positive,0);(86814638355864586953162459%positive,1);(86870255413249780749692635%positive,1);(355820566172671100024994065855%positive,0);(355820566172741908535704809179%positive,1);(355820566172741912971869351359%positive,0);(79523277693636787931%positive,1)]]
  | StD => [HRank [(395434571953867782681404038142%positive,0);(395434571953796969734528752638%positive,0);(385531127115591035171410132717%positive,1);(395434628540408145892022414782%positive,0);(86870237274720671616130030%positive,0);(86814638285051678330044397%positive,1);(385531052820176356801584225262%positive,0);(395434628540408150290060394477%positive,1);(1473108574575881547182%positive,0);(94123810330937420875677421%positive,1);(96541657358480660797517246%positive,0);(89763438484673474266%positive,1);(76808992811154%positive,2);(355820491877327230204005243886%positive,0);(86814638355864625205329901%positive,1);(5425914401840887569505278%positive,0);(94123792192408446664367086%positive,0);(395434628540337337343185108973%positive,1);(5425914472653834444790782%positive,0);(19311202604547902%positive,0);(21914904931240238%positive,0);(355820566172741908573831151341%positive,1);(86870255413249645827440365%positive,1);(350638431580754669%positive,3);(86814638355860227167350206%positive,0);(1473108785377171659501%positive,1);(4970204856001229805%positive,1)]]
  end.

Lemma cqh_h_00488 : iqh tmq_h_00488.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00488 StA 2 4 2 27 20000
                lsetq_h_00488 rsetq_h_00488 certq_h_00488 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 27) 2000 tmq_h_00488); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00489 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StB)
  | StB, S0 => Some (mkTrans S1 DL StA)
  | StB, S1 => Some (mkTrans S0 DR StC)
  | StC, S0 => Some (mkTrans S1 DL StC)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Definition lsetq_h_00489 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S1)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StC,S1);(StD,S0)])]].

Definition rsetq_h_00489 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S1);(StC,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StB,S1);(StC,S1)]);(S1,[(StC,S0);(StB,S1);(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StB,S1);(StC,S1)]);(S1,[(StD,S1);(StD,S0);(StB,S1);(StC,S1)])];
   [(S1,[(StD,S1);(StD,S0);(StB,S1);(StC,S1)]);(S1,[(StC,S1);(StD,S0);(StB,S1);(StC,S1)])]].

Definition certq_h_00489 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 45 [(384842019199245203674016247230%positive,1);(345914586773754214201160892123%positive,0);(21875736092576062%positive,1);(384844437046254732549788462527%positive,1);(345914607802970400670371737023%positive,1);(5340788668563%positive,0);(20286373164956582784731%positive,0);(5278238034102935581285374%positive,1);(84377892658281315956878782%positive,1);(5872260086764530562423806%positive,1);(93956156254128913805213403%positive,0);(79235125651630403290%positive,0);(84377892586223621136374766%positive,1);(345914607803042458127119604734%positive,1);(84452066944144142385802971%positive,0);(384844437046272746811007884286%positive,1);(19311508611099950%positive,1);(384842019199227189174723861486%positive,1);(89603010155035705051%positive,0);(384844437046200689354260016575%positive,1);(1267780024859104570798%positive,1);(84452066998187337914248923%positive,0);(384841998239060192361859772123%positive,0);(75366860945106%positive,1);(84377892640266816664820718%positive,1);(384844416016984502885049171675%positive,0);(345914607803024443865900182975%positive,1);(384841998239114235557388218075%positive,0);(1433657247745151593919%positive,1);(84451803411543394106998491%positive,0);(384842019199173145979195415534%positive,1);(93955571093548030209027518%positive,1)] [384842019199245203674016247230%positive;345914586773754214201160892123%positive;21875736092576062%positive;384844437046254732549788462527%positive;345914607802970400670371737023%positive;5340788668563%positive;20286373164956582784731%positive;5278238034102935581285374%positive;84377892658281315956878782%positive;5872260086764530562423806%positive;93956156254128913805213403%positive;79235125651630403290%positive;84377892586223621136374766%positive;345914607803042458127119604734%positive;84452066944144142385802971%positive;384844437046272746811007884286%positive;19311508611099950%positive;384842019199227189174723861486%positive;89603010155035705051%positive;384844437046200689354260016575%positive;1267780024859104570798%positive;84452066998187337914248923%positive;384841998239060192361859772123%positive;75366860945106%positive;84377892640266816664820718%positive;384844416016984502885049171675%positive;345914607803024443865900182975%positive;384841998239114235557388218075%positive;1433657247745151593919%positive;84451803411543394106998491%positive;384842019199173145979195415534%positive;93955571093548030209027518%positive]]
  | StC => [HRank [(84377892640266951807319789%positive,0);(345914586773754214201160892123%positive,1);(384844437046254732549788462527%positive,0);(84377892586223756278873837%positive,0);(345914607802970400670371737023%positive,0);(5600188439699518445%positive,0);(5340788668563%positive,1);(384842019199227189309866360557%positive,0);(308984137407918829%positive,0);(20286373164956582784731%positive,1);(1267780024962035145453%positive,0);(384842019199173146114337914605%positive,0);(93956156254128913805213403%positive,1);(84452066944144142385802971%positive,1);(84451808545646969309478893%positive,0);(345914607803042458230049849325%positive,0);(93956161388232489007693805%positive,0);(89603010155035705051%positive,1);(384844437046272746913938128877%positive,0);(384844437046200689354260016575%positive,0);(84452066998187337914248923%positive,1);(384841998239060192361859772123%positive,1);(384844416016984502885049171675%positive,1);(345914607803024443865900182975%positive,0);(384841998239114235557388218075%positive,1);(1433657247745151593919%positive,0);(84451803411543394106998491%positive,1)]]
  | StD => [HRank [(384842019199245203674016247230%positive,0);(21875736092576062%positive,0);(1267780024859104570798%positive,0);(84377892586223756278873837%positive,1);(384844437046272746811007884286%positive,0);(345914607803042458127119604734%positive,0);(384842019199227189309866360557%positive,1);(5278238034102935581285374%positive,0);(19311508611099950%positive,0);(1267780024962035145453%positive,1);(5872260086764530562423806%positive,0);(5600188439699518445%positive,1);(84377892658281315956878782%positive,0);(79235125651630403290%positive,1);(84377892586223621136374766%positive,0);(84451808545646969309478893%positive,1);(84377892640266816664820718%positive,0);(345914607803042458230049849325%positive,1);(384842019199173145979195415534%positive,0);(93956161388232489007693805%positive,1);(384842019199227189174723861486%positive,0);(384844437046272746913938128877%positive,1);(384842019199173146114337914605%positive,1);(75366860945106%positive,2);(308984137407918829%positive,3);(84377892640266951807319789%positive,1);(93955571093548030209027518%positive,0)]]
  end.

Lemma cqh_h_00489 : iqh tmq_h_00489.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00489 StA 2 4 2 27 20000
                lsetq_h_00489 rsetq_h_00489 certq_h_00489 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 27) 2000 tmq_h_00489); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00490 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StB)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StA)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S0 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00490 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition rsetq_h_00490 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition certq_h_00490 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 35 [(5453667406779%positive,0);(351078360865895151%positive,1);(357411547841885946%positive,1);(306064359855454111%positive,1);(357411548697523962%positive,1);(1195563884074911%positive,1);(357411547841884911%positive,1);(1150007538%positive,1);(351078360865896366%positive,1);(19641575789098746%positive,1);(351078361721533167%positive,1);(351078361721534382%positive,1);(19641576644736762%positive,1);(4722827818783%positive,1);(294402117422%positive,1);(19641576644735727%positive,1);(357411547841886126%positive,1);(19641575789097711%positive,1);(357411548697522927%positive,1);(357411548697524142%positive,1);(19641575789098926%positive,1);(306067452231907231%positive,1);(19641576644736942%positive,1);(1195575963670431%positive,1);(5357030642619%positive,0);(351078360865896186%positive,1);(351078361721534202%positive,1)] [5453667406779%positive;351078360865895151%positive;357411547841885946%positive;306064359855454111%positive;357411548697523962%positive;1195563884074911%positive;357411547841884911%positive;1150007538%positive;351078360865896366%positive;19641575789098746%positive;351078361721533167%positive;351078361721534382%positive;19641576644736762%positive;4722827818783%positive;294402117422%positive;19641576644735727%positive;357411547841886126%positive;19641575789097711%positive;357411548697522927%positive;357411548697524142%positive;19641575789098926%positive;306067452231907231%positive;19641576644736942%positive;1195575963670431%positive;5357030642619%positive;351078360865896186%positive;351078361721534202%positive]]
  | StC => [HMeas MLeft 35 [(5453667406779%positive,1);(351078360865895151%positive,2);(306064359855454111%positive,2);(1195563884074911%positive,2);(357411547841884911%positive,2);(351078361721533167%positive,2);(4722827818783%positive,2);(19641576644735727%positive,2);(18419783537%positive,2);(19641575789097711%positive,2);(306067452231905785%positive,2);(1195575963668985%positive,0);(357411548697522927%positive,2);(306067452231907231%positive,2);(75565245100537%positive,2);(1195575963670431%positive,2);(5357030642619%positive,1);(1195563884073465%positive,0);(306064359855452665%positive,2)] [5453667406779%positive;351078360865895151%positive;306064359855454111%positive;1195563884074911%positive;357411547841884911%positive;351078361721533167%positive;4722827818783%positive;19641576644735727%positive;18419783537%positive;19641575789097711%positive;306067452231905785%positive;357411548697522927%positive;1195575963668985%positive;306067452231907231%positive;75565245100537%positive;1195575963670431%positive;5357030642619%positive;1195563884073465%positive;306064359855452665%positive]]
  | StD => [HMeas MRight 35 [(357411547841885946%positive,0);(357411548697523962%positive,1);(1150007538%positive,0);(351078360865896366%positive,2);(19641575789098746%positive,0);(351078361721534382%positive,2);(19641576644736762%positive,1);(294402117422%positive,2);(357411547841886126%positive,2);(18419783537%positive,1);(306067452231905785%positive,1);(1195575963668985%positive,2);(357411548697524142%positive,2);(19641575789098926%positive,2);(19641576644736942%positive,2);(75565245100537%positive,1);(1195563884073465%positive,2);(306064359855452665%positive,1);(351078360865896186%positive,0);(351078361721534202%positive,1)] [357411547841885946%positive;357411548697523962%positive;1150007538%positive;351078360865896366%positive;19641575789098746%positive;351078361721534382%positive;19641576644736762%positive;294402117422%positive;357411547841886126%positive;18419783537%positive;306067452231905785%positive;1195575963668985%positive;357411548697524142%positive;19641575789098926%positive;19641576644736942%positive;75565245100537%positive;1195563884073465%positive;306064359855452665%positive;351078360865896186%positive;351078361721534202%positive]]
  end.

Lemma cqh_h_00490 : iqh tmq_h_00490.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00490 StA 13 2 2 38 20000
                lsetq_h_00490 rsetq_h_00490 certq_h_00490 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 38) 2000 tmq_h_00490); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00491 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StC)
  | StB, S0 => Some (mkTrans S0 DL StA)
  | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StB)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DR StD)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00491 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S1);(StC,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S1);(StC,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StC,S0);(StB,S1);(StD,S1)]);(S1,[(StC,S1);(StC,S0);(StB,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StC,S0);(StB,S1);(StD,S1)]);(S1,[(StD,S0);(StB,S1);(StD,S1);(StD,S0)])]].

Definition rsetq_h_00491 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S1);(StD,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StB,S1);(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StB,S1);(StD,S1);(StC,S0)])];
   [(S1,[(StC,S0);(StB,S1);(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StC,S0);(StB,S1);(StD,S1);(StD,S0)]);(S1,[(StC,S0);(StB,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StC,S0);(StB,S1);(StD,S1);(StD,S1)]);(S1,[(StC,S0);(StB,S1);(StD,S1);(StC,S1)])]].

Definition certq_h_00491 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 45 [(346533580312924666656001097134%positive,1);(1438511856542610095551%positive,1);(386147586172449198678801373935%positive,1);(346533580312994274538132340142%positive,1);(346533503734795021444787460863%positive,1);(396051105306210232440752429823%positive,1);(396051181884339877651966066094%positive,1);(22512901889100095%positive,1);(386147586172518806560932616943%positive,1);(346533580312994278861553467354%positive,0);(96692183077231174454804442%positive,0);(396051181884409485534097309102%positive,1);(84379073248578178720657370%positive,0);(84379073178970296589414362%positive,0);(94274336049687801623739823%positive,1);(23016195324629300395994%positive,0);(84379073248582651249884591%positive,1);(84602906185235321700473599%positive,1);(4715718612978%positive,0);(96692164381381613447535359%positive,1);(5273691888889367046380271%positive,1);(386147680459592379211523227055%positive,1);(396051181884409489857518436314%positive,0);(79236169094081228762%positive,0);(386147680459592374738993999834%positive,0);(386147680459522766856862756826%positive,0);(5273691958497249177623279%positive,1);(84602924881084882707742682%positive,0);(92212838403860807643%positive,0);(19315584553285423%positive,1);(1267778701181878205870%positive,1);(79144922605715%positive,1)] [346533580312924666656001097134%positive;1438511856542610095551%positive;386147586172449198678801373935%positive;346533580312994274538132340142%positive;79144922605715%positive;346533503734795021444787460863%positive;396051105306210232440752429823%positive;396051181884339877651966066094%positive;22512901889100095%positive;386147586172518806560932616943%positive;346533580312994278861553467354%positive;96692183077231174454804442%positive;396051181884409485534097309102%positive;84379073248578178720657370%positive;84379073178970296589414362%positive;94274336049687801623739823%positive;23016195324629300395994%positive;84379073248582651249884591%positive;84602906185235321700473599%positive;4715718612978%positive;96692164381381613447535359%positive;5273691888889367046380271%positive;396051181884409489857518436314%positive;79236169094081228762%positive;386147680459592374738993999834%positive;386147680459522766856862756826%positive;5273691958497249177623279%positive;84602924881084882707742682%positive;92212838403860807643%positive;19315584553285423%positive;1267778701181878205870%positive;386147680459592379211523227055%positive]]
  | StC => [HRank [(94274336049687801623739823%positive,0);(92212838403860807643%positive,1);(79144922605715%positive,2);(360206400015078397%positive,3);(1438511856542610095551%positive,0);(386147586172449198678801373935%positive,0);(5273691958497249177623279%positive,0);(5273691888889367046380271%positive,0);(4952260568671548157%positive,1);(346533503734795021444787460863%positive,0);(396051105306210232440752429823%positive,0);(22512901889100095%positive,0);(386147586172518806560932616943%positive,0);(84602906185235321700473599%positive,0);(84379073178970371080433405%positive,1);(396051181884409489932135280637%positive,1);(84379073248578253211676413%positive,1);(84602924881084749798813693%positive,1);(1438512207789330783229%positive,1);(96692183077231041545875453%positive,1);(84379073248582651249884591%positive,0);(96692164381381613447535359%positive,0);(386147680459592379211523227055%positive,0);(386147680459522766931353775869%positive,1);(386147680459592374813485018877%positive,1);(19315584553285423%positive,0);(346533580312994278936170311677%positive,1)]]
  | StD => [HRank [(360206400015078397%positive,0);(346533580312924666656001097134%positive,0);(346533580312994274538132340142%positive,0);(4952260568671548157%positive,0);(396051181884339877651966066094%positive,0);(386147680459592374813485018877%positive,0);(386147680459522766931353775869%positive,0);(346533580312994278861553467354%positive,1);(1438512207789330783229%positive,0);(96692183077231174454804442%positive,1);(84379073178970371080433405%positive,0);(396051181884409489932135280637%positive,0);(84379073248578253211676413%positive,0);(84602924881084749798813693%positive,0);(396051181884409485534097309102%positive,0);(346533580312994278936170311677%positive,0);(84379073248578178720657370%positive,1);(84379073178970296589414362%positive,1);(96692183077231041545875453%positive,0);(23016195324629300395994%positive,1);(4715718612978%positive,1);(396051181884409489857518436314%positive,1);(79236169094081228762%positive,1);(386147680459592374738993999834%positive,1);(386147680459522766856862756826%positive,1);(84602924881084882707742682%positive,1);(1267778701181878205870%positive,0)]]
  end.

Lemma cqh_h_00491 : iqh tmq_h_00491.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00491 StA 2 4 2 27 20000
                lsetq_h_00491 rsetq_h_00491 certq_h_00491 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 27) 2000 tmq_h_00491); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00492 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StC)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StA)
  end.

Definition lsetq_h_00492 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S1,[(StA,S1);(StB,S1)])];
   [(S1,[(StA,S1);(StB,S1)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition rsetq_h_00492 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition certq_h_00492 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 48 [(1334049735266782%positive,1);(323514222544615102%positive,1);(347849918707528158%positive,1);(75285048259563%positive,1);(323514226923467755%positive,1);(323511130168161982%positive,1);(4705315516222%positive,1);(323511134547014635%positive,1);(341516735957258718%positive,1);(323511130170225322%positive,0);(1358788746891742%positive,1);(323514222544614379%positive,1);(4936435274410%positive,1);(19087145909481950%positive,1);(323511130168161259%positive,1);(341516731731538398%positive,1);(4936388088490%positive,0);(347849922933248478%positive,1);(18416111347%positive,1);(74559165649374%positive,1);(323514226923468478%positive,1);(75289427112939%positive,1);(323511134547015358%positive,1);(4705589194558%positive,1);(323514222546678442%positive,1);(19087150135202270%positive,1)] [347849918707528158%positive;1334049735266782%positive;323514222544615102%positive;323514226923467755%positive;75285048259563%positive;323511130168161982%positive;323511134547014635%positive;4705315516222%positive;341516735957258718%positive;323511130170225322%positive;1358788746891742%positive;323514222544614379%positive;4936435274410%positive;19087145909481950%positive;323511130168161259%positive;341516731731538398%positive;4936388088490%positive;347849922933248478%positive;18416111347%positive;74559165649374%positive;323514226923468478%positive;75289427112939%positive;323511134547015358%positive;4705589194558%positive;323514222546678442%positive;19087150135202270%positive]]
  | StC => [HMeas MRight 48 [(19087145909482985%positive,0);(75285048259563%positive,1);(323514226923467755%positive,1);(1149729265%positive,0);(347849918707529373%positive,2);(294330785565%positive,2);(341516735957259753%positive,2);(323511134547014635%positive,1);(74559165650589%positive,2);(1334049735267997%positive,2);(19087150135203485%positive,2);(341516731731539433%positive,0);(323514222544614379%positive,1);(1358788746892777%positive,2);(323511130168161259%positive,1);(347849922933249513%positive,2);(19087145909483165%positive,2);(18416111347%positive,1);(341516735957259933%positive,2);(347849918707529193%positive,0);(74559165650409%positive,2);(75289427112939%positive,1);(1334049735267817%positive,2);(19087150135203305%positive,2);(341516731731539613%positive,2);(1358788746892957%positive,2);(347849922933249693%positive,2)] [19087145909482985%positive;75285048259563%positive;323514226923467755%positive;1149729265%positive;347849918707529373%positive;294330785565%positive;341516735957259753%positive;323511134547014635%positive;74559165650589%positive;1334049735267997%positive;19087150135203485%positive;341516731731539433%positive;323514222544614379%positive;1358788746892777%positive;323511130168161259%positive;347849922933249513%positive;19087145909483165%positive;18416111347%positive;341516735957259933%positive;347849918707529193%positive;74559165650409%positive;75289427112939%positive;1334049735267817%positive;19087150135203305%positive;341516731731539613%positive;1358788746892957%positive;347849922933249693%positive]]
  | StD => [HMeas MLeft 48 [(1334049735266782%positive,4);(19087145909482985%positive,4);(323514222544615102%positive,4);(347849918707528158%positive,4);(1149729265%positive,4);(323511130168161982%positive,4);(347849918707529373%positive,4);(294330785565%positive,4);(4705315516222%positive,4);(341516735957259753%positive,2);(74559165650589%positive,0);(341516735957258718%positive,4);(1334049735267997%positive,0);(323511130170225322%positive,3);(19087150135203485%positive,0);(341516731731539433%positive,4);(1358788746891742%positive,4);(4936435274410%positive,1);(1358788746892777%positive,2);(19087145909481950%positive,4);(341516731731538398%positive,4);(347849922933249513%positive,2);(4936388088490%positive,3);(19087145909483165%positive,4);(347849922933248478%positive,4);(341516735957259933%positive,0);(347849918707529193%positive,4);(74559165649374%positive,4);(323514226923468478%positive,4);(74559165650409%positive,2);(323511134547015358%positive,4);(1334049735267817%positive,2);(4705589194558%positive,4);(19087150135203305%positive,2);(341516731731539613%positive,4);(323514222546678442%positive,1);(19087150135202270%positive,4);(1358788746892957%positive,0);(347849922933249693%positive,0)] [347849918707528158%positive;19087145909482985%positive;323514222544615102%positive;1334049735266782%positive;1149729265%positive;323511130168161982%positive;347849918707529373%positive;294330785565%positive;4705315516222%positive;341516735957259753%positive;74559165650589%positive;341516735957258718%positive;1334049735267997%positive;323511130170225322%positive;19087150135203485%positive;341516731731539433%positive;1358788746891742%positive;4936435274410%positive;1358788746892777%positive;19087145909481950%positive;341516731731538398%positive;347849922933249513%positive;4936388088490%positive;19087145909483165%positive;347849922933248478%positive;341516735957259933%positive;347849918707529193%positive;74559165649374%positive;323514226923468478%positive;74559165650409%positive;323511134547015358%positive;1334049735267817%positive;4705589194558%positive;19087150135203305%positive;341516731731539613%positive;323514222546678442%positive;19087150135202270%positive;1358788746892957%positive;347849922933249693%positive]]
  end.

Lemma cqh_h_00492 : iqh tmq_h_00492.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00492 StA 8 2 2 33 20000
                lsetq_h_00492 rsetq_h_00492 certq_h_00492 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 33) 2000 tmq_h_00492); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00493 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StC)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00493 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition rsetq_h_00493 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition certq_h_00493 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 37 [(347849918707528158%positive,1);(323514222544615102%positive,1);(1334049735266782%positive,1);(75285048259563%positive,1);(323514226923467755%positive,1);(323511130168161982%positive,1);(4705315516222%positive,1);(323511134547014635%positive,1);(1358788746891742%positive,1);(323514222544614379%positive,1);(4936435274410%positive,1);(19087145909481950%positive,1);(323511130168161259%positive,1);(341516731731538398%positive,1);(4936388088490%positive,0);(18416111347%positive,1);(74559165649374%positive,1);(323514226923468478%positive,1);(323511134547015358%positive,1);(75289427112939%positive,1);(4705589194558%positive,1)] [1334049735266782%positive;347849918707528158%positive;323514222544615102%positive;323514226923467755%positive;75285048259563%positive;323511130168161982%positive;323511134547014635%positive;4705315516222%positive;1358788746891742%positive;323514222544614379%positive;4936435274410%positive;19087145909481950%positive;323511130168161259%positive;341516731731538398%positive;4936388088490%positive;18416111347%positive;74559165649374%positive;323514226923468478%positive;323511134547015358%positive;75289427112939%positive;4705589194558%positive]]
  | StC => [HMeas MRight 37 [(19087145909482985%positive,0);(75285048259563%positive,1);(323514226923467755%positive,1);(1149729265%positive,0);(347849918707529373%positive,2);(294330785565%positive,2);(323511134547014635%positive,1);(74559165650589%positive,2);(1334049735267997%positive,2);(341516731731539433%positive,0);(323514222544614379%positive,1);(1358788746892777%positive,2);(323511130168161259%positive,1);(19087145909483165%positive,2);(18416111347%positive,1);(347849918707529193%positive,0);(74559165650409%positive,2);(75289427112939%positive,1);(1334049735267817%positive,2);(341516731731539613%positive,2);(1358788746892957%positive,2)] [19087145909482985%positive;75285048259563%positive;323514226923467755%positive;1149729265%positive;347849918707529373%positive;294330785565%positive;323511134547014635%positive;74559165650589%positive;1334049735267997%positive;341516731731539433%positive;323514222544614379%positive;1358788746892777%positive;323511130168161259%positive;19087145909483165%positive;18416111347%positive;347849918707529193%positive;74559165650409%positive;75289427112939%positive;1334049735267817%positive;341516731731539613%positive;1358788746892957%positive]]
  | StD => [HMeas MLeft 37 [(347849918707528158%positive,4);(19087145909482985%positive,4);(323514222544615102%positive,4);(1334049735266782%positive,4);(1149729265%positive,4);(323511130168161982%positive,4);(347849918707529373%positive,4);(294330785565%positive,4);(4705315516222%positive,4);(74559165650589%positive,0);(1334049735267997%positive,0);(341516731731539433%positive,4);(1358788746891742%positive,4);(4936435274410%positive,1);(1358788746892777%positive,2);(19087145909481950%positive,4);(341516731731538398%positive,4);(4936388088490%positive,3);(19087145909483165%positive,4);(347849918707529193%positive,4);(74559165649374%positive,4);(323514226923468478%positive,4);(74559165650409%positive,2);(323511134547015358%positive,4);(1334049735267817%positive,2);(4705589194558%positive,4);(341516731731539613%positive,4);(1358788746892957%positive,0)] [1334049735266782%positive;19087145909482985%positive;323514222544615102%positive;347849918707528158%positive;1149729265%positive;323511130168161982%positive;347849918707529373%positive;294330785565%positive;4705315516222%positive;74559165650589%positive;1334049735267997%positive;341516731731539433%positive;1358788746891742%positive;4936435274410%positive;19087145909481950%positive;1358788746892777%positive;341516731731538398%positive;4936388088490%positive;19087145909483165%positive;347849918707529193%positive;74559165649374%positive;323514226923468478%positive;74559165650409%positive;323511134547015358%positive;1334049735267817%positive;4705589194558%positive;341516731731539613%positive;1358788746892957%positive]]
  end.

Lemma cqh_h_00493 : iqh tmq_h_00493.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00493 StA 8 2 2 33 20000
                lsetq_h_00493 rsetq_h_00493 certq_h_00493 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 33) 2000 tmq_h_00493); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00494 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StC)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StB)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S0 DL StA)
  end.

Definition lsetq_h_00494 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition rsetq_h_00494 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition certq_h_00494 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 50 [(4711489950378%positive,0);(312234334099559403%positive,1);(19067385031905758%positive,1);(348966818560669374%positive,1);(19066264045441502%positive,1);(305078164816613854%positive,1);(1207992429007326%positive,1);(305060229033185758%positive,1);(76229085033451%positive,1);(312234334099927722%positive,1);(348966818560668330%positive,1);(85196976747499%positive,1);(4764317814590%positive,1);(5324811046718%positive,1);(4711490319018%positive,1);(312234334099928766%positive,1);(1207991674032606%positive,1);(312234334099928043%positive,1);(20800043155%positive,1);(348966818560668651%positive,1);(312234334099559082%positive,0);(348966818560299690%positive,0);(305078165571588574%positive,1);(312234334099560126%positive,1);(348966818560300734%positive,1);(348966818560300011%positive,1);(305060229788160478%positive,1);(75499210494430%positive,1)] [312234334099559403%positive;19067385031905758%positive;348966818560669374%positive;19066264045441502%positive;305078164816613854%positive;305060229788160478%positive;1207992429007326%positive;305060229033185758%positive;76229085033451%positive;312234334099927722%positive;348966818560668330%positive;85196976747499%positive;4764317814590%positive;5324811046718%positive;4711490319018%positive;312234334099928766%positive;1207991674032606%positive;312234334099928043%positive;20800043155%positive;348966818560668651%positive;312234334099559082%positive;348966818560299690%positive;305078165571588574%positive;312234334099560126%positive;348966818560300734%positive;348966818560300011%positive;4711489950378%positive;75499210494430%positive]]
  | StC => [HMeas MLeft 50 [(1136457873%positive,0);(75499210495645%positive,2);(1207991674033821%positive,2);(1207992429008361%positive,2);(305060229033186793%positive,2);(305060229788161693%positive,2);(19067385031906793%positive,0);(305078165571589789%positive,2);(312234334099559403%positive,1);(19066264045442537%positive,2);(290945206557%positive,2);(76229085033451%positive,1);(85196976747499%positive,1);(75499210495465%positive,2);(1207991674033641%positive,2);(19067385031906973%positive,2);(305078165571589609%positive,0);(19066264045442717%positive,2);(305060229788161513%positive,2);(312234334099928043%positive,1);(305078164816615069%positive,2);(305060229033186973%positive,2);(20800043155%positive,1);(348966818560668651%positive,1);(305078164816614889%positive,0);(1207992429008541%positive,2);(348966818560300011%positive,1)] [1136457873%positive;75499210495645%positive;1207991674033821%positive;1207992429008361%positive;305060229788161693%positive;305078165571589789%positive;19067385031906793%positive;312234334099559403%positive;19066264045442537%positive;290945206557%positive;76229085033451%positive;85196976747499%positive;75499210495465%positive;1207991674033641%positive;19067385031906973%positive;305078165571589609%positive;19066264045442717%positive;305060229788161513%positive;312234334099928043%positive;305078164816615069%positive;305060229033186973%positive;20800043155%positive;348966818560668651%positive;305078164816614889%positive;1207992429008541%positive;348966818560300011%positive;305060229033186793%positive]]
  | StD => [HMeas MRight 50 [(1136457873%positive,4);(75499210495645%positive,0);(1207991674033821%positive,0);(4711489950378%positive,3);(1207992429008361%positive,2);(305060229033186793%positive,2);(305060229788161693%positive,0);(19067385031906793%positive,4);(305078165571589789%positive,4);(19066264045442537%positive,2);(19067385031905758%positive,4);(348966818560669374%positive,4);(19066264045441502%positive,4);(305078164816613854%positive,4);(290945206557%positive,4);(1207992429007326%positive,4);(305060229033185758%positive,4);(312234334099927722%positive,1);(348966818560668330%positive,1);(4764317814590%positive,4);(5324811046718%positive,4);(4711490319018%positive,1);(312234334099928766%positive,4);(75499210495465%positive,2);(1207991674033641%positive,2);(19067385031906973%positive,4);(305078165571589609%positive,4);(19066264045442717%positive,0);(1207991674032606%positive,4);(305060229788161513%positive,2);(305078164816615069%positive,4);(305060229033186973%positive,0);(312234334099559082%positive,3);(348966818560299690%positive,3);(305078164816614889%positive,4);(305078165571588574%positive,4);(1207992429008541%positive,0);(312234334099560126%positive,4);(348966818560300734%positive,4);(305060229788160478%positive,4);(75499210494430%positive,4)] [1136457873%positive;75499210495645%positive;1207991674033821%positive;4711489950378%positive;1207992429008361%positive;305060229788161693%positive;305078165571589789%positive;19067385031906793%positive;19066264045442537%positive;19067385031905758%positive;348966818560669374%positive;19066264045441502%positive;305078164816613854%positive;290945206557%positive;305060229788160478%positive;1207992429007326%positive;305060229033185758%positive;312234334099927722%positive;348966818560668330%positive;4764317814590%positive;5324811046718%positive;4711490319018%positive;312234334099928766%positive;75499210495465%positive;1207991674033641%positive;19067385031906973%positive;305078165571589609%positive;19066264045442717%positive;1207991674032606%positive;305060229788161513%positive;305078164816615069%positive;305060229033186973%positive;312234334099559082%positive;348966818560299690%positive;305078164816614889%positive;305078165571588574%positive;1207992429008541%positive;312234334099560126%positive;348966818560300734%positive;305060229033186793%positive;75499210494430%positive]]
  end.

Lemma cqh_h_00494 : iqh tmq_h_00494.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00494 StA 13 2 2 38 20000
                lsetq_h_00494 rsetq_h_00494 certq_h_00494 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 38) 2000 tmq_h_00494); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00495 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StC)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StB)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S0 DR StA)
  end.

Definition lsetq_h_00495 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition rsetq_h_00495 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition certq_h_00495 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 37 [(312234334099559403%positive,1);(19067385031905758%positive,1);(348966818560669374%positive,1);(305078164816613854%positive,1);(1207992429007326%positive,1);(76229085033451%positive,1);(85196976747499%positive,1);(4764317814590%positive,1);(5324811046718%positive,1);(4711490319018%positive,1);(312234334099928766%positive,1);(1207991674032606%positive,1);(312234334099928043%positive,1);(20800043155%positive,1);(348966818560668651%positive,1);(305078165571588574%positive,1);(312234334099560126%positive,1);(348966818560300734%positive,1);(348966818560300011%positive,1);(4711489950378%positive,0);(75499210494430%positive,1)] [312234334099559403%positive;19067385031905758%positive;348966818560669374%positive;305078164816613854%positive;1207992429007326%positive;76229085033451%positive;85196976747499%positive;4764317814590%positive;5324811046718%positive;4711490319018%positive;312234334099928766%positive;1207991674032606%positive;312234334099928043%positive;20800043155%positive;348966818560668651%positive;305078165571588574%positive;312234334099560126%positive;348966818560300734%positive;348966818560300011%positive;4711489950378%positive;75499210494430%positive]]
  | StC => [HMeas MLeft 37 [(1136457873%positive,0);(75499210495645%positive,2);(1207991674033821%positive,2);(1207992429008361%positive,2);(19067385031906793%positive,0);(305078165571589789%positive,2);(312234334099559403%positive,1);(290945206557%positive,2);(76229085033451%positive,1);(85196976747499%positive,1);(75499210495465%positive,2);(1207991674033641%positive,2);(19067385031906973%positive,2);(305078165571589609%positive,0);(305078164816615069%positive,2);(312234334099928043%positive,1);(20800043155%positive,1);(348966818560668651%positive,1);(305078164816614889%positive,0);(1207992429008541%positive,2);(348966818560300011%positive,1)] [1136457873%positive;75499210495645%positive;1207991674033821%positive;1207992429008361%positive;305078165571589789%positive;19067385031906793%positive;312234334099559403%positive;290945206557%positive;76229085033451%positive;85196976747499%positive;75499210495465%positive;1207991674033641%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;312234334099928043%positive;20800043155%positive;348966818560668651%positive;305078164816614889%positive;1207992429008541%positive;348966818560300011%positive]]
  | StD => [HMeas MRight 37 [(1136457873%positive,4);(75499210495645%positive,0);(1207991674033821%positive,0);(1207992429008361%positive,2);(19067385031906793%positive,4);(305078165571589789%positive,4);(19067385031905758%positive,4);(348966818560669374%positive,4);(305078164816613854%positive,4);(290945206557%positive,4);(1207992429007326%positive,4);(4764317814590%positive,4);(5324811046718%positive,4);(4711490319018%positive,1);(312234334099928766%positive,4);(75499210495465%positive,2);(1207991674033641%positive,2);(19067385031906973%positive,4);(305078165571589609%positive,4);(305078164816615069%positive,4);(1207991674032606%positive,4);(305078164816614889%positive,4);(305078165571588574%positive,4);(1207992429008541%positive,0);(312234334099560126%positive,4);(348966818560300734%positive,4);(4711489950378%positive,3);(75499210494430%positive,4)] [1136457873%positive;75499210495645%positive;1207991674033821%positive;1207992429008361%positive;305078165571589789%positive;19067385031906793%positive;19067385031905758%positive;348966818560669374%positive;305078164816613854%positive;290945206557%positive;1207992429007326%positive;4764317814590%positive;5324811046718%positive;4711490319018%positive;312234334099928766%positive;75499210495465%positive;1207991674033641%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;1207991674032606%positive;305078164816614889%positive;305078165571588574%positive;1207992429008541%positive;312234334099560126%positive;348966818560300734%positive;4711489950378%positive;75499210494430%positive]]
  end.

Lemma cqh_h_00495 : iqh tmq_h_00495.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00495 StA 5 2 2 30 20000
                lsetq_h_00495 rsetq_h_00495 certq_h_00495 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 30) 2000 tmq_h_00495); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00496 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StC)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00496 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition rsetq_h_00496 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition certq_h_00496 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 35 [(1207989527598782%positive,2);(1207989527598059%positive,0);(312255777477710302%positive,2);(19067385031905758%positive,2);(348966818560669374%positive,2);(4713636385450%positive,1);(305078164816613854%positive,2);(85196976747499%positive,2);(1207989527967422%positive,2);(5324811046718%positive,2);(312255776722735582%positive,2);(19515985776038366%positive,2);(20800043155%positive,2);(348966818560668651%positive,2);(4714391360170%positive,1);(305078165571588574%positive,2);(1207989527966699%positive,0);(348966818560300734%positive,2);(348966818560300011%positive,2)] [1207989527598782%positive;1207989527598059%positive;312255777477710302%positive;19067385031905758%positive;348966818560669374%positive;305078164816613854%positive;4713636385450%positive;85196976747499%positive;1207989527967422%positive;5324811046718%positive;312255776722735582%positive;19515985776038366%positive;20800043155%positive;348966818560668651%positive;4714391360170%positive;305078165571588574%positive;1207989527966699%positive;348966818560300734%positive;348966818560300011%positive]]
  | StC => [HMeas MLeft 35 [(1136457873%positive,0);(1207989527598059%positive,2);(19067385031906793%positive,0);(305078165571589789%positive,2);(312255776722736617%positive,1);(19515985776039401%positive,1);(312255777477711517%positive,2);(290945206557%positive,2);(85196976747499%positive,1);(19067385031906973%positive,2);(305078165571589609%positive,0);(305078164816615069%positive,2);(20800043155%positive,1);(348966818560668651%positive,1);(312255776722736797%positive,2);(19515985776039581%positive,2);(312255777477711337%positive,1);(305078164816614889%positive,0);(1207989527966699%positive,2);(348966818560300011%positive,1)] [1136457873%positive;1207989527598059%positive;305078165571589789%positive;19067385031906793%positive;312255776722736617%positive;19515985776039401%positive;312255777477711517%positive;290945206557%positive;85196976747499%positive;348966818560300011%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;20800043155%positive;348966818560668651%positive;312255776722736797%positive;19515985776039581%positive;312255777477711337%positive;305078164816614889%positive;1207989527966699%positive]]
  | StD => [HMeas MRight 35 [(1136457873%positive,1);(1207989527598782%positive,1);(312255777477710302%positive,1);(19067385031906793%positive,1);(305078165571589789%positive,1);(19067385031905758%positive,1);(348966818560669374%positive,1);(312255776722736617%positive,1);(19515985776039401%positive,1);(4713636385450%positive,0);(312255777477711517%positive,1);(305078164816613854%positive,1);(290945206557%positive,1);(1207989527967422%positive,1);(5324811046718%positive,1);(312255776722735582%positive,1);(19067385031906973%positive,1);(305078165571589609%positive,1);(305078164816615069%positive,1);(19515985776038366%positive,1);(4714391360170%positive,0);(312255776722736797%positive,1);(19515985776039581%positive,1);(312255777477711337%positive,1);(305078164816614889%positive,1);(305078165571588574%positive,1);(348966818560300734%positive,1)] [1136457873%positive;1207989527598782%positive;312255777477710302%positive;305078165571589789%positive;19067385031906793%positive;19067385031905758%positive;348966818560669374%positive;312255776722736617%positive;19515985776039401%positive;4713636385450%positive;312255777477711517%positive;305078164816613854%positive;290945206557%positive;1207989527967422%positive;5324811046718%positive;312255776722735582%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;19515985776038366%positive;4714391360170%positive;312255776722736797%positive;19515985776039581%positive;312255777477711337%positive;305078164816614889%positive;305078165571588574%positive;348966818560300734%positive]]
  end.

Lemma cqh_h_00496 : iqh tmq_h_00496.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00496 StA 4 2 2 29 20000
                lsetq_h_00496 rsetq_h_00496 certq_h_00496 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00496); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00497 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StA)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00497 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00497 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition certq_h_00497 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 37 [(314652163455309742%positive,4);(356852788752799647%positive,4);(5445141436191%positive,4);(75791334364922%positive,2);(1212666493260527%positive,4);(4709410501563%positive,1);(356852788753168287%positive,4);(314652164210284282%positive,4);(75791334363887%positive,4);(321809154152691615%positive,4);(1212665738286842%positive,2);(1172076690%positive,4);(19665759941678842%positive,4);(1212666493261562%positive,2);(314652164210283247%positive,4);(4709410132923%positive,3);(321809154152322975%positive,4);(1212665738285807%positive,4);(19665759941677807%positive,4);(314652163455309562%positive,4);(75791334365102%positive,0);(4910418007839%positive,4);(314652164210284462%positive,4);(314652163455308527%positive,4);(1212665738287022%positive,0);(19665759941679022%positive,4);(1212666493261742%positive,0);(300075682094%positive,4)] [314652163455309742%positive;356852788752799647%positive;5445141436191%positive;75791334364922%positive;1212666493260527%positive;4709410501563%positive;314652164210284282%positive;75791334363887%positive;321809154152691615%positive;1212665738286842%positive;1172076690%positive;19665759941678842%positive;1212666493261562%positive;314652164210283247%positive;4709410132923%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;314652163455309562%positive;75791334365102%positive;4910418007839%positive;314652164210284462%positive;1212666493261742%positive;314652163455308527%positive;1212665738287022%positive;19665759941679022%positive;356852788753168287%positive;300075682094%positive]]
  | StC => [HMeas MRight 37 [(78566688125433%positive,1);(356852788752799647%positive,1);(321809154152690169%positive,1);(5445141436191%positive,1);(1212666493260527%positive,1);(321809154152321529%positive,1);(4709410501563%positive,1);(356852788753168287%positive,1);(75791334363887%positive,1);(21270083729%positive,1);(321809154152691615%positive,1);(314652164210283247%positive,1);(4709410132923%positive,0);(87122262979065%positive,1);(321809154152322975%positive,1);(1212665738285807%positive,1);(19665759941677807%positive,1);(356852788753166841%positive,1);(4910418007839%positive,1);(314652163455308527%positive,1);(356852788752798201%positive,1)] [78566688125433%positive;356852788752799647%positive;321809154152690169%positive;5445141436191%positive;1212666493260527%positive;321809154152321529%positive;4709410501563%positive;75791334363887%positive;21270083729%positive;321809154152691615%positive;314652164210283247%positive;4709410132923%positive;87122262979065%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;356852788753166841%positive;4910418007839%positive;314652163455308527%positive;356852788752798201%positive;356852788753168287%positive]]
  | StD => [HMeas MLeft 37 [(314652163455309742%positive,2);(78566688125433%positive,1);(321809154152690169%positive,1);(75791334364922%positive,2);(321809154152321529%positive,1);(314652164210284282%positive,0);(21270083729%positive,1);(1212665738286842%positive,2);(1172076690%positive,0);(19665759941678842%positive,0);(1212666493261562%positive,2);(87122262979065%positive,1);(314652163455309562%positive,0);(75791334365102%positive,2);(356852788753166841%positive,1);(314652164210284462%positive,2);(1212665738287022%positive,2);(19665759941679022%positive,2);(356852788752798201%positive,1);(1212666493261742%positive,2);(300075682094%positive,2)] [314652163455309742%positive;78566688125433%positive;321809154152690169%positive;75791334364922%positive;321809154152321529%positive;314652164210284282%positive;21270083729%positive;1212665738286842%positive;1172076690%positive;19665759941678842%positive;1212666493261562%positive;87122262979065%positive;314652163455309562%positive;75791334365102%positive;356852788753166841%positive;314652164210284462%positive;1212665738287022%positive;19665759941679022%positive;356852788752798201%positive;1212666493261742%positive;300075682094%positive]]
  end.

Lemma cqh_h_00497 : iqh tmq_h_00497.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00497 StA 23 2 2 48 20000
                lsetq_h_00497 rsetq_h_00497 certq_h_00497 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 48) 2000 tmq_h_00497); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00498 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StA)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00498 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00498 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition certq_h_00498 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 37 [(314652163455309742%positive,4);(356852788752799647%positive,4);(5445141436191%positive,4);(75791334364922%positive,2);(1212666493260527%positive,4);(4709410501563%positive,1);(356852788753168287%positive,4);(314652164210284282%positive,4);(75791334363887%positive,4);(321809154152691615%positive,4);(1212665738286842%positive,2);(1172076690%positive,4);(19665759941678842%positive,4);(1212666493261562%positive,2);(314652164210283247%positive,4);(4709410132923%positive,3);(321809154152322975%positive,4);(1212665738285807%positive,4);(19665759941677807%positive,4);(314652163455309562%positive,4);(75791334365102%positive,0);(4910418007839%positive,4);(314652164210284462%positive,4);(314652163455308527%positive,4);(1212665738287022%positive,0);(19665759941679022%positive,4);(1212666493261742%positive,0);(300075682094%positive,4)] [314652163455309742%positive;356852788752799647%positive;5445141436191%positive;75791334364922%positive;1212666493260527%positive;4709410501563%positive;314652164210284282%positive;75791334363887%positive;321809154152691615%positive;1212665738286842%positive;1172076690%positive;19665759941678842%positive;1212666493261562%positive;314652164210283247%positive;4709410132923%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;314652163455309562%positive;75791334365102%positive;4910418007839%positive;314652164210284462%positive;1212666493261742%positive;314652163455308527%positive;1212665738287022%positive;19665759941679022%positive;356852788753168287%positive;300075682094%positive]]
  | StC => [HMeas MRight 37 [(78566688125433%positive,1);(356852788752799647%positive,1);(321809154152690169%positive,1);(5445141436191%positive,1);(1212666493260527%positive,1);(321809154152321529%positive,1);(4709410501563%positive,1);(356852788753168287%positive,1);(75791334363887%positive,1);(21270083729%positive,1);(321809154152691615%positive,1);(314652164210283247%positive,1);(4709410132923%positive,0);(87122262979065%positive,1);(321809154152322975%positive,1);(1212665738285807%positive,1);(19665759941677807%positive,1);(356852788753166841%positive,1);(4910418007839%positive,1);(314652163455308527%positive,1);(356852788752798201%positive,1)] [78566688125433%positive;356852788752799647%positive;321809154152690169%positive;5445141436191%positive;1212666493260527%positive;321809154152321529%positive;4709410501563%positive;75791334363887%positive;21270083729%positive;321809154152691615%positive;314652164210283247%positive;4709410132923%positive;87122262979065%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;356852788753166841%positive;4910418007839%positive;314652163455308527%positive;356852788752798201%positive;356852788753168287%positive]]
  | StD => [HMeas MLeft 37 [(314652163455309742%positive,2);(78566688125433%positive,1);(321809154152690169%positive,1);(75791334364922%positive,2);(321809154152321529%positive,1);(314652164210284282%positive,0);(21270083729%positive,1);(1212665738286842%positive,2);(1172076690%positive,0);(19665759941678842%positive,0);(1212666493261562%positive,2);(87122262979065%positive,1);(314652163455309562%positive,0);(75791334365102%positive,2);(356852788753166841%positive,1);(314652164210284462%positive,2);(1212665738287022%positive,2);(19665759941679022%positive,2);(356852788752798201%positive,1);(1212666493261742%positive,2);(300075682094%positive,2)] [314652163455309742%positive;78566688125433%positive;321809154152690169%positive;75791334364922%positive;321809154152321529%positive;314652164210284282%positive;21270083729%positive;1212665738286842%positive;1172076690%positive;19665759941678842%positive;1212666493261562%positive;87122262979065%positive;314652163455309562%positive;75791334365102%positive;356852788753166841%positive;314652164210284462%positive;1212665738287022%positive;19665759941679022%positive;356852788752798201%positive;1212666493261742%positive;300075682094%positive]]
  end.

Lemma cqh_h_00498 : iqh tmq_h_00498.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00498 StA 25 2 2 50 20000
                lsetq_h_00498 rsetq_h_00498 certq_h_00498 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 50) 2000 tmq_h_00498); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00499 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => None
  end.

Definition lsetq_h_00499 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StA,S0);(StC,S1)])]].

Definition rsetq_h_00499 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StA,S0)])]].

Definition certq_h_00499 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 37 [(4524071228074%positive,3);(1358737207285225%positive,2);(19073951769851369%positive,4);(347836724567896542%positive,4);(74507626043037%positive,0);(1333998195660445%positive,0);(347836724567897757%positive,4);(4524118413994%positive,1);(296492628957918862%positive,4);(1358737207284190%positive,4);(1149728881%positive,4);(4705315516174%positive,4);(74507626042857%positive,2);(341503537591907817%positive,4);(341503537591907997%positive,4);(19073951769850334%positive,4);(1358737207285405%positive,0);(74507626041822%positive,4);(294330779421%positive,4);(1333998195660265%positive,2);(347836724567897577%positive,4);(4705576611598%positive,4);(341503537591906782%positive,4);(296492624780392078%positive,4);(296489532403938958%positive,4);(19073951769851549%positive,4);(296489536581465742%positive,4);(1333998195659230%positive,4)] [4524071228074%positive;1358737207285225%positive;19073951769851369%positive;74507626043037%positive;347836724567896542%positive;1333998195660445%positive;347836724567897757%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;1149728881%positive;4705315516174%positive;74507626042857%positive;341503537591907817%positive;19073951769850334%positive;1358737207285405%positive;74507626041822%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;19073951769851549%positive;341503537591907997%positive;296489536581465742%positive;1333998195659230%positive]]
  | StB => [HMeas MLeft 37 [(4524071228074%positive,0);(296489536581464296%positive,1);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(347836724567896542%positive,1);(4524118413994%positive,1);(296492628957918862%positive,1);(1358737207284190%positive,1);(296492628957917416%positive,1);(18415324912%positive,1);(4705315516174%positive,1);(19073951769850334%positive,1);(74507626041822%positive,1);(4705576611598%positive,1);(341503537591906782%positive,1);(296492624780392078%positive,1);(296489532403938958%positive,1);(75285048258792%positive,1);(296489536581465742%positive,1);(1333998195659230%positive,1)] [4524071228074%positive;296489536581464296%positive;296492624780390632%positive;296489532403937512%positive;75289225785576%positive;347836724567896542%positive;4524118413994%positive;296492628957918862%positive;1358737207284190%positive;296492628957917416%positive;18415324912%positive;4705315516174%positive;19073951769850334%positive;74507626041822%positive;4705576611598%positive;341503537591906782%positive;296492624780392078%positive;296489532403938958%positive;75285048258792%positive;296489536581465742%positive;1333998195659230%positive]]
  | StC => [HMeas MRight 37 [(296489536581464296%positive,1);(1358737207285225%positive,2);(19073951769851369%positive,0);(296492624780390632%positive,1);(296489532403937512%positive,1);(75289225785576%positive,1);(74507626043037%positive,2);(1333998195660445%positive,2);(347836724567897757%positive,2);(296492628957917416%positive,1);(1149728881%positive,0);(18415324912%positive,1);(74507626042857%positive,2);(341503537591907817%positive,0);(341503537591907997%positive,2);(1358737207285405%positive,2);(294330779421%positive,2);(1333998195660265%positive,2);(347836724567897577%positive,0);(19073951769851549%positive,2);(75285048258792%positive,1)] [296489536581464296%positive;1358737207285225%positive;296492624780390632%positive;19073951769851369%positive;296489532403937512%positive;75289225785576%positive;74507626043037%positive;1333998195660445%positive;347836724567897757%positive;296492628957917416%positive;1149728881%positive;18415324912%positive;75285048258792%positive;74507626042857%positive;341503537591907817%positive;1358737207285405%positive;294330779421%positive;1333998195660265%positive;347836724567897577%positive;19073951769851549%positive;341503537591907997%positive]]
  | StD => []
  end.

Lemma cqh_h_00499 : iqh tmq_h_00499.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00499 StD 8 2 2 33 20000
                lsetq_h_00499 rsetq_h_00499 certq_h_00499 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 33) 2000 tmq_h_00499); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition nghw_04 : list TM :=
  [tmq_h_00400;
   tmq_h_00401;
   tmq_h_00402;
   tmq_h_00403;
   tmq_h_00404;
   tmq_h_00405;
   tmq_h_00406;
   tmq_h_00407;
   tmq_h_00408;
   tmq_h_00409;
   tmq_h_00410;
   tmq_h_00411;
   tmq_h_00412;
   tmq_h_00413;
   tmq_h_00414;
   tmq_h_00415;
   tmq_h_00416;
   tmq_h_00417;
   tmq_h_00418;
   tmq_h_00419;
   tmq_h_00420;
   tmq_h_00421;
   tmq_h_00422;
   tmq_h_00423;
   tmq_h_00424;
   tmq_h_00425;
   tmq_h_00426;
   tmq_h_00427;
   tmq_h_00428;
   tmq_h_00429;
   tmq_h_00430;
   tmq_h_00431;
   tmq_h_00432;
   tmq_h_00433;
   tmq_h_00434;
   tmq_h_00435;
   tmq_h_00436;
   tmq_h_00437;
   tmq_h_00438;
   tmq_h_00439;
   tmq_h_00440;
   tmq_h_00441;
   tmq_h_00442;
   tmq_h_00443;
   tmq_h_00444;
   tmq_h_00445;
   tmq_h_00446;
   tmq_h_00447;
   tmq_h_00448;
   tmq_h_00449;
   tmq_h_00450;
   tmq_h_00451;
   tmq_h_00452;
   tmq_h_00453;
   tmq_h_00454;
   tmq_h_00455;
   tmq_h_00456;
   tmq_h_00457;
   tmq_h_00458;
   tmq_h_00459;
   tmq_h_00460;
   tmq_h_00461;
   tmq_h_00462;
   tmq_h_00463;
   tmq_h_00464;
   tmq_h_00465;
   tmq_h_00466;
   tmq_h_00467;
   tmq_h_00468;
   tmq_h_00469;
   tmq_h_00470;
   tmq_h_00471;
   tmq_h_00472;
   tmq_h_00473;
   tmq_h_00474;
   tmq_h_00475;
   tmq_h_00476;
   tmq_h_00477;
   tmq_h_00478;
   tmq_h_00479;
   tmq_h_00480;
   tmq_h_00481;
   tmq_h_00482;
   tmq_h_00483;
   tmq_h_00484;
   tmq_h_00485;
   tmq_h_00486;
   tmq_h_00487;
   tmq_h_00488;
   tmq_h_00489;
   tmq_h_00490;
   tmq_h_00491;
   tmq_h_00492;
   tmq_h_00493;
   tmq_h_00494;
   tmq_h_00495;
   tmq_h_00496;
   tmq_h_00497;
   tmq_h_00498;
   tmq_h_00499].

Lemma nghw_04_all : Forall iqh nghw_04.

Proof. unfold nghw_04. exact (Forall_cons _ cqh_h_00400 (Forall_cons _ cqh_h_00401 (Forall_cons _ cqh_h_00402 (Forall_cons _ cqh_h_00403 (Forall_cons _ cqh_h_00404 (Forall_cons _ cqh_h_00405 (Forall_cons _ cqh_h_00406 (Forall_cons _ cqh_h_00407 (Forall_cons _ cqh_h_00408 (Forall_cons _ cqh_h_00409 (Forall_cons _ cqh_h_00410 (Forall_cons _ cqh_h_00411 (Forall_cons _ cqh_h_00412 (Forall_cons _ cqh_h_00413 (Forall_cons _ cqh_h_00414 (Forall_cons _ cqh_h_00415 (Forall_cons _ cqh_h_00416 (Forall_cons _ cqh_h_00417 (Forall_cons _ cqh_h_00418 (Forall_cons _ cqh_h_00419 (Forall_cons _ cqh_h_00420 (Forall_cons _ cqh_h_00421 (Forall_cons _ cqh_h_00422 (Forall_cons _ cqh_h_00423 (Forall_cons _ cqh_h_00424 (Forall_cons _ cqh_h_00425 (Forall_cons _ cqh_h_00426 (Forall_cons _ cqh_h_00427 (Forall_cons _ cqh_h_00428 (Forall_cons _ cqh_h_00429 (Forall_cons _ cqh_h_00430 (Forall_cons _ cqh_h_00431 (Forall_cons _ cqh_h_00432 (Forall_cons _ cqh_h_00433 (Forall_cons _ cqh_h_00434 (Forall_cons _ cqh_h_00435 (Forall_cons _ cqh_h_00436 (Forall_cons _ cqh_h_00437 (Forall_cons _ cqh_h_00438 (Forall_cons _ cqh_h_00439 (Forall_cons _ cqh_h_00440 (Forall_cons _ cqh_h_00441 (Forall_cons _ cqh_h_00442 (Forall_cons _ cqh_h_00443 (Forall_cons _ cqh_h_00444 (Forall_cons _ cqh_h_00445 (Forall_cons _ cqh_h_00446 (Forall_cons _ cqh_h_00447 (Forall_cons _ cqh_h_00448 (Forall_cons _ cqh_h_00449 (Forall_cons _ cqh_h_00450 (Forall_cons _ cqh_h_00451 (Forall_cons _ cqh_h_00452 (Forall_cons _ cqh_h_00453 (Forall_cons _ cqh_h_00454 (Forall_cons _ cqh_h_00455 (Forall_cons _ cqh_h_00456 (Forall_cons _ cqh_h_00457 (Forall_cons _ cqh_h_00458 (Forall_cons _ cqh_h_00459 (Forall_cons _ cqh_h_00460 (Forall_cons _ cqh_h_00461 (Forall_cons _ cqh_h_00462 (Forall_cons _ cqh_h_00463 (Forall_cons _ cqh_h_00464 (Forall_cons _ cqh_h_00465 (Forall_cons _ cqh_h_00466 (Forall_cons _ cqh_h_00467 (Forall_cons _ cqh_h_00468 (Forall_cons _ cqh_h_00469 (Forall_cons _ cqh_h_00470 (Forall_cons _ cqh_h_00471 (Forall_cons _ cqh_h_00472 (Forall_cons _ cqh_h_00473 (Forall_cons _ cqh_h_00474 (Forall_cons _ cqh_h_00475 (Forall_cons _ cqh_h_00476 (Forall_cons _ cqh_h_00477 (Forall_cons _ cqh_h_00478 (Forall_cons _ cqh_h_00479 (Forall_cons _ cqh_h_00480 (Forall_cons _ cqh_h_00481 (Forall_cons _ cqh_h_00482 (Forall_cons _ cqh_h_00483 (Forall_cons _ cqh_h_00484 (Forall_cons _ cqh_h_00485 (Forall_cons _ cqh_h_00486 (Forall_cons _ cqh_h_00487 (Forall_cons _ cqh_h_00488 (Forall_cons _ cqh_h_00489 (Forall_cons _ cqh_h_00490 (Forall_cons _ cqh_h_00491 (Forall_cons _ cqh_h_00492 (Forall_cons _ cqh_h_00493 (Forall_cons _ cqh_h_00494 (Forall_cons _ cqh_h_00495 (Forall_cons _ cqh_h_00496 (Forall_cons _ cqh_h_00497 (Forall_cons _ cqh_h_00498 (Forall_cons _ cqh_h_00499 (Forall_nil iqh))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))). Qed.
