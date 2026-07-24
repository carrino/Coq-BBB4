(* UNTRUSTED-generated R_QH tier; the Coq kernel re-checks via vm_compute. *)
From Coq Require Import List ZArith Lia.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import NGram NGramHist NGramHistWrap.
From BBB4.Census Require Import TNF_QH.
Import ListNotations.

Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.


Definition tmq_h_00000 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StB)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => None
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Definition lsetq_h_00000 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StC,S0)]);(S0,[(StB,S1);(StD,S1)])];
   [(S0,[(StB,S1);(StC,S0)]);(S1,[(StD,S0)])];
   [(S0,[(StB,S1);(StC,S0)]);(S1,[(StD,S0);(StB,S1)])];
   [(S0,[(StB,S1);(StD,S1)]);(S0,[(StB,S1);(StC,S0)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1)]);(S0,[(StB,S1);(StC,S0)])]].

Definition rsetq_h_00000 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S0);(StB,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S1)]);(S0,[(StB,S0);(StB,S0)])];
   [(S1,[(StC,S0);(StB,S1)]);(S1,[(StD,S1);(StD,S0)])];
   [(S1,[(StD,S1);(StD,S0)]);(S1,[(StC,S0);(StB,S1)])]].

Definition certq_h_00000 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 35 [(324213790123415515%positive,0);(339406014060032730%positive,1);(20230174866%positive,1);(324213792388339135%positive,2);(302680954405050331%positive,1);(1207744659%positive,0);(20263361758811583%positive,2);(302680956669973951%positive,2);(82862796305114%positive,1);(18917559526413759%positive,2);(339406014061138650%positive,1);(324213792388339675%positive,0);(1203315462238938%positive,2);(302680954405049791%positive,2);(324213790123414975%positive,2);(302680956669974491%positive,1);(18917559526414299%positive,1);(309194361151%positive,2);(20263361758812123%positive,0);(1203315463344858%positive,2)] [324213790123415515%positive;339406014060032730%positive;20230174866%positive;324213792388339135%positive;1207744659%positive;302680954405050331%positive;20263361758811583%positive;302680956669973951%positive;82862796305114%positive;18917559526413759%positive;339406014061138650%positive;324213792388339675%positive;1203315462238938%positive;302680954405049791%positive;324213790123414975%positive;302680956669974491%positive;18917559526414299%positive;309194361151%positive;20263361758812123%positive;1203315463344858%positive]]
  | StC => [HMeas MRight 35 [(324213790123415515%positive,1);(1203315462239661%positive,1);(324213790123414525%positive,1);(324213792388339135%positive,1);(302680954405050331%positive,1);(1207744659%positive,1);(20263361758811583%positive,1);(302680956669973951%positive,1);(324213792388338685%positive,1);(18917559526413759%positive,1);(324213792388339675%positive,1);(4715716202905%positive,0);(1203315463345581%positive,1);(302680954405049791%positive,1);(302680956669973501%positive,1);(339406014060033453%positive,1);(4713451278745%positive,0);(324213790123414975%positive,1);(302680956669974491%positive,1);(20263361758811133%positive,1);(18917559526414299%positive,1);(309194361151%positive,1);(20263361758812123%positive,1);(18917559526413309%positive,1);(5178924769069%positive,1);(302680954405049341%positive,1);(339406014061139373%positive,1)] [324213790123415515%positive;1203315462239661%positive;324213790123414525%positive;324213792388339135%positive;1207744659%positive;302680954405050331%positive;20263361758811583%positive;302680956669973951%positive;324213792388338685%positive;18917559526413759%positive;324213792388339675%positive;4715716202905%positive;1203315463345581%positive;302680954405049791%positive;302680956669973501%positive;339406014060033453%positive;4713451278745%positive;324213790123414975%positive;302680956669974491%positive;20263361758811133%positive;18917559526414299%positive;309194361151%positive;20263361758812123%positive;18917559526413309%positive;5178924769069%positive;302680954405049341%positive;339406014061139373%positive]]
  | StD => [HMeas MRight 35 [(339406014060032730%positive,2);(20230174866%positive,2);(1203315462239661%positive,2);(324213790123414525%positive,2);(82862796305114%positive,2);(324213792388338685%positive,2);(339406014061138650%positive,2);(4715716202905%positive,1);(1203315463345581%positive,2);(1203315462238938%positive,0);(302680956669973501%positive,2);(339406014060033453%positive,2);(4713451278745%positive,1);(20263361758811133%positive,2);(18917559526413309%positive,2);(5178924769069%positive,2);(302680954405049341%positive,2);(339406014061139373%positive,2);(1203315463344858%positive,0)] [339406014060032730%positive;20230174866%positive;1203315462239661%positive;324213790123414525%positive;82862796305114%positive;324213792388338685%positive;339406014061138650%positive;4715716202905%positive;1203315463345581%positive;1203315462238938%positive;302680956669973501%positive;339406014060033453%positive;4713451278745%positive;20263361758811133%positive;18917559526413309%positive;5178924769069%positive;302680954405049341%positive;339406014061139373%positive;1203315463344858%positive]]
  end.

Lemma cqh_h_00000 : iqh tmq_h_00000.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00000 StA 0 2 2 25 20000
                lsetq_h_00000 rsetq_h_00000 certq_h_00000 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00000); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00001 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StB)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => None
  end.

Definition lsetq_h_00001 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StC,S1)]);(S0,[(StB,S1);(StD,S0)])];
   [(S0,[(StB,S1);(StD,S0)]);(S0,[(StB,S1);(StC,S1)])];
   [(S0,[(StB,S1);(StD,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StB,S1);(StD,S0)]);(S1,[(StC,S0);(StB,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S1)]);(S0,[(StB,S1);(StD,S0)])]].

Definition rsetq_h_00001 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S0);(StB,S0)]);(S0,[])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StB,S0);(StB,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StB,S1)])];
   [(S1,[(StD,S0);(StB,S1)]);(S1,[(StC,S1);(StC,S0)])]].

Definition certq_h_00001 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 37 [(19665244546586030%positive,2);(75207219795374%positive,2);(339964292163359707%positive,1);(302668857749197787%positive,1);(314643915726575022%positive,2);(75207219795674%positive,2);(1203318497924526%positive,2);(73893763707867%positive,1);(19665244546586330%positive,0);(1203319756215726%positive,2);(20263450771%positive,1);(314643916984866222%positive,2);(300067817774%positive,2);(1172109458%positive,0);(1203318497924826%positive,2);(302668857748583387%positive,1);(339964292162745307%positive,1);(314643915726575322%positive,0);(314643916984866522%positive,0);(1203319756216026%positive,2);(82999094375387%positive,1)] [19665244546586030%positive;75207219795374%positive;339964292163359707%positive;302668857749197787%positive;314643915726575022%positive;75207219795674%positive;1203318497924526%positive;73893763707867%positive;19665244546586330%positive;1203319756215726%positive;20263450771%positive;314643916984866222%positive;300067817774%positive;1172109458%positive;302668857748583387%positive;1203318497924826%positive;339964292162745307%positive;314643915726575322%positive;314643916984866522%positive;1203319756216026%positive;82999094375387%positive]]
  | StC => [HMeas MRight 37 [(4711422718361%positive,1);(339964292163359707%positive,1);(302668857749197787%positive,1);(73893763707867%positive,1);(20263450771%positive,1);(5187443398461%positive,1);(339964292163360189%positive,1);(4618360231741%positive,1);(302668857749198269%positive,1);(302668857748583387%positive,1);(339964292162745307%positive,1);(4711423332761%positive,0);(75207219794669%positive,1);(314643915726574317%positive,1);(19665244546585325%positive,1);(1203318497923821%positive,1);(339964292162745789%positive,1);(302668857748583869%positive,1);(1203319756215021%positive,1);(82999094375387%positive,1);(314643916984865517%positive,1)] [4711422718361%positive;339964292163359707%positive;302668857749197787%positive;73893763707867%positive;20263450771%positive;5187443398461%positive;339964292163360189%positive;4618360231741%positive;302668857748583387%positive;302668857749198269%positive;339964292162745307%positive;4711423332761%positive;75207219794669%positive;19665244546585325%positive;314643915726574317%positive;1203318497923821%positive;339964292162745789%positive;302668857748583869%positive;1203319756215021%positive;82999094375387%positive;314643916984865517%positive]]
  | StD => [HMeas MRight 37 [(19665244546586030%positive,4);(4711422718361%positive,1);(75207219795374%positive,0);(314643915726575022%positive,4);(75207219795674%positive,2);(1203318497924526%positive,0);(19665244546586330%positive,4);(1203319756215726%positive,0);(314643916984866222%positive,4);(300067817774%positive,4);(5187443398461%positive,4);(339964292163360189%positive,4);(1172109458%positive,4);(4618360231741%positive,4);(1203318497924826%positive,2);(302668857749198269%positive,4);(314643915726575322%positive,4);(4711423332761%positive,3);(75207219794669%positive,4);(314643916984866522%positive,4);(1203319756216026%positive,2);(314643915726574317%positive,4);(19665244546585325%positive,4);(1203318497923821%positive,4);(339964292162745789%positive,4);(302668857748583869%positive,4);(1203319756215021%positive,4);(314643916984865517%positive,4)] [19665244546586030%positive;4711422718361%positive;75207219795374%positive;314643915726575022%positive;75207219795674%positive;1203318497924526%positive;19665244546586330%positive;1203319756215726%positive;314643916984866222%positive;300067817774%positive;5187443398461%positive;339964292163360189%positive;1172109458%positive;4618360231741%positive;302668857749198269%positive;1203318497924826%positive;314643915726575322%positive;4711423332761%positive;75207219794669%positive;314643916984866522%positive;1203319756216026%positive;314643915726574317%positive;19665244546585325%positive;1203318497923821%positive;339964292162745789%positive;302668857748583869%positive;1203319756215021%positive;314643916984865517%positive]]
  end.

Lemma cqh_h_00001 : iqh tmq_h_00001.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00001 StA 0 2 2 25 20000
                lsetq_h_00001 rsetq_h_00001 certq_h_00001 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00001); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00002 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StB)
  | StC, S0 => Some (mkTrans S1 DL StB)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => None
  end.

Definition lsetq_h_00002 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StA,S0)]);(S0,[])];
   [(S0,[(StB,S0);(StB,S0)]);(S0,[(StA,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StB,S0);(StB,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StB,S1)])];
   [(S1,[(StD,S0);(StB,S1)]);(S1,[(StC,S1);(StC,S0)])]].

Definition rsetq_h_00002 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StC,S1)]);(S0,[(StB,S1);(StD,S0)])];
   [(S0,[(StB,S1);(StD,S0)]);(S0,[(StB,S1);(StC,S1)])];
   [(S0,[(StB,S1);(StD,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StB,S1);(StD,S0)]);(S1,[(StC,S0);(StB,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S1)]);(S0,[(StB,S1);(StD,S0)])]].

Definition certq_h_00002 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 37 [(75563231835099%positive,1);(339405395668629210%positive,0);(1150007794%positive,0);(322952306689012699%positive,1);(18411919219%positive,1);(322947152728257499%positive,1);(21212837075277530%positive,2);(75558785872859%positive,1);(322952302243050459%positive,1);(1228113728820654%positive,2);(21872544051942830%positive,2);(349960707295278510%positive,2);(19649822125323694%positive,2);(294402055982%positive,2);(322947148282295259%positive,1);(21872544051943130%positive,2);(1228113728820954%positive,2);(19649822125323994%positive,0);(349960707295278810%positive,0);(21212837075277230%positive,2);(339405395668628910%positive,2)] [75563231835099%positive;322952306689012699%positive;1150007794%positive;339405395668629210%positive;18411919219%positive;322947152728257499%positive;21212837075277530%positive;75558785872859%positive;322952302243050459%positive;1228113728820654%positive;21872544051942830%positive;19649822125323694%positive;349960707295278510%positive;294402055982%positive;322947148282295259%positive;21872544051943130%positive;1228113728820954%positive;19649822125323994%positive;349960707295278810%positive;21212837075277230%positive;339405395668628910%positive]]
  | StC => [HMeas MLeft 37 [(349960707295277805%positive,1);(21872544051942125%positive,1);(19649822125322989%positive,1);(75563231835099%positive,1);(322952306689012699%positive,1);(18411919219%positive,1);(339405395668628205%positive,1);(322947148282295741%positive,1);(1228113728819949%positive,1);(322947152728257499%positive,1);(78845777039769%positive,0);(322952306689013181%positive,1);(75558785872859%positive,1);(322952302243050459%positive,1);(21212837075276525%positive,1);(78844518748569%positive,1);(4722701989693%positive,1);(322947152728257981%positive,1);(322947148282295259%positive,1);(322952302243050941%positive,1);(4722424117053%positive,1)] [349960707295277805%positive;21872544051942125%positive;19649822125322989%positive;75563231835099%positive;322952306689012699%positive;18411919219%positive;339405395668628205%positive;322947148282295741%positive;1228113728819949%positive;322947152728257499%positive;78845777039769%positive;322952306689013181%positive;75558785872859%positive;322952302243050459%positive;21212837075276525%positive;78844518748569%positive;4722701989693%positive;322947152728257981%positive;322947148282295259%positive;322952302243050941%positive;4722424117053%positive]]
  | StD => [HMeas MLeft 37 [(349960707295277805%positive,4);(21872544051942125%positive,4);(19649822125322989%positive,4);(339405395668629210%positive,4);(1150007794%positive,4);(339405395668628205%positive,4);(322947148282295741%positive,4);(1228113728819949%positive,4);(21212837075277530%positive,2);(78845777039769%positive,3);(322952306689013181%positive,4);(21212837075276525%positive,4);(78844518748569%positive,1);(1228113728820654%positive,0);(21872544051942830%positive,0);(4722701989693%positive,4);(322947152728257981%positive,4);(349960707295278510%positive,4);(19649822125323694%positive,4);(294402055982%positive,4);(322952302243050941%positive,4);(21872544051943130%positive,2);(1228113728820954%positive,2);(19649822125323994%positive,4);(349960707295278810%positive,4);(21212837075277230%positive,0);(339405395668628910%positive,4);(4722424117053%positive,4)] [349960707295277805%positive;21872544051942125%positive;19649822125322989%positive;1150007794%positive;339405395668629210%positive;339405395668628205%positive;322947148282295741%positive;1228113728819949%positive;21212837075277530%positive;78845777039769%positive;322952306689013181%positive;21212837075276525%positive;78844518748569%positive;1228113728820654%positive;21872544051942830%positive;4722701989693%positive;322947152728257981%positive;349960707295278510%positive;19649822125323694%positive;294402055982%positive;322952302243050941%positive;21872544051943130%positive;1228113728820954%positive;19649822125323994%positive;349960707295278810%positive;21212837075277230%positive;339405395668628910%positive;4722424117053%positive]]
  end.

Lemma cqh_h_00002 : iqh tmq_h_00002.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00002 StA 0 2 2 25 20000
                lsetq_h_00002 rsetq_h_00002 certq_h_00002 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00002); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00003 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StB)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => None
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00003 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StA,S0)]);(S0,[])];
   [(S0,[(StB,S0);(StB,S0)]);(S0,[(StA,S0)])];
   [(S1,[(StC,S0);(StB,S1)]);(S0,[(StB,S0);(StB,S0)])];
   [(S1,[(StC,S0);(StB,S1)]);(S1,[(StD,S1);(StD,S0)])];
   [(S1,[(StD,S1);(StD,S0)]);(S1,[(StC,S0);(StB,S1)])]].

Definition rsetq_h_00003 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StC,S0)]);(S0,[(StB,S1);(StD,S1)])];
   [(S0,[(StB,S1);(StC,S0)]);(S1,[(StD,S0)])];
   [(S0,[(StB,S1);(StC,S0)]);(S1,[(StD,S0);(StB,S1)])];
   [(S0,[(StB,S1);(StD,S1)]);(S0,[(StB,S1);(StC,S0)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1)]);(S0,[(StB,S1);(StC,S0)])]].

Definition certq_h_00003 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 35 [(20208375173052379%positive,0);(19621263929299674%positive,2);(75838043189978%positive,1);(20208372606137791%positive,2);(1150286195%positive,0);(18411659250%positive,1);(358963507077412287%positive,2);(358963509644326335%positive,2);(313949505414230746%positive,1);(294473357119%positive,2);(339963946149443547%positive,1);(339963948716357595%positive,0);(358963507077412827%positive,1);(20208375173051839%positive,2);(19621843749884634%positive,2);(313940228284871386%positive,1);(358963509644326875%positive,0);(339963946149443007%positive,2);(20208372606138331%positive,1);(339963948716357055%positive,2)] [20208375173052379%positive;19621263929299674%positive;75838043189978%positive;20208372606137791%positive;1150286195%positive;18411659250%positive;358963507077412287%positive;358963509644326335%positive;313949505414230746%positive;294473357119%positive;339963946149443547%positive;339963948716357595%positive;358963507077412827%positive;20208375173051839%positive;19621843749884634%positive;313940228284871386%positive;358963509644326875%positive;339963946149443007%positive;20208372606138331%positive;339963948716357055%positive]]
  | StC => [HMeas MLeft 35 [(20208375173052379%positive,1);(20208375173051389%positive,1);(19621843749885357%positive,1);(20208372606137791%positive,1);(1150286195%positive,1);(313940228284872109%positive,1);(339963946149442557%positive,1);(358963507077412287%positive,1);(339963948716356605%positive,1);(358963509644326335%positive,1);(294473357119%positive,1);(339963946149443547%positive,1);(19621263929300397%positive,1);(82999010415001%positive,0);(339963948716357595%positive,1);(358963507077412827%positive,1);(4739877699373%positive,1);(313949505414231469%positive,1);(20208375173051839%positive,1);(20208372606137341%positive,1);(87637575094681%positive,0);(358963507077411837%positive,1);(358963509644326875%positive,1);(339963946149443007%positive,1);(358963509644325885%positive,1);(20208372606138331%positive,1);(339963948716357055%positive,1)] [20208375173052379%positive;20208375173051389%positive;19621843749885357%positive;20208372606137791%positive;1150286195%positive;313940228284872109%positive;339963946149442557%positive;358963507077412287%positive;339963948716356605%positive;358963509644326335%positive;294473357119%positive;339963946149443547%positive;19621263929300397%positive;82999010415001%positive;339963948716357595%positive;358963507077412827%positive;4739877699373%positive;313949505414231469%positive;20208375173051839%positive;20208372606137341%positive;87637575094681%positive;358963507077411837%positive;358963509644326875%positive;339963946149443007%positive;358963509644325885%positive;20208372606138331%positive;339963948716357055%positive]]
  | StD => [HMeas MLeft 35 [(19621263929299674%positive,0);(75838043189978%positive,2);(20208375173051389%positive,2);(19621843749885357%positive,2);(18411659250%positive,2);(313940228284872109%positive,2);(339963946149442557%positive,2);(339963948716356605%positive,2);(313949505414230746%positive,2);(19621263929300397%positive,2);(82999010415001%positive,1);(4739877699373%positive,2);(313949505414231469%positive,2);(19621843749884634%positive,0);(20208372606137341%positive,2);(87637575094681%positive,1);(358963507077411837%positive,2);(313940228284871386%positive,2);(358963509644325885%positive,2)] [19621263929299674%positive;75838043189978%positive;20208375173051389%positive;19621843749885357%positive;313940228284872109%positive;18411659250%positive;339963946149442557%positive;339963948716356605%positive;313949505414230746%positive;19621263929300397%positive;82999010415001%positive;4739877699373%positive;313949505414231469%positive;19621843749884634%positive;20208372606137341%positive;87637575094681%positive;358963507077411837%positive;313940228284871386%positive;358963509644325885%positive]]
  end.

Lemma cqh_h_00003 : iqh tmq_h_00003.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00003 StA 0 2 2 25 20000
                lsetq_h_00003 rsetq_h_00003 certq_h_00003 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00003); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00004 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Definition lsetq_h_00004 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StD,S1)]);(S0,[(StC,S1);(StD,S1)])];
   [(S0,[(StC,S1);(StD,S1)]);(S1,[(StD,S0)])];
   [(S0,[(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StD,S0);(StC,S1)])]].

Definition rsetq_h_00004 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StD,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StD,S1);(StD,S0)]);(S1,[(StD,S1);(StD,S0)])]].

Definition certq_h_00004 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => []
  | StC => [HMeas MLeft 68 [(324206369496323775%positive,1);(19081654844126911%positive,1);(19081653586450111%positive,1);(20262897904383979%positive,0);(312243682985506795%positive,0);(312243684244412395%positive,0);(324206369495709375%positive,1);(79151944562667%positive,0);(324206370754615275%positive,0);(19515229998110399%positive,1);(19081654844741611%positive,1);(20262897904998079%positive,1);(76231366801087%positive,1);(19081653585836011%positive,1);(1192603160630975%positive,1);(79151944562367%positive,1);(19515229997496299%positive,0);(20262897904383679%positive,1);(312243682985506495%positive,1);(1192603160016875%positive,1);(312243682986120895%positive,1);(312243684243797995%positive,0);(19081653585835711%positive,1);(324206370754614975%positive,1);(324206370754000875%positive,0);(312243682986121195%positive,0);(19081654844741311%positive,1);(324206369496324075%positive,0);(19081653586450411%positive,1);(19515229997495999%positive,1);(19081654844127211%positive,1);(19324205203%positive,0);(1192603160016575%positive,1);(19515229998110699%positive,0);(312243684244412095%positive,1);(20262897904998379%positive,0);(324206369495709675%positive,0);(1192603160631275%positive,1);(76231366801387%positive,0);(324206370754000575%positive,1);(312243684243797695%positive,1);(309187283263%positive,1)] [324206369496323775%positive;19081654844126911%positive;19081653586450111%positive;20262897904383979%positive;312243682985506795%positive;312243684244412395%positive;324206370754615275%positive;19515229998110399%positive;324206369495709375%positive;19081654844741611%positive;20262897904998079%positive;76231366801087%positive;19081653585836011%positive;1192603160630975%positive;79151944562367%positive;19515229997496299%positive;312243684243797695%positive;20262897904383679%positive;312243682985506495%positive;1192603160016875%positive;312243684243797995%positive;19081653585835711%positive;324206370754614975%positive;324206370754000875%positive;312243682986121195%positive;19081654844741311%positive;324206369496324075%positive;19081653586450411%positive;19515229997495999%positive;19081654844127211%positive;19324205203%positive;1192603160016575%positive;19515229998110699%positive;312243684244412095%positive;20262897904998379%positive;324206369495709675%positive;1192603160631275%positive;76231366801387%positive;324206370754000575%positive;79151944562667%positive;309187283263%positive;312243682986120895%positive]]
  | StD => [HMeas MRight 68 [(312243682985505790%positive,1);(324206370754614270%positive,1);(19081653585835006%positive,1);(19081654844740606%positive,1);(19515229997495294%positive,1);(1192603160015870%positive,1);(75290687959722%positive,1);(75289430282922%positive,0);(20262897904997374%positive,1);(312243684243796990%positive,1);(79151944561662%positive,1);(324206370753999870%positive,1);(19081654844126206%positive,1);(312243682986120190%positive,1);(75289429668522%positive,1);(324206369496323070%positive,1);(19081653586449406%positive,1);(19515229998109694%positive,1);(1192603160630270%positive,1);(76231366800382%positive,1);(324206369495708670%positive,1);(75290688574122%positive,0);(20262897904382974%positive,1);(312243684244411390%positive,1)] [312243682985505790%positive;324206370754614270%positive;19081653585835006%positive;19081654844740606%positive;19515229997495294%positive;1192603160015870%positive;75290687959722%positive;75289430282922%positive;20262897904997374%positive;312243684243796990%positive;324206370753999870%positive;79151944561662%positive;19081654844126206%positive;312243682986120190%positive;75289429668522%positive;324206369496323070%positive;19081653586449406%positive;19515229998109694%positive;1192603160630270%positive;76231366800382%positive;324206369495708670%positive;75290688574122%positive;20262897904382974%positive;312243684244411390%positive]]
  end.

Lemma cqh_h_00004 : iqh tmq_h_00004.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00004 StA 0 2 2 25 20000
                lsetq_h_00004 rsetq_h_00004 certq_h_00004 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00004); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00005 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Definition lsetq_h_00005 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S1);(StD,S1)]);(S1,[(StC,S1);(StD,S1)])];
   [(S1,[(StC,S1);(StD,S1)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0)]);(S0,[])]].

Definition rsetq_h_00005 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StC,S1)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StD,S1);(StC,S1)]);(S1,[(StD,S1);(StC,S1)])]].

Definition certq_h_00005 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => []
  | StC => [HMeas MLeft 21 [(20934817939%positive,0);(21952572398991343%positive,1);(351241162675156975%positive,1);(85752235554799%positive,1);(19516054631839727%positive,1);(1192603160639471%positive,1);(312256878400731119%positive,1);(334969669951%positive,1);(19081654861527023%positive,1);(76234588026863%positive,1)] [312256878400731119%positive;351241162675156975%positive;334969669951%positive;19081654861527023%positive;85752235554799%positive;76234588026863%positive;19516054631839727%positive;20934817939%positive;21952572398991343%positive;1192603160639471%positive]]
  | StD => [HMeas MRight 21 [(351241162675156734%positive,1);(21952572398991102%positive,1);(312256878400730878%positive,1);(19081654861526782%positive,1);(19516054631839486%positive,1);(1192603160639230%positive,1);(85752235553790%positive,1);(75290705359530%positive,0);(76234588025854%positive,1)] [21952572398991102%positive;1192603160639230%positive;76234588025854%positive;312256878400730878%positive;351241162675156734%positive;85752235553790%positive;75290705359530%positive;19081654861526782%positive;19516054631839486%positive]]
  end.

Lemma cqh_h_00005 : iqh tmq_h_00005.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00005 StA 0 2 2 25 20000
                lsetq_h_00005 rsetq_h_00005 certq_h_00005 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00005); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00006 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Definition lsetq_h_00006 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StD,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StD,S1);(StD,S0)]);(S1,[(StD,S1);(StD,S0)])]].

Definition rsetq_h_00006 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StD,S1)]);(S0,[(StC,S1);(StD,S1)])];
   [(S0,[(StC,S1);(StD,S1)]);(S1,[(StD,S0)])];
   [(S0,[(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StD,S0);(StC,S1)])]].

Definition certq_h_00006 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => []
  | StC => [HMeas MRight 68 [(20225484895811563%positive,0);(1404487198922431%positive,1);(1363235380221631%positive,1);(75836231251647%positive,1);(359543570746570431%positive,1);(20230638856566763%positive,0);(348993413080676331%positive,0);(79005798979563%positive,1);(1404467066263231%positive,1);(359548724707325931%positive,0);(75834805188287%positive,1);(359543569320507071%positive,1);(348988259119921131%positive,0);(20225484895811263%positive,1);(348993411654612971%positive,0);(79025931638763%positive,1);(20230640282629823%positive,1);(359548723281262571%positive,0);(359543570746570731%positive,0);(348988257693857771%positive,0);(18404581363%positive,0);(20225486321874623%positive,1);(20230638856566463%positive,1);(79005798979263%positive,1);(1363255512881131%positive,1);(348993413080676031%positive,1);(359548724707325631%positive,1);(294473301823%positive,1);(1404487198922731%positive,1);(348988259119920831%positive,1);(79025931638463%positive,1);(75836231251947%positive,0);(348993411654612671%positive,1);(1363235380221931%positive,1);(359548723281262271%positive,1);(20225486321874923%positive,0);(348988257693857471%positive,1);(1404467066263531%positive,1);(1363255512880831%positive,1);(75834805188587%positive,0);(359543569320507371%positive,0);(20230640282630123%positive,0)] [20225484895811563%positive;1404487198922431%positive;1363235380221631%positive;75836231251647%positive;359543570746570431%positive;20230638856566763%positive;348993413080676331%positive;79005798979563%positive;75834805188287%positive;359548724707325931%positive;1404467066263231%positive;359543569320507071%positive;348988259119921131%positive;20225484895811263%positive;348993411654612971%positive;79025931638763%positive;20230640282629823%positive;359548723281262571%positive;359543570746570731%positive;18404581363%positive;348988257693857771%positive;20225486321874623%positive;20230638856566463%positive;79005798979263%positive;1363255512881131%positive;348993413080676031%positive;359548724707325631%positive;294473301823%positive;1404487198922731%positive;348988259119920831%positive;348993411654612671%positive;79025931638463%positive;75836231251947%positive;1363235380221931%positive;359548723281262271%positive;20225486321874923%positive;348988257693857471%positive;1404467066263531%positive;1363255512880831%positive;75834805188587%positive;359543569320507371%positive;20230640282630123%positive]]
  | StD => [HMeas MLeft 68 [(20230638856565758%positive,1);(348993413080675326%positive,1);(79005798978558%positive,1);(359548724707324926%positive,1);(348988259119920126%positive,1);(348993411654611966%positive,1);(359543570746569726%positive,1);(5325138203306%positive,1);(359548723281261566%positive,1);(348988257693856766%positive,1);(1363255512880126%positive,1);(359543569320506366%positive,1);(5325216846506%positive,0);(1404487198921726%positive,1);(1363235380220926%positive,1);(75836231250942%positive,1);(5486278120106%positive,0);(20230640282629118%positive,1);(20225486321873918%positive,1);(75834805187582%positive,1);(1404467066262526%positive,1);(5486199476906%positive,1);(20225484895810558%positive,1);(79025931637758%positive,1)] [20230638856565758%positive;348993413080675326%positive;79005798978558%positive;359548724707324926%positive;348988259119920126%positive;348993411654611966%positive;359543570746569726%positive;5325138203306%positive;359548723281261566%positive;348988257693856766%positive;1363255512880126%positive;359543569320506366%positive;5325216846506%positive;1404487198921726%positive;20230640282629118%positive;1363235380220926%positive;75836231250942%positive;5486278120106%positive;20225486321873918%positive;75834805187582%positive;1404467066262526%positive;5486199476906%positive;20225484895810558%positive;79025931637758%positive]]
  end.

Lemma cqh_h_00006 : iqh tmq_h_00006.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00006 StA 0 2 2 25 20000
                lsetq_h_00006 rsetq_h_00006 certq_h_00006 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00006); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00007 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Definition lsetq_h_00007 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StC,S1)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StD,S1);(StC,S1)]);(S1,[(StD,S1);(StC,S1)])]].

Definition rsetq_h_00007 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S1);(StD,S1)]);(S1,[(StC,S1);(StD,S1)])];
   [(S1,[(StC,S1);(StD,S1)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0)]);(S0,[])]].

Definition certq_h_00007 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => []
  | StC => [HMeas MRight 21 [(359689529490667503%positive,1);(18417164275%positive,0);(75834806761455%positive,1);(359689534137956335%positive,1);(20230712224905199%positive,1);(75839454050287%positive,1);(79026200074223%positive,1);(1405037223172079%positive,1);(20230707577616367%positive,1);(294674726719%positive,1)] [18417164275%positive;75834806761455%positive;359689534137956335%positive;20230712224905199%positive;75839454050287%positive;1405037223172079%positive;359689529490667503%positive;79026200074223%positive;20230707577616367%positive;294674726719%positive]]
  | StD => [HMeas MLeft 21 [(75834806760446%positive,1);(359689534137956094%positive,1);(20230712224904958%positive,1);(75839454049278%positive,1);(79026200073982%positive,1);(1405037223171838%positive,1);(20230707577616126%positive,1);(5488426652330%positive,0);(359689529490667262%positive,1)] [75834806760446%positive;359689534137956094%positive;20230712224904958%positive;75839454049278%positive;5488426652330%positive;1405037223171838%positive;359689529490667262%positive;79026200073982%positive;20230707577616126%positive]]
  end.

Lemma cqh_h_00007 : iqh tmq_h_00007.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00007 StA 0 2 2 25 20000
                lsetq_h_00007 rsetq_h_00007 certq_h_00007 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00007); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00008 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StD)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Definition lsetq_h_00008 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StD,S0)]);(S0,[])]].

Definition rsetq_h_00008 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StC,S0)]);(S1,[(StD,S1);(StD,S0)])];
   [(S1,[(StD,S1);(StD,S0)]);(S0,[(StC,S1);(StD,S0)])];
   [(S1,[(StD,S1);(StD,S1)]);(S1,[(StB,S0)])];
   [(S1,[(StD,S1);(StD,S1)]);(S1,[(StD,S1);(StD,S0)])]].

Definition certq_h_00008 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => []
  | StC => [HRank [(4936259116847%positive,0);(20218917439271679%positive,0);(79150870819819%positive,1);(1207744659%positive,1);(343546693951%positive,0);(18787313811%positive,2)]]
  | StD => [HRank [(19282262162%positive,0);(309183088958%positive,0);(79156239529662%positive,0)]]
  end.

Lemma cqh_h_00008 : iqh tmq_h_00008.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00008 StA 0 2 2 25 20000
                lsetq_h_00008 rsetq_h_00008 certq_h_00008 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00008); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00009 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StD)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StC)
  end.

Definition lsetq_h_00009 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StD,S0)])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StD,S1)]);(S0,[(StC,S1);(StC,S0)])]].

Definition rsetq_h_00009 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StD,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StD,S0)]);(S1,[(StC,S0);(StC,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StC,S1)]);(S0,[(StD,S1);(StD,S0)])]].

Definition certq_h_00009 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => []
  | StC => [HRank [(20254840543729599%positive,0);(75565379310587%positive,0);(1207220371%positive,0);(324077452829086715%positive,0);(4722836206911%positive,0);(309064337727%positive,0);(4722578117627%positive,0);(324077452829087679%positive,0);(18420307795%positive,0);(20254840543728635%positive,0);(295161132351%positive,0)]]
  | StD => [HRank [(5316362673966%positive,0);(85061802783466%positive,0);(20767041682%positive,0);(1150003698%positive,0);(299840872238%positive,0);(348413144663455406%positive,0);(294401072942%positive,0);(4797453955818%positive,0);(19650371865408234%positive,0);(19650371865409198%positive,0);(348413144663454442%positive,0)]]
  end.

Lemma cqh_h_00009 : iqh tmq_h_00009.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00009 StA 0 2 2 25 20000
                lsetq_h_00009 rsetq_h_00009 certq_h_00009 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00009); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00010 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => Some (mkTrans S0 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00010 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StC,S1);(StC,S0)])]].

Definition rsetq_h_00010 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StD,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StC,S1)])];
   [(S1,[(StC,S0);(StD,S1)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StD,S1)]);(S1,[(StC,S0);(StD,S1)])]].

Definition certq_h_00010 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => []
  | StC => [HMeas MLeft 68 [(1371497824113391%positive,1);(357433538927620847%positive,1);(351103444328084207%positive,1);(75561067573999%positive,1);(5357413372859%positive,1);(76810802811631%positive,1);(1396236835738351%positive,1);(75560211935983%positive,1);(1371485744517871%positive,1);(357436631304073967%positive,1);(19663566874833647%positive,1);(351100351951631087%positive,1);(1396224756142831%positive,1);(5454050137019%positive,1);(351100351095993071%positive,1);(76822882407151%positive,1);(357433538071982831%positive,1);(5454002951099%positive,0);(5357366186939%positive,0);(351103443472446191%positive,1);(19666659251286767%positive,1);(19666658395648751%positive,1);(357436630448435951%positive,1);(19663566019195631%positive,1)] [1371497824113391%positive;357433538927620847%positive;351103444328084207%positive;75561067573999%positive;5357413372859%positive;1396236835738351%positive;76810802811631%positive;75560211935983%positive;1371485744517871%positive;357436631304073967%positive;19663566874833647%positive;351100351951631087%positive;1396224756142831%positive;5454050137019%positive;76822882407151%positive;351100351095993071%positive;357433538071982831%positive;5454002951099%positive;5357366186939%positive;351103443472446191%positive;19666659251286767%positive;19666658395648751%positive;357436630448435951%positive;19663566019195631%positive]]
  | StD => [HMeas MRight 68 [(357433538927621882%positive,0);(351103444328085242%positive,0);(76810802812666%positive,1);(19666658395649966%positive,1);(75561067575034%positive,0);(19663566874834682%positive,0);(1371485744518906%positive,1);(357436631304075002%positive,0);(1396224756143866%positive,1);(1371497824114426%positive,1);(351100351951632122%positive,0);(1371497824114606%positive,1);(351103444328085422%positive,1);(76822882408186%positive,1);(357433538071983866%positive,0);(357433538927622062%positive,1);(18400122738%positive,0);(351103443472447226%positive,0);(75561067575214%positive,1);(19666659251287802%positive,0);(75560211937018%positive,0);(1396236835739566%positive,1);(1396236835739386%positive,1);(76810802812846%positive,1);(294401963822%positive,1);(357436631304075182%positive,1);(19663566874834862%positive,1);(357436630448436986%positive,0);(1371485744519086%positive,1);(19663566019196666%positive,0);(351100351951632302%positive,1);(1396224756144046%positive,1);(76822882408366%positive,1);(351100351095994106%positive,0);(19666659251287982%positive,1);(19666658395649786%positive,0);(357433538071984046%positive,1);(351103443472447406%positive,1);(75560211937198%positive,1);(19663566019196846%positive,1);(357436630448437166%positive,1);(351100351095994286%positive,1)] [357433538927621882%positive;351103444328085242%positive;75561067575034%positive;19666658395649966%positive;76810802812666%positive;19663566874834682%positive;1371485744518906%positive;357436631304075002%positive;1396224756143866%positive;1371497824114426%positive;351100351951632122%positive;1371497824114606%positive;351103444328085422%positive;357433538927622062%positive;76822882408186%positive;357433538071983866%positive;18400122738%positive;351103443472447226%positive;19666659251287802%positive;75561067575214%positive;75560211937018%positive;1396236835739566%positive;1396236835739386%positive;76810802812846%positive;294401963822%positive;357436631304075182%positive;19663566874834862%positive;357436630448436986%positive;1371485744519086%positive;19663566019196666%positive;351100351951632302%positive;1396224756144046%positive;76822882408366%positive;351100351095994106%positive;19666659251287982%positive;19666658395649786%positive;357433538071984046%positive;351103443472447406%positive;75560211937198%positive;19663566019196846%positive;357436630448437166%positive;351100351095994286%positive]]
  end.

Lemma cqh_h_00010 : iqh tmq_h_00010.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00010 StA 0 2 2 25 20000
                lsetq_h_00010 rsetq_h_00010 certq_h_00010 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00010); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00011 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StD)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StC)
  end.

Definition lsetq_h_00011 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StD,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StD,S0)]);(S1,[(StC,S0);(StC,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StC,S1)]);(S0,[(StD,S1);(StD,S0)])]].

Definition rsetq_h_00011 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StD,S0)])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StD,S1)]);(S0,[(StC,S1);(StC,S0)])]].

Definition certq_h_00011 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => []
  | StC => [HRank [(20208650034706367%positive,0);(294472341311%positive,0);(21337188499%positive,0);(308359501631%positive,0);(357978622087492603%positive,0);(357978622087493567%positive,0);(87397124109307%positive,0);(1150282099%positive,0);(20208650034705403%positive,0);(5462320256831%positive,0);(4933752026107%positive,0)]]
  | StD => [HRank [(299941988654%positive,0);(4739944807726%positive,0);(314511975405048554%positive,0);(75839116923626%positive,0);(18415853522%positive,0);(4739691434730%positive,0);(296230714670%positive,0);(314511975405049518%positive,0);(19656998209442538%positive,0);(1171585170%positive,0);(19656998209443502%positive,0)]]
  end.

Lemma cqh_h_00011 : iqh tmq_h_00011.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00011 StA 0 2 2 25 20000
                lsetq_h_00011 rsetq_h_00011 certq_h_00011 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00011); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00012 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StB)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00012 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00012 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition certq_h_00012 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 35 [(20114360685811450%positive,1);(321829776116404975%positive,1);(321829775361430255%positive,1);(321829776116406010%positive,1);(314652163455309742%positive,1);(1212660372199327%positive,1);(356852788752799647%positive,1);(321829775361431290%positive,1);(4714776220603%positive,0);(5445141436191%positive,1);(321829776116406190%positive,1);(20114360685811630%positive,1);(314652164210284282%positive,1);(1172076690%positive,1);(19665759941678842%positive,1);(321829775361431470%positive,1);(314652164210283247%positive,1);(19665759941677807%positive,1);(314652163455309562%positive,1);(20114360685810415%positive,1);(314652164210284462%positive,1);(314652163455308527%positive,1);(19665759941679022%positive,1);(1212660372567967%positive,1);(4715531195323%positive,0);(356852788753168287%positive,1);(300075682094%positive,1)] [20114360685811450%positive;321829776116404975%positive;321829775361430255%positive;314652163455309742%positive;1212660372199327%positive;356852788752799647%positive;321829775361431290%positive;5445141436191%positive;321829776116406190%positive;4715531195323%positive;20114360685811630%positive;314652164210284282%positive;1172076690%positive;19665759941678842%positive;321829775361431470%positive;314652164210283247%positive;19665759941677807%positive;300075682094%positive;314652163455309562%positive;20114360685810415%positive;314652164210284462%positive;314652163455308527%positive;19665759941679022%positive;1212660372567967%positive;321829776116406010%positive;356852788753168287%positive;4714776220603%positive]]
  | StC => [HMeas MRight 35 [(321829776116404975%positive,2);(321829775361430255%positive,2);(1212660372199327%positive,2);(356852788752799647%positive,2);(4714776220603%positive,1);(5445141436191%positive,2);(21270083729%positive,2);(314652164210283247%positive,2);(87122262979065%positive,2);(19665759941677807%positive,2);(1212660372566521%positive,0);(356852788753166841%positive,2);(20114360685810415%positive,2);(314652163455308527%positive,2);(1212660372197881%positive,0);(356852788752798201%positive,2);(1212660372567967%positive,2);(4715531195323%positive,1);(356852788753168287%positive,2)] [321829776116404975%positive;321829775361430255%positive;1212660372199327%positive;356852788752799647%positive;5445141436191%positive;21270083729%positive;314652164210283247%positive;87122262979065%positive;19665759941677807%positive;1212660372566521%positive;356852788753166841%positive;20114360685810415%positive;314652163455308527%positive;1212660372197881%positive;356852788752798201%positive;1212660372567967%positive;4715531195323%positive;356852788753168287%positive;4714776220603%positive]]
  | StD => [HMeas MLeft 35 [(20114360685811450%positive,1);(321829776116406010%positive,1);(314652163455309742%positive,2);(321829775361431290%positive,1);(321829776116406190%positive,2);(20114360685811630%positive,2);(314652164210284282%positive,0);(21270083729%positive,1);(1172076690%positive,0);(19665759941678842%positive,0);(321829775361431470%positive,2);(87122262979065%positive,1);(1212660372566521%positive,2);(314652163455309562%positive,0);(356852788753166841%positive,1);(314652164210284462%positive,2);(1212660372197881%positive,2);(356852788752798201%positive,1);(19665759941679022%positive,2);(300075682094%positive,2)] [20114360685811450%positive;314652163455309742%positive;321829775361431290%positive;321829776116406190%positive;20114360685811630%positive;314652164210284282%positive;21270083729%positive;1172076690%positive;19665759941678842%positive;321829775361431470%positive;87122262979065%positive;1212660372566521%positive;314652163455309562%positive;356852788753166841%positive;314652164210284462%positive;1212660372197881%positive;356852788752798201%positive;19665759941679022%positive;321829776116406010%positive;300075682094%positive]]
  end.

Lemma cqh_h_00012 : iqh tmq_h_00012.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00012 StA 0 2 2 25 20000
                lsetq_h_00012 rsetq_h_00012 certq_h_00012 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00012); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00013 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00013 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StD,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StC,S1)])];
   [(S1,[(StC,S0);(StD,S1)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StD,S1)]);(S1,[(StC,S0);(StD,S1)])]].

Definition rsetq_h_00013 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StC,S1);(StC,S0)])]].

Definition certq_h_00013 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => []
  | StC => [HMeas MRight 68 [(321809160276005615%positive,1);(314631547614909167%positive,1);(76814341468911%positive,1);(4714778842043%positive,0);(314631547615277807%positive,1);(20113072198243055%positive,1);(4714779210683%positive,1);(1212665741275887%positive,1);(75791337353967%positive,1);(314631548370252527%positive,1);(1212666495881967%positive,1);(321809159521030895%positive,1);(1212666496250607%positive,1);(314631548369883887%positive,1);(78566688125679%positive,1);(19664471454479087%positive,1);(321809159521399535%positive,1);(75791336985327%positive,1);(20113072198611695%positive,1);(19664471454110447%positive,1);(4715534185403%positive,1);(4715533816763%positive,0);(1212665740907247%positive,1);(321809160276374255%positive,1)] [321809160276005615%positive;314631547614909167%positive;76814341468911%positive;4714778842043%positive;314631547615277807%positive;20113072198243055%positive;4714779210683%positive;1212665741275887%positive;1212666496250607%positive;75791337353967%positive;314631548370252527%positive;1212666495881967%positive;321809159521030895%positive;314631548369883887%positive;78566688125679%positive;19664471454479087%positive;321809159521399535%positive;75791336985327%positive;20113072198611695%positive;19664471454110447%positive;4715534185403%positive;4715533816763%positive;1212665740907247%positive;321809160276374255%positive]]
  | StD => [HMeas MLeft 68 [(20113072198244090%positive,0);(18753501330%positive,0);(1212665740908462%positive,1);(314631547614910382%positive,1);(321809160276375470%positive,1);(75791336986542%positive,1);(20113072198612910%positive,1);(1212665741276922%positive,1);(321809160276006830%positive,1);(76814341470126%positive,1);(1212666495883002%positive,1);(321809159521031930%positive,0);(75791337355002%positive,1);(20113072198612730%positive,0);(314631548370253562%positive,0);(20113072198244270%positive,1);(314631548369884922%positive,0);(78566688126714%positive,0);(1212665741277102%positive,1);(19664471454480122%positive,0);(321809159521400570%positive,0);(314631547615279022%positive,1);(19664471454111482%positive,0);(321809159521032110%positive,1);(1212666496251642%positive,1);(1212666496251822%positive,1);(314631548370253742%positive,1);(75791337355182%positive,1);(78566688126894%positive,1);(1212666495883182%positive,1);(19664471454480302%positive,1);(1212665740908282%positive,1);(314631548369885102%positive,1);(321809160276375290%positive,0);(75791336986362%positive,1);(314631547614910202%positive,0);(300056021294%positive,1);(321809160276006650%positive,0);(321809159521400750%positive,1);(19664471454111662%positive,1);(76814341469946%positive,0);(314631547615278842%positive,0)] [20113072198244090%positive;18753501330%positive;1212665740908462%positive;314631547614910382%positive;321809160276375470%positive;75791336986542%positive;20113072198612910%positive;1212665741276922%positive;321809160276006830%positive;76814341470126%positive;1212666495883002%positive;321809159521031930%positive;75791337355002%positive;314631548370253562%positive;20113072198244270%positive;314631548369884922%positive;78566688126714%positive;1212665741277102%positive;19664471454480122%positive;321809159521400570%positive;314631547615279022%positive;19664471454111482%positive;321809159521032110%positive;1212666496251642%positive;1212666496251822%positive;314631548370253742%positive;75791337355182%positive;78566688126894%positive;1212666495883182%positive;19664471454480302%positive;1212665740908282%positive;314631548369885102%positive;321809160276375290%positive;75791336986362%positive;314631547614910202%positive;300056021294%positive;321809160276006650%positive;321809159521400750%positive;19664471454111662%positive;20113072198612730%positive;76814341469946%positive;314631547615278842%positive]]
  end.

Lemma cqh_h_00013 : iqh tmq_h_00013.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00013 StA 0 2 2 25 20000
                lsetq_h_00013 rsetq_h_00013 certq_h_00013 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00013); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00014 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Definition lsetq_h_00014 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StC,S1)]);(S1,[(StC,S0)])];
   [(S1,[(StD,S1);(StC,S1)]);(S1,[(StD,S1);(StC,S1)])]].

Definition rsetq_h_00014 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StC,S1);(StD,S1)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StD,S1)]);(S1,[(StC,S1);(StD,S1)])]].

Definition certq_h_00014 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => []
  | StC => [HMeas MRight 21 [(87814826455791%positive,1);(78572056834799%positive,1);(359689534137956335%positive,1);(75791336994799%positive,1);(4714795627451%positive,0);(1212665757693935%positive,1);(22480595610761199%positive,1);(20114446587787247%positive,1);(321831149770373103%positive,1)] [78572056834799%positive;22480595610761199%positive;20114446587787247%positive;359689534137956335%positive;75791336994799%positive;321831149770373103%positive;4714795627451%positive;1212665757693935%positive;87814826455791%positive]]
  | StD => [HMeas MLeft 21 [(343026665774%positive,1);(87814826456830%positive,1);(78572056835838%positive,1);(75791336994558%positive,1);(21437855890%positive,0);(359689534137956094%positive,1);(22480595610760958%positive,1);(20114446587787006%positive,1);(1212665757693694%positive,1);(321831149770372862%positive,1)] [21437855890%positive;343026665774%positive;359689534137956094%positive;87814826456830%positive;22480595610760958%positive;321831149770372862%positive;78572056835838%positive;20114446587787006%positive;1212665757693694%positive;75791336994558%positive]]
  end.

Lemma cqh_h_00014 : iqh tmq_h_00014.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00014 StA 0 2 2 25 20000
                lsetq_h_00014 rsetq_h_00014 certq_h_00014 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00014); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00015 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StA)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00015 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00015 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition certq_h_00015 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 37 [(314652163455309742%positive,4);(356852788752799647%positive,4);(5445141436191%positive,4);(75791334364922%positive,2);(1212666493260527%positive,4);(4709410501563%positive,1);(356852788753168287%positive,4);(314652164210284282%positive,4);(75791334363887%positive,4);(321809154152691615%positive,4);(1212665738286842%positive,2);(1172076690%positive,4);(19665759941678842%positive,4);(1212666493261562%positive,2);(314652164210283247%positive,4);(4709410132923%positive,3);(321809154152322975%positive,4);(1212665738285807%positive,4);(19665759941677807%positive,4);(314652163455309562%positive,4);(75791334365102%positive,0);(4910418007839%positive,4);(314652164210284462%positive,4);(314652163455308527%positive,4);(1212665738287022%positive,0);(19665759941679022%positive,4);(1212666493261742%positive,0);(300075682094%positive,4)] [314652163455309742%positive;356852788752799647%positive;5445141436191%positive;75791334364922%positive;1212666493260527%positive;4709410501563%positive;314652164210284282%positive;75791334363887%positive;321809154152691615%positive;1212665738286842%positive;1172076690%positive;19665759941678842%positive;1212666493261562%positive;314652164210283247%positive;4709410132923%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;314652163455309562%positive;75791334365102%positive;4910418007839%positive;314652164210284462%positive;1212666493261742%positive;314652163455308527%positive;1212665738287022%positive;19665759941679022%positive;356852788753168287%positive;300075682094%positive]]
  | StC => [HMeas MRight 37 [(78566688125433%positive,1);(356852788752799647%positive,1);(321809154152690169%positive,1);(5445141436191%positive,1);(1212666493260527%positive,1);(321809154152321529%positive,1);(4709410501563%positive,1);(356852788753168287%positive,1);(75791334363887%positive,1);(21270083729%positive,1);(321809154152691615%positive,1);(314652164210283247%positive,1);(4709410132923%positive,0);(87122262979065%positive,1);(321809154152322975%positive,1);(1212665738285807%positive,1);(19665759941677807%positive,1);(356852788753166841%positive,1);(4910418007839%positive,1);(314652163455308527%positive,1);(356852788752798201%positive,1)] [78566688125433%positive;356852788752799647%positive;321809154152690169%positive;5445141436191%positive;1212666493260527%positive;321809154152321529%positive;4709410501563%positive;75791334363887%positive;21270083729%positive;321809154152691615%positive;314652164210283247%positive;4709410132923%positive;87122262979065%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;356852788753166841%positive;4910418007839%positive;314652163455308527%positive;356852788752798201%positive;356852788753168287%positive]]
  | StD => [HMeas MLeft 37 [(314652163455309742%positive,2);(78566688125433%positive,1);(321809154152690169%positive,1);(75791334364922%positive,2);(321809154152321529%positive,1);(314652164210284282%positive,0);(21270083729%positive,1);(1212665738286842%positive,2);(1172076690%positive,0);(19665759941678842%positive,0);(1212666493261562%positive,2);(87122262979065%positive,1);(314652163455309562%positive,0);(75791334365102%positive,2);(356852788753166841%positive,1);(314652164210284462%positive,2);(1212665738287022%positive,2);(19665759941679022%positive,2);(356852788752798201%positive,1);(1212666493261742%positive,2);(300075682094%positive,2)] [314652163455309742%positive;78566688125433%positive;321809154152690169%positive;75791334364922%positive;321809154152321529%positive;314652164210284282%positive;21270083729%positive;1212665738286842%positive;1172076690%positive;19665759941678842%positive;1212666493261562%positive;87122262979065%positive;314652163455309562%positive;75791334365102%positive;356852788753166841%positive;314652164210284462%positive;1212665738287022%positive;19665759941679022%positive;356852788752798201%positive;1212666493261742%positive;300075682094%positive]]
  end.

Lemma cqh_h_00015 : iqh tmq_h_00015.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00015 StA 9 2 2 34 20000
                lsetq_h_00015 rsetq_h_00015 certq_h_00015 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00015); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00016 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StC)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StD)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S0 DL StB)
  end.

Definition lsetq_h_00016 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StB,S1);(StB,S0)]);(S1,[(StC,S0);(StC,S1)])];
   [(S0,[(StB,S1);(StD,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StC,S1)]);(S0,[(StB,S1);(StD,S0)])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StB,S1);(StB,S0)])]].

Definition rsetq_h_00016 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StB,S1)])];
   [(S0,[(StD,S1);(StC,S0)]);(S1,[(StD,S0);(StB,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StB,S1)]);(S0,[(StD,S1);(StC,S0)])];
   [(S1,[(StD,S0);(StB,S1)]);(S0,[(StC,S1);(StC,S0)])]].

Definition certq_h_00016 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(299933600047%positive,0);(82724199690715%positive,1);(315065580583310058%positive,0);(18415849170%positive,0);(314503180385703599%positive,0);(19082749993644507%positive,1);(4705584999726%positive,2);(338838323536949723%positive,1);(4658874118619%positive,1);(294083161390%positive,2);(314503179310912250%positive,0);(75290434786026%positive,0);(1173649554%positive,0);(315065579508520878%positive,2);(19656448452514554%positive,0);(19691598464866222%positive,2)]]
  | StC => [HRank [(20263463057%positive,0);(299933600047%positive,1);(82724199690715%positive,2);(338838321389991357%positive,0);(339964496174740441%positive,0);(294463952669%positive,0);(314503180385703599%positive,1);(338838323536949723%positive,2);(4658874118619%positive,2);(19082747846686141%positive,0);(1149725041%positive,0);(5187446544157%positive,0);(19082749993644507%positive,2);(339964498321700253%positive,0)]]
  | StD => [HMeas MRight 26 [(315065580583310058%positive,28);(338838321389991357%positive,29);(18415849170%positive,28);(4705584999726%positive,0);(339964496174740441%positive,29);(294463952669%positive,29);(294083161390%positive,0);(314503179310912250%positive,28);(75290434786026%positive,28);(19082747846686141%positive,29);(1173649554%positive,2);(1149725041%positive,27);(5187446544157%positive,27);(315065579508520878%positive,2);(19656448452514554%positive,26);(19691598464866222%positive,2);(20263463057%positive,29);(339964498321700253%positive,29)] [294463952669%positive;315065579508520878%positive;19656448452514554%positive;294083161390%positive;315065580583310058%positive;314503179310912250%positive;75290434786026%positive;19691598464866222%positive;338838321389991357%positive;19082747846686141%positive;1173649554%positive;5187446544157%positive;4705584999726%positive;18415849170%positive;20263463057%positive;339964498321700253%positive;1149725041%positive;339964496174740441%positive]]
  end.

Lemma cqh_h_00016 : iqh tmq_h_00016.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00016 StA 0 2 2 25 20000
                lsetq_h_00016 rsetq_h_00016 certq_h_00016 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00016); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00017 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => None
  end.

Definition lsetq_h_00017 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition rsetq_h_00017 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition certq_h_00017 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 37 [(1334049735266782%positive,1);(323514222544615102%positive,1);(347849918707528158%positive,1);(75285048259563%positive,1);(323514226923467755%positive,1);(323511130168161982%positive,1);(4705315516222%positive,1);(323511134547014635%positive,1);(1358788746891742%positive,1);(323514222544614379%positive,1);(4936435274410%positive,1);(19087145909481950%positive,1);(323511130168161259%positive,1);(341516731731538398%positive,1);(4936388088490%positive,0);(18416111347%positive,1);(74559165649374%positive,1);(323514226923468478%positive,1);(323511134547015358%positive,1);(75289427112939%positive,1);(4705589194558%positive,1)] [347849918707528158%positive;1334049735266782%positive;323514222544615102%positive;323514226923467755%positive;75285048259563%positive;323511130168161982%positive;323511134547014635%positive;4705315516222%positive;1358788746891742%positive;323514222544614379%positive;4936435274410%positive;19087145909481950%positive;323511130168161259%positive;341516731731538398%positive;4936388088490%positive;18416111347%positive;74559165649374%positive;323514226923468478%positive;323511134547015358%positive;75289427112939%positive;4705589194558%positive]]
  | StC => [HMeas MRight 37 [(19087145909482985%positive,0);(75285048259563%positive,1);(323514226923467755%positive,1);(1149729265%positive,0);(347849918707529373%positive,2);(294330785565%positive,2);(323511134547014635%positive,1);(74559165650589%positive,2);(1334049735267997%positive,2);(341516731731539433%positive,0);(323514222544614379%positive,1);(1358788746892777%positive,2);(323511130168161259%positive,1);(19087145909483165%positive,2);(18416111347%positive,1);(347849918707529193%positive,0);(74559165650409%positive,2);(75289427112939%positive,1);(1334049735267817%positive,2);(341516731731539613%positive,2);(1358788746892957%positive,2)] [19087145909482985%positive;75285048259563%positive;323514226923467755%positive;1149729265%positive;347849918707529373%positive;294330785565%positive;323511134547014635%positive;74559165650589%positive;1334049735267997%positive;341516731731539433%positive;323514222544614379%positive;1358788746892777%positive;323511130168161259%positive;19087145909483165%positive;18416111347%positive;347849918707529193%positive;74559165650409%positive;75289427112939%positive;1334049735267817%positive;341516731731539613%positive;1358788746892957%positive]]
  | StD => [HMeas MLeft 37 [(1334049735266782%positive,4);(19087145909482985%positive,4);(323514222544615102%positive,4);(347849918707528158%positive,4);(1149729265%positive,4);(323511130168161982%positive,4);(347849918707529373%positive,4);(294330785565%positive,4);(4705315516222%positive,4);(74559165650589%positive,0);(1334049735267997%positive,0);(341516731731539433%positive,4);(1358788746891742%positive,4);(4936435274410%positive,1);(1358788746892777%positive,2);(19087145909481950%positive,4);(341516731731538398%positive,4);(4936388088490%positive,3);(19087145909483165%positive,4);(347849918707529193%positive,4);(74559165649374%positive,4);(323514226923468478%positive,4);(74559165650409%positive,2);(323511134547015358%positive,4);(1334049735267817%positive,2);(4705589194558%positive,4);(341516731731539613%positive,4);(1358788746892957%positive,0)] [347849918707528158%positive;19087145909482985%positive;323514222544615102%positive;1334049735266782%positive;1149729265%positive;323511130168161982%positive;347849918707529373%positive;294330785565%positive;4705315516222%positive;74559165650589%positive;1334049735267997%positive;341516731731539433%positive;1358788746891742%positive;4936435274410%positive;19087145909481950%positive;1358788746892777%positive;341516731731538398%positive;4936388088490%positive;19087145909483165%positive;347849918707529193%positive;74559165649374%positive;323514226923468478%positive;74559165650409%positive;323511134547015358%positive;1334049735267817%positive;4705589194558%positive;341516731731539613%positive;1358788746892957%positive]]
  end.

Lemma cqh_h_00017 : iqh tmq_h_00017.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00017 StA 0 2 2 25 20000
                lsetq_h_00017 rsetq_h_00017 certq_h_00017 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00017); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00018 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Definition lsetq_h_00018 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition rsetq_h_00018 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition certq_h_00018 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 35 [(5307768541866%positive,1);(347849918707528158%positive,2);(323514226923467755%positive,2);(1263727430424254%positive,2);(19087146765119966%positive,2);(323511134547014635%positive,2);(1263715350828734%positive,2);(19087145909481950%positive,2);(341516731731538398%positive,2);(341516732587176414%positive,2);(1263727430423531%positive,0);(1263715350828011%positive,0);(18416111347%positive,2);(5211131777706%positive,1);(323514226923468478%positive,2);(347849919563166174%positive,2);(323511134547015358%positive,2);(75289427112939%positive,2);(4705589194558%positive,2)] [5307768541866%positive;347849918707528158%positive;323514226923467755%positive;19087146765119966%positive;1263727430424254%positive;323511134547014635%positive;1263715350828734%positive;19087145909481950%positive;341516731731538398%positive;341516732587176414%positive;1263727430423531%positive;1263715350828011%positive;18416111347%positive;5211131777706%positive;323514226923468478%positive;347849919563166174%positive;323511134547015358%positive;75289427112939%positive;4705589194558%positive]]
  | StC => [HMeas MRight 35 [(341516732587177449%positive,1);(19087145909482985%positive,0);(323514226923467755%positive,1);(1149729265%positive,0);(347849919563167389%positive,2);(323511134547014635%positive,1);(294330785565%positive,2);(347849918707529373%positive,2);(341516731731539433%positive,0);(347849919563167209%positive,1);(1263727430423531%positive,2);(19087145909483165%positive,2);(19087146765121181%positive,2);(1263715350828011%positive,2);(18416111347%positive,1);(347849918707529193%positive,0);(19087146765121001%positive,1);(75289427112939%positive,1);(341516731731539613%positive,2);(341516732587177629%positive,2)] [341516732587177449%positive;19087145909482985%positive;323514226923467755%positive;1149729265%positive;347849918707529373%positive;347849919563167389%positive;323511134547014635%positive;294330785565%positive;341516731731539433%positive;347849919563167209%positive;1263727430423531%positive;19087145909483165%positive;19087146765121181%positive;1263715350828011%positive;18416111347%positive;347849918707529193%positive;19087146765121001%positive;75289427112939%positive;341516731731539613%positive;341516732587177629%positive]]
  | StD => [HMeas MLeft 35 [(5307768541866%positive,0);(341516732587177449%positive,1);(347849918707528158%positive,1);(19087145909482985%positive,1);(1149729265%positive,1);(1263727430424254%positive,1);(19087146765119966%positive,1);(347849919563167389%positive,1);(294330785565%positive,1);(347849918707529373%positive,1);(1263715350828734%positive,1);(341516731731539433%positive,1);(347849919563167209%positive,1);(19087145909481950%positive,1);(341516731731538398%positive,1);(341516732587176414%positive,1);(19087145909483165%positive,1);(19087146765121181%positive,1);(347849918707529193%positive,1);(5211131777706%positive,0);(19087146765121001%positive,1);(323514226923468478%positive,1);(347849919563166174%positive,1);(323511134547015358%positive,1);(4705589194558%positive,1);(341516731731539613%positive,1);(341516732587177629%positive,1)] [5307768541866%positive;341516732587177449%positive;347849918707528158%positive;19087145909482985%positive;1149729265%positive;1263727430424254%positive;19087146765119966%positive;347849919563167389%positive;294330785565%positive;347849918707529373%positive;1263715350828734%positive;341516731731539433%positive;347849919563167209%positive;19087145909481950%positive;341516731731538398%positive;341516732587176414%positive;19087145909483165%positive;19087146765121181%positive;347849918707529193%positive;5211131777706%positive;19087146765121001%positive;323514226923468478%positive;347849919563166174%positive;323511134547015358%positive;4705589194558%positive;341516731731539613%positive;341516732587177629%positive]]
  end.

Lemma cqh_h_00018 : iqh tmq_h_00018.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00018 StA 0 2 2 25 20000
                lsetq_h_00018 rsetq_h_00018 certq_h_00018 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00018); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00019 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Definition lsetq_h_00019 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StD,S1)]);(S0,[(StC,S1);(StD,S1)])];
   [(S0,[(StC,S1);(StD,S1)]);(S1,[(StD,S0)])];
   [(S0,[(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StD,S0);(StC,S1)])]].

Definition rsetq_h_00019 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StD,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StD,S1);(StD,S0)]);(S1,[(StD,S1);(StD,S0)])]].

Definition certq_h_00019 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => []
  | StC => [HMeas MLeft 68 [(324206369496323775%positive,1);(1207993823614955%positive,1);(1207992564709355%positive,1);(20262897904383979%positive,0);(75499346810559%positive,1);(312243682985506795%positive,0);(312243684244412395%positive,0);(324206369495709375%positive,1);(79151944562667%positive,0);(324206370754615275%positive,0);(19515229998110399%positive,1);(75499346196459%positive,1);(20262897904998079%positive,1);(76231366801087%positive,1);(79151944562367%positive,1);(19515229997496299%positive,0);(1207992564709055%positive,1);(20262897904383679%positive,1);(312243682985506495%positive,1);(312243682986120895%positive,1);(1207993823000555%positive,1);(1207992565323755%positive,1);(312243684243797995%positive,0);(75499346196159%positive,1);(324206370754614975%positive,1);(312243682986121195%positive,0);(324206370754000875%positive,0);(324206369496324075%positive,0);(19515229997495999%positive,1);(75499346810859%positive,1);(1207993823614655%positive,1);(19324205203%positive,0);(324206370754000575%positive,1);(19515229998110699%positive,0);(312243684244412095%positive,1);(20262897904998379%positive,0);(1207993823000255%positive,1);(324206369495709675%positive,0);(1207992565323455%positive,1);(76231366801387%positive,0);(312243684243797695%positive,1);(309187283263%positive,1)] [324206369496323775%positive;1207993823614955%positive;1207992564709355%positive;20262897904383979%positive;75499346810559%positive;312243682985506795%positive;312243684244412395%positive;324206370754615275%positive;19515229998110399%positive;324206369495709375%positive;20262897904998079%positive;76231366801087%positive;75499346196459%positive;79151944562367%positive;19515229997496299%positive;312243684243797695%positive;1207992564709055%positive;20262897904383679%positive;312243682985506495%positive;1207993823000555%positive;1207992565323755%positive;312243684243797995%positive;75499346196159%positive;324206370754614975%positive;312243682986121195%positive;324206370754000875%positive;324206369496324075%positive;19515229997495999%positive;75499346810859%positive;1207993823614655%positive;19324205203%positive;19515229998110699%positive;312243684244412095%positive;20262897904998379%positive;1207993823000255%positive;324206369495709675%positive;1207992565323455%positive;76231366801387%positive;324206370754000575%positive;79151944562667%positive;309187283263%positive;312243682986120895%positive]]
  | StD => [HMeas MRight 68 [(312243682985505790%positive,1);(324206370754614270%positive,1);(75499346195454%positive,1);(19515229997495294%positive,1);(4714527675050%positive,0);(4715785351850%positive,1);(20262897904997374%positive,1);(1207993822999550%positive,1);(1207992565322750%positive,1);(312243684243796990%positive,1);(79151944561662%positive,1);(324206370753999870%positive,1);(312243682986120190%positive,1);(324206369496323070%positive,1);(75499346809854%positive,1);(19515229998109694%positive,1);(76231366800382%positive,1);(324206369495708670%positive,1);(1207993823613950%positive,1);(1207992564708350%positive,1);(4715785966250%positive,0);(4714527060650%positive,1);(20262897904382974%positive,1);(312243684244411390%positive,1)] [312243682985505790%positive;324206370754614270%positive;75499346195454%positive;19515229997495294%positive;4714527675050%positive;4715785351850%positive;20262897904997374%positive;1207993822999550%positive;1207992565322750%positive;312243684243796990%positive;324206370753999870%positive;79151944561662%positive;312243682986120190%positive;324206369496323070%positive;75499346809854%positive;19515229998109694%positive;324206369495708670%positive;76231366800382%positive;1207993823613950%positive;1207992564708350%positive;4715785966250%positive;4714527060650%positive;20262897904382974%positive;312243684244411390%positive]]
  end.

Lemma cqh_h_00019 : iqh tmq_h_00019.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00019 StA 0 2 2 25 20000
                lsetq_h_00019 rsetq_h_00019 certq_h_00019 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00019); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00020 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Definition lsetq_h_00020 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S1);(StD,S1)]);(S1,[(StC,S1);(StD,S1)])];
   [(S1,[(StC,S1);(StD,S1)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0)]);(S0,[])]].

Definition rsetq_h_00020 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StC,S1)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StD,S1);(StC,S1)]);(S1,[(StD,S1);(StC,S1)])]].

Definition certq_h_00020 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => []
  | StC => [HMeas MLeft 21 [(20934817939%positive,0);(21952572398991343%positive,1);(351241162675156975%positive,1);(75499346819055%positive,1);(85752235554799%positive,1);(19516054631839727%positive,1);(1207993840400367%positive,1);(312256878400731119%positive,1);(334969669951%positive,1);(76234588026863%positive,1)] [312256878400731119%positive;351241162675156975%positive;334969669951%positive;75499346819055%positive;85752235554799%positive;76234588026863%positive;19516054631839727%positive;1207993840400367%positive;20934817939%positive;21952572398991343%positive]]
  | StD => [HMeas MRight 21 [(351241162675156734%positive,1);(1207993840400126%positive,1);(21952572398991102%positive,1);(312256878400730878%positive,1);(75499346818814%positive,1);(19516054631839486%positive,1);(85752235553790%positive,1);(4715802751658%positive,0);(76234588025854%positive,1)] [21952572398991102%positive;76234588025854%positive;312256878400730878%positive;351241162675156734%positive;85752235553790%positive;75499346818814%positive;4715802751658%positive;19516054631839486%positive;1207993840400126%positive]]
  end.

Lemma cqh_h_00020 : iqh tmq_h_00020.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00020 StA 0 2 2 25 20000
                lsetq_h_00020 rsetq_h_00020 certq_h_00020 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00020); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00021 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Definition lsetq_h_00021 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StA,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0)]);(S0,[(StA,S0)])];
   [(S1,[(StD,S1);(StD,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StD,S1);(StD,S0)]);(S1,[(StD,S1);(StD,S0)])]].

Definition rsetq_h_00021 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StD,S1)]);(S0,[(StC,S1);(StD,S1)])];
   [(S0,[(StC,S1);(StD,S1)]);(S1,[(StD,S0)])];
   [(S0,[(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StD,S0);(StC,S1)])]].

Definition certq_h_00021 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => []
  | StC => [HMeas MRight 68 [(20225484895811563%positive,0);(22471473030846143%positive,1);(21812088176728043%positive,1);(1264092754302655%positive,1);(75836231251647%positive,1);(359543570746570431%positive,1);(20230638856566763%positive,0);(22471795153393643%positive,1);(348993413080676331%positive,0);(75834805188287%positive,1);(21811766054180843%positive,1);(359548724707325931%positive,0);(1264414876849855%positive,1);(359543569320507071%positive,1);(348988259119921131%positive,0);(20225484895811263%positive,1);(348993411654612971%positive,0);(20230640282629823%positive,1);(359548723281262571%positive,0);(21812088176727743%positive,1);(359543570746570731%positive,0);(348988257693857771%positive,0);(18404581363%positive,0);(20225486321874623%positive,1);(22471795153393343%positive,1);(20230638856566463%positive,1);(348993413080676031%positive,1);(21811766054180543%positive,1);(359548724707325631%positive,1);(294473301823%positive,1);(22471473030846443%positive,1);(1264092754302955%positive,1);(348988259119920831%positive,1);(75836231251947%positive,0);(348993411654612671%positive,1);(359548723281262271%positive,1);(20225486321874923%positive,0);(348988257693857471%positive,1);(1264414876850155%positive,1);(75834805188587%positive,0);(359543569320507371%positive,0);(20230640282630123%positive,0)] [20225484895811563%positive;22471473030846143%positive;21812088176728043%positive;1264092754302655%positive;75836231251647%positive;359543570746570431%positive;20230638856566763%positive;22471795153393643%positive;348993413080676331%positive;75834805188287%positive;21811766054180843%positive;359548724707325931%positive;1264414876849855%positive;359543569320507071%positive;348988259119921131%positive;20225484895811263%positive;348993411654612971%positive;20230640282629823%positive;359548723281262571%positive;21812088176727743%positive;359543570746570731%positive;18404581363%positive;348988257693857771%positive;20225486321874623%positive;20230638856566463%positive;22471795153393343%positive;348993413080676031%positive;21811766054180543%positive;359548724707325631%positive;294473301823%positive;22471473030846443%positive;1264092754302955%positive;348988259119920831%positive;75836231251947%positive;348993411654612671%positive;359548723281262271%positive;20225486321874923%positive;348988257693857471%positive;1264414876850155%positive;75834805188587%positive;359543569320507371%positive;20230640282630123%positive]]
  | StD => [HMeas MLeft 68 [(22471795153392638%positive,1);(20230638856565758%positive,1);(1363235373118122%positive,1);(21811766054179838%positive,1);(348993413080675326%positive,1);(359548724707324926%positive,1);(348988259119920126%positive,1);(348993411654611966%positive,1);(22471473030845438%positive,1);(359543570746569726%positive,1);(359548723281261566%positive,1);(348988257693856766%positive,1);(359543569320506366%positive,1);(1404467059159722%positive,1);(1264092754301950%positive,1);(75836231250942%positive,1);(20230640282629118%positive,1);(20225486321873918%positive,1);(75834805187582%positive,1);(1264414876849150%positive,1);(20225484895810558%positive,1);(1363255505777322%positive,0);(21812088176727038%positive,1);(1404487191818922%positive,0)] [20230638856565758%positive;22471795153392638%positive;1363235373118122%positive;348993413080675326%positive;21811766054179838%positive;359548724707324926%positive;348988259119920126%positive;348993411654611966%positive;22471473030845438%positive;359543570746569726%positive;359548723281261566%positive;348988257693856766%positive;359543569320506366%positive;1404467059159722%positive;20230640282629118%positive;1264092754301950%positive;75836231250942%positive;20225486321873918%positive;75834805187582%positive;1264414876849150%positive;20225484895810558%positive;1363255505777322%positive;21812088176727038%positive;1404487191818922%positive]]
  end.

Lemma cqh_h_00021 : iqh tmq_h_00021.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00021 StA 0 2 2 25 20000
                lsetq_h_00021 rsetq_h_00021 certq_h_00021 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00021); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00022 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Definition lsetq_h_00022 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StA,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0)]);(S0,[(StA,S0)])];
   [(S1,[(StD,S1);(StC,S1)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StD,S1);(StC,S1)]);(S1,[(StD,S1);(StC,S1)])]].

Definition rsetq_h_00022 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S1);(StD,S1)]);(S1,[(StC,S1);(StD,S1)])];
   [(S1,[(StC,S1);(StD,S1)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0)]);(S0,[])]].

Definition certq_h_00022 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => []
  | StC => [HMeas MRight 21 [(359689529490667503%positive,1);(1264419171817455%positive,1);(18417164275%positive,0);(75834806761455%positive,1);(22480595541383151%positive,1);(359689534137956335%positive,1);(75839454050287%positive,1);(20230712224905199%positive,1);(20230707577616367%positive,1);(294674726719%positive,1)] [18417164275%positive;75834806761455%positive;359689534137956335%positive;75839454050287%positive;20230712224905199%positive;22480595541383151%positive;359689529490667503%positive;20230707577616367%positive;294674726719%positive;1264419171817455%positive]]
  | StD => [HMeas MLeft 21 [(22480595541382910%positive,1);(1264419171817214%positive,1);(75834806760446%positive,1);(359689534137956094%positive,1);(20230712224904958%positive,1);(1405037216068266%positive,0);(75839454049278%positive,1);(20230707577616126%positive,1);(359689529490667262%positive,1)] [75834806760446%positive;22480595541382910%positive;359689534137956094%positive;20230712224904958%positive;1264419171817214%positive;1405037216068266%positive;75839454049278%positive;359689529490667262%positive;20230707577616126%positive]]
  end.

Lemma cqh_h_00022 : iqh tmq_h_00022.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00022 StA 0 2 2 25 20000
                lsetq_h_00022 rsetq_h_00022 certq_h_00022 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00022); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00023 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StD)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StC)
  end.

Definition lsetq_h_00023 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StD,S0)])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StD,S1)]);(S0,[(StC,S1);(StC,S0)])]].

Definition rsetq_h_00023 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StD,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StD,S0)]);(S1,[(StC,S0);(StC,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StC,S1)]);(S0,[(StD,S1);(StD,S0)])]].

Definition certq_h_00023 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => []
  | StC => [HRank [(20254840543729599%positive,0);(75565379310587%positive,0);(1207220371%positive,0);(324077452829086715%positive,0);(4722836206911%positive,0);(309064337727%positive,0);(4722578117627%positive,0);(324077452829087679%positive,0);(18420307795%positive,0);(20254840543728635%positive,0);(295161132351%positive,0)]]
  | StD => [HRank [(5316362673966%positive,0);(85061802783466%positive,0);(20767041682%positive,0);(1150003698%positive,0);(299840872238%positive,0);(348413144663455406%positive,0);(294401072942%positive,0);(4797453955818%positive,0);(19650371865408234%positive,0);(19650371865409198%positive,0);(348413144663454442%positive,0)]]
  end.

Lemma cqh_h_00023 : iqh tmq_h_00023.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00023 StA 0 2 2 25 20000
                lsetq_h_00023 rsetq_h_00023 certq_h_00023 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00023); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00024 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S0 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00024 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition rsetq_h_00024 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition certq_h_00024 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 35 [(5453667406779%positive,0);(351078360865895151%positive,1);(357411547841885946%positive,1);(306064359855454111%positive,1);(357411548697523962%positive,1);(1195563884074911%positive,1);(357411547841884911%positive,1);(1150007538%positive,1);(351078360865896366%positive,1);(19641575789098746%positive,1);(351078361721533167%positive,1);(351078361721534382%positive,1);(19641576644736762%positive,1);(4722827818783%positive,1);(294402117422%positive,1);(19641576644735727%positive,1);(357411547841886126%positive,1);(19641575789097711%positive,1);(357411548697522927%positive,1);(357411548697524142%positive,1);(19641575789098926%positive,1);(306067452231907231%positive,1);(19641576644736942%positive,1);(1195575963670431%positive,1);(5357030642619%positive,0);(351078360865896186%positive,1);(351078361721534202%positive,1)] [5453667406779%positive;351078360865895151%positive;357411547841885946%positive;306064359855454111%positive;357411548697523962%positive;1195563884074911%positive;357411547841884911%positive;1150007538%positive;351078360865896366%positive;19641575789098746%positive;351078361721533167%positive;351078361721534382%positive;19641576644736762%positive;4722827818783%positive;294402117422%positive;19641576644735727%positive;357411547841886126%positive;19641575789097711%positive;357411548697522927%positive;357411548697524142%positive;19641575789098926%positive;306067452231907231%positive;19641576644736942%positive;1195575963670431%positive;5357030642619%positive;351078360865896186%positive;351078361721534202%positive]]
  | StC => [HMeas MLeft 35 [(5453667406779%positive,1);(351078360865895151%positive,2);(306064359855454111%positive,2);(1195563884074911%positive,2);(357411547841884911%positive,2);(351078361721533167%positive,2);(4722827818783%positive,2);(19641576644735727%positive,2);(18419783537%positive,2);(19641575789097711%positive,2);(306067452231905785%positive,2);(1195575963668985%positive,0);(357411548697522927%positive,2);(306067452231907231%positive,2);(75565245100537%positive,2);(1195575963670431%positive,2);(5357030642619%positive,1);(1195563884073465%positive,0);(306064359855452665%positive,2)] [5453667406779%positive;351078360865895151%positive;306064359855454111%positive;1195563884074911%positive;357411547841884911%positive;351078361721533167%positive;4722827818783%positive;19641576644735727%positive;18419783537%positive;19641575789097711%positive;306067452231905785%positive;357411548697522927%positive;1195575963668985%positive;306067452231907231%positive;75565245100537%positive;1195575963670431%positive;5357030642619%positive;1195563884073465%positive;306064359855452665%positive]]
  | StD => [HMeas MRight 35 [(357411547841885946%positive,0);(357411548697523962%positive,1);(1150007538%positive,0);(351078360865896366%positive,2);(19641575789098746%positive,0);(351078361721534382%positive,2);(19641576644736762%positive,1);(294402117422%positive,2);(357411547841886126%positive,2);(18419783537%positive,1);(306067452231905785%positive,1);(1195575963668985%positive,2);(357411548697524142%positive,2);(19641575789098926%positive,2);(19641576644736942%positive,2);(75565245100537%positive,1);(1195563884073465%positive,2);(306064359855452665%positive,1);(351078360865896186%positive,0);(351078361721534202%positive,1)] [357411547841885946%positive;357411548697523962%positive;1150007538%positive;351078360865896366%positive;19641575789098746%positive;351078361721534382%positive;19641576644736762%positive;294402117422%positive;357411547841886126%positive;18419783537%positive;306067452231905785%positive;1195575963668985%positive;357411548697524142%positive;19641575789098926%positive;19641576644736942%positive;75565245100537%positive;1195563884073465%positive;306064359855452665%positive;351078360865896186%positive;351078361721534202%positive]]
  end.

Lemma cqh_h_00024 : iqh tmq_h_00024.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00024 StA 0 2 2 25 20000
                lsetq_h_00024 rsetq_h_00024 certq_h_00024 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00024); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00025 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => Some (mkTrans S0 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00025 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StC,S1);(StC,S0)])]].

Definition rsetq_h_00025 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StD,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StC,S1)])];
   [(S1,[(StC,S0);(StD,S1)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StD,S1)]);(S1,[(StC,S0);(StD,S1)])]].

Definition certq_h_00025 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => []
  | StC => [HMeas MLeft 68 [(1371497824113391%positive,1);(357433538927620847%positive,1);(351103444328084207%positive,1);(75561067573999%positive,1);(5357413372859%positive,1);(76810802811631%positive,1);(1396236835738351%positive,1);(75560211935983%positive,1);(1371485744517871%positive,1);(357436631304073967%positive,1);(19663566874833647%positive,1);(351100351951631087%positive,1);(1396224756142831%positive,1);(5454050137019%positive,1);(351100351095993071%positive,1);(76822882407151%positive,1);(357433538071982831%positive,1);(5454002951099%positive,0);(5357366186939%positive,0);(351103443472446191%positive,1);(19666659251286767%positive,1);(19666658395648751%positive,1);(357436630448435951%positive,1);(19663566019195631%positive,1)] [1371497824113391%positive;357433538927620847%positive;351103444328084207%positive;75561067573999%positive;5357413372859%positive;1396236835738351%positive;76810802811631%positive;75560211935983%positive;1371485744517871%positive;357436631304073967%positive;19663566874833647%positive;351100351951631087%positive;1396224756142831%positive;5454050137019%positive;76822882407151%positive;351100351095993071%positive;357433538071982831%positive;5454002951099%positive;5357366186939%positive;351103443472446191%positive;19666659251286767%positive;19666658395648751%positive;357436630448435951%positive;19663566019195631%positive]]
  | StD => [HMeas MRight 68 [(357433538927621882%positive,0);(351103444328085242%positive,0);(76810802812666%positive,1);(19666658395649966%positive,1);(75561067575034%positive,0);(19663566874834682%positive,0);(1371485744518906%positive,1);(357436631304075002%positive,0);(1396224756143866%positive,1);(1371497824114426%positive,1);(351100351951632122%positive,0);(1371497824114606%positive,1);(351103444328085422%positive,1);(76822882408186%positive,1);(357433538071983866%positive,0);(357433538927622062%positive,1);(18400122738%positive,0);(351103443472447226%positive,0);(75561067575214%positive,1);(19666659251287802%positive,0);(75560211937018%positive,0);(1396236835739386%positive,1);(1396236835739566%positive,1);(76810802812846%positive,1);(294401963822%positive,1);(357436631304075182%positive,1);(19663566874834862%positive,1);(357436630448436986%positive,0);(1371485744519086%positive,1);(19663566019196666%positive,0);(351100351951632302%positive,1);(1396224756144046%positive,1);(76822882408366%positive,1);(351100351095994106%positive,0);(19666659251287982%positive,1);(19666658395649786%positive,0);(357433538071984046%positive,1);(351103443472447406%positive,1);(75560211937198%positive,1);(19663566019196846%positive,1);(357436630448437166%positive,1);(351100351095994286%positive,1)] [357433538927621882%positive;351103444328085242%positive;75561067575034%positive;19666658395649966%positive;76810802812666%positive;19663566874834682%positive;1371485744518906%positive;357436631304075002%positive;1396224756143866%positive;1371497824114426%positive;351100351951632122%positive;1371497824114606%positive;351103444328085422%positive;357433538927622062%positive;76822882408186%positive;357433538071983866%positive;18400122738%positive;351103443472447226%positive;19666659251287802%positive;75561067575214%positive;75560211937018%positive;1396236835739386%positive;1396236835739566%positive;76810802812846%positive;294401963822%positive;357436631304075182%positive;19663566874834862%positive;357436630448436986%positive;1371485744519086%positive;19663566019196666%positive;351100351951632302%positive;1396224756144046%positive;76822882408366%positive;351100351095994106%positive;19666659251287982%positive;19666658395649786%positive;357433538071984046%positive;351103443472447406%positive;75560211937198%positive;19663566019196846%positive;357436630448437166%positive;351100351095994286%positive]]
  end.

Lemma cqh_h_00025 : iqh tmq_h_00025.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00025 StA 0 2 2 25 20000
                lsetq_h_00025 rsetq_h_00025 certq_h_00025 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00025); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00026 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => Some (mkTrans S0 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Definition lsetq_h_00026 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StC,S1);(StD,S1)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StD,S1)]);(S1,[(StC,S1);(StD,S1)])]].

Definition rsetq_h_00026 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StC,S1)]);(S1,[(StC,S0)])];
   [(S1,[(StD,S1);(StC,S1)]);(S1,[(StD,S1);(StC,S1)])]].

Definition certq_h_00026 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => []
  | StC => [HMeas MLeft 21 [(75565583266543%positive,1);(19663635596933103%positive,1);(351241158162085871%positive,1);(75561070195439%positive,1);(19663640110004207%positive,1);(351241162675156975%positive,1);(1372035768768495%positive,1);(5359514719163%positive,0);(76811071248367%positive,1)] [75565583266543%positive;351241162675156975%positive;19663635596933103%positive;5359514719163%positive;351241158162085871%positive;1372035768768495%positive;76811071248367%positive;75561070195439%positive;19663640110004207%positive]]
  | StD => [HMeas MRight 21 [(19663640110003966%positive,1);(351241162675156734%positive,1);(75561070196478%positive,1);(18421094258%positive,0);(76811071248126%positive,1);(1372035768768254%positive,1);(75565583267582%positive,1);(19663635596932862%positive,1);(351241158162085630%positive,1);(294737671982%positive,1)] [75561070196478%positive;76811071248126%positive;19663640110003966%positive;18421094258%positive;1372035768768254%positive;351241162675156734%positive;75565583267582%positive;294737671982%positive;19663635596932862%positive;351241158162085630%positive]]
  end.

Lemma cqh_h_00026 : iqh tmq_h_00026.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00026 StA 0 2 2 25 20000
                lsetq_h_00026 rsetq_h_00026 certq_h_00026 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00026); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00027 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StD)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StC)
  end.

Definition lsetq_h_00027 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StD,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StD,S0)]);(S1,[(StC,S0);(StA,S0)])];
   [(S0,[(StD,S1);(StD,S0)]);(S1,[(StC,S0);(StC,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StA,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StC,S1)]);(S0,[(StD,S1);(StD,S0)])]].

Definition rsetq_h_00027 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StD,S0)])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StD,S1)]);(S0,[(StC,S1);(StC,S0)])]].

Definition certq_h_00027 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => []
  | StC => [HRank [(20208650034706367%positive,0);(1398353984582651%positive,0);(294472341311%positive,0);(21337188499%positive,0);(308359501631%positive,0);(357978622087492603%positive,0);(357978622087493567%positive,0);(87397124109307%positive,0);(1150282099%positive,0);(20208650034705403%positive,0);(5462320256831%positive,0);(78940031251451%positive,0);(4933752026107%positive,0)]]
  | StD => [HRank [(299941988654%positive,0);(4739944807726%positive,0);(314511975405048554%positive,0);(75839116923626%positive,0);(18415853522%positive,0);(4739691434730%positive,0);(296230714670%positive,0);(314511975405049518%positive,0);(19656998209442538%positive,0);(314511968962598574%positive,0);(1171585170%positive,0);(19656998209443502%positive,0);(4799071817902%positive,0);(4739542154542%positive,0)]]
  end.

Lemma cqh_h_00027 : iqh tmq_h_00027.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00027 StA 0 2 2 25 20000
                lsetq_h_00027 rsetq_h_00027 certq_h_00027 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00027); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00028 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00028 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StA,S0)]);(S0,[])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0)]);(S0,[(StA,S0)])];
   [(S1,[(StD,S1);(StC,S0)]);(S1,[(StD,S1);(StD,S0)])];
   [(S1,[(StD,S1);(StD,S0)]);(S0,[(StC,S1);(StD,S0)])];
   [(S1,[(StD,S1);(StD,S1)]);(S1,[(StB,S0)])];
   [(S1,[(StD,S1);(StD,S1)]);(S1,[(StD,S1);(StD,S0)])]].

Definition rsetq_h_00028 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StD,S0)]);(S0,[])]].

Definition certq_h_00028 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => []
  | StC => [HRank [(294741734719%positive,0);(4739759210287%positive,0);(1150286195%positive,1);(20225486237987583%positive,0);(75836230726635%positive,1);(18400386899%positive,2)]]
  | StD => [HRank [(18404253682%positive,0);(75836233348798%positive,0);(294473269054%positive,0)]]
  end.

Lemma cqh_h_00028 : iqh tmq_h_00028.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00028 StA 0 2 2 25 20000
                lsetq_h_00028 rsetq_h_00028 certq_h_00028 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00028); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00029 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00029 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StD,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StC,S1)])];
   [(S1,[(StC,S0);(StD,S1)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StD,S1)]);(S1,[(StC,S0);(StD,S1)])]].

Definition rsetq_h_00029 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StC,S1);(StC,S0)])]].

Definition certq_h_00029 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => []
  | StC => [HMeas MRight 68 [(321809160276005615%positive,1);(314631547614909167%positive,1);(76814341468911%positive,1);(4714778842043%positive,0);(314631547615277807%positive,1);(20113072198243055%positive,1);(4714779210683%positive,1);(1212665741275887%positive,1);(75791337353967%positive,1);(314631548370252527%positive,1);(1212666495881967%positive,1);(321809159521030895%positive,1);(1212666496250607%positive,1);(314631548369883887%positive,1);(78566688125679%positive,1);(19664471454479087%positive,1);(321809159521399535%positive,1);(75791336985327%positive,1);(20113072198611695%positive,1);(19664471454110447%positive,1);(4715534185403%positive,1);(4715533816763%positive,0);(1212665740907247%positive,1);(321809160276374255%positive,1)] [321809160276005615%positive;314631547614909167%positive;76814341468911%positive;4714778842043%positive;314631547615277807%positive;20113072198243055%positive;4714779210683%positive;1212665741275887%positive;1212666496250607%positive;75791337353967%positive;314631548370252527%positive;1212666495881967%positive;321809159521030895%positive;314631548369883887%positive;78566688125679%positive;19664471454479087%positive;321809159521399535%positive;75791336985327%positive;20113072198611695%positive;19664471454110447%positive;4715534185403%positive;4715533816763%positive;1212665740907247%positive;321809160276374255%positive]]
  | StD => [HMeas MLeft 68 [(20113072198244090%positive,0);(18753501330%positive,0);(1212665740908462%positive,1);(314631547614910382%positive,1);(321809160276375470%positive,1);(75791336986542%positive,1);(20113072198612910%positive,1);(1212665741276922%positive,1);(321809160276006830%positive,1);(76814341470126%positive,1);(1212666495883002%positive,1);(321809159521031930%positive,0);(75791337355002%positive,1);(20113072198612730%positive,0);(314631548370253562%positive,0);(20113072198244270%positive,1);(314631548369884922%positive,0);(78566688126714%positive,0);(1212665741277102%positive,1);(19664471454480122%positive,0);(321809159521400570%positive,0);(314631547615279022%positive,1);(19664471454111482%positive,0);(321809159521032110%positive,1);(1212666496251642%positive,1);(1212666496251822%positive,1);(314631548370253742%positive,1);(75791337355182%positive,1);(78566688126894%positive,1);(1212666495883182%positive,1);(19664471454480302%positive,1);(1212665740908282%positive,1);(314631548369885102%positive,1);(321809160276375290%positive,0);(75791336986362%positive,1);(314631547614910202%positive,0);(300056021294%positive,1);(321809160276006650%positive,0);(321809159521400750%positive,1);(19664471454111662%positive,1);(76814341469946%positive,0);(314631547615278842%positive,0)] [20113072198244090%positive;18753501330%positive;1212665740908462%positive;314631547614910382%positive;321809160276375470%positive;75791336986542%positive;20113072198612910%positive;1212665741276922%positive;321809160276006830%positive;76814341470126%positive;1212666495883002%positive;321809159521031930%positive;75791337355002%positive;314631548370253562%positive;20113072198244270%positive;314631548369884922%positive;78566688126714%positive;1212665741277102%positive;19664471454480122%positive;321809159521400570%positive;314631547615279022%positive;19664471454111482%positive;321809159521032110%positive;1212666496251642%positive;1212666496251822%positive;314631548370253742%positive;75791337355182%positive;78566688126894%positive;1212666495883182%positive;19664471454480302%positive;1212665740908282%positive;314631548369885102%positive;321809160276375290%positive;75791336986362%positive;314631547614910202%positive;300056021294%positive;321809160276006650%positive;321809159521400750%positive;19664471454111662%positive;20113072198612730%positive;76814341469946%positive;314631547615278842%positive]]
  end.

Lemma cqh_h_00029 : iqh tmq_h_00029.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00029 StA 0 2 2 25 20000
                lsetq_h_00029 rsetq_h_00029 certq_h_00029 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00029); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00030 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StC)
  | StC, S0 => Some (mkTrans S1 DL StB)
  | StC, S1 => Some (mkTrans S0 DR StD)
  | StD, S0 => Some (mkTrans S1 DR StD)
  | StD, S1 => Some (mkTrans S0 DR StB)
  end.

Definition lsetq_h_00030 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StB,S1)])];
   [(S0,[(StD,S1);(StC,S0)]);(S1,[(StD,S0);(StB,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StB,S1)]);(S0,[(StD,S1);(StC,S0)])];
   [(S1,[(StD,S0);(StB,S1)]);(S0,[(StC,S1);(StC,S0)])]].

Definition rsetq_h_00030 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StB,S1);(StB,S0)]);(S1,[(StC,S0);(StC,S1)])];
   [(S0,[(StB,S1);(StD,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StC,S1)]);(S0,[(StB,S1);(StD,S0)])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StB,S1);(StB,S0)])]].

Definition certq_h_00030 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(294401007407%positive,0);(20766484626%positive,0);(19641026015523578%positive,0);(357419794161333935%positive,0);(322951550640542171%positive,1);(20184471665332699%positive,1);(5316220063534%positive,2);(348403798813569786%positive,0);(357419794228376298%positive,0);(1150019826%positive,0);(348403798880614318%positive,2);(4722443899355%positive,1);(299698261806%positive,2);(75563097608667%positive,1);(19641026082568110%positive,2);(87260691755754%positive,0)]]
  | StC => [HRank [(18411919313%positive,0);(294401007407%positive,1);(322951550774793629%positive,0);(304941550311822297%positive,0);(357419794161333935%positive,1);(322951550640542171%positive,2);(307990595869%positive,0);(304941550177572285%positive,0);(4722443899355%positive,2);(4722701991197%positive,0);(19058846636398013%positive,0);(20184471665332699%positive,2);(1135917201%positive,0);(75563097608667%positive,2)]]
  | StD => [HMeas MLeft 26 [(20766484626%positive,28);(322951550774793629%positive,29);(19641026015523578%positive,26);(5316220063534%positive,0);(348403798813569786%positive,28);(307990595869%positive,29);(304941550177572285%positive,29);(357419794228376298%positive,28);(304941550311822297%positive,29);(1150019826%positive,2);(348403798880614318%positive,2);(4722701991197%positive,27);(19058846636398013%positive,29);(299698261806%positive,0);(1135917201%positive,27);(19641026082568110%positive,2);(87260691755754%positive,28);(18411919313%positive,29)] [304941550311822297%positive;1150019826%positive;348403798880614318%positive;299698261806%positive;4722701991197%positive;5316220063534%positive;1135917201%positive;322951550774793629%positive;20766484626%positive;348403798813569786%positive;19641026015523578%positive;87260691755754%positive;18411919313%positive;307990595869%positive;19641026082568110%positive;304941550177572285%positive;357419794228376298%positive;19058846636398013%positive]]
  end.

Lemma cqh_h_00030 : iqh tmq_h_00030.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00030 StA 0 2 2 25 20000
                lsetq_h_00030 rsetq_h_00030 certq_h_00030 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00030); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00031 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StB)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => None
  end.

Definition lsetq_h_00031 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition rsetq_h_00031 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition certq_h_00031 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 37 [(312234334099559403%positive,1);(19067385031905758%positive,1);(348966818560669374%positive,1);(305078164816613854%positive,1);(1207992429007326%positive,1);(76229085033451%positive,1);(85196976747499%positive,1);(4764317814590%positive,1);(5324811046718%positive,1);(4711490319018%positive,1);(312234334099928766%positive,1);(1207991674032606%positive,1);(312234334099928043%positive,1);(20800043155%positive,1);(348966818560668651%positive,1);(305078165571588574%positive,1);(312234334099560126%positive,1);(348966818560300734%positive,1);(348966818560300011%positive,1);(4711489950378%positive,0);(75499210494430%positive,1)] [312234334099559403%positive;19067385031905758%positive;348966818560669374%positive;305078164816613854%positive;1207992429007326%positive;76229085033451%positive;85196976747499%positive;4764317814590%positive;5324811046718%positive;4711490319018%positive;312234334099928766%positive;1207991674032606%positive;312234334099928043%positive;20800043155%positive;348966818560668651%positive;305078165571588574%positive;312234334099560126%positive;348966818560300734%positive;348966818560300011%positive;4711489950378%positive;75499210494430%positive]]
  | StC => [HMeas MLeft 37 [(1136457873%positive,0);(75499210495645%positive,2);(1207991674033821%positive,2);(1207992429008361%positive,2);(19067385031906793%positive,0);(305078165571589789%positive,2);(312234334099559403%positive,1);(290945206557%positive,2);(76229085033451%positive,1);(85196976747499%positive,1);(75499210495465%positive,2);(1207991674033641%positive,2);(19067385031906973%positive,2);(305078165571589609%positive,0);(305078164816615069%positive,2);(312234334099928043%positive,1);(20800043155%positive,1);(348966818560668651%positive,1);(305078164816614889%positive,0);(1207992429008541%positive,2);(348966818560300011%positive,1)] [1136457873%positive;75499210495645%positive;1207991674033821%positive;1207992429008361%positive;305078165571589789%positive;19067385031906793%positive;312234334099559403%positive;290945206557%positive;76229085033451%positive;85196976747499%positive;75499210495465%positive;1207991674033641%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;312234334099928043%positive;20800043155%positive;348966818560668651%positive;305078164816614889%positive;1207992429008541%positive;348966818560300011%positive]]
  | StD => [HMeas MRight 37 [(1136457873%positive,4);(75499210495645%positive,0);(1207991674033821%positive,0);(1207992429008361%positive,2);(19067385031906793%positive,4);(305078165571589789%positive,4);(19067385031905758%positive,4);(348966818560669374%positive,4);(305078164816613854%positive,4);(290945206557%positive,4);(1207992429007326%positive,4);(4764317814590%positive,4);(5324811046718%positive,4);(4711490319018%positive,1);(312234334099928766%positive,4);(75499210495465%positive,2);(1207991674033641%positive,2);(19067385031906973%positive,4);(305078165571589609%positive,4);(305078164816615069%positive,4);(1207991674032606%positive,4);(305078164816614889%positive,4);(305078165571588574%positive,4);(1207992429008541%positive,0);(312234334099560126%positive,4);(348966818560300734%positive,4);(4711489950378%positive,3);(75499210494430%positive,4)] [1136457873%positive;75499210495645%positive;1207991674033821%positive;1207992429008361%positive;305078165571589789%positive;19067385031906793%positive;19067385031905758%positive;348966818560669374%positive;305078164816613854%positive;290945206557%positive;1207992429007326%positive;4764317814590%positive;5324811046718%positive;4711490319018%positive;312234334099928766%positive;75499210495465%positive;1207991674033641%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;1207991674032606%positive;305078164816614889%positive;305078165571588574%positive;1207992429008541%positive;312234334099560126%positive;348966818560300734%positive;4711489950378%positive;75499210494430%positive]]
  end.

Lemma cqh_h_00031 : iqh tmq_h_00031.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00031 StA 0 2 2 25 20000
                lsetq_h_00031 rsetq_h_00031 certq_h_00031 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00031); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00032 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Definition lsetq_h_00032 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition rsetq_h_00032 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition certq_h_00032 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 35 [(1207989527598782%positive,2);(1207989527598059%positive,0);(312255777477710302%positive,2);(19067385031905758%positive,2);(348966818560669374%positive,2);(4713636385450%positive,1);(305078164816613854%positive,2);(85196976747499%positive,2);(1207989527967422%positive,2);(5324811046718%positive,2);(312255776722735582%positive,2);(19515985776038366%positive,2);(20800043155%positive,2);(348966818560668651%positive,2);(4714391360170%positive,1);(1207989527966699%positive,0);(305078165571588574%positive,2);(348966818560300734%positive,2);(348966818560300011%positive,2)] [1207989527598782%positive;1207989527598059%positive;312255777477710302%positive;19067385031905758%positive;348966818560669374%positive;305078164816613854%positive;4713636385450%positive;85196976747499%positive;1207989527967422%positive;5324811046718%positive;312255776722735582%positive;19515985776038366%positive;20800043155%positive;348966818560668651%positive;4714391360170%positive;305078165571588574%positive;1207989527966699%positive;348966818560300734%positive;348966818560300011%positive]]
  | StC => [HMeas MLeft 35 [(1136457873%positive,0);(1207989527598059%positive,2);(19067385031906793%positive,0);(305078165571589789%positive,2);(312255776722736617%positive,1);(19515985776039401%positive,1);(312255777477711517%positive,2);(290945206557%positive,2);(85196976747499%positive,1);(19067385031906973%positive,2);(305078165571589609%positive,0);(305078164816615069%positive,2);(20800043155%positive,1);(348966818560668651%positive,1);(312255776722736797%positive,2);(19515985776039581%positive,2);(312255777477711337%positive,1);(305078164816614889%positive,0);(1207989527966699%positive,2);(348966818560300011%positive,1)] [1136457873%positive;1207989527598059%positive;305078165571589789%positive;19067385031906793%positive;312255776722736617%positive;19515985776039401%positive;312255777477711517%positive;290945206557%positive;85196976747499%positive;348966818560300011%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;20800043155%positive;348966818560668651%positive;312255776722736797%positive;19515985776039581%positive;312255777477711337%positive;305078164816614889%positive;1207989527966699%positive]]
  | StD => [HMeas MRight 35 [(1136457873%positive,1);(1207989527598782%positive,1);(312255777477710302%positive,1);(19067385031906793%positive,1);(305078165571589789%positive,1);(19067385031905758%positive,1);(348966818560669374%positive,1);(312255776722736617%positive,1);(19515985776039401%positive,1);(4713636385450%positive,0);(312255777477711517%positive,1);(305078164816613854%positive,1);(290945206557%positive,1);(1207989527967422%positive,1);(5324811046718%positive,1);(312255776722735582%positive,1);(19067385031906973%positive,1);(305078165571589609%positive,1);(305078164816615069%positive,1);(19515985776038366%positive,1);(4714391360170%positive,0);(312255776722736797%positive,1);(19515985776039581%positive,1);(312255777477711337%positive,1);(305078164816614889%positive,1);(305078165571588574%positive,1);(348966818560300734%positive,1)] [1136457873%positive;1207989527598782%positive;312255777477710302%positive;305078165571589789%positive;19067385031906793%positive;19067385031905758%positive;348966818560669374%positive;312255776722736617%positive;19515985776039401%positive;4713636385450%positive;312255777477711517%positive;305078164816613854%positive;290945206557%positive;1207989527967422%positive;5324811046718%positive;312255776722735582%positive;19067385031906973%positive;305078165571589609%positive;305078164816615069%positive;19515985776038366%positive;4714391360170%positive;312255776722736797%positive;19515985776039581%positive;312255777477711337%positive;305078164816614889%positive;305078165571588574%positive;348966818560300734%positive]]
  end.

Lemma cqh_h_00032 : iqh tmq_h_00032.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00032 StA 0 2 2 25 20000
                lsetq_h_00032 rsetq_h_00032 certq_h_00032 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 25) 2000 tmq_h_00032); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00033 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StA)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => Some (mkTrans S0 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Definition lsetq_h_00033 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)])]].

Definition rsetq_h_00033 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00033 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(96506244151734932528823967%positive,0);(395289576045616243870191315455%positive,0);(395289576045508157479134423551%positive,0);(1272356869486641675967%positive,0);(86815892754912382467697151%positive,0);(356478221541895532295539301886%positive,1);(356478221541895532089555020255%positive,0);(395284740351525128597623269855%positive,0);(395289576045616244011751088126%positive,1);(5439425987881799326886367%positive,0);(86815892718883795727810207%positive,0);(6031566472647875933759967%positive,0);(5752220401271370238%positive,1);(79524556147012878315%positive,1);(75385173311315%positive,2);(309059144859841534%positive,3);(395284740351525128803607551486%positive,1);(86815892646826132970577918%positive,1);(86815892646825991410805247%positive,0);(87030815806108789221268990%positive,1);(22469610942466335%positive,0);(395289576045508157620694196222%positive,1);(19316196576851263%positive,0);(1272356869692626299902%positive,1);(96505063562366014931246590%positive,1);(395289576045580215283451559583%positive,0);(86815892754912524027469822%positive,1)]]
  | StC => [HMeas MLeft 45 [(356478221541823474632781987485%positive,1);(5485676198033%positive,0);(395289551557455399771264122857%positive,0);(92035520718772838377%positive,0);(96506244151734932528823967%positive,1);(86890067004746519077322729%positive,0);(395289576045616243870191315455%positive,1);(395289576045508157479134423551%positive,1);(1472550408361321037469%positive,1);(1272356869486641675967%positive,1);(20364736985982012145641%positive,0);(395284740351453071140850237085%positive,1);(5439425987881799326886367%positive,1);(356478221541895532089555020255%positive,1);(356478197192193354998930857961%positive,0);(86815892718883795727810207%positive,1);(79524556147012878315%positive,0);(86890067112832910134214633%positive,0);(6031566472647875933759967%positive,1);(395284740351525128597623269855%positive,1);(395284716001822951506999107561%positive,0);(87030809861357281091903465%positive,0);(22469610942466335%positive,1);(356478221541931561023838879389%positive,1);(19316196576851263%positive,1);(395289551557563486162321014761%positive,0);(395289576045580215283451559583%positive,1);(395284740351561157531907128989%positive,1);(75385173311315%positive,1);(96505057617614506801881065%positive,0);(86815892646825991410805247%positive,1);(86815892754912382467697151%positive,1)] [356478221541823474632781987485%positive;5485676198033%positive;395289551557455399771264122857%positive;92035520718772838377%positive;96506244151734932528823967%positive;86890067004746519077322729%positive;395289576045616243870191315455%positive;395289576045508157479134423551%positive;1472550408361321037469%positive;1272356869486641675967%positive;20364736985982012145641%positive;356478197192193354998930857961%positive;395284740351453071140850237085%positive;5439425987881799326886367%positive;356478221541895532089555020255%positive;86815892718883795727810207%positive;79524556147012878315%positive;86890067112832910134214633%positive;6031566472647875933759967%positive;395284740351525128597623269855%positive;395284716001822951506999107561%positive;87030809861357281091903465%positive;22469610942466335%positive;356478221541931561023838879389%positive;19316196576851263%positive;395289551557563486162321014761%positive;395289576045580215283451559583%positive;395284740351561157531907128989%positive;75385173311315%positive;96505057617614506801881065%positive;86815892646825991410805247%positive;86815892754912382467697151%positive]]
  | StD => [HRank [(356478221541823474632781987485%positive,0);(5752220401271370238%positive,0);(5485676198033%positive,1);(356478221541895532295539301886%positive,0);(395284740351525128803607551486%positive,0);(395289551557455399771264122857%positive,1);(87030815806108789221268990%positive,0);(96505063562366014931246590%positive,0);(92035520718772838377%positive,1);(1272356869692626299902%positive,0);(86890067004746519077322729%positive,1);(1472550408361321037469%positive,0);(309059144859841534%positive,0);(20364736985982012145641%positive,1);(395289576045616244011751088126%positive,0);(395284740351453071140850237085%positive,0);(86815892754912524027469822%positive,0);(356478197192193354998930857961%positive,1);(86890067112832910134214633%positive,1);(86815892646826132970577918%positive,0);(395284716001822951506999107561%positive,1);(87030809861357281091903465%positive,1);(356478221541931561023838879389%positive,0);(395289576045508157620694196222%positive,0);(395289551557563486162321014761%positive,1);(395284740351561157531907128989%positive,0);(96505057617614506801881065%positive,1)]]
  end.

Lemma cqh_h_00033 : iqh tmq_h_00033.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00033 StA 4 4 2 29 20000
                lsetq_h_00033 rsetq_h_00033 certq_h_00033 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00033); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00034 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StC)
  | StB, S0 => Some (mkTrans S1 DL StA)
  | StB, S1 => Some (mkTrans S1 DR StB)
  | StC, S0 => Some (mkTrans S1 DR StC)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00034 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StA,S1);(StC,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StA,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StA,S1);(StC,S1)]);(S1,[(StD,S1);(StD,S0);(StA,S1);(StC,S1)])];
   [(S1,[(StD,S1);(StD,S0);(StA,S1);(StC,S1)]);(S1,[(StC,S1);(StD,S0);(StA,S1);(StC,S1)])]].

Definition rsetq_h_00034 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S1)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S0)])]].

Definition certq_h_00034 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MRight 45 [(94114347458316807332875246%positive,1);(355781880472656385225673600191%positive,1);(94114365579957415850536651%positive,0);(355781880472726142641386220735%positive,1);(4714582220659%positive,0);(355781880472726138173009424075%positive,0);(385492441415505511823252581567%positive,1);(385492441415575269238965202111%positive,1);(86814564498004942135754443%positive,0);(385492441415575264770588405451%positive,0);(89754431268238864074%positive,0);(86814564567762357848374987%positive,0);(1272371321632298626239%positive,1);(395395886322957545211619101694%positive,1);(19310927726116670%positive,1);(1472964459370625821870%positive,1);(86860810662269640802299595%positive,0);(23567434718627486805707%positive,0);(76800402860178%positive,1);(96532212607500522863389886%positive,1);(355781806246486750149932927982%positive,1);(395395942840392375561539284158%positive,1);(395395886323027302627331722238%positive,1);(385492367189335876747511909358%positive,1);(5425909790084498250451966%positive,1);(395395942840322622473400221387%positive,0);(21912704833980718%positive,1);(86814564567758030274817214%positive,1);(395395942840392379889112841931%positive,0);(86860792540629032284638190%positive,1);(79523207322745126603%positive,0);(5425909859841913963072510%positive,1)] [94114347458316807332875246%positive;355781880472656385225673600191%positive;94114365579957415850536651%positive;355781880472726142641386220735%positive;4714582220659%positive;355781880472726138173009424075%positive;385492441415505511823252581567%positive;385492441415575269238965202111%positive;86814564498004942135754443%positive;385492441415575264770588405451%positive;89754431268238864074%positive;86814564567762357848374987%positive;1272371321632298626239%positive;395395886322957545211619101694%positive;19310927726116670%positive;1472964459370625821870%positive;86860810662269640802299595%positive;23567434718627486805707%positive;76800402860178%positive;96532212607500522863389886%positive;395395942840392375561539284158%positive;355781806246486750149932927982%positive;395395886323027302627331722238%positive;385492367189335876747511909358%positive;5425909790084498250451966%positive;395395942840322622473400221387%positive;21912704833980718%positive;86814564567758030274817214%positive;395395942840392379889112841931%positive;86860792540629032284638190%positive;79523207322745126603%positive;5425909859841913963072510%positive]]
  | StB => []
  | StC => [HRank [(1472964669914217892588%positive,0);(355781880472656385225673600191%positive,0);(94114365579957415850536651%positive,1);(355781880472726142641386220735%positive,0);(385492441415575264840926936812%positive,0);(4970200457946330092%positive,0);(4714582220659%positive,1);(395395942840322622543864578028%positive,0);(395395942840392379959577198572%positive,0);(355781880472726138173009424075%positive,1);(385492441415505511823252581567%positive,0);(385492441415575269238965202111%positive,0);(86860810662269507893247724%positive,0);(86814564498004942135754443%positive,1);(385492441415575264770588405451%positive,1);(355781880472726138243347955436%positive,0);(86814564567762357848374987%positive,1);(94114365579957282941484780%positive,0);(1272371321632298626239%positive,0);(86860810662269640802299595%positive,1);(350603247141556972%positive,0);(23567434718627486805707%positive,1);(86814564498005012600111084%positive,0);(86814564567762428312731628%positive,0);(395395942840322622473400221387%positive,1);(395395942840392379889112841931%positive,1);(79523207322745126603%positive,1)]]
  | StD => [HRank [(21912704833980718%positive,0);(1472964669914217892588%positive,1);(94114347458316807332875246%positive,0);(395395886322957545211619101694%positive,0);(395395886323027302627331722238%positive,0);(385492441415575264840926936812%positive,1);(96532212607500522863389886%positive,0);(89754431268238864074%positive,1);(395395942840322622543864578028%positive,1);(1472964459370625821870%positive,0);(94114365579957282941484780%positive,1);(385492367189335876747511909358%positive,0);(395395942840392379959577198572%positive,1);(19310927726116670%positive,0);(76800402860178%positive,2);(86860792540629032284638190%positive,0);(86814564498005012600111084%positive,1);(355781806246486750149932927982%positive,0);(395395942840392375561539284158%positive,0);(355781880472726138243347955436%positive,1);(86814564567762428312731628%positive,1);(5425909790084498250451966%positive,0);(350603247141556972%positive,3);(5425909859841913963072510%positive,0);(4970200457946330092%positive,1);(86860810662269507893247724%positive,1);(86814564567758030274817214%positive,0)]]
  end.

Lemma cqh_h_00034 : iqh tmq_h_00034.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00034 StB 4 4 2 29 20000
                lsetq_h_00034 rsetq_h_00034 certq_h_00034 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00034); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00035 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StC)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StA)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00035 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00035 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition certq_h_00035 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 50 [(321812664966698746%positive,2);(321812664211722991%positive,4);(321812664966697711%positive,4);(20113291238954926%positive,0);(314652163455309742%positive,4);(356852788752799647%positive,4);(5445141436191%positive,4);(75791334364922%positive,2);(321812664211724206%positive,0);(1212660372566971%positive,1);(321812664966698926%positive,0);(1212666493260527%positive,4);(4709410501563%positive,1);(314652164210284282%positive,4);(75791334363887%positive,4);(321809154152691615%positive,4);(1212665738286842%positive,2);(19665759941678842%positive,4);(1212660372198331%positive,3);(1172076690%positive,4);(1212666493261562%positive,2);(314652164210283247%positive,4);(4709410132923%positive,3);(321809154152322975%positive,4);(1212665738285807%positive,4);(19665759941677807%positive,4);(314652163455309562%positive,4);(321812658846004155%positive,1);(75791334365102%positive,0);(4910418007839%positive,4);(20113291238954746%positive,2);(314652164210284462%positive,4);(1212666493261742%positive,0);(314652163455308527%positive,4);(20113291238953711%positive,4);(1212665738287022%positive,0);(19665759941679022%positive,4);(321812658845635515%positive,3);(356852788753168287%positive,4);(321812664211724026%positive,2);(300075682094%positive,4)] [321812664966698746%positive;321812664211722991%positive;314652163455309742%positive;321812664966697711%positive;20113291238954926%positive;356852788752799647%positive;5445141436191%positive;75791334364922%positive;321812664211724206%positive;1212660372566971%positive;321812664966698926%positive;1212666493260527%positive;4709410501563%positive;356852788753168287%positive;314652164210284282%positive;75791334363887%positive;321809154152691615%positive;1212665738286842%positive;19665759941678842%positive;1212660372198331%positive;1172076690%positive;1212666493261562%positive;314652164210283247%positive;4709410132923%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;314652163455309562%positive;321812658846004155%positive;75791334365102%positive;4910418007839%positive;20113291238954746%positive;314652164210284462%positive;314652163455308527%positive;20113291238953711%positive;1212665738287022%positive;19665759941679022%positive;321812658845635515%positive;1212666493261742%positive;321812664211724026%positive;300075682094%positive]]
  | StC => [HMeas MRight 50 [(321812664211722991%positive,1);(321812664966697711%positive,1);(78566688125433%positive,1);(356852788752799647%positive,1);(321809154152690169%positive,1);(5445141436191%positive,1);(1212660372566971%positive,1);(1212666493260527%positive,1);(321809154152321529%positive,1);(4709410501563%positive,1);(75791334363887%positive,1);(21270083729%positive,1);(321809154152691615%positive,1);(1212660372198331%positive,0);(314652164210283247%positive,1);(4709410132923%positive,0);(87122262979065%positive,1);(321809154152322975%positive,1);(1212665738285807%positive,1);(19665759941677807%positive,1);(321812658846004155%positive,1);(356852788753166841%positive,1);(4910418007839%positive,1);(314652163455308527%positive,1);(20113291238953711%positive,1);(321812658845635515%positive,0);(356852788752798201%positive,1);(356852788753168287%positive,1)] [321812664211722991%positive;321812664966697711%positive;78566688125433%positive;356852788752799647%positive;321809154152690169%positive;5445141436191%positive;1212660372566971%positive;1212666493260527%positive;321809154152321529%positive;4709410501563%positive;75791334363887%positive;21270083729%positive;321809154152691615%positive;1212660372198331%positive;314652164210283247%positive;4709410132923%positive;87122262979065%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;321812658846004155%positive;356852788753166841%positive;4910418007839%positive;314652163455308527%positive;20113291238953711%positive;356852788752798201%positive;321812658845635515%positive;356852788753168287%positive]]
  | StD => [HMeas MLeft 50 [(321812664966698746%positive,2);(78566688125433%positive,1);(20113291238954926%positive,2);(314652163455309742%positive,2);(321809154152690169%positive,1);(75791334364922%positive,2);(321812664211724206%positive,2);(321812664966698926%positive,2);(321809154152321529%positive,1);(314652164210284282%positive,0);(21270083729%positive,1);(1212665738286842%positive,2);(19665759941678842%positive,0);(1172076690%positive,0);(1212666493261562%positive,2);(87122262979065%positive,1);(314652163455309562%positive,0);(75791334365102%positive,2);(356852788753166841%positive,1);(20113291238954746%positive,2);(314652164210284462%positive,2);(1212666493261742%positive,2);(1212665738287022%positive,2);(19665759941679022%positive,2);(356852788752798201%positive,1);(321812664211724026%positive,2);(300075682094%positive,2)] [321812664966698746%positive;314652163455309742%positive;78566688125433%positive;20113291238954926%positive;321809154152690169%positive;75791334364922%positive;321812664211724206%positive;321812664966698926%positive;321809154152321529%positive;314652164210284282%positive;21270083729%positive;1212665738286842%positive;19665759941678842%positive;1172076690%positive;1212666493261562%positive;87122262979065%positive;314652163455309562%positive;75791334365102%positive;356852788753166841%positive;20113291238954746%positive;314652164210284462%positive;1212665738287022%positive;19665759941679022%positive;356852788752798201%positive;1212666493261742%positive;321812664211724026%positive;300075682094%positive]]
  end.

Lemma cqh_h_00035 : iqh tmq_h_00035.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00035 StA 9 2 2 34 20000
                lsetq_h_00035 rsetq_h_00035 certq_h_00035 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00035); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00036 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StC)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00036 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00036 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition certq_h_00036 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 50 [(321812664966698746%positive,2);(321812664211722991%positive,4);(321812664966697711%positive,4);(20113291238954926%positive,0);(314652163455309742%positive,4);(356852788752799647%positive,4);(5445141436191%positive,4);(75791334364922%positive,2);(321812664211724206%positive,0);(1212660372566971%positive,1);(321812664966698926%positive,0);(1212666493260527%positive,4);(4709410501563%positive,1);(356852788753168287%positive,4);(314652164210284282%positive,4);(75791334363887%positive,4);(321809154152691615%positive,4);(1212665738286842%positive,2);(1212660372198331%positive,3);(1172076690%positive,4);(19665759941678842%positive,4);(1212666493261562%positive,2);(314652164210283247%positive,4);(4709410132923%positive,3);(321809154152322975%positive,4);(1212665738285807%positive,4);(19665759941677807%positive,4);(314652163455309562%positive,4);(321812658846004155%positive,1);(75791334365102%positive,0);(4910418007839%positive,4);(20113291238954746%positive,2);(314652164210284462%positive,4);(314652163455308527%positive,4);(20113291238953711%positive,4);(1212665738287022%positive,0);(19665759941679022%positive,4);(321812658845635515%positive,3);(1212666493261742%positive,0);(321812664211724026%positive,2);(300075682094%positive,4)] [321812664966698746%positive;321812664211722991%positive;314652163455309742%positive;321812664966697711%positive;20113291238954926%positive;356852788752799647%positive;5445141436191%positive;75791334364922%positive;321812664211724206%positive;1212660372566971%positive;321812664966698926%positive;1212666493260527%positive;4709410501563%positive;314652164210284282%positive;75791334363887%positive;321809154152691615%positive;1212665738286842%positive;1212660372198331%positive;1172076690%positive;19665759941678842%positive;1212666493261562%positive;314652164210283247%positive;4709410132923%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;314652163455309562%positive;321812658846004155%positive;75791334365102%positive;4910418007839%positive;20113291238954746%positive;314652164210284462%positive;1212666493261742%positive;314652163455308527%positive;20113291238953711%positive;1212665738287022%positive;19665759941679022%positive;321812658845635515%positive;356852788753168287%positive;321812664211724026%positive;300075682094%positive]]
  | StC => [HMeas MRight 50 [(321812664211722991%positive,1);(321812664966697711%positive,1);(78566688125433%positive,1);(356852788752799647%positive,1);(321809154152690169%positive,1);(5445141436191%positive,1);(1212660372566971%positive,1);(1212666493260527%positive,1);(321809154152321529%positive,1);(4709410501563%positive,1);(356852788753168287%positive,1);(75791334363887%positive,1);(21270083729%positive,1);(321809154152691615%positive,1);(1212660372198331%positive,0);(314652164210283247%positive,1);(4709410132923%positive,0);(87122262979065%positive,1);(321809154152322975%positive,1);(1212665738285807%positive,1);(19665759941677807%positive,1);(321812658846004155%positive,1);(356852788753166841%positive,1);(4910418007839%positive,1);(314652163455308527%positive,1);(20113291238953711%positive,1);(321812658845635515%positive,0);(356852788752798201%positive,1)] [321812664211722991%positive;321812664966697711%positive;78566688125433%positive;356852788752799647%positive;321809154152690169%positive;5445141436191%positive;1212660372566971%positive;1212666493260527%positive;321809154152321529%positive;4709410501563%positive;75791334363887%positive;21270083729%positive;321809154152691615%positive;1212660372198331%positive;314652164210283247%positive;4709410132923%positive;87122262979065%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;321812658846004155%positive;356852788753166841%positive;4910418007839%positive;314652163455308527%positive;20113291238953711%positive;356852788752798201%positive;321812658845635515%positive;356852788753168287%positive]]
  | StD => [HMeas MLeft 50 [(321812664966698746%positive,2);(78566688125433%positive,1);(20113291238954926%positive,2);(314652163455309742%positive,2);(321809154152690169%positive,1);(75791334364922%positive,2);(321812664211724206%positive,2);(321812664966698926%positive,2);(321809154152321529%positive,1);(314652164210284282%positive,0);(21270083729%positive,1);(1212665738286842%positive,2);(1172076690%positive,0);(19665759941678842%positive,0);(1212666493261562%positive,2);(87122262979065%positive,1);(314652163455309562%positive,0);(75791334365102%positive,2);(356852788753166841%positive,1);(20113291238954746%positive,2);(314652164210284462%positive,2);(1212665738287022%positive,2);(19665759941679022%positive,2);(356852788752798201%positive,1);(1212666493261742%positive,2);(321812664211724026%positive,2);(300075682094%positive,2)] [321812664966698746%positive;314652163455309742%positive;78566688125433%positive;20113291238954926%positive;321809154152690169%positive;75791334364922%positive;321812664211724206%positive;321812664966698926%positive;321809154152321529%positive;314652164210284282%positive;21270083729%positive;1212665738286842%positive;1172076690%positive;19665759941678842%positive;1212666493261562%positive;87122262979065%positive;314652163455309562%positive;75791334365102%positive;356852788753166841%positive;20113291238954746%positive;314652164210284462%positive;1212665738287022%positive;19665759941679022%positive;356852788752798201%positive;1212666493261742%positive;321812664211724026%positive;300075682094%positive]]
  end.

Lemma cqh_h_00036 : iqh tmq_h_00036.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00036 StA 9 2 2 34 20000
                lsetq_h_00036 rsetq_h_00036 certq_h_00036 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00036); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00037 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StC)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StA)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S0 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00037 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition rsetq_h_00037 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition certq_h_00037 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 37 [(357411547841885946%positive,4);(351078360865895151%positive,4);(1396138856798126%positive,0);(306064359855454111%positive,4);(4670218605499%positive,1);(306064355677927327%positive,4);(76724903465711%positive,4);(357411547841884911%positive,4);(1150007538%positive,4);(351078360865896366%positive,4);(76724903466926%positive,0);(19641575789098746%positive,4);(4722827818783%positive,4);(294402117422%positive,4);(4722566723359%positive,4);(357411547841886126%positive,4);(19641575789097711%positive,4);(19641575789098926%positive,4);(1371399845172986%positive,2);(306067452231907231%positive,4);(306067448054380447%positive,4);(1396138856797946%positive,2);(1371399845171951%positive,4);(4670171419579%positive,3);(1396138856796911%positive,4);(351078360865896186%positive,4);(1371399845173166%positive,0);(76724903466746%positive,2)] [357411547841885946%positive;351078360865895151%positive;1396138856798126%positive;306064359855454111%positive;4670218605499%positive;306064355677927327%positive;76724903465711%positive;357411547841884911%positive;1150007538%positive;351078360865896366%positive;76724903466926%positive;19641575789098746%positive;4722827818783%positive;294402117422%positive;4722566723359%positive;357411547841886126%positive;19641575789097711%positive;19641575789098926%positive;1371399845172986%positive;306067452231907231%positive;306067448054380447%positive;1396138856797946%positive;1371399845171951%positive;4670171419579%positive;1396138856796911%positive;351078360865896186%positive;1371399845173166%positive;76724903466746%positive]]
  | StC => [HMeas MLeft 37 [(351078360865895151%positive,1);(306064359855454111%positive,1);(4670218605499%positive,1);(306064355677927327%positive,1);(76724903465711%positive,1);(357411547841884911%positive,1);(4722827818783%positive,1);(4722566723359%positive,1);(306067448054379001%positive,1);(18419783537%positive,1);(19641575789097711%positive,1);(306067452231905785%positive,1);(306067452231907231%positive,1);(306067448054380447%positive,1);(75561067573753%positive,1);(75565245100537%positive,1);(1371399845171951%positive,1);(4670171419579%positive,0);(306064355677925881%positive,1);(1396138856796911%positive,1);(306064359855452665%positive,1)] [351078360865895151%positive;306064359855454111%positive;4670218605499%positive;306064355677927327%positive;76724903465711%positive;357411547841884911%positive;4722827818783%positive;4722566723359%positive;306067448054379001%positive;18419783537%positive;19641575789097711%positive;306067452231905785%positive;306067452231907231%positive;306067448054380447%positive;75561067573753%positive;75565245100537%positive;1371399845171951%positive;4670171419579%positive;306064355677925881%positive;1396138856796911%positive;306064359855452665%positive]]
  | StD => [HMeas MRight 37 [(357411547841885946%positive,0);(1396138856798126%positive,2);(1150007538%positive,0);(351078360865896366%positive,2);(76724903466926%positive,2);(19641575789098746%positive,0);(294402117422%positive,2);(357411547841886126%positive,2);(306067448054379001%positive,1);(18419783537%positive,1);(306067452231905785%positive,1);(19641575789098926%positive,2);(1371399845172986%positive,2);(75561067573753%positive,1);(75565245100537%positive,1);(1396138856797946%positive,2);(306064355677925881%positive,1);(306064359855452665%positive,1);(351078360865896186%positive,0);(1371399845173166%positive,2);(76724903466746%positive,2)] [357411547841885946%positive;1396138856798126%positive;1150007538%positive;351078360865896366%positive;76724903466926%positive;19641575789098746%positive;294402117422%positive;357411547841886126%positive;306067448054379001%positive;18419783537%positive;306067452231905785%positive;19641575789098926%positive;1371399845172986%positive;75561067573753%positive;75565245100537%positive;1396138856797946%positive;306064355677925881%positive;351078360865896186%positive;306064359855452665%positive;1371399845173166%positive;76724903466746%positive]]
  end.

Lemma cqh_h_00037 : iqh tmq_h_00037.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00037 StA 9 2 2 34 20000
                lsetq_h_00037 rsetq_h_00037 certq_h_00037 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00037); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00038 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StC)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StA)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S0 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00038 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition rsetq_h_00038 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition certq_h_00038 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 37 [(357411547841885946%positive,4);(351078360865895151%positive,4);(1396138856798126%positive,0);(306064359855454111%positive,4);(4670218605499%positive,1);(306064355677927327%positive,4);(76724903465711%positive,4);(357411547841884911%positive,4);(1150007538%positive,4);(351078360865896366%positive,4);(76724903466926%positive,0);(19641575789098746%positive,4);(4722827818783%positive,4);(294402117422%positive,4);(4722566723359%positive,4);(357411547841886126%positive,4);(19641575789097711%positive,4);(19641575789098926%positive,4);(1371399845172986%positive,2);(306067452231907231%positive,4);(306067448054380447%positive,4);(1396138856797946%positive,2);(1371399845171951%positive,4);(4670171419579%positive,3);(351078360865896186%positive,4);(1396138856796911%positive,4);(1371399845173166%positive,0);(76724903466746%positive,2)] [357411547841885946%positive;351078360865895151%positive;1396138856798126%positive;306064359855454111%positive;4670218605499%positive;306064355677927327%positive;76724903465711%positive;357411547841884911%positive;1150007538%positive;351078360865896366%positive;76724903466926%positive;19641575789098746%positive;4722827818783%positive;294402117422%positive;4722566723359%positive;357411547841886126%positive;19641575789097711%positive;19641575789098926%positive;1371399845172986%positive;306067452231907231%positive;306067448054380447%positive;1396138856797946%positive;1371399845171951%positive;4670171419579%positive;351078360865896186%positive;1396138856796911%positive;1371399845173166%positive;76724903466746%positive]]
  | StC => [HMeas MLeft 37 [(351078360865895151%positive,1);(306064359855454111%positive,1);(4670218605499%positive,1);(306064355677927327%positive,1);(76724903465711%positive,1);(357411547841884911%positive,1);(4722827818783%positive,1);(4722566723359%positive,1);(306067448054379001%positive,1);(18419783537%positive,1);(19641575789097711%positive,1);(306067452231905785%positive,1);(306067452231907231%positive,1);(306067448054380447%positive,1);(75561067573753%positive,1);(75565245100537%positive,1);(1371399845171951%positive,1);(4670171419579%positive,0);(306064355677925881%positive,1);(306064359855452665%positive,1);(1396138856796911%positive,1)] [351078360865895151%positive;306064359855454111%positive;4670218605499%positive;306064355677927327%positive;76724903465711%positive;357411547841884911%positive;4722827818783%positive;4722566723359%positive;306067448054379001%positive;18419783537%positive;19641575789097711%positive;306067452231905785%positive;306067452231907231%positive;306067448054380447%positive;75561067573753%positive;75565245100537%positive;1371399845171951%positive;4670171419579%positive;306064355677925881%positive;1396138856796911%positive;306064359855452665%positive]]
  | StD => [HMeas MRight 37 [(357411547841885946%positive,0);(1396138856798126%positive,2);(1150007538%positive,0);(351078360865896366%positive,2);(76724903466926%positive,2);(19641575789098746%positive,0);(294402117422%positive,2);(357411547841886126%positive,2);(306067448054379001%positive,1);(18419783537%positive,1);(306067452231905785%positive,1);(19641575789098926%positive,2);(1371399845172986%positive,2);(75561067573753%positive,1);(75565245100537%positive,1);(1396138856797946%positive,2);(306064355677925881%positive,1);(351078360865896186%positive,0);(306064359855452665%positive,1);(1371399845173166%positive,2);(76724903466746%positive,2)] [357411547841885946%positive;1396138856798126%positive;1150007538%positive;351078360865896366%positive;76724903466926%positive;19641575789098746%positive;294402117422%positive;357411547841886126%positive;306067448054379001%positive;18419783537%positive;306067452231905785%positive;19641575789098926%positive;1371399845172986%positive;75561067573753%positive;75565245100537%positive;1396138856797946%positive;306064355677925881%positive;351078360865896186%positive;306064359855452665%positive;1371399845173166%positive;76724903466746%positive]]
  end.

Lemma cqh_h_00038 : iqh tmq_h_00038.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00038 StA 9 2 2 34 20000
                lsetq_h_00038 rsetq_h_00038 certq_h_00038 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00038); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00039 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StD)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DR StD)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00039 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StC,S1);(StC,S0);(StA,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StD,S1);(StD,S0)])]].

Definition rsetq_h_00039 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S0)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)])]].

Definition certq_h_00039 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MRight 45 [(396012496184393715203614178478%positive,1);(396012419675369752386680113919%positive,1);(396012496184325162852645600430%positive,1);(5273687345685328695905007%positive,1);(94264891298707663689612463%positive,1);(79136332654739%positive,1);(4715651504114%positive,0);(84378999460475949615869898%positive,0);(386108994759576604376298614730%positive,0);(346494894612909951856680631470%positive,1);(84378999460480454357351599%positive,1);(96682719647289974116043519%positive,1);(79236098723189567434%positive,0);(386108900541678326506860301039%positive,1);(386108994759576608881040096431%positive,1);(23013889477222040125386%positive,0);(19315309674854191%positive,1);(1438367741337354370239%positive,1);(92203831187426197451%positive,0);(84378999391923598647291850%positive,0);(5273687277132977727326959%positive,1);(1267777575279823879342%positive,1);(84593461451143682368981759%positive,1);(346494818103954541390715144959%positive,1);(386108900541609774155891722991%positive,1);(386108994759508052025330036682%positive,0);(96682738326251034507411402%positive,0);(346494894612978508498858082250%positive,0);(396012496184393719494823051210%positive,0);(346494894612978504207649209518%positive,1);(22510701791840575%positive,1);(84593480130104742760349642%positive,0)] [396012496184393715203614178478%positive;396012419675369752386680113919%positive;5273687345685328695905007%positive;396012496184325162852645600430%positive;94264891298707663689612463%positive;79136332654739%positive;4715651504114%positive;84378999460475949615869898%positive;386108994759576604376298614730%positive;346494894612909951856680631470%positive;84378999460480454357351599%positive;96682719647289974116043519%positive;79236098723189567434%positive;386108900541678326506860301039%positive;386108994759576608881040096431%positive;23013889477222040125386%positive;19315309674854191%positive;1438367741337354370239%positive;92203831187426197451%positive;84378999391923598647291850%positive;5273687277132977727326959%positive;1267777575279823879342%positive;84593461451143682368981759%positive;346494818103954541390715144959%positive;386108900541609774155891722991%positive;386108994759508052025330036682%positive;96682738326251034507411402%positive;346494894612978508498858082250%positive;396012496184393719494823051210%positive;346494894612978504207649209518%positive;22510701791840575%positive;84593480130104742760349642%positive]]
  | StB => []
  | StC => [HRank [(396012419675369752386680113919%positive,0);(22510701791840575%positive,0);(1438368092326377016316%positive,1);(5273687345685328695905007%positive,0);(94264891298707663689612463%positive,0);(92203831187426197451%positive,1);(79136332654739%positive,2);(5273687277132977727326959%positive,0);(4952256170616648444%positive,1);(84378999460480454357351599%positive,0);(96682719647289974116043519%positive,0);(386108900541678326506860301039%positive,0);(386108900541609774155891722991%positive,0);(346494894612978508605687115772%positive,1);(386108994759576608881040096431%positive,0);(346494818103954541390715144959%positive,0);(84378999460476056319078140%positive,1);(19315309674854191%positive,0);(1438367741337354370239%positive,0);(84593461451143682368981759%positive,0);(360171215575880700%positive,3);(396012496184393719601652084732%positive,1);(96682738326250903611682812%positive,1);(386108994759576604483001822972%positive,1);(84378999391923705350500092%positive,1);(84593480130104611864621052%positive,1);(386108994759508052132033244924%positive,1)]]
  | StD => [HRank [(396012496184393715203614178478%positive,0);(1438368092326377016316%positive,0);(396012496184325162852645600430%positive,0);(4952256170616648444%positive,0);(4715651504114%positive,1);(346494894612978508605687115772%positive,0);(84378999460475949615869898%positive,1);(396012496184393719601652084732%positive,0);(386108994759576604376298614730%positive,1);(346494894612909951856680631470%positive,0);(84378999460476056319078140%positive,0);(84378999391923705350500092%positive,0);(79236098723189567434%positive,1);(360171215575880700%positive,0);(23013889477222040125386%positive,1);(84593480130104611864621052%positive,0);(84378999391923598647291850%positive,1);(1267777575279823879342%positive,0);(96682738326250903611682812%positive,0);(386108994759576604483001822972%positive,0);(386108994759508052025330036682%positive,1);(96682738326251034507411402%positive,1);(386108994759508052132033244924%positive,0);(346494894612978508498858082250%positive,1);(396012496184393719494823051210%positive,1);(346494894612978504207649209518%positive,0);(84593480130104742760349642%positive,1)]]
  end.

Lemma cqh_h_00039 : iqh tmq_h_00039.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00039 StB 6 4 2 31 20000
                lsetq_h_00039 rsetq_h_00039 certq_h_00039 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 31) 2000 tmq_h_00039); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00040 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StD)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StC)
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DR StD)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00040 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StC,S1);(StC,S0);(StA,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StD,S1);(StD,S0)])]].

Definition rsetq_h_00040 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S0)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)])]].

Definition certq_h_00040 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MRight 45 [(396012496184393715203614178478%positive,1);(396012419675369752386680113919%positive,1);(396012496184325162852645600430%positive,1);(5273687345685328695905007%positive,1);(94264891298707663689612463%positive,1);(79136332654739%positive,1);(4715651504114%positive,0);(84378999460475949615869898%positive,0);(386108994759576604376298614730%positive,0);(346494894612909951856680631470%positive,1);(84378999460480454357351599%positive,1);(96682719647289974116043519%positive,1);(79236098723189567434%positive,0);(386108900541678326506860301039%positive,1);(386108994759576608881040096431%positive,1);(23013889477222040125386%positive,0);(19315309674854191%positive,1);(1438367741337354370239%positive,1);(92203831187426197451%positive,0);(84378999391923598647291850%positive,0);(5273687277132977727326959%positive,1);(1267777575279823879342%positive,1);(84593461451143682368981759%positive,1);(346494818103954541390715144959%positive,1);(386108900541609774155891722991%positive,1);(386108994759508052025330036682%positive,0);(96682738326251034507411402%positive,0);(346494894612978508498858082250%positive,0);(396012496184393719494823051210%positive,0);(346494894612978504207649209518%positive,1);(22510701791840575%positive,1);(84593480130104742760349642%positive,0)] [396012496184393715203614178478%positive;396012419675369752386680113919%positive;5273687345685328695905007%positive;396012496184325162852645600430%positive;94264891298707663689612463%positive;79136332654739%positive;4715651504114%positive;84378999460475949615869898%positive;386108994759576604376298614730%positive;346494894612909951856680631470%positive;84378999460480454357351599%positive;96682719647289974116043519%positive;79236098723189567434%positive;386108900541678326506860301039%positive;386108994759576608881040096431%positive;23013889477222040125386%positive;19315309674854191%positive;1438367741337354370239%positive;92203831187426197451%positive;84378999391923598647291850%positive;5273687277132977727326959%positive;1267777575279823879342%positive;84593461451143682368981759%positive;346494818103954541390715144959%positive;386108900541609774155891722991%positive;386108994759508052025330036682%positive;96682738326251034507411402%positive;346494894612978508498858082250%positive;396012496184393719494823051210%positive;346494894612978504207649209518%positive;22510701791840575%positive;84593480130104742760349642%positive]]
  | StB => []
  | StC => [HRank [(396012419675369752386680113919%positive,0);(22510701791840575%positive,0);(1438368092326377016316%positive,1);(5273687345685328695905007%positive,0);(94264891298707663689612463%positive,0);(92203831187426197451%positive,1);(79136332654739%positive,2);(5273687277132977727326959%positive,0);(4952256170616648444%positive,1);(84378999460480454357351599%positive,0);(96682719647289974116043519%positive,0);(386108900541678326506860301039%positive,0);(386108900541609774155891722991%positive,0);(346494894612978508605687115772%positive,1);(386108994759576608881040096431%positive,0);(346494818103954541390715144959%positive,0);(84378999460476056319078140%positive,1);(19315309674854191%positive,0);(1438367741337354370239%positive,0);(84593461451143682368981759%positive,0);(360171215575880700%positive,3);(396012496184393719601652084732%positive,1);(96682738326250903611682812%positive,1);(386108994759576604483001822972%positive,1);(84378999391923705350500092%positive,1);(84593480130104611864621052%positive,1);(386108994759508052132033244924%positive,1)]]
  | StD => [HRank [(396012496184393715203614178478%positive,0);(1438368092326377016316%positive,0);(396012496184325162852645600430%positive,0);(4952256170616648444%positive,0);(4715651504114%positive,1);(346494894612978508605687115772%positive,0);(84378999460475949615869898%positive,1);(396012496184393719601652084732%positive,0);(386108994759576604376298614730%positive,1);(346494894612909951856680631470%positive,0);(84378999460476056319078140%positive,0);(84378999391923705350500092%positive,0);(79236098723189567434%positive,1);(360171215575880700%positive,0);(23013889477222040125386%positive,1);(84593480130104611864621052%positive,0);(84378999391923598647291850%positive,1);(1267777575279823879342%positive,0);(96682738326250903611682812%positive,0);(386108994759576604483001822972%positive,0);(386108994759508052025330036682%positive,1);(96682738326251034507411402%positive,1);(386108994759508052132033244924%positive,0);(346494894612978508498858082250%positive,1);(396012496184393719494823051210%positive,1);(346494894612978504207649209518%positive,0);(84593480130104742760349642%positive,1)]]
  end.

Lemma cqh_h_00040 : iqh tmq_h_00040.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00040 StB 4 4 2 29 20000
                lsetq_h_00040 rsetq_h_00040 certq_h_00040 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00040); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00041 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StD)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S1 DR StC)
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DR StD)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00041 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StA,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0);(StA,S0)])];
   [(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StC,S1);(StC,S0);(StA,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StD,S1);(StD,S0)])]].

Definition rsetq_h_00041 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S0)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)])]].

Definition certq_h_00041 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MRight 58 [(396012496184393715203614178478%positive,1);(1546923813219792081571217354%positive,0);(396012419675369752386680113919%positive,1);(1266181105199251%positive,1);(396012496184325162852645600430%positive,1);(5273687345685328695905007%positive,1);(94264891298707663689612463%positive,1);(79136332654739%positive,1);(1353495682081451413618229194%positive,0);(4715651504114%positive,0);(84378999460475949615869898%positive,0);(368222231635545673744330%positive,0);(386108994759576604376298614730%positive,0);(360171228669448383%positive,1);(346494894612909951856680631470%positive,1);(84378999460480454357351599%positive,1);(96682719647289974116043519%positive,1);(23013883861397245525183%positive,1);(79236098723189567434%positive,0);(386108900541678326506860301039%positive,1);(386108994759576608881040096431%positive,1);(19315309674854191%positive,1);(23013889477222040125386%positive,0);(5273687277132977727326959%positive,1);(84593461451143682368981759%positive,1);(84378999391923598647291850%positive,0);(1438367741337354370239%positive,1);(1267777575279823879342%positive,1);(346494818103954541390715144959%positive,1);(386108900541609774155891722991%positive,1);(1546923514356417078742207231%positive,1);(92203831187426197451%positive,0);(386108994759508052025330036682%positive,0);(96682738326251034507411402%positive,0);(346494894612978508498858082250%positive,0);(396012496184393719494823051210%positive,0);(1475261298998818947019%positive,0);(1353495383218076410789219071%positive,1);(346494894612978504207649209518%positive,1);(22510701791840575%positive,1);(84593480130104742760349642%positive,0)] [396012496184393715203614178478%positive;1546923813219792081571217354%positive;396012419675369752386680113919%positive;1266181105199251%positive;396012496184325162852645600430%positive;5273687345685328695905007%positive;94264891298707663689612463%positive;79136332654739%positive;1353495682081451413618229194%positive;4715651504114%positive;84378999460475949615869898%positive;368222231635545673744330%positive;386108994759576604376298614730%positive;360171228669448383%positive;346494894612909951856680631470%positive;84378999460480454357351599%positive;96682719647289974116043519%positive;23013883861397245525183%positive;79236098723189567434%positive;386108900541678326506860301039%positive;386108994759576608881040096431%positive;19315309674854191%positive;23013889477222040125386%positive;5273687277132977727326959%positive;84593461451143682368981759%positive;84378999391923598647291850%positive;1438367741337354370239%positive;1267777575279823879342%positive;346494818103954541390715144959%positive;386108900541609774155891722991%positive;1546923514356417078742207231%positive;92203831187426197451%positive;386108994759508052025330036682%positive;96682738326251034507411402%positive;346494894612978508498858082250%positive;396012496184393719494823051210%positive;1475261298998818947019%positive;1353495383218076410789219071%positive;346494894612978504207649209518%positive;22510701791840575%positive;84593480130104742760349642%positive]]
  | StB => []
  | StC => [HRank [(396012419675369752386680113919%positive,0);(360171228669448383%positive,0);(23013889477221604117500%positive,1);(22510701791840575%positive,0);(1438368092326377016316%positive,1);(23013883861397245525183%positive,0);(1353495682081451282722500604%positive,1);(94264891298707663689612463%positive,0);(1475261298998818947019%positive,1);(1266181105199251%positive,2);(5273687345685328695905007%positive,0);(92203831187426197451%positive,1);(79136332654739%positive,2);(5273687277132977727326959%positive,0);(4952256170616648444%positive,1);(84378999460480454357351599%positive,0);(96682719647289974116043519%positive,0);(386108900541678326506860301039%positive,0);(386108900541609774155891722991%positive,0);(346494894612978508605687115772%positive,1);(386108994759576608881040096431%positive,0);(346494818103954541390715144959%positive,0);(84378999460476056319078140%positive,1);(19315309674854191%positive,0);(84593461451143682368981759%positive,0);(1438367741337354370239%positive,0);(1546923514356417078742207231%positive,0);(360171215575880700%positive,3);(396012496184393719601652084732%positive,1);(96682738326250903611682812%positive,1);(386108994759576604483001822972%positive,1);(1353495383218076410789219071%positive,0);(84378999391923705350500092%positive,1);(84593480130104611864621052%positive,1);(5762739449214077948%positive,3);(386108994759508052132033244924%positive,1);(1546923813219791950675488764%positive,1)]]
  | StD => [HRank [(396012496184393715203614178478%positive,0);(23013889477221604117500%positive,0);(1546923813219792081571217354%positive,1);(1438368092326377016316%positive,0);(1353495682081451282722500604%positive,0);(396012496184325162852645600430%positive,0);(1353495682081451413618229194%positive,1);(4952256170616648444%positive,0);(4715651504114%positive,1);(346494894612978508605687115772%positive,0);(84378999460475949615869898%positive,1);(5762739449214077948%positive,0);(368222231635545673744330%positive,1);(396012496184393719601652084732%positive,0);(386108994759576604376298614730%positive,1);(346494894612909951856680631470%positive,0);(84378999460476056319078140%positive,0);(84378999391923705350500092%positive,0);(79236098723189567434%positive,1);(360171215575880700%positive,0);(23013889477222040125386%positive,1);(84593480130104611864621052%positive,0);(84378999391923598647291850%positive,1);(1267777575279823879342%positive,0);(96682738326250903611682812%positive,0);(386108994759576604483001822972%positive,0);(1546923813219791950675488764%positive,0);(386108994759508052025330036682%positive,1);(96682738326251034507411402%positive,1);(386108994759508052132033244924%positive,0);(346494894612978508498858082250%positive,1);(396012496184393719494823051210%positive,1);(346494894612978504207649209518%positive,0);(84593480130104742760349642%positive,1)]]
  end.

Lemma cqh_h_00041 : iqh tmq_h_00041.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00041 StB 4 4 2 29 20000
                lsetq_h_00041 rsetq_h_00041 certq_h_00041 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00041); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00042 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StA)
  | StB, S1 => Some (mkTrans S1 DR StC)
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DR StD)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00042 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StC,S1);(StC,S0);(StA,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StD,S1);(StD,S0)])]].

Definition rsetq_h_00042 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S0)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)])]].

Definition certq_h_00042 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MRight 45 [(396012496184393715203614178478%positive,1);(396012419675369752386680113919%positive,1);(396012496184325162852645600430%positive,1);(5273687345685328695905007%positive,1);(94264891298707663689612463%positive,1);(79136332654739%positive,1);(4715651504114%positive,0);(84378999460475949615869898%positive,0);(386108994759576604376298614730%positive,0);(346494894612909951856680631470%positive,1);(84378999460480454357351599%positive,1);(96682719647289974116043519%positive,1);(79236098723189567434%positive,0);(386108900541678326506860301039%positive,1);(386108994759576608881040096431%positive,1);(23013889477222040125386%positive,0);(19315309674854191%positive,1);(1438367741337354370239%positive,1);(92203831187426197451%positive,0);(84378999391923598647291850%positive,0);(5273687277132977727326959%positive,1);(1267777575279823879342%positive,1);(84593461451143682368981759%positive,1);(346494818103954541390715144959%positive,1);(386108900541609774155891722991%positive,1);(386108994759508052025330036682%positive,0);(96682738326251034507411402%positive,0);(346494894612978508498858082250%positive,0);(396012496184393719494823051210%positive,0);(346494894612978504207649209518%positive,1);(22510701791840575%positive,1);(84593480130104742760349642%positive,0)] [396012496184393715203614178478%positive;396012419675369752386680113919%positive;5273687345685328695905007%positive;396012496184325162852645600430%positive;94264891298707663689612463%positive;79136332654739%positive;4715651504114%positive;84378999460475949615869898%positive;386108994759576604376298614730%positive;346494894612909951856680631470%positive;84378999460480454357351599%positive;96682719647289974116043519%positive;79236098723189567434%positive;386108900541678326506860301039%positive;386108994759576608881040096431%positive;23013889477222040125386%positive;19315309674854191%positive;1438367741337354370239%positive;92203831187426197451%positive;84378999391923598647291850%positive;5273687277132977727326959%positive;1267777575279823879342%positive;84593461451143682368981759%positive;346494818103954541390715144959%positive;386108900541609774155891722991%positive;386108994759508052025330036682%positive;96682738326251034507411402%positive;346494894612978508498858082250%positive;396012496184393719494823051210%positive;346494894612978504207649209518%positive;22510701791840575%positive;84593480130104742760349642%positive]]
  | StB => []
  | StC => [HRank [(396012419675369752386680113919%positive,0);(22510701791840575%positive,0);(1438368092326377016316%positive,1);(5273687345685328695905007%positive,0);(94264891298707663689612463%positive,0);(92203831187426197451%positive,1);(79136332654739%positive,2);(5273687277132977727326959%positive,0);(4952256170616648444%positive,1);(84378999460480454357351599%positive,0);(96682719647289974116043519%positive,0);(386108900541678326506860301039%positive,0);(386108900541609774155891722991%positive,0);(346494894612978508605687115772%positive,1);(386108994759576608881040096431%positive,0);(346494818103954541390715144959%positive,0);(84378999460476056319078140%positive,1);(19315309674854191%positive,0);(1438367741337354370239%positive,0);(84593461451143682368981759%positive,0);(360171215575880700%positive,3);(396012496184393719601652084732%positive,1);(96682738326250903611682812%positive,1);(386108994759576604483001822972%positive,1);(84378999391923705350500092%positive,1);(84593480130104611864621052%positive,1);(386108994759508052132033244924%positive,1)]]
  | StD => [HRank [(396012496184393715203614178478%positive,0);(1438368092326377016316%positive,0);(396012496184325162852645600430%positive,0);(4952256170616648444%positive,0);(4715651504114%positive,1);(346494894612978508605687115772%positive,0);(84378999460475949615869898%positive,1);(396012496184393719601652084732%positive,0);(386108994759576604376298614730%positive,1);(346494894612909951856680631470%positive,0);(84378999460476056319078140%positive,0);(84378999391923705350500092%positive,0);(79236098723189567434%positive,1);(360171215575880700%positive,0);(23013889477222040125386%positive,1);(84593480130104611864621052%positive,0);(84378999391923598647291850%positive,1);(1267777575279823879342%positive,0);(96682738326250903611682812%positive,0);(386108994759576604483001822972%positive,0);(386108994759508052025330036682%positive,1);(96682738326251034507411402%positive,1);(386108994759508052132033244924%positive,0);(346494894612978508498858082250%positive,1);(396012496184393719494823051210%positive,1);(346494894612978504207649209518%positive,0);(84593480130104742760349642%positive,1)]]
  end.

Lemma cqh_h_00042 : iqh tmq_h_00042.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00042 StB 3 4 2 28 20000
                lsetq_h_00042 rsetq_h_00042 certq_h_00042 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00042); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00043 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DR StD)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00043 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StC,S1);(StC,S0);(StA,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StD,S1);(StD,S0)])]].

Definition rsetq_h_00043 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S0)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)])]].

Definition certq_h_00043 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MRight 45 [(396012496184393715203614178478%positive,1);(396012419675369752386680113919%positive,1);(396012496184325162852645600430%positive,1);(5273687345685328695905007%positive,1);(94264891298707663689612463%positive,1);(79136332654739%positive,1);(4715651504114%positive,0);(84378999460475949615869898%positive,0);(386108994759576604376298614730%positive,0);(346494894612909951856680631470%positive,1);(84378999460480454357351599%positive,1);(96682719647289974116043519%positive,1);(79236098723189567434%positive,0);(386108900541678326506860301039%positive,1);(386108994759576608881040096431%positive,1);(23013889477222040125386%positive,0);(19315309674854191%positive,1);(1438367741337354370239%positive,1);(92203831187426197451%positive,0);(5273687277132977727326959%positive,1);(84593461451143682368981759%positive,1);(1267777575279823879342%positive,1);(84378999391923598647291850%positive,0);(346494818103954541390715144959%positive,1);(386108900541609774155891722991%positive,1);(386108994759508052025330036682%positive,0);(96682738326251034507411402%positive,0);(346494894612978508498858082250%positive,0);(396012496184393719494823051210%positive,0);(346494894612978504207649209518%positive,1);(22510701791840575%positive,1);(84593480130104742760349642%positive,0)] [396012496184393715203614178478%positive;396012419675369752386680113919%positive;5273687345685328695905007%positive;396012496184325162852645600430%positive;94264891298707663689612463%positive;79136332654739%positive;4715651504114%positive;84378999460475949615869898%positive;386108994759576604376298614730%positive;346494894612909951856680631470%positive;84378999460480454357351599%positive;96682719647289974116043519%positive;79236098723189567434%positive;386108900541678326506860301039%positive;386108994759576608881040096431%positive;23013889477222040125386%positive;19315309674854191%positive;1438367741337354370239%positive;92203831187426197451%positive;5273687277132977727326959%positive;84593461451143682368981759%positive;1267777575279823879342%positive;84378999391923598647291850%positive;346494818103954541390715144959%positive;386108900541609774155891722991%positive;386108994759508052025330036682%positive;96682738326251034507411402%positive;346494894612978508498858082250%positive;396012496184393719494823051210%positive;346494894612978504207649209518%positive;22510701791840575%positive;84593480130104742760349642%positive]]
  | StB => []
  | StC => [HRank [(396012419675369752386680113919%positive,0);(22510701791840575%positive,0);(1438368092326377016316%positive,1);(5273687345685328695905007%positive,0);(94264891298707663689612463%positive,0);(92203831187426197451%positive,1);(79136332654739%positive,2);(5273687277132977727326959%positive,0);(4952256170616648444%positive,1);(84378999460480454357351599%positive,0);(96682719647289974116043519%positive,0);(386108900541678326506860301039%positive,0);(386108900541609774155891722991%positive,0);(346494894612978508605687115772%positive,1);(386108994759576608881040096431%positive,0);(346494818103954541390715144959%positive,0);(84378999460476056319078140%positive,1);(19315309674854191%positive,0);(1438367741337354370239%positive,0);(84593461451143682368981759%positive,0);(360171215575880700%positive,3);(396012496184393719601652084732%positive,1);(96682738326250903611682812%positive,1);(386108994759576604483001822972%positive,1);(84378999391923705350500092%positive,1);(84593480130104611864621052%positive,1);(386108994759508052132033244924%positive,1)]]
  | StD => [HRank [(396012496184393715203614178478%positive,0);(1438368092326377016316%positive,0);(396012496184325162852645600430%positive,0);(4952256170616648444%positive,0);(4715651504114%positive,1);(346494894612978508605687115772%positive,0);(84378999460475949615869898%positive,1);(396012496184393719601652084732%positive,0);(386108994759576604376298614730%positive,1);(346494894612909951856680631470%positive,0);(84378999460476056319078140%positive,0);(84378999391923705350500092%positive,0);(79236098723189567434%positive,1);(360171215575880700%positive,0);(23013889477222040125386%positive,1);(1267777575279823879342%positive,0);(84593480130104611864621052%positive,0);(84378999391923598647291850%positive,1);(96682738326250903611682812%positive,0);(386108994759576604483001822972%positive,0);(386108994759508052025330036682%positive,1);(96682738326251034507411402%positive,1);(386108994759508052132033244924%positive,0);(346494894612978508498858082250%positive,1);(396012496184393719494823051210%positive,1);(346494894612978504207649209518%positive,0);(84593480130104742760349642%positive,1)]]
  end.

Lemma cqh_h_00043 : iqh tmq_h_00043.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00043 StB 4 4 2 29 20000
                lsetq_h_00043 rsetq_h_00043 certq_h_00043 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00043); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00044 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StA)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00044 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00044 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StA,S1);(StC,S1)]);(S0,[(StD,S0);(StD,S0)])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[(StA,S1);(StC,S1)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition certq_h_00044 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 48 [(314652163455309742%positive,4);(321826127863444411%positive,1);(356852788752799647%positive,4);(5445141436191%positive,4);(321826127863075771%positive,3);(75791334364922%positive,2);(21837325471307514%positive,2);(1212666493260527%positive,4);(356852788753168287%positive,4);(4709410501563%positive,1);(314652164210284282%positive,4);(21837325471306479%positive,4);(75791334363887%positive,4);(321809154152691615%positive,4);(1212665738286842%positive,2);(19665759941678842%positive,4);(1172076690%positive,4);(1212666493261562%positive,2);(349397211929368314%positive,2);(349397212684343034%positive,2);(314652164210283247%positive,4);(4709410132923%positive,3);(321809154152322975%positive,4);(1212665738285807%positive,4);(19665759941677807%positive,4);(314652163455309562%positive,4);(75791334365102%positive,0);(21837325471307694%positive,0);(349397211929367279%positive,4);(349397212684341999%positive,4);(4910418007839%positive,4);(314652164210284462%positive,4);(314652163455308527%positive,4);(349397211929368494%positive,0);(1212665738287022%positive,0);(19665759941679022%positive,4);(349397212684343214%positive,0);(1212666493261742%positive,0);(300075682094%positive,4)] [314652163455309742%positive;321826127863444411%positive;356852788752799647%positive;5445141436191%positive;321826127863075771%positive;75791334364922%positive;21837325471307514%positive;1212666493260527%positive;4709410501563%positive;314652164210284282%positive;21837325471306479%positive;75791334363887%positive;321809154152691615%positive;1212665738286842%positive;19665759941678842%positive;1172076690%positive;1212666493261562%positive;349397211929368314%positive;349397212684343034%positive;314652164210283247%positive;4709410132923%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;314652163455309562%positive;75791334365102%positive;21837325471307694%positive;349397211929367279%positive;349397212684341999%positive;4910418007839%positive;314652164210284462%positive;1212666493261742%positive;314652163455308527%positive;349397211929368494%positive;1212665738287022%positive;19665759941679022%positive;349397212684343214%positive;356852788753168287%positive;300075682094%positive]]
  | StC => [HMeas MRight 48 [(78566688125433%positive,1);(321826127863444411%positive,1);(356852788752799647%positive,1);(321809154152690169%positive,1);(5445141436191%positive,1);(321826127863075771%positive,0);(321809154152321529%positive,1);(1212666493260527%positive,1);(356852788753168287%positive,1);(4709410501563%positive,1);(21837325471306479%positive,1);(75791334363887%positive,1);(21270083729%positive,1);(321809154152691615%positive,1);(314652164210283247%positive,1);(4709410132923%positive,0);(87122262979065%positive,1);(321809154152322975%positive,1);(1212665738285807%positive,1);(19665759941677807%positive,1);(349397211929367279%positive,1);(349397212684341999%positive,1);(356852788753166841%positive,1);(4910418007839%positive,1);(314652163455308527%positive,1);(356852788752798201%positive,1)] [78566688125433%positive;321826127863444411%positive;356852788752799647%positive;321809154152690169%positive;5445141436191%positive;321826127863075771%positive;321809154152321529%positive;1212666493260527%positive;4709410501563%positive;21837325471306479%positive;75791334363887%positive;21270083729%positive;321809154152691615%positive;314652164210283247%positive;4709410132923%positive;87122262979065%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;349397211929367279%positive;349397212684341999%positive;356852788753166841%positive;4910418007839%positive;314652163455308527%positive;356852788752798201%positive;356852788753168287%positive]]
  | StD => [HMeas MLeft 48 [(314652163455309742%positive,2);(78566688125433%positive,1);(321809154152690169%positive,1);(75791334364922%positive,2);(21837325471307514%positive,2);(321809154152321529%positive,1);(314652164210284282%positive,0);(21270083729%positive,1);(1212665738286842%positive,2);(19665759941678842%positive,0);(1172076690%positive,0);(1212666493261562%positive,2);(349397211929368314%positive,2);(349397212684343034%positive,2);(87122262979065%positive,1);(314652163455309562%positive,0);(75791334365102%positive,2);(21837325471307694%positive,2);(356852788753166841%positive,1);(314652164210284462%positive,2);(349397211929368494%positive,2);(1212665738287022%positive,2);(19665759941679022%positive,2);(356852788752798201%positive,1);(349397212684343214%positive,2);(1212666493261742%positive,2);(300075682094%positive,2)] [314652163455309742%positive;78566688125433%positive;321809154152690169%positive;75791334364922%positive;21837325471307514%positive;321809154152321529%positive;314652164210284282%positive;21270083729%positive;1212665738286842%positive;19665759941678842%positive;1172076690%positive;1212666493261562%positive;349397211929368314%positive;349397212684343034%positive;87122262979065%positive;21837325471307694%positive;314652163455309562%positive;75791334365102%positive;356852788753166841%positive;314652164210284462%positive;349397211929368494%positive;1212665738287022%positive;19665759941679022%positive;356852788752798201%positive;349397212684343214%positive;1212666493261742%positive;300075682094%positive]]
  end.

Lemma cqh_h_00044 : iqh tmq_h_00044.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00044 StA 9 2 2 34 20000
                lsetq_h_00044 rsetq_h_00044 certq_h_00044 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00044); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00045 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DR StD)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00045 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StA,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0);(StA,S0)])];
   [(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StC,S1);(StC,S0);(StA,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StD,S1);(StD,S0)])]].

Definition rsetq_h_00045 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S0)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)])]].

Definition certq_h_00045 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MRight 58 [(396012496184393715203614178478%positive,1);(1546923813219792081571217354%positive,0);(396012419675369752386680113919%positive,1);(1266181105199251%positive,1);(396012496184325162852645600430%positive,1);(5273687345685328695905007%positive,1);(94264891298707663689612463%positive,1);(79136332654739%positive,1);(1353495682081451413618229194%positive,0);(4715651504114%positive,0);(84378999460475949615869898%positive,0);(368222231635545673744330%positive,0);(386108994759576604376298614730%positive,0);(360171228669448383%positive,1);(346494894612909951856680631470%positive,1);(84378999460480454357351599%positive,1);(96682719647289974116043519%positive,1);(23013883861397245525183%positive,1);(79236098723189567434%positive,0);(386108900541678326506860301039%positive,1);(386108994759576608881040096431%positive,1);(19315309674854191%positive,1);(23013889477222040125386%positive,0);(5273687277132977727326959%positive,1);(84593461451143682368981759%positive,1);(84378999391923598647291850%positive,0);(1438367741337354370239%positive,1);(1267777575279823879342%positive,1);(346494818103954541390715144959%positive,1);(386108900541609774155891722991%positive,1);(1546923514356417078742207231%positive,1);(92203831187426197451%positive,0);(386108994759508052025330036682%positive,0);(96682738326251034507411402%positive,0);(346494894612978508498858082250%positive,0);(396012496184393719494823051210%positive,0);(1353495383218076410789219071%positive,1);(1475261298998818947019%positive,0);(346494894612978504207649209518%positive,1);(22510701791840575%positive,1);(84593480130104742760349642%positive,0)] [396012496184393715203614178478%positive;1546923813219792081571217354%positive;396012419675369752386680113919%positive;1266181105199251%positive;396012496184325162852645600430%positive;5273687345685328695905007%positive;94264891298707663689612463%positive;79136332654739%positive;1353495682081451413618229194%positive;4715651504114%positive;84378999460475949615869898%positive;368222231635545673744330%positive;386108994759576604376298614730%positive;360171228669448383%positive;346494894612909951856680631470%positive;84378999460480454357351599%positive;96682719647289974116043519%positive;23013883861397245525183%positive;79236098723189567434%positive;386108900541678326506860301039%positive;386108994759576608881040096431%positive;19315309674854191%positive;23013889477222040125386%positive;5273687277132977727326959%positive;84593461451143682368981759%positive;84378999391923598647291850%positive;1438367741337354370239%positive;1267777575279823879342%positive;346494818103954541390715144959%positive;386108900541609774155891722991%positive;1546923514356417078742207231%positive;92203831187426197451%positive;386108994759508052025330036682%positive;96682738326251034507411402%positive;346494894612978508498858082250%positive;396012496184393719494823051210%positive;1353495383218076410789219071%positive;1475261298998818947019%positive;346494894612978504207649209518%positive;22510701791840575%positive;84593480130104742760349642%positive]]
  | StB => []
  | StC => [HRank [(396012419675369752386680113919%positive,0);(360171228669448383%positive,0);(23013889477221604117500%positive,1);(22510701791840575%positive,0);(1438368092326377016316%positive,1);(23013883861397245525183%positive,0);(1353495682081451282722500604%positive,1);(94264891298707663689612463%positive,0);(1475261298998818947019%positive,1);(1266181105199251%positive,2);(5273687345685328695905007%positive,0);(92203831187426197451%positive,1);(79136332654739%positive,2);(5273687277132977727326959%positive,0);(4952256170616648444%positive,1);(84378999460480454357351599%positive,0);(96682719647289974116043519%positive,0);(386108900541678326506860301039%positive,0);(386108900541609774155891722991%positive,0);(346494894612978508605687115772%positive,1);(386108994759576608881040096431%positive,0);(346494818103954541390715144959%positive,0);(84378999460476056319078140%positive,1);(19315309674854191%positive,0);(84593461451143682368981759%positive,0);(1438367741337354370239%positive,0);(1546923514356417078742207231%positive,0);(360171215575880700%positive,3);(396012496184393719601652084732%positive,1);(96682738326250903611682812%positive,1);(386108994759576604483001822972%positive,1);(1353495383218076410789219071%positive,0);(84378999391923705350500092%positive,1);(84593480130104611864621052%positive,1);(5762739449214077948%positive,3);(386108994759508052132033244924%positive,1);(1546923813219791950675488764%positive,1)]]
  | StD => [HRank [(396012496184393715203614178478%positive,0);(23013889477221604117500%positive,0);(1546923813219792081571217354%positive,1);(1438368092326377016316%positive,0);(1353495682081451282722500604%positive,0);(396012496184325162852645600430%positive,0);(1353495682081451413618229194%positive,1);(4952256170616648444%positive,0);(4715651504114%positive,1);(346494894612978508605687115772%positive,0);(84378999460475949615869898%positive,1);(5762739449214077948%positive,0);(368222231635545673744330%positive,1);(396012496184393719601652084732%positive,0);(386108994759576604376298614730%positive,1);(346494894612909951856680631470%positive,0);(84378999460476056319078140%positive,0);(84378999391923705350500092%positive,0);(79236098723189567434%positive,1);(360171215575880700%positive,0);(23013889477222040125386%positive,1);(84593480130104611864621052%positive,0);(84378999391923598647291850%positive,1);(1267777575279823879342%positive,0);(96682738326250903611682812%positive,0);(386108994759576604483001822972%positive,0);(1546923813219791950675488764%positive,0);(386108994759508052025330036682%positive,1);(96682738326251034507411402%positive,1);(386108994759508052132033244924%positive,0);(346494894612978508498858082250%positive,1);(396012496184393719494823051210%positive,1);(346494894612978504207649209518%positive,0);(84593480130104742760349642%positive,1)]]
  end.

Lemma cqh_h_00045 : iqh tmq_h_00045.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00045 StB 4 4 2 29 20000
                lsetq_h_00045 rsetq_h_00045 certq_h_00045 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00045); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00046 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DR StD)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00046 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StC,S1);(StC,S0);(StA,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StD,S1);(StD,S0)])]].

Definition rsetq_h_00046 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S0)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)])]].

Definition certq_h_00046 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MRight 45 [(396012496184393715203614178478%positive,1);(396012419675369752386680113919%positive,1);(396012496184325162852645600430%positive,1);(5273687345685328695905007%positive,1);(94264891298707663689612463%positive,1);(79136332654739%positive,1);(4715651504114%positive,0);(84378999460475949615869898%positive,0);(386108994759576604376298614730%positive,0);(346494894612909951856680631470%positive,1);(84378999460480454357351599%positive,1);(96682719647289974116043519%positive,1);(79236098723189567434%positive,0);(386108900541678326506860301039%positive,1);(386108994759576608881040096431%positive,1);(23013889477222040125386%positive,0);(19315309674854191%positive,1);(1438367741337354370239%positive,1);(84593461451143682368981759%positive,1);(84378999391923598647291850%positive,0);(92203831187426197451%positive,0);(1267777575279823879342%positive,1);(5273687277132977727326959%positive,1);(346494818103954541390715144959%positive,1);(386108900541609774155891722991%positive,1);(386108994759508052025330036682%positive,0);(96682738326251034507411402%positive,0);(346494894612978508498858082250%positive,0);(396012496184393719494823051210%positive,0);(346494894612978504207649209518%positive,1);(22510701791840575%positive,1);(84593480130104742760349642%positive,0)] [396012496184393715203614178478%positive;396012419675369752386680113919%positive;5273687345685328695905007%positive;396012496184325162852645600430%positive;94264891298707663689612463%positive;79136332654739%positive;4715651504114%positive;84378999460475949615869898%positive;386108994759576604376298614730%positive;346494894612909951856680631470%positive;84378999460480454357351599%positive;96682719647289974116043519%positive;79236098723189567434%positive;386108900541678326506860301039%positive;386108994759576608881040096431%positive;23013889477222040125386%positive;19315309674854191%positive;1438367741337354370239%positive;84593461451143682368981759%positive;84378999391923598647291850%positive;92203831187426197451%positive;1267777575279823879342%positive;5273687277132977727326959%positive;346494818103954541390715144959%positive;386108900541609774155891722991%positive;386108994759508052025330036682%positive;96682738326251034507411402%positive;346494894612978508498858082250%positive;396012496184393719494823051210%positive;346494894612978504207649209518%positive;22510701791840575%positive;84593480130104742760349642%positive]]
  | StB => []
  | StC => [HRank [(396012419675369752386680113919%positive,0);(22510701791840575%positive,0);(1438368092326377016316%positive,1);(5273687345685328695905007%positive,0);(94264891298707663689612463%positive,0);(92203831187426197451%positive,1);(79136332654739%positive,2);(5273687277132977727326959%positive,0);(4952256170616648444%positive,1);(84378999460480454357351599%positive,0);(96682719647289974116043519%positive,0);(386108900541678326506860301039%positive,0);(386108900541609774155891722991%positive,0);(346494894612978508605687115772%positive,1);(386108994759576608881040096431%positive,0);(346494818103954541390715144959%positive,0);(84378999460476056319078140%positive,1);(19315309674854191%positive,0);(1438367741337354370239%positive,0);(84593461451143682368981759%positive,0);(360171215575880700%positive,3);(396012496184393719601652084732%positive,1);(96682738326250903611682812%positive,1);(386108994759576604483001822972%positive,1);(84378999391923705350500092%positive,1);(84593480130104611864621052%positive,1);(386108994759508052132033244924%positive,1)]]
  | StD => [HRank [(396012496184393715203614178478%positive,0);(1438368092326377016316%positive,0);(396012496184325162852645600430%positive,0);(4952256170616648444%positive,0);(4715651504114%positive,1);(346494894612978508605687115772%positive,0);(84378999460475949615869898%positive,1);(396012496184393719601652084732%positive,0);(386108994759576604376298614730%positive,1);(346494894612909951856680631470%positive,0);(84378999460476056319078140%positive,0);(84378999391923705350500092%positive,0);(79236098723189567434%positive,1);(360171215575880700%positive,0);(23013889477222040125386%positive,1);(84593480130104611864621052%positive,0);(84378999391923598647291850%positive,1);(1267777575279823879342%positive,0);(96682738326250903611682812%positive,0);(386108994759576604483001822972%positive,0);(386108994759508052025330036682%positive,1);(96682738326251034507411402%positive,1);(386108994759508052132033244924%positive,0);(346494894612978508498858082250%positive,1);(396012496184393719494823051210%positive,1);(346494894612978504207649209518%positive,0);(84593480130104742760349642%positive,1)]]
  end.

Lemma cqh_h_00046 : iqh tmq_h_00046.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00046 StB 4 4 2 29 20000
                lsetq_h_00046 rsetq_h_00046 certq_h_00046 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00046); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00047 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00047 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00047 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition certq_h_00047 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 50 [(321812664966698746%positive,2);(321812664211722991%positive,4);(321812664966697711%positive,4);(314652163455309742%positive,4);(20113291238954926%positive,0);(356852788752799647%positive,4);(5445141436191%positive,4);(75791334364922%positive,2);(321812664211724206%positive,0);(1212660372566971%positive,1);(321812664966698926%positive,0);(1212666493260527%positive,4);(4709410501563%positive,1);(314652164210284282%positive,4);(75791334363887%positive,4);(321809154152691615%positive,4);(1212665738286842%positive,2);(19665759941678842%positive,4);(1212660372198331%positive,3);(1172076690%positive,4);(1212666493261562%positive,2);(314652164210283247%positive,4);(4709410132923%positive,3);(321809154152322975%positive,4);(1212665738285807%positive,4);(19665759941677807%positive,4);(314652163455309562%positive,4);(321812658846004155%positive,1);(75791334365102%positive,0);(4910418007839%positive,4);(20113291238954746%positive,2);(314652164210284462%positive,4);(1212666493261742%positive,0);(314652163455308527%positive,4);(20113291238953711%positive,4);(1212665738287022%positive,0);(19665759941679022%positive,4);(321812658845635515%positive,3);(356852788753168287%positive,4);(321812664211724026%positive,2);(300075682094%positive,4)] [321812664966698746%positive;321812664211722991%positive;314652163455309742%positive;321812664966697711%positive;20113291238954926%positive;356852788752799647%positive;5445141436191%positive;75791334364922%positive;321812664211724206%positive;1212660372566971%positive;321812664966698926%positive;1212666493260527%positive;4709410501563%positive;356852788753168287%positive;314652164210284282%positive;75791334363887%positive;321809154152691615%positive;1212665738286842%positive;19665759941678842%positive;1212660372198331%positive;1172076690%positive;1212666493261562%positive;314652164210283247%positive;4709410132923%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;314652163455309562%positive;321812658846004155%positive;75791334365102%positive;4910418007839%positive;20113291238954746%positive;314652164210284462%positive;314652163455308527%positive;20113291238953711%positive;1212665738287022%positive;19665759941679022%positive;321812658845635515%positive;1212666493261742%positive;321812664211724026%positive;300075682094%positive]]
  | StC => [HMeas MRight 50 [(321812664211722991%positive,1);(321812664966697711%positive,1);(78566688125433%positive,1);(356852788752799647%positive,1);(321809154152690169%positive,1);(5445141436191%positive,1);(1212660372566971%positive,1);(321809154152321529%positive,1);(1212666493260527%positive,1);(4709410501563%positive,1);(75791334363887%positive,1);(21270083729%positive,1);(321809154152691615%positive,1);(1212660372198331%positive,0);(314652164210283247%positive,1);(87122262979065%positive,1);(4709410132923%positive,0);(321809154152322975%positive,1);(1212665738285807%positive,1);(19665759941677807%positive,1);(321812658846004155%positive,1);(356852788753166841%positive,1);(4910418007839%positive,1);(314652163455308527%positive,1);(20113291238953711%positive,1);(321812658845635515%positive,0);(356852788752798201%positive,1);(356852788753168287%positive,1)] [321812664211722991%positive;321812664966697711%positive;78566688125433%positive;356852788752799647%positive;321809154152690169%positive;5445141436191%positive;1212660372566971%positive;321809154152321529%positive;1212666493260527%positive;4709410501563%positive;75791334363887%positive;21270083729%positive;321809154152691615%positive;1212660372198331%positive;314652164210283247%positive;87122262979065%positive;4709410132923%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;321812658846004155%positive;356852788753166841%positive;4910418007839%positive;314652163455308527%positive;20113291238953711%positive;356852788752798201%positive;321812658845635515%positive;356852788753168287%positive]]
  | StD => [HMeas MLeft 50 [(321812664966698746%positive,2);(314652163455309742%positive,2);(20113291238954926%positive,2);(78566688125433%positive,1);(321809154152690169%positive,1);(75791334364922%positive,2);(321812664211724206%positive,2);(321812664966698926%positive,2);(321809154152321529%positive,1);(314652164210284282%positive,0);(21270083729%positive,1);(1212665738286842%positive,2);(19665759941678842%positive,0);(1172076690%positive,0);(1212666493261562%positive,2);(87122262979065%positive,1);(314652163455309562%positive,0);(75791334365102%positive,2);(356852788753166841%positive,1);(20113291238954746%positive,2);(314652164210284462%positive,2);(1212666493261742%positive,2);(1212665738287022%positive,2);(19665759941679022%positive,2);(356852788752798201%positive,1);(321812664211724026%positive,2);(300075682094%positive,2)] [321812664966698746%positive;314652163455309742%positive;78566688125433%positive;20113291238954926%positive;321809154152690169%positive;75791334364922%positive;321812664211724206%positive;321812664966698926%positive;321809154152321529%positive;314652164210284282%positive;21270083729%positive;1212665738286842%positive;19665759941678842%positive;1172076690%positive;1212666493261562%positive;87122262979065%positive;314652163455309562%positive;75791334365102%positive;356852788753166841%positive;20113291238954746%positive;314652164210284462%positive;1212665738287022%positive;19665759941679022%positive;356852788752798201%positive;1212666493261742%positive;321812664211724026%positive;300075682094%positive]]
  end.

Lemma cqh_h_00047 : iqh tmq_h_00047.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00047 StA 9 2 2 34 20000
                lsetq_h_00047 rsetq_h_00047 certq_h_00047 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00047); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00048 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StB)
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DR StD)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00048 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StA,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StC,S1);(StC,S0);(StA,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StD,S1);(StD,S0)])]].

Definition rsetq_h_00048 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S0)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)])]].

Definition certq_h_00048 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MRight 52 [(396012496184393715203614178478%positive,1);(396012419675369752386680113919%positive,1);(1266181105199251%positive,1);(396012496184325162852645600430%positive,1);(5273687345685328695905007%positive,1);(94264891298707663689612463%positive,1);(79136332654739%positive,1);(1353495682081451413618229194%positive,1);(4715651504114%positive,0);(84378999460475949615869898%positive,0);(368222231635545673744330%positive,0);(386108994759576604376298614730%positive,0);(360171228669448383%positive,1);(346494894612909951856680631470%positive,1);(84378999460480454357351599%positive,1);(96682719647289974116043519%positive,1);(79236098723189567434%positive,0);(386108900541678326506860301039%positive,1);(386108994759576608881040096431%positive,1);(19315309674854191%positive,1);(23013889477222040125386%positive,0);(5273687277132977727326959%positive,1);(84593461451143682368981759%positive,1);(84378999391923598647291850%positive,0);(1438367741337354370239%positive,1);(1267777575279823879342%positive,1);(92203831187426197451%positive,0);(346494818103954541390715144959%positive,1);(386108900541609774155891722991%positive,1);(386108994759508052025330036682%positive,0);(96682738326251034507411402%positive,0);(346494894612978508498858082250%positive,0);(396012496184393719494823051210%positive,0);(1475261298998818947019%positive,0);(346494894612978504207649209518%positive,1);(22510701791840575%positive,1);(84593480130104742760349642%positive,0)] [396012496184393715203614178478%positive;396012419675369752386680113919%positive;1266181105199251%positive;5273687345685328695905007%positive;396012496184325162852645600430%positive;94264891298707663689612463%positive;79136332654739%positive;1353495682081451413618229194%positive;4715651504114%positive;84378999460475949615869898%positive;368222231635545673744330%positive;386108994759576604376298614730%positive;360171228669448383%positive;346494894612909951856680631470%positive;84378999460480454357351599%positive;96682719647289974116043519%positive;79236098723189567434%positive;386108900541678326506860301039%positive;386108994759576608881040096431%positive;19315309674854191%positive;23013889477222040125386%positive;5273687277132977727326959%positive;84593461451143682368981759%positive;84378999391923598647291850%positive;1438367741337354370239%positive;1267777575279823879342%positive;92203831187426197451%positive;346494818103954541390715144959%positive;386108900541609774155891722991%positive;386108994759508052025330036682%positive;96682738326251034507411402%positive;346494894612978508498858082250%positive;396012496184393719494823051210%positive;1475261298998818947019%positive;346494894612978504207649209518%positive;22510701791840575%positive;84593480130104742760349642%positive]]
  | StB => []
  | StC => [HRank [(396012419675369752386680113919%positive,0);(360171228669448383%positive,0);(23013889477221604117500%positive,1);(22510701791840575%positive,0);(1438368092326377016316%positive,1);(94264891298707663689612463%positive,0);(1475261298998818947019%positive,1);(1266181105199251%positive,2);(5273687345685328695905007%positive,0);(92203831187426197451%positive,1);(79136332654739%positive,2);(5273687277132977727326959%positive,0);(4952256170616648444%positive,1);(84378999460480454357351599%positive,0);(96682719647289974116043519%positive,0);(386108900541678326506860301039%positive,0);(386108900541609774155891722991%positive,0);(346494894612978508605687115772%positive,1);(386108994759576608881040096431%positive,0);(346494818103954541390715144959%positive,0);(84378999460476056319078140%positive,1);(19315309674854191%positive,0);(84593461451143682368981759%positive,0);(1438367741337354370239%positive,0);(360171215575880700%positive,3);(396012496184393719601652084732%positive,1);(96682738326250903611682812%positive,1);(386108994759576604483001822972%positive,1);(84378999391923705350500092%positive,1);(84593480130104611864621052%positive,1);(5762739449214077948%positive,3);(386108994759508052132033244924%positive,1)]]
  | StD => [HRank [(396012496184393715203614178478%positive,0);(23013889477221604117500%positive,0);(1438368092326377016316%positive,0);(396012496184325162852645600430%positive,0);(1353495682081451413618229194%positive,1);(4952256170616648444%positive,0);(4715651504114%positive,1);(346494894612978508605687115772%positive,0);(84378999460475949615869898%positive,1);(5762739449214077948%positive,0);(368222231635545673744330%positive,1);(396012496184393719601652084732%positive,0);(386108994759576604376298614730%positive,1);(346494894612909951856680631470%positive,0);(84378999460476056319078140%positive,0);(84378999391923705350500092%positive,0);(79236098723189567434%positive,1);(360171215575880700%positive,0);(23013889477222040125386%positive,1);(84593480130104611864621052%positive,0);(84378999391923598647291850%positive,1);(1267777575279823879342%positive,0);(96682738326250903611682812%positive,0);(386108994759576604483001822972%positive,0);(386108994759508052025330036682%positive,1);(96682738326251034507411402%positive,1);(386108994759508052132033244924%positive,0);(346494894612978508498858082250%positive,1);(396012496184393719494823051210%positive,1);(346494894612978504207649209518%positive,0);(84593480130104742760349642%positive,1)]]
  end.

Lemma cqh_h_00048 : iqh tmq_h_00048.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00048 StB 6 4 2 31 20000
                lsetq_h_00048 rsetq_h_00048 certq_h_00048 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 31) 2000 tmq_h_00048); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00049 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StA)
  | StC, S1 => Some (mkTrans S0 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StD)
  | StD, S1 => Some (mkTrans S1 DR StB)
  end.

Definition lsetq_h_00049 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)])]].

Definition rsetq_h_00049 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)])]].

Definition certq_h_00049 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(5121400252161856676293087%positive,0);(19315842251812639%positive,0);(336666231129655607476438428159%positive,0);(91865338864502422595960479%positive,0);(92221282669268254699%positive,1);(22514964547406143%positive,0);(396087353015353860671596390911%positive,0);(376280314747900420265453545951%positive,0);(376280314747971008911956765151%positive,0);(396087430838708343138374033406%positive,1);(1401753406032447798975%positive,0);(81942401319767723897912991%positive,0);(376280427989074121697149714079%positive,0);(82193904084370949397801471%positive,0);(81942401249170281318489598%positive,1);(1401753827888430836734%positive,1);(82193923084213352343707646%positive,1);(81942401319758927821708798%positive,1);(79152975685779%positive,2);(96701013919746499494275583%positive,0);(376280427989003524254570290686%positive,1);(376280427989074112901073509886%positive,1);(5121400181573210173073887%positive,0);(4934250293338501630%positive,1);(336666308953010089943216070654%positive,1);(96701032919588902440181758%positive,1);(360239385426826238%positive,3)]]
  | StC => [HMeas MRight 45 [(336666308953010081147139915421%positive,1);(82193923084213487265775593%positive,0);(5121400252161856676293087%positive,1);(19315842251812639%positive,1);(4715781263345%positive,0);(376280427989074112856781348841%positive,0);(1263168066298580172445%positive,1);(336666231129655607476438428159%positive,1);(396087430838637745695794658973%positive,1);(22428061246214901252073%positive,0);(92221282669268254699%positive,0);(22514964547406143%positive,1);(396087353015353860671596390911%positive,1);(336666308953010089898672259049%positive,0);(1401753406032447798975%positive,1);(81942401319767723897912991%positive,1);(376280427989074121697149714079%positive,1);(376280314747900420265453545951%positive,1);(96701032919589037362249705%positive,0);(376280314747971008911956765151%positive,1);(78948004690632056809%positive,0);(79152975685779%positive,1);(81942401249170237026328553%positive,0);(396087430838708343093830221801%positive,0);(396087430838708334342297878173%positive,1);(91865338864502422595960479%positive,1);(82193904084370949397801471%positive,1);(81942401319758883529547753%positive,0);(336666308952939492500636696221%positive,1);(376280427989003524210278129641%positive,0);(5121400181573210173073887%positive,1);(96701013919746499494275583%positive,1)] [336666308953010081147139915421%positive;82193923084213487265775593%positive;5121400252161856676293087%positive;19315842251812639%positive;4715781263345%positive;376280427989074112856781348841%positive;1263168066298580172445%positive;336666231129655607476438428159%positive;396087430838637745695794658973%positive;22428061246214901252073%positive;92221282669268254699%positive;22514964547406143%positive;396087353015353860671596390911%positive;336666308953010089898672259049%positive;1401753406032447798975%positive;81942401319767723897912991%positive;376280427989074121697149714079%positive;376280314747900420265453545951%positive;96701032919589037362249705%positive;376280314747971008911956765151%positive;78948004690632056809%positive;79152975685779%positive;5121400181573210173073887%positive;81942401249170237026328553%positive;396087430838708343093830221801%positive;396087430838708334342297878173%positive;91865338864502422595960479%positive;82193904084370949397801471%positive;81942401319758883529547753%positive;336666308952939492500636696221%positive;376280427989003524210278129641%positive;96701013919746499494275583%positive]]
  | StD => [HRank [(336666308953010081147139915421%positive,0);(1401753827888430836734%positive,0);(82193923084213487265775593%positive,1);(4934250293338501630%positive,0);(4715781263345%positive,1);(396087430838708343138374033406%positive,0);(376280427989074112856781348841%positive,1);(1263168066298580172445%positive,0);(396087430838637745695794658973%positive,0);(360239385426826238%positive,0);(22428061246214901252073%positive,1);(376280427989003524254570290686%positive,0);(376280427989074112901073509886%positive,0);(336666308953010089898672259049%positive,1);(81942401249170281318489598%positive,0);(96701032919589037362249705%positive,1);(82193923084213352343707646%positive,0);(81942401319758927821708798%positive,0);(78948004690632056809%positive,1);(81942401249170237026328553%positive,1);(396087430838708343093830221801%positive,1);(396087430838708334342297878173%positive,0);(336666308953010089943216070654%positive,0);(81942401319758883529547753%positive,1);(336666308952939492500636696221%positive,0);(96701032919588902440181758%positive,0);(376280427989003524210278129641%positive,1)]]
  end.

Lemma cqh_h_00049 : iqh tmq_h_00049.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00049 StA 3 4 2 28 20000
                lsetq_h_00049 rsetq_h_00049 certq_h_00049 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00049); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00050 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DR StD)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00050 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StC,S1);(StC,S0);(StA,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StD,S1);(StD,S0)])]].

Definition rsetq_h_00050 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S0)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)])]].

Definition certq_h_00050 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MRight 45 [(396012496184393715203614178478%positive,1);(396012419675369752386680113919%positive,1);(396012496184325162852645600430%positive,1);(5273687345685328695905007%positive,1);(94264891298707663689612463%positive,1);(79136332654739%positive,1);(4715651504114%positive,0);(84378999460475949615869898%positive,0);(386108994759576604376298614730%positive,0);(346494894612909951856680631470%positive,1);(84378999460480454357351599%positive,1);(96682719647289974116043519%positive,1);(79236098723189567434%positive,0);(386108900541678326506860301039%positive,1);(386108994759576608881040096431%positive,1);(23013889477222040125386%positive,0);(19315309674854191%positive,1);(1438367741337354370239%positive,1);(92203831187426197451%positive,0);(84378999391923598647291850%positive,0);(5273687277132977727326959%positive,1);(1267777575279823879342%positive,1);(84593461451143682368981759%positive,1);(346494818103954541390715144959%positive,1);(386108900541609774155891722991%positive,1);(386108994759508052025330036682%positive,0);(96682738326251034507411402%positive,0);(346494894612978508498858082250%positive,0);(396012496184393719494823051210%positive,0);(346494894612978504207649209518%positive,1);(22510701791840575%positive,1);(84593480130104742760349642%positive,0)] [396012496184393715203614178478%positive;396012419675369752386680113919%positive;5273687345685328695905007%positive;396012496184325162852645600430%positive;94264891298707663689612463%positive;79136332654739%positive;4715651504114%positive;84378999460475949615869898%positive;386108994759576604376298614730%positive;346494894612909951856680631470%positive;84378999460480454357351599%positive;96682719647289974116043519%positive;79236098723189567434%positive;386108900541678326506860301039%positive;386108994759576608881040096431%positive;23013889477222040125386%positive;19315309674854191%positive;1438367741337354370239%positive;92203831187426197451%positive;84378999391923598647291850%positive;5273687277132977727326959%positive;1267777575279823879342%positive;84593461451143682368981759%positive;346494818103954541390715144959%positive;386108900541609774155891722991%positive;386108994759508052025330036682%positive;96682738326251034507411402%positive;346494894612978508498858082250%positive;396012496184393719494823051210%positive;346494894612978504207649209518%positive;22510701791840575%positive;84593480130104742760349642%positive]]
  | StB => []
  | StC => [HRank [(396012419675369752386680113919%positive,0);(22510701791840575%positive,0);(1438368092326377016316%positive,1);(5273687345685328695905007%positive,0);(94264891298707663689612463%positive,0);(92203831187426197451%positive,1);(79136332654739%positive,2);(5273687277132977727326959%positive,0);(4952256170616648444%positive,1);(84378999460480454357351599%positive,0);(96682719647289974116043519%positive,0);(386108900541678326506860301039%positive,0);(386108900541609774155891722991%positive,0);(346494894612978508605687115772%positive,1);(386108994759576608881040096431%positive,0);(346494818103954541390715144959%positive,0);(84378999460476056319078140%positive,1);(19315309674854191%positive,0);(1438367741337354370239%positive,0);(84593461451143682368981759%positive,0);(360171215575880700%positive,3);(396012496184393719601652084732%positive,1);(96682738326250903611682812%positive,1);(386108994759576604483001822972%positive,1);(84378999391923705350500092%positive,1);(84593480130104611864621052%positive,1);(386108994759508052132033244924%positive,1)]]
  | StD => [HRank [(396012496184393715203614178478%positive,0);(1438368092326377016316%positive,0);(396012496184325162852645600430%positive,0);(4952256170616648444%positive,0);(4715651504114%positive,1);(346494894612978508605687115772%positive,0);(84378999460475949615869898%positive,1);(396012496184393719601652084732%positive,0);(386108994759576604376298614730%positive,1);(346494894612909951856680631470%positive,0);(84378999460476056319078140%positive,0);(84378999391923705350500092%positive,0);(79236098723189567434%positive,1);(360171215575880700%positive,0);(23013889477222040125386%positive,1);(84593480130104611864621052%positive,0);(84378999391923598647291850%positive,1);(1267777575279823879342%positive,0);(96682738326250903611682812%positive,0);(386108994759576604483001822972%positive,0);(386108994759508052025330036682%positive,1);(96682738326251034507411402%positive,1);(386108994759508052132033244924%positive,0);(346494894612978508498858082250%positive,1);(396012496184393719494823051210%positive,1);(346494894612978504207649209518%positive,0);(84593480130104742760349642%positive,1)]]
  end.

Lemma cqh_h_00050 : iqh tmq_h_00050.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00050 StB 1 4 2 26 20000
                lsetq_h_00050 rsetq_h_00050 certq_h_00050 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00050); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00051 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DL StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StA)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S0 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00051 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition rsetq_h_00051 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition certq_h_00051 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 37 [(357411547841885946%positive,4);(351078360865895151%positive,4);(1396138856798126%positive,0);(306064359855454111%positive,4);(4670218605499%positive,1);(306064355677927327%positive,4);(76724903465711%positive,4);(357411547841884911%positive,4);(1150007538%positive,4);(351078360865896366%positive,4);(76724903466926%positive,0);(19641575789098746%positive,4);(4722827818783%positive,4);(294402117422%positive,4);(4722566723359%positive,4);(357411547841886126%positive,4);(19641575789097711%positive,4);(19641575789098926%positive,4);(1371399845172986%positive,2);(306067452231907231%positive,4);(306067448054380447%positive,4);(1396138856797946%positive,2);(1371399845171951%positive,4);(4670171419579%positive,3);(351078360865896186%positive,4);(1396138856796911%positive,4);(1371399845173166%positive,0);(76724903466746%positive,2)] [357411547841885946%positive;351078360865895151%positive;1396138856798126%positive;306064359855454111%positive;4670218605499%positive;306064355677927327%positive;76724903465711%positive;357411547841884911%positive;1150007538%positive;351078360865896366%positive;76724903466926%positive;19641575789098746%positive;4722827818783%positive;294402117422%positive;4722566723359%positive;357411547841886126%positive;19641575789097711%positive;19641575789098926%positive;1371399845172986%positive;306067452231907231%positive;306067448054380447%positive;1396138856797946%positive;1371399845171951%positive;4670171419579%positive;351078360865896186%positive;1396138856796911%positive;1371399845173166%positive;76724903466746%positive]]
  | StC => [HMeas MLeft 37 [(351078360865895151%positive,1);(306064359855454111%positive,1);(4670218605499%positive,1);(306064355677927327%positive,1);(76724903465711%positive,1);(357411547841884911%positive,1);(4722827818783%positive,1);(4722566723359%positive,1);(306067448054379001%positive,1);(18419783537%positive,1);(19641575789097711%positive,1);(306067452231905785%positive,1);(306067452231907231%positive,1);(306067448054380447%positive,1);(75561067573753%positive,1);(75565245100537%positive,1);(1371399845171951%positive,1);(4670171419579%positive,0);(306064355677925881%positive,1);(1396138856796911%positive,1);(306064359855452665%positive,1)] [351078360865895151%positive;306064359855454111%positive;4670218605499%positive;306064355677927327%positive;76724903465711%positive;357411547841884911%positive;4722827818783%positive;4722566723359%positive;306067448054379001%positive;18419783537%positive;19641575789097711%positive;306067452231905785%positive;306067452231907231%positive;306067448054380447%positive;75561067573753%positive;75565245100537%positive;1371399845171951%positive;4670171419579%positive;306064355677925881%positive;1396138856796911%positive;306064359855452665%positive]]
  | StD => [HMeas MRight 37 [(357411547841885946%positive,0);(1396138856798126%positive,2);(1150007538%positive,0);(351078360865896366%positive,2);(76724903466926%positive,2);(19641575789098746%positive,0);(294402117422%positive,2);(357411547841886126%positive,2);(306067448054379001%positive,1);(18419783537%positive,1);(306067452231905785%positive,1);(19641575789098926%positive,2);(1371399845172986%positive,2);(75561067573753%positive,1);(75565245100537%positive,1);(1396138856797946%positive,2);(306064355677925881%positive,1);(351078360865896186%positive,0);(306064359855452665%positive,1);(1371399845173166%positive,2);(76724903466746%positive,2)] [357411547841885946%positive;1396138856798126%positive;1150007538%positive;351078360865896366%positive;76724903466926%positive;19641575789098746%positive;294402117422%positive;357411547841886126%positive;306067448054379001%positive;18419783537%positive;306067452231905785%positive;19641575789098926%positive;1371399845172986%positive;75561067573753%positive;75565245100537%positive;1396138856797946%positive;306064355677925881%positive;351078360865896186%positive;306064359855452665%positive;1371399845173166%positive;76724903466746%positive]]
  end.

Lemma cqh_h_00051 : iqh tmq_h_00051.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00051 StA 9 2 2 34 20000
                lsetq_h_00051 rsetq_h_00051 certq_h_00051 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00051); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00052 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DR StC)
  | StB, S0 => Some (mkTrans S1 DL StA)
  | StB, S1 => Some (mkTrans S1 DR StB)
  | StC, S0 => Some (mkTrans S1 DL StC)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StA)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Definition lsetq_h_00052 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S0)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S1)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StC,S1)])];
   [(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StC,S1);(StD,S0)])]].

Definition rsetq_h_00052 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StA,S1);(StC,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StA,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StD,S0);(StA,S1);(StC,S1)]);(S1,[(StD,S1);(StD,S0);(StA,S1);(StC,S1)])];
   [(S1,[(StD,S1);(StD,S0);(StA,S1);(StC,S1)]);(S1,[(StC,S1);(StD,S0);(StA,S1);(StC,S1)])]].

Definition certq_h_00052 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 45 [(5862815335784392754121726%positive,1);(84442354066891636254965451%positive,0);(384223047998938764755581979630%positive,1);(384223009330005543572479405771%positive,0);(1267779954490352004270%positive,1);(384223047999010822450276986046%positive,1);(384225465845966308130520755391%positive,1);(93804455077865825276259518%positive,1);(384225465846020351326049201343%positive,1);(384223009329951500376950959819%positive,0);(1431351400337891388607%positive,1);(384225427107875810900140359371%positive,0);(84377818871234652240276670%positive,1);(84377818799176957545597934%positive,1);(75366793836114%positive,1);(79235121253575503562%positive,0);(345875920996223098907365133310%positive,1);(21840551653378366%positive,1);(5332198733971%positive,0);(19311491422840110%positive,1);(93805035914991066596769483%positive,0);(5277647720278178357758974%positive,1);(384223047998992807951110425582%positive,1);(89458890568913338059%positive,0);(345875920996151041450491440319%positive,1);(84377818853220153074043886%positive,1);(84450886406496251624550091%positive,0);(345875920996205084646019886271%positive,1);(345875882258060544220111044299%positive,0);(384225465846038365587394448382%positive,1);(20286373094587704323787%positive,0);(84450886352453056096104139%positive,0)] [5862815335784392754121726%positive;84442354066891636254965451%positive;384223009330005543572479405771%positive;384223047998938764755581979630%positive;1267779954490352004270%positive;384225465845966308130520755391%positive;384223047999010822450276986046%positive;93804455077865825276259518%positive;384225465846020351326049201343%positive;384223009329951500376950959819%positive;1431351400337891388607%positive;384225427107875810900140359371%positive;84377818871234652240276670%positive;84377818799176957545597934%positive;75366793836114%positive;79235121253575503562%positive;345875920996223098907365133310%positive;21840551653378366%positive;5332198733971%positive;19311491422840110%positive;93805035914991066596769483%positive;5277647720278178357758974%positive;384223047998992807951110425582%positive;89458890568913338059%positive;345875920996151041450491440319%positive;84377818853220153074043886%positive;84450886406496251624550091%positive;345875920996205084646019886271%positive;345875882258060544220111044299%positive;384225465846038365587394448382%positive;20286373094587704323787%positive;84450886352453056096104139%positive]]
  | StB => []
  | StC => [HRank [(384225465846038365690198802412%positive,0);(84377818799177092562206444%positive,0);(93805045372550284074860524%positive,0);(84442354066891636254965451%positive,1);(345875920996223099010169487340%positive,0);(384223009330005543572479405771%positive,1);(384225465845966308130520755391%positive,0);(384225465846020351326049201343%positive,0);(384223009329951500376950959819%positive,1);(1431351400337891388607%positive,0);(384223047998992808086127034092%positive,0);(384225427107875810900140359371%positive,1);(5591181223264908268%positive,0);(5332198733971%positive,1);(384223047998938764890598588140%positive,0);(93805035914991066596769483%positive,1);(84442363524450853733056492%positive,0);(89458890568913338059%positive,1);(345875920996151041450491440319%positive,0);(308983862529487596%positive,0);(1267779954593156745964%positive,0);(84450886406496251624550091%positive,1);(345875920996205084646019886271%positive,0);(84377818853220288090652396%positive,0);(345875882258060544220111044299%positive,1);(20286373094587704323787%positive,1);(84450886352453056096104139%positive,1)]]
  | StD => [HRank [(5862815335784392754121726%positive,0);(384223047998992807951110425582%positive,0);(384225465846038365690198802412%positive,1);(1267779954490352004270%positive,0);(84377818799177092562206444%positive,1);(384223047998938764755581979630%positive,0);(93805045372550284074860524%positive,1);(384223047999010822450276986046%positive,0);(93804455077865825276259518%positive,0);(84377818871234652240276670%positive,0);(84377818799176957545597934%positive,0);(79235121253575503562%positive,1);(75366793836114%positive,2);(345875920996223098907365133310%positive,0);(5277647720278178357758974%positive,0);(5591181223264908268%positive,1);(21840551653378366%positive,0);(19311491422840110%positive,0);(84377818853220153074043886%positive,0);(345875920996223099010169487340%positive,1);(84442363524450853733056492%positive,1);(384225465846038365587394448382%positive,0);(384223047998992808086127034092%positive,1);(308983862529487596%positive,3);(1267779954593156745964%positive,1);(384223047998938764890598588140%positive,1);(84377818853220288090652396%positive,1)]]
  end.

Lemma cqh_h_00052 : iqh tmq_h_00052.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00052 StB 4 4 2 29 20000
                lsetq_h_00052 rsetq_h_00052 certq_h_00052 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 29) 2000 tmq_h_00052); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00053 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DR StC)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StA)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00053 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00053 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition certq_h_00053 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 37 [(314652163455309742%positive,4);(356852788752799647%positive,4);(5445141436191%positive,4);(75791334364922%positive,2);(1212666493260527%positive,4);(4709410501563%positive,1);(356852788753168287%positive,4);(314652164210284282%positive,4);(75791334363887%positive,4);(321809154152691615%positive,4);(1212665738286842%positive,2);(19665759941678842%positive,4);(1172076690%positive,4);(1212666493261562%positive,2);(314652164210283247%positive,4);(4709410132923%positive,3);(321809154152322975%positive,4);(1212665738285807%positive,4);(19665759941677807%positive,4);(314652163455309562%positive,4);(75791334365102%positive,0);(4910418007839%positive,4);(314652164210284462%positive,4);(314652163455308527%positive,4);(1212665738287022%positive,0);(19665759941679022%positive,4);(1212666493261742%positive,0);(300075682094%positive,4)] [314652163455309742%positive;356852788752799647%positive;5445141436191%positive;75791334364922%positive;1212666493260527%positive;4709410501563%positive;314652164210284282%positive;75791334363887%positive;321809154152691615%positive;1212665738286842%positive;19665759941678842%positive;1172076690%positive;1212666493261562%positive;314652164210283247%positive;4709410132923%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;314652163455309562%positive;75791334365102%positive;4910418007839%positive;314652164210284462%positive;1212666493261742%positive;314652163455308527%positive;1212665738287022%positive;19665759941679022%positive;356852788753168287%positive;300075682094%positive]]
  | StC => [HMeas MRight 37 [(78566688125433%positive,1);(356852788752799647%positive,1);(321809154152690169%positive,1);(5445141436191%positive,1);(1212666493260527%positive,1);(321809154152321529%positive,1);(4709410501563%positive,1);(356852788753168287%positive,1);(75791334363887%positive,1);(21270083729%positive,1);(321809154152691615%positive,1);(314652164210283247%positive,1);(4709410132923%positive,0);(87122262979065%positive,1);(321809154152322975%positive,1);(1212665738285807%positive,1);(19665759941677807%positive,1);(356852788753166841%positive,1);(4910418007839%positive,1);(314652163455308527%positive,1);(356852788752798201%positive,1)] [78566688125433%positive;356852788752799647%positive;321809154152690169%positive;5445141436191%positive;1212666493260527%positive;321809154152321529%positive;4709410501563%positive;75791334363887%positive;21270083729%positive;321809154152691615%positive;314652164210283247%positive;4709410132923%positive;87122262979065%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;356852788753166841%positive;4910418007839%positive;314652163455308527%positive;356852788752798201%positive;356852788753168287%positive]]
  | StD => [HMeas MLeft 37 [(314652163455309742%positive,2);(78566688125433%positive,1);(321809154152690169%positive,1);(75791334364922%positive,2);(321809154152321529%positive,1);(314652164210284282%positive,0);(21270083729%positive,1);(1212665738286842%positive,2);(19665759941678842%positive,0);(1172076690%positive,0);(1212666493261562%positive,2);(87122262979065%positive,1);(314652163455309562%positive,0);(75791334365102%positive,2);(356852788753166841%positive,1);(314652164210284462%positive,2);(1212665738287022%positive,2);(19665759941679022%positive,2);(356852788752798201%positive,1);(1212666493261742%positive,2);(300075682094%positive,2)] [314652163455309742%positive;78566688125433%positive;321809154152690169%positive;75791334364922%positive;321809154152321529%positive;314652164210284282%positive;21270083729%positive;1212665738286842%positive;19665759941678842%positive;1172076690%positive;1212666493261562%positive;87122262979065%positive;314652163455309562%positive;75791334365102%positive;356852788753166841%positive;314652164210284462%positive;1212665738287022%positive;19665759941679022%positive;356852788752798201%positive;1212666493261742%positive;300075682094%positive]]
  end.

Lemma cqh_h_00053 : iqh tmq_h_00053.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00053 StA 9 2 2 34 20000
                lsetq_h_00053 rsetq_h_00053 certq_h_00053 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00053); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00054 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DR StC)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00054 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00054 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition certq_h_00054 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 37 [(314652163455309742%positive,4);(356852788752799647%positive,4);(5445141436191%positive,4);(75791334364922%positive,2);(1212666493260527%positive,4);(4709410501563%positive,1);(356852788753168287%positive,4);(314652164210284282%positive,4);(75791334363887%positive,4);(321809154152691615%positive,4);(1212665738286842%positive,2);(1172076690%positive,4);(19665759941678842%positive,4);(1212666493261562%positive,2);(314652164210283247%positive,4);(4709410132923%positive,3);(321809154152322975%positive,4);(1212665738285807%positive,4);(19665759941677807%positive,4);(314652163455309562%positive,4);(75791334365102%positive,0);(4910418007839%positive,4);(314652164210284462%positive,4);(314652163455308527%positive,4);(1212665738287022%positive,0);(19665759941679022%positive,4);(1212666493261742%positive,0);(300075682094%positive,4)] [314652163455309742%positive;356852788752799647%positive;5445141436191%positive;75791334364922%positive;1212666493260527%positive;4709410501563%positive;314652164210284282%positive;75791334363887%positive;321809154152691615%positive;1212665738286842%positive;1172076690%positive;19665759941678842%positive;1212666493261562%positive;314652164210283247%positive;4709410132923%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;314652163455309562%positive;75791334365102%positive;4910418007839%positive;314652164210284462%positive;1212666493261742%positive;314652163455308527%positive;1212665738287022%positive;19665759941679022%positive;356852788753168287%positive;300075682094%positive]]
  | StC => [HMeas MRight 37 [(78566688125433%positive,1);(356852788752799647%positive,1);(321809154152690169%positive,1);(5445141436191%positive,1);(1212666493260527%positive,1);(321809154152321529%positive,1);(4709410501563%positive,1);(356852788753168287%positive,1);(75791334363887%positive,1);(21270083729%positive,1);(321809154152691615%positive,1);(314652164210283247%positive,1);(87122262979065%positive,1);(4709410132923%positive,0);(321809154152322975%positive,1);(1212665738285807%positive,1);(19665759941677807%positive,1);(356852788753166841%positive,1);(4910418007839%positive,1);(314652163455308527%positive,1);(356852788752798201%positive,1)] [78566688125433%positive;356852788752799647%positive;321809154152690169%positive;5445141436191%positive;1212666493260527%positive;321809154152321529%positive;4709410501563%positive;75791334363887%positive;21270083729%positive;321809154152691615%positive;314652164210283247%positive;87122262979065%positive;4709410132923%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;356852788753166841%positive;4910418007839%positive;314652163455308527%positive;356852788752798201%positive;356852788753168287%positive]]
  | StD => [HMeas MLeft 37 [(314652163455309742%positive,2);(78566688125433%positive,1);(321809154152690169%positive,1);(75791334364922%positive,2);(321809154152321529%positive,1);(314652164210284282%positive,0);(21270083729%positive,1);(1212665738286842%positive,2);(1172076690%positive,0);(19665759941678842%positive,0);(1212666493261562%positive,2);(87122262979065%positive,1);(314652163455309562%positive,0);(75791334365102%positive,2);(356852788753166841%positive,1);(314652164210284462%positive,2);(1212665738287022%positive,2);(19665759941679022%positive,2);(356852788752798201%positive,1);(1212666493261742%positive,2);(300075682094%positive,2)] [314652163455309742%positive;78566688125433%positive;321809154152690169%positive;75791334364922%positive;321809154152321529%positive;314652164210284282%positive;21270083729%positive;1212665738286842%positive;1172076690%positive;19665759941678842%positive;1212666493261562%positive;87122262979065%positive;314652163455309562%positive;75791334365102%positive;356852788753166841%positive;314652164210284462%positive;1212665738287022%positive;19665759941679022%positive;356852788752798201%positive;1212666493261742%positive;300075682094%positive]]
  end.

Lemma cqh_h_00054 : iqh tmq_h_00054.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00054 StA 9 2 2 34 20000
                lsetq_h_00054 rsetq_h_00054 certq_h_00054 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00054); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00055 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DR StC)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00055 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StB,S1);(StB,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S0,[(StC,S0);(StC,S0)])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StB,S1);(StB,S0)])]].

Definition rsetq_h_00055 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StD,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S0,[(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S0)])]].

Definition certq_h_00055 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 43 [(5307768541866%positive,1);(347849918707528158%positive,2);(341516731731538602%positive,1);(323514226923467755%positive,2);(323514226923886270%positive,2);(19087146765119966%positive,2);(1263727430424254%positive,2);(323511134547014635%positive,2);(1263715350828734%positive,2);(323511134547433150%positive,2);(347849919563166378%positive,1);(347849918707528362%positive,1);(19087145909481950%positive,2);(341516731731538398%positive,2);(341516732587176414%positive,2);(323514226923885547%positive,0);(1263727430423531%positive,0);(323511134547432427%positive,0);(1263715350828011%positive,0);(18416111347%positive,2);(5211131777706%positive,1);(323514226923468478%positive,2);(347849919563166174%positive,2);(323511134547015358%positive,2);(75289427112939%positive,2);(4705589194558%positive,2);(341516732587176618%positive,1)] [5307768541866%positive;347849918707528158%positive;341516731731538602%positive;323514226923467755%positive;323514226923886270%positive;19087146765119966%positive;1263727430424254%positive;323511134547014635%positive;1263715350828734%positive;323511134547433150%positive;347849919563166378%positive;347849918707528362%positive;19087145909481950%positive;341516731731538398%positive;341516732587176414%positive;323514226923885547%positive;1263727430423531%positive;323511134547432427%positive;1263715350828011%positive;18416111347%positive;5211131777706%positive;323514226923468478%positive;347849919563166174%positive;323511134547015358%positive;75289427112939%positive;4705589194558%positive;341516732587176618%positive]]
  | StC => [HMeas MRight 43 [(341516732587177449%positive,1);(19087145909482985%positive,0);(323514226923467755%positive,1);(1149729265%positive,0);(347849919563167389%positive,2);(323511134547014635%positive,1);(294330785565%positive,2);(347849918707529373%positive,2);(341516731731539433%positive,0);(347849919563167209%positive,1);(323514226923885547%positive,2);(1263727430423531%positive,2);(19087145909483165%positive,2);(19087146765121181%positive,2);(323511134547432427%positive,2);(1263715350828011%positive,2);(18416111347%positive,1);(347849918707529193%positive,0);(19087146765121001%positive,1);(75289427112939%positive,1);(341516731731539613%positive,2);(341516732587177629%positive,2)] [341516732587177449%positive;19087145909482985%positive;323514226923467755%positive;1149729265%positive;347849918707529373%positive;347849919563167389%positive;323511134547014635%positive;294330785565%positive;341516731731539433%positive;347849919563167209%positive;323514226923885547%positive;1263727430423531%positive;19087145909483165%positive;19087146765121181%positive;323511134547432427%positive;1263715350828011%positive;18416111347%positive;347849918707529193%positive;19087146765121001%positive;75289427112939%positive;341516731731539613%positive;341516732587177629%positive]]
  | StD => [HMeas MLeft 43 [(5307768541866%positive,0);(341516732587177449%positive,1);(347849918707528158%positive,1);(19087145909482985%positive,1);(341516731731538602%positive,0);(323514226923886270%positive,1);(19087146765119966%positive,1);(1263727430424254%positive,1);(1149729265%positive,1);(347849919563167389%positive,1);(294330785565%positive,1);(347849918707529373%positive,1);(1263715350828734%positive,1);(323511134547433150%positive,1);(347849919563166378%positive,0);(341516731731539433%positive,1);(347849919563167209%positive,1);(347849918707528362%positive,0);(19087145909481950%positive,1);(341516731731538398%positive,1);(341516732587176414%positive,1);(19087145909483165%positive,1);(19087146765121181%positive,1);(347849918707529193%positive,1);(5211131777706%positive,0);(19087146765121001%positive,1);(323514226923468478%positive,1);(347849919563166174%positive,1);(323511134547015358%positive,1);(4705589194558%positive,1);(341516731731539613%positive,1);(341516732587177629%positive,1);(341516732587176618%positive,0)] [5307768541866%positive;341516732587177449%positive;347849918707528158%positive;19087145909482985%positive;341516731731538602%positive;323514226923886270%positive;19087146765119966%positive;1263727430424254%positive;1149729265%positive;347849919563167389%positive;294330785565%positive;347849918707529373%positive;1263715350828734%positive;323511134547433150%positive;347849919563166378%positive;341516731731539433%positive;347849919563167209%positive;347849918707528362%positive;19087145909481950%positive;341516731731538398%positive;341516732587176414%positive;19087145909483165%positive;19087146765121181%positive;347849918707529193%positive;5211131777706%positive;19087146765121001%positive;323514226923468478%positive;347849919563166174%positive;323511134547015358%positive;4705589194558%positive;341516731731539613%positive;341516732587177629%positive;341516732587176618%positive]]
  end.

Lemma cqh_h_00055 : iqh tmq_h_00055.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00055 StA 18 2 2 43 20000
                lsetq_h_00055 rsetq_h_00055 certq_h_00055 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 43) 2000 tmq_h_00055); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00056 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DR StC)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StA)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S0 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00056 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition rsetq_h_00056 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition certq_h_00056 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 50 [(357411547841885946%positive,4);(351078360865895151%positive,4);(1396138856798126%positive,0);(306064359855454111%positive,4);(19641576642696954%positive,2);(4670218605499%positive,1);(76724903465711%positive,4);(306064355677927327%positive,4);(351078361719493359%positive,4);(357411547841884911%positive,4);(357411548695484154%positive,2);(1150007538%positive,4);(351078360865896366%positive,4);(306067448054797243%positive,1);(19641576642695919%positive,4);(19641575789098746%positive,4);(76724903466926%positive,0);(4722827818783%positive,4);(294402117422%positive,4);(351078361719494574%positive,0);(357411548695483119%positive,4);(4722566723359%positive,4);(19641576642697134%positive,0);(357411547841886126%positive,4);(19641575789097711%positive,4);(357411548695484334%positive,0);(19641575789098926%positive,4);(1195563884073915%positive,3);(1371399845172986%positive,2);(306067452231907231%positive,4);(306067448054380447%positive,4);(306064355678344123%positive,3);(1396138856797946%positive,2);(1371399845171951%positive,4);(1195575963669435%positive,1);(4670171419579%positive,3);(1396138856796911%positive,4);(351078360865896186%positive,4);(1371399845173166%positive,0);(76724903466746%positive,2);(351078361719494394%positive,2)] [357411547841885946%positive;351078360865895151%positive;1396138856798126%positive;306064359855454111%positive;19641576642696954%positive;4670218605499%positive;76724903465711%positive;306064355677927327%positive;351078361719493359%positive;357411547841884911%positive;357411548695484154%positive;1150007538%positive;351078360865896366%positive;306067448054797243%positive;76724903466926%positive;19641576642695919%positive;19641575789098746%positive;4722827818783%positive;294402117422%positive;351078361719494574%positive;357411548695483119%positive;4722566723359%positive;19641576642697134%positive;357411547841886126%positive;19641575789097711%positive;357411548695484334%positive;19641575789098926%positive;1195563884073915%positive;1371399845172986%positive;306067452231907231%positive;306067448054380447%positive;306064355678344123%positive;1396138856797946%positive;1371399845171951%positive;1195575963669435%positive;4670171419579%positive;1396138856796911%positive;351078360865896186%positive;1371399845173166%positive;76724903466746%positive;351078361719494394%positive]]
  | StC => [HMeas MLeft 50 [(351078360865895151%positive,1);(306064359855454111%positive,1);(4670218605499%positive,1);(76724903465711%positive,1);(306064355677927327%positive,1);(351078361719493359%positive,1);(357411547841884911%positive,1);(306067448054797243%positive,1);(19641576642695919%positive,1);(4722827818783%positive,1);(357411548695483119%positive,1);(4722566723359%positive,1);(306067448054379001%positive,1);(18419783537%positive,1);(19641575789097711%positive,1);(306067452231905785%positive,1);(1195563884073915%positive,0);(306067452231907231%positive,1);(306067448054380447%positive,1);(75561067573753%positive,1);(306064355678344123%positive,0);(75565245100537%positive,1);(1371399845171951%positive,1);(1195575963669435%positive,1);(4670171419579%positive,0);(306064355677925881%positive,1);(1396138856796911%positive,1);(306064359855452665%positive,1)] [351078360865895151%positive;306064359855454111%positive;4670218605499%positive;306064355677927327%positive;76724903465711%positive;351078361719493359%positive;357411547841884911%positive;306067448054797243%positive;19641576642695919%positive;4722827818783%positive;4722566723359%positive;357411548695483119%positive;306067448054379001%positive;18419783537%positive;19641575789097711%positive;306067452231905785%positive;1195563884073915%positive;306067452231907231%positive;306067448054380447%positive;75561067573753%positive;306064355678344123%positive;75565245100537%positive;1371399845171951%positive;1195575963669435%positive;4670171419579%positive;306064355677925881%positive;1396138856796911%positive;306064359855452665%positive]]
  | StD => [HMeas MRight 50 [(357411547841885946%positive,0);(1396138856798126%positive,2);(19641576642696954%positive,2);(357411548695484154%positive,2);(1150007538%positive,0);(351078360865896366%positive,2);(19641575789098746%positive,0);(76724903466926%positive,2);(294402117422%positive,2);(351078361719494574%positive,2);(19641576642697134%positive,2);(306067448054379001%positive,1);(357411547841886126%positive,2);(18419783537%positive,1);(306067452231905785%positive,1);(357411548695484334%positive,2);(19641575789098926%positive,2);(1371399845172986%positive,2);(75561067573753%positive,1);(75565245100537%positive,1);(1396138856797946%positive,2);(306064355677925881%positive,1);(306064359855452665%positive,1);(351078360865896186%positive,0);(1371399845173166%positive,2);(76724903466746%positive,2);(351078361719494394%positive,2)] [357411547841885946%positive;1396138856798126%positive;19641576642696954%positive;357411548695484154%positive;1150007538%positive;351078360865896366%positive;76724903466926%positive;19641575789098746%positive;294402117422%positive;351078361719494574%positive;357411547841886126%positive;19641576642697134%positive;306067448054379001%positive;18419783537%positive;306067452231905785%positive;357411548695484334%positive;19641575789098926%positive;1371399845172986%positive;75561067573753%positive;75565245100537%positive;1396138856797946%positive;306064355677925881%positive;351078360865896186%positive;306064359855452665%positive;1371399845173166%positive;76724903466746%positive;351078361719494394%positive]]
  end.

Lemma cqh_h_00056 : iqh tmq_h_00056.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00056 StA 9 2 2 34 20000
                lsetq_h_00056 rsetq_h_00056 certq_h_00056 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00056); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00057 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DR StC)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StA)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S0 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00057 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition rsetq_h_00057 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition certq_h_00057 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 50 [(357411547841885946%positive,4);(351078360865895151%positive,4);(1396138856798126%positive,0);(306064359855454111%positive,4);(19641576642696954%positive,2);(4670218605499%positive,1);(76724903465711%positive,4);(306064355677927327%positive,4);(351078361719493359%positive,4);(357411547841884911%positive,4);(357411548695484154%positive,2);(1150007538%positive,4);(351078360865896366%positive,4);(306067448054797243%positive,1);(19641576642695919%positive,4);(76724903466926%positive,0);(19641575789098746%positive,4);(4722827818783%positive,4);(294402117422%positive,4);(351078361719494574%positive,0);(357411548695483119%positive,4);(4722566723359%positive,4);(19641576642697134%positive,0);(357411547841886126%positive,4);(19641575789097711%positive,4);(357411548695484334%positive,0);(19641575789098926%positive,4);(1195563884073915%positive,3);(1371399845172986%positive,2);(306067452231907231%positive,4);(306067448054380447%positive,4);(306064355678344123%positive,3);(1396138856797946%positive,2);(1371399845171951%positive,4);(1195575963669435%positive,1);(4670171419579%positive,3);(351078360865896186%positive,4);(1396138856796911%positive,4);(1371399845173166%positive,0);(76724903466746%positive,2);(351078361719494394%positive,2)] [357411547841885946%positive;351078360865895151%positive;1396138856798126%positive;306064359855454111%positive;19641576642696954%positive;4670218605499%positive;76724903465711%positive;306064355677927327%positive;351078361719493359%positive;357411547841884911%positive;357411548695484154%positive;1150007538%positive;351078360865896366%positive;306067448054797243%positive;76724903466926%positive;19641576642695919%positive;19641575789098746%positive;4722827818783%positive;294402117422%positive;351078361719494574%positive;357411548695483119%positive;4722566723359%positive;19641576642697134%positive;357411547841886126%positive;19641575789097711%positive;357411548695484334%positive;19641575789098926%positive;1195563884073915%positive;1371399845172986%positive;306067452231907231%positive;306067448054380447%positive;306064355678344123%positive;1396138856797946%positive;1371399845171951%positive;1195575963669435%positive;4670171419579%positive;351078360865896186%positive;1396138856796911%positive;1371399845173166%positive;76724903466746%positive;351078361719494394%positive]]
  | StC => [HMeas MLeft 50 [(351078360865895151%positive,1);(306064359855454111%positive,1);(4670218605499%positive,1);(76724903465711%positive,1);(306064355677927327%positive,1);(351078361719493359%positive,1);(357411547841884911%positive,1);(306067448054797243%positive,1);(19641576642695919%positive,1);(4722827818783%positive,1);(357411548695483119%positive,1);(4722566723359%positive,1);(306067448054379001%positive,1);(18419783537%positive,1);(19641575789097711%positive,1);(306067452231905785%positive,1);(1195563884073915%positive,0);(306067452231907231%positive,1);(306067448054380447%positive,1);(75561067573753%positive,1);(306064355678344123%positive,0);(75565245100537%positive,1);(1371399845171951%positive,1);(1195575963669435%positive,1);(4670171419579%positive,0);(306064355677925881%positive,1);(306064359855452665%positive,1);(1396138856796911%positive,1)] [351078360865895151%positive;306064359855454111%positive;4670218605499%positive;306064355677927327%positive;76724903465711%positive;351078361719493359%positive;357411547841884911%positive;306067448054797243%positive;19641576642695919%positive;4722827818783%positive;4722566723359%positive;357411548695483119%positive;306067448054379001%positive;18419783537%positive;19641575789097711%positive;306067452231905785%positive;1195563884073915%positive;306067452231907231%positive;306067448054380447%positive;75561067573753%positive;306064355678344123%positive;75565245100537%positive;1371399845171951%positive;1195575963669435%positive;4670171419579%positive;306064355677925881%positive;1396138856796911%positive;306064359855452665%positive]]
  | StD => [HMeas MRight 50 [(357411547841885946%positive,0);(1396138856798126%positive,2);(19641576642696954%positive,2);(357411548695484154%positive,2);(1150007538%positive,0);(351078360865896366%positive,2);(76724903466926%positive,2);(19641575789098746%positive,0);(294402117422%positive,2);(351078361719494574%positive,2);(19641576642697134%positive,2);(306067448054379001%positive,1);(357411547841886126%positive,2);(18419783537%positive,1);(306067452231905785%positive,1);(357411548695484334%positive,2);(19641575789098926%positive,2);(1371399845172986%positive,2);(75561067573753%positive,1);(75565245100537%positive,1);(1396138856797946%positive,2);(306064355677925881%positive,1);(351078360865896186%positive,0);(306064359855452665%positive,1);(1371399845173166%positive,2);(76724903466746%positive,2);(351078361719494394%positive,2)] [357411547841885946%positive;1396138856798126%positive;19641576642696954%positive;357411548695484154%positive;1150007538%positive;351078360865896366%positive;76724903466926%positive;19641575789098746%positive;294402117422%positive;351078361719494574%positive;357411547841886126%positive;19641576642697134%positive;306067448054379001%positive;18419783537%positive;306067452231905785%positive;357411548695484334%positive;19641575789098926%positive;1371399845172986%positive;75561067573753%positive;75565245100537%positive;1396138856797946%positive;306064355677925881%positive;351078360865896186%positive;306064359855452665%positive;1371399845173166%positive;76724903466746%positive;351078361719494394%positive]]
  end.

Lemma cqh_h_00057 : iqh tmq_h_00057.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00057 StA 9 2 2 34 20000
                lsetq_h_00057 rsetq_h_00057 certq_h_00057 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00057); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00058 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StA)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StA)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Definition lsetq_h_00058 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S0)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)])]].

Definition rsetq_h_00058 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StC,S1);(StC,S0);(StA,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00058 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 45 [(19316163274073407%positive,1);(394090319349755802079393676463%positive,1);(394087842842082104443097247690%positive,0);(6013304161112283374144239%positive,1);(1272374747580052274367%positive,1);(394087901502728258668090346223%positive,1);(86815745180823489839876863%positive,1);(394090319349683744311826959103%positive,1);(86887705929455169969520586%positive,0);(1468091836209017584814%positive,1);(394090260619862299778210791370%positive,0);(394090260619952371770758201290%positive,0);(86887705839383177422110666%positive,0);(5438245361358461812067055%positive,1);(356400848002061808775800015599%positive,1);(79524547625781510091%positive,0);(86815745090751497292466943%positive,1);(20364754864040819605450%positive,0);(5469067016338%positive,0);(96213456872480992784743599%positive,1);(96212852256349718947491786%positive,0);(394087901502656201211074051246%positive,1);(394087901502746273203621461166%positive,1);(87011911460288573954256842%positive,0);(75385043287635%positive,1);(91756289037841149898%positive,0);(86815745162809264858987695%positive,1);(22401441091782959%positive,1);(394090319349773816304374369023%positive,1);(356400848002079823311331130542%positive,1);(356400789341415654550806917066%positive,0);(356400848001989751318783720622%positive,1)] [19316163274073407%positive;394090319349755802079393676463%positive;394087842842082104443097247690%positive;6013304161112283374144239%positive;1272374747580052274367%positive;394087901502728258668090346223%positive;86815745180823489839876863%positive;394090319349683744311826959103%positive;86887705929455169969520586%positive;1468091836209017584814%positive;394090260619862299778210791370%positive;394090260619952371770758201290%positive;86887705839383177422110666%positive;5438245361358461812067055%positive;356400848002061808775800015599%positive;79524547625781510091%positive;86815745090751497292466943%positive;20364754864040819605450%positive;5469067016338%positive;96213456872480992784743599%positive;96212852256349718947491786%positive;394087901502656201211074051246%positive;394087901502746273203621461166%positive;87011911460288573954256842%positive;75385043287635%positive;91756289037841149898%positive;86815745162809264858987695%positive;22401441091782959%positive;394090319349773816304374369023%positive;356400848002079823311331130542%positive;356400789341415654550806917066%positive;356400848001989751318783720622%positive]]
  | StB => []
  | StC => [HRank [(19316163274073407%positive,0);(86815745162809264858987695%positive,0);(79524547625781510091%positive,1);(75385043287635%positive,2);(309058612282881020%positive,3);(394090319349755802079393676463%positive,0);(394087901502728258668090346223%positive,0);(356400848002061808775800015599%positive,0);(394090319349683744450995859452%positive,1);(6013304161112283374144239%positive,0);(5438245361358461812067055%positive,0);(5734768919496454908%positive,1);(394090319349773816304374369023%positive,0);(394087901502728258839471501052%positive,1);(1272374747580052274367%positive,0);(86815745180823489839876863%positive,0);(394090319349683744311826959103%positive,0);(86815745090751497292466943%positive,0);(87011925781735388992548604%positive,1);(1272374747751433882620%positive,1);(356400848002061808947181170428%positive,1);(394090319349773816443543269372%positive,1);(96213456872480992784743599%positive,0);(96212866577796533985783548%positive,1);(86815745090751636461367292%positive,1);(86815745180823629008777212%positive,1);(22401441091782959%positive,0)]]
  | StD => [HRank [(309058612282881020%positive,0);(394090319349683744450995859452%positive,0);(394090319349773816443543269372%positive,0);(394087842842082104443097247690%positive,1);(5734768919496454908%positive,0);(394087901502728258839471501052%positive,0);(87011925781735388992548604%positive,0);(1272374747751433882620%positive,0);(86887705929455169969520586%positive,1);(1468091836209017584814%positive,0);(356400848002061808947181170428%positive,0);(394090260619862299778210791370%positive,1);(394090260619952371770758201290%positive,1);(86887705839383177422110666%positive,1);(20364754864040819605450%positive,1);(5469067016338%positive,1);(96212852256349718947491786%positive,1);(96212866577796533985783548%positive,0);(86815745090751636461367292%positive,0);(394087901502656201211074051246%positive,0);(394087901502746273203621461166%positive,0);(86815745180823629008777212%positive,0);(87011911460288573954256842%positive,1);(91756289037841149898%positive,1);(356400848002079823311331130542%positive,0);(356400789341415654550806917066%positive,1);(356400848001989751318783720622%positive,0)]]
  end.

Lemma cqh_h_00058 : iqh tmq_h_00058.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00058 StB 3 4 2 28 20000
                lsetq_h_00058 rsetq_h_00058 certq_h_00058 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00058); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00059 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StA)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Definition lsetq_h_00059 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S0)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StC,S0);(StA,S1);(StD,S1);(StD,S1)]);(S1,[(StC,S0);(StA,S1);(StD,S1);(StC,S1)])]].

Definition rsetq_h_00059 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StC,S1);(StC,S0);(StA,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StC,S0);(StA,S1);(StD,S1)]);(S1,[(StD,S0);(StA,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00059 (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 45 [(19316163274073407%positive,1);(394090319349755802079393676463%positive,1);(394087842842082104443097247690%positive,0);(6013304161112283374144239%positive,1);(1272374747580052274367%positive,1);(394087901502728258668090346223%positive,1);(86815745180823489839876863%positive,1);(394090319349683744311826959103%positive,1);(86887705929455169969520586%positive,0);(1468091836209017584814%positive,1);(394090260619862299778210791370%positive,0);(394090260619952371770758201290%positive,0);(86887705839383177422110666%positive,0);(5438245361358461812067055%positive,1);(356400848002061808775800015599%positive,1);(79524547625781510091%positive,0);(86815745090751497292466943%positive,1);(20364754864040819605450%positive,0);(5469067016338%positive,0);(96213456872480992784743599%positive,1);(96212852256349718947491786%positive,0);(394087901502656201211074051246%positive,1);(394087901502746273203621461166%positive,1);(87011911460288573954256842%positive,0);(75385043287635%positive,1);(91756289037841149898%positive,0);(86815745162809264858987695%positive,1);(22401441091782959%positive,1);(394090319349773816304374369023%positive,1);(356400848002079823311331130542%positive,1);(356400789341415654550806917066%positive,0);(356400848001989751318783720622%positive,1)] [19316163274073407%positive;394090319349755802079393676463%positive;394087842842082104443097247690%positive;6013304161112283374144239%positive;1272374747580052274367%positive;394087901502728258668090346223%positive;86815745180823489839876863%positive;394090319349683744311826959103%positive;86887705929455169969520586%positive;1468091836209017584814%positive;394090260619862299778210791370%positive;394090260619952371770758201290%positive;86887705839383177422110666%positive;5438245361358461812067055%positive;356400848002061808775800015599%positive;79524547625781510091%positive;86815745090751497292466943%positive;20364754864040819605450%positive;5469067016338%positive;96213456872480992784743599%positive;96212852256349718947491786%positive;394087901502656201211074051246%positive;394087901502746273203621461166%positive;87011911460288573954256842%positive;75385043287635%positive;91756289037841149898%positive;86815745162809264858987695%positive;22401441091782959%positive;394090319349773816304374369023%positive;356400848002079823311331130542%positive;356400789341415654550806917066%positive;356400848001989751318783720622%positive]]
  | StB => []
  | StC => [HRank [(19316163274073407%positive,0);(86815745162809264858987695%positive,0);(79524547625781510091%positive,1);(75385043287635%positive,2);(309058612282881020%positive,3);(394090319349755802079393676463%positive,0);(394087901502728258668090346223%positive,0);(356400848002061808775800015599%positive,0);(394090319349683744450995859452%positive,1);(6013304161112283374144239%positive,0);(5438245361358461812067055%positive,0);(5734768919496454908%positive,1);(394090319349773816304374369023%positive,0);(394087901502728258839471501052%positive,1);(1272374747580052274367%positive,0);(86815745180823489839876863%positive,0);(394090319349683744311826959103%positive,0);(86815745090751497292466943%positive,0);(87011925781735388992548604%positive,1);(1272374747751433882620%positive,1);(356400848002061808947181170428%positive,1);(394090319349773816443543269372%positive,1);(96213456872480992784743599%positive,0);(96212866577796533985783548%positive,1);(86815745090751636461367292%positive,1);(86815745180823629008777212%positive,1);(22401441091782959%positive,0)]]
  | StD => [HRank [(309058612282881020%positive,0);(394090319349683744450995859452%positive,0);(394090319349773816443543269372%positive,0);(394087842842082104443097247690%positive,1);(5734768919496454908%positive,0);(394087901502728258839471501052%positive,0);(87011925781735388992548604%positive,0);(1272374747751433882620%positive,0);(86887705929455169969520586%positive,1);(1468091836209017584814%positive,0);(356400848002061808947181170428%positive,0);(394090260619862299778210791370%positive,1);(394090260619952371770758201290%positive,1);(86887705839383177422110666%positive,1);(20364754864040819605450%positive,1);(5469067016338%positive,1);(96212852256349718947491786%positive,1);(96212866577796533985783548%positive,0);(86815745090751636461367292%positive,0);(394087901502656201211074051246%positive,0);(394087901502746273203621461166%positive,0);(86815745180823629008777212%positive,0);(87011911460288573954256842%positive,1);(91756289037841149898%positive,1);(356400848002079823311331130542%positive,0);(356400789341415654550806917066%positive,1);(356400848001989751318783720622%positive,0)]]
  end.

Lemma cqh_h_00059 : iqh tmq_h_00059.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00059 StB 1 4 2 26 20000
                lsetq_h_00059 rsetq_h_00059 certq_h_00059 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00059); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00060 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DR StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StA)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00060 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00060 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition certq_h_00060 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 37 [(314652163455309742%positive,4);(356852788752799647%positive,4);(5445141436191%positive,4);(75791334364922%positive,2);(1212666493260527%positive,4);(356852788753168287%positive,4);(4709410501563%positive,1);(314652164210284282%positive,4);(75791334363887%positive,4);(321809154152691615%positive,4);(1212665738286842%positive,2);(19665759941678842%positive,4);(1172076690%positive,4);(1212666493261562%positive,2);(314652164210283247%positive,4);(4709410132923%positive,3);(321809154152322975%positive,4);(1212665738285807%positive,4);(19665759941677807%positive,4);(314652163455309562%positive,4);(75791334365102%positive,0);(4910418007839%positive,4);(314652164210284462%positive,4);(314652163455308527%positive,4);(1212665738287022%positive,0);(19665759941679022%positive,4);(1212666493261742%positive,0);(300075682094%positive,4)] [314652163455309742%positive;356852788752799647%positive;5445141436191%positive;75791334364922%positive;1212666493260527%positive;4709410501563%positive;314652164210284282%positive;75791334363887%positive;321809154152691615%positive;1212665738286842%positive;19665759941678842%positive;1172076690%positive;1212666493261562%positive;314652164210283247%positive;4709410132923%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;314652163455309562%positive;75791334365102%positive;4910418007839%positive;314652164210284462%positive;1212666493261742%positive;314652163455308527%positive;1212665738287022%positive;19665759941679022%positive;356852788753168287%positive;300075682094%positive]]
  | StC => [HMeas MRight 37 [(78566688125433%positive,1);(356852788752799647%positive,1);(321809154152690169%positive,1);(5445141436191%positive,1);(321809154152321529%positive,1);(1212666493260527%positive,1);(356852788753168287%positive,1);(4709410501563%positive,1);(75791334363887%positive,1);(21270083729%positive,1);(321809154152691615%positive,1);(314652164210283247%positive,1);(4709410132923%positive,0);(87122262979065%positive,1);(321809154152322975%positive,1);(1212665738285807%positive,1);(19665759941677807%positive,1);(356852788753166841%positive,1);(4910418007839%positive,1);(314652163455308527%positive,1);(356852788752798201%positive,1)] [78566688125433%positive;356852788752799647%positive;321809154152690169%positive;5445141436191%positive;321809154152321529%positive;1212666493260527%positive;4709410501563%positive;75791334363887%positive;21270083729%positive;321809154152691615%positive;314652164210283247%positive;4709410132923%positive;87122262979065%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;356852788753166841%positive;4910418007839%positive;314652163455308527%positive;356852788752798201%positive;356852788753168287%positive]]
  | StD => [HMeas MLeft 37 [(314652163455309742%positive,2);(78566688125433%positive,1);(321809154152690169%positive,1);(75791334364922%positive,2);(321809154152321529%positive,1);(314652164210284282%positive,0);(21270083729%positive,1);(1212665738286842%positive,2);(19665759941678842%positive,0);(1172076690%positive,0);(1212666493261562%positive,2);(87122262979065%positive,1);(314652163455309562%positive,0);(75791334365102%positive,2);(356852788753166841%positive,1);(314652164210284462%positive,2);(1212665738287022%positive,2);(19665759941679022%positive,2);(356852788752798201%positive,1);(1212666493261742%positive,2);(300075682094%positive,2)] [314652163455309742%positive;78566688125433%positive;321809154152690169%positive;75791334364922%positive;321809154152321529%positive;314652164210284282%positive;21270083729%positive;1212665738286842%positive;19665759941678842%positive;1172076690%positive;1212666493261562%positive;87122262979065%positive;314652163455309562%positive;75791334365102%positive;356852788753166841%positive;314652164210284462%positive;1212665738287022%positive;19665759941679022%positive;356852788752798201%positive;1212666493261742%positive;300075682094%positive]]
  end.

Lemma cqh_h_00060 : iqh tmq_h_00060.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00060 StA 9 2 2 34 20000
                lsetq_h_00060 rsetq_h_00060 certq_h_00060 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00060); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00061 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DR StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StA)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S0 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00061 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StA,S1);(StC,S1)]);(S0,[(StD,S0);(StD,S0)])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[(StA,S1);(StC,S1)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition rsetq_h_00061 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition certq_h_00061 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 48 [(357411547841885946%positive,4);(351078365007827695%positive,4);(351078360865895151%positive,4);(1396138856798126%positive,0);(357411551983818490%positive,2);(4670218605499%positive,1);(306064359855454111%positive,4);(76724903465711%positive,4);(19641579931030255%positive,4);(306064355677927327%positive,4);(357411551983817455%positive,4);(357411547841884911%positive,4);(1150007538%positive,4);(351078365007828910%positive,0);(351078360865896366%positive,4);(76724903466926%positive,0);(19641575789098746%positive,4);(306064355679949755%positive,3);(19641579931031290%positive,2);(4722827818783%positive,4);(294402117422%positive,4);(4722566723359%positive,4);(357411547841886126%positive,4);(19641575789097711%positive,4);(357411551983818670%positive,0);(19641575789098926%positive,4);(1371399845172986%positive,2);(19641579931031470%positive,0);(306067452231907231%positive,4);(306067448054380447%positive,4);(1396138856797946%positive,2);(1371399845171951%positive,4);(4670171419579%positive,3);(306067448056402875%positive,1);(351078360865896186%positive,4);(1396138856796911%positive,4);(1371399845173166%positive,0);(351078365007828730%positive,2);(76724903466746%positive,2)] [357411547841885946%positive;351078365007827695%positive;351078360865895151%positive;1396138856798126%positive;357411551983818490%positive;4670218605499%positive;306064359855454111%positive;76724903465711%positive;19641579931030255%positive;306064355677927327%positive;357411551983817455%positive;357411547841884911%positive;1150007538%positive;351078360865896366%positive;351078365007828910%positive;76724903466926%positive;19641575789098746%positive;306064355679949755%positive;19641579931031290%positive;4722827818783%positive;294402117422%positive;4722566723359%positive;357411547841886126%positive;19641575789097711%positive;357411551983818670%positive;19641575789098926%positive;1371399845172986%positive;19641579931031470%positive;306067452231907231%positive;306067448054380447%positive;1396138856797946%positive;1371399845171951%positive;4670171419579%positive;306067448056402875%positive;351078360865896186%positive;1396138856796911%positive;1371399845173166%positive;351078365007828730%positive;76724903466746%positive]]
  | StC => [HMeas MLeft 48 [(351078365007827695%positive,1);(351078360865895151%positive,1);(4670218605499%positive,1);(306064359855454111%positive,1);(76724903465711%positive,1);(19641579931030255%positive,1);(306064355677927327%positive,1);(357411551983817455%positive,1);(357411547841884911%positive,1);(306064355679949755%positive,0);(4722827818783%positive,1);(4722566723359%positive,1);(306067448054379001%positive,1);(18419783537%positive,1);(19641575789097711%positive,1);(306067452231905785%positive,1);(306067452231907231%positive,1);(306067448054380447%positive,1);(75561067573753%positive,1);(75565245100537%positive,1);(1371399845171951%positive,1);(4670171419579%positive,0);(306067448056402875%positive,1);(306064355677925881%positive,1);(1396138856796911%positive,1);(306064359855452665%positive,1)] [351078365007827695%positive;351078360865895151%positive;306064359855454111%positive;4670218605499%positive;306064355677927327%positive;76724903465711%positive;19641579931030255%positive;357411551983817455%positive;357411547841884911%positive;306064355679949755%positive;4722827818783%positive;4722566723359%positive;306067448054379001%positive;18419783537%positive;19641575789097711%positive;306067452231905785%positive;306067452231907231%positive;306067448054380447%positive;75561067573753%positive;75565245100537%positive;1371399845171951%positive;4670171419579%positive;306067448056402875%positive;306064355677925881%positive;1396138856796911%positive;306064359855452665%positive]]
  | StD => [HMeas MRight 48 [(357411547841885946%positive,0);(1396138856798126%positive,2);(357411551983818490%positive,2);(1150007538%positive,0);(351078365007828910%positive,2);(351078360865896366%positive,2);(76724903466926%positive,2);(19641575789098746%positive,0);(19641579931031290%positive,2);(294402117422%positive,2);(357411547841886126%positive,2);(306067448054379001%positive,1);(18419783537%positive,1);(306067452231905785%positive,1);(357411551983818670%positive,2);(19641575789098926%positive,2);(1371399845172986%positive,2);(19641579931031470%positive,2);(75561067573753%positive,1);(75565245100537%positive,1);(1396138856797946%positive,2);(306064355677925881%positive,1);(351078360865896186%positive,0);(306064359855452665%positive,1);(1371399845173166%positive,2);(351078365007828730%positive,2);(76724903466746%positive,2)] [357411547841885946%positive;1396138856798126%positive;357411551983818490%positive;1150007538%positive;351078360865896366%positive;351078365007828910%positive;76724903466926%positive;19641575789098746%positive;19641579931031290%positive;294402117422%positive;357411547841886126%positive;306067448054379001%positive;18419783537%positive;306067452231905785%positive;357411551983818670%positive;19641575789098926%positive;1371399845172986%positive;19641579931031470%positive;75561067573753%positive;75565245100537%positive;1396138856797946%positive;306064355677925881%positive;351078360865896186%positive;306064359855452665%positive;1371399845173166%positive;351078365007828730%positive;76724903466746%positive]]
  end.

Lemma cqh_h_00061 : iqh tmq_h_00061.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00061 StA 9 2 2 34 20000
                lsetq_h_00061 rsetq_h_00061 certq_h_00061 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00061); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00062 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DR StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StA)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S0 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00062 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition rsetq_h_00062 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition certq_h_00062 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 50 [(357411547841885946%positive,4);(351078360865895151%positive,4);(1396138856798126%positive,0);(306064359855454111%positive,4);(19641576642696954%positive,2);(4670218605499%positive,1);(76724903465711%positive,4);(306064355677927327%positive,4);(351078361719493359%positive,4);(357411547841884911%positive,4);(357411548695484154%positive,2);(1150007538%positive,4);(351078360865896366%positive,4);(306067448054797243%positive,1);(19641576642695919%positive,4);(19641575789098746%positive,4);(76724903466926%positive,0);(4722827818783%positive,4);(294402117422%positive,4);(351078361719494574%positive,0);(357411548695483119%positive,4);(357411547841886126%positive,4);(19641576642697134%positive,0);(4722566723359%positive,4);(19641575789097711%positive,4);(357411548695484334%positive,0);(19641575789098926%positive,4);(1195563884073915%positive,3);(1371399845172986%positive,2);(306067452231907231%positive,4);(306067448054380447%positive,4);(306064355678344123%positive,3);(1396138856797946%positive,2);(1371399845171951%positive,4);(1195575963669435%positive,1);(4670171419579%positive,3);(351078360865896186%positive,4);(1396138856796911%positive,4);(1371399845173166%positive,0);(76724903466746%positive,2);(351078361719494394%positive,2)] [357411547841885946%positive;351078360865895151%positive;1396138856798126%positive;306064359855454111%positive;19641576642696954%positive;4670218605499%positive;76724903465711%positive;306064355677927327%positive;351078361719493359%positive;357411547841884911%positive;357411548695484154%positive;1150007538%positive;351078360865896366%positive;306067448054797243%positive;76724903466926%positive;19641576642695919%positive;19641575789098746%positive;4722827818783%positive;294402117422%positive;351078361719494574%positive;357411548695483119%positive;357411547841886126%positive;19641576642697134%positive;4722566723359%positive;19641575789097711%positive;357411548695484334%positive;19641575789098926%positive;1195563884073915%positive;1371399845172986%positive;306067452231907231%positive;306067448054380447%positive;306064355678344123%positive;1396138856797946%positive;1371399845171951%positive;1195575963669435%positive;4670171419579%positive;351078360865896186%positive;1396138856796911%positive;1371399845173166%positive;76724903466746%positive;351078361719494394%positive]]
  | StC => [HMeas MLeft 50 [(351078360865895151%positive,1);(306064359855454111%positive,1);(4670218605499%positive,1);(76724903465711%positive,1);(306064355677927327%positive,1);(351078361719493359%positive,1);(357411547841884911%positive,1);(306067448054797243%positive,1);(19641576642695919%positive,1);(4722827818783%positive,1);(357411548695483119%positive,1);(306067448054379001%positive,1);(4722566723359%positive,1);(18419783537%positive,1);(19641575789097711%positive,1);(306067452231905785%positive,1);(1195563884073915%positive,0);(306067452231907231%positive,1);(306067448054380447%positive,1);(75561067573753%positive,1);(306064355678344123%positive,0);(75565245100537%positive,1);(1371399845171951%positive,1);(1195575963669435%positive,1);(4670171419579%positive,0);(306064355677925881%positive,1);(1396138856796911%positive,1);(306064359855452665%positive,1)] [351078360865895151%positive;306064359855454111%positive;4670218605499%positive;306064355677927327%positive;76724903465711%positive;351078361719493359%positive;357411547841884911%positive;306067448054797243%positive;19641576642695919%positive;4722827818783%positive;4722566723359%positive;357411548695483119%positive;306067448054379001%positive;18419783537%positive;19641575789097711%positive;306067452231905785%positive;1195563884073915%positive;306067452231907231%positive;306067448054380447%positive;75561067573753%positive;306064355678344123%positive;75565245100537%positive;1371399845171951%positive;1195575963669435%positive;4670171419579%positive;306064355677925881%positive;1396138856796911%positive;306064359855452665%positive]]
  | StD => [HMeas MRight 50 [(357411547841885946%positive,0);(1396138856798126%positive,2);(19641576642696954%positive,2);(357411548695484154%positive,2);(1150007538%positive,0);(351078360865896366%positive,2);(19641575789098746%positive,0);(76724903466926%positive,2);(294402117422%positive,2);(351078361719494574%positive,2);(357411547841886126%positive,2);(19641576642697134%positive,2);(306067448054379001%positive,1);(18419783537%positive,1);(306067452231905785%positive,1);(357411548695484334%positive,2);(19641575789098926%positive,2);(1371399845172986%positive,2);(75561067573753%positive,1);(75565245100537%positive,1);(1396138856797946%positive,2);(306064355677925881%positive,1);(351078360865896186%positive,0);(306064359855452665%positive,1);(1371399845173166%positive,2);(76724903466746%positive,2);(351078361719494394%positive,2)] [357411547841885946%positive;1396138856798126%positive;19641576642696954%positive;357411548695484154%positive;1150007538%positive;351078360865896366%positive;76724903466926%positive;19641575789098746%positive;294402117422%positive;351078361719494574%positive;357411547841886126%positive;19641576642697134%positive;306067448054379001%positive;18419783537%positive;306067452231905785%positive;357411548695484334%positive;19641575789098926%positive;1371399845172986%positive;75561067573753%positive;75565245100537%positive;1396138856797946%positive;306064355677925881%positive;351078360865896186%positive;306064359855452665%positive;1371399845173166%positive;76724903466746%positive;351078361719494394%positive]]
  end.

Lemma cqh_h_00062 : iqh tmq_h_00062.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00062 StA 9 2 2 34 20000
                lsetq_h_00062 rsetq_h_00062 certq_h_00062 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00062); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00063 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S0 DR StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => Some (mkTrans S0 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Definition lsetq_h_00063 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)])]].

Definition rsetq_h_00063 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00063 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(96506244151734932528823967%positive,0);(395289576045616243870191315455%positive,0);(395289576045508157479134423551%positive,0);(1272356869486641675967%positive,0);(86815892754912382467697151%positive,0);(356478221541895532295539301886%positive,1);(356478221541895532089555020255%positive,0);(395284740351525128597623269855%positive,0);(395289576045616244011751088126%positive,1);(5439425987881799326886367%positive,0);(86815892718883795727810207%positive,0);(6031566472647875933759967%positive,0);(5752220401271370238%positive,1);(79524556147012878315%positive,1);(75385173311315%positive,2);(309059144859841534%positive,3);(395284740351525128803607551486%positive,1);(86815892646826132970577918%positive,1);(86815892646825991410805247%positive,0);(87030815806108789221268990%positive,1);(22469610942466335%positive,0);(395289576045508157620694196222%positive,1);(19316196576851263%positive,0);(1272356869692626299902%positive,1);(96505063562366014931246590%positive,1);(395289576045580215283451559583%positive,0);(86815892754912524027469822%positive,1)]]
  | StC => [HMeas MLeft 45 [(356478221541823474632781987485%positive,1);(5485676198033%positive,0);(395289551557455399771264122857%positive,0);(92035520718772838377%positive,0);(96506244151734932528823967%positive,1);(86890067004746519077322729%positive,0);(395289576045616243870191315455%positive,1);(395289576045508157479134423551%positive,1);(1472550408361321037469%positive,1);(1272356869486641675967%positive,1);(20364736985982012145641%positive,0);(395284740351453071140850237085%positive,1);(5439425987881799326886367%positive,1);(356478221541895532089555020255%positive,1);(356478197192193354998930857961%positive,0);(86815892718883795727810207%positive,1);(79524556147012878315%positive,0);(86890067112832910134214633%positive,0);(6031566472647875933759967%positive,1);(395284740351525128597623269855%positive,1);(395284716001822951506999107561%positive,0);(87030809861357281091903465%positive,0);(22469610942466335%positive,1);(356478221541931561023838879389%positive,1);(19316196576851263%positive,1);(395289551557563486162321014761%positive,0);(395289576045580215283451559583%positive,1);(395284740351561157531907128989%positive,1);(75385173311315%positive,1);(96505057617614506801881065%positive,0);(86815892646825991410805247%positive,1);(86815892754912382467697151%positive,1)] [356478221541823474632781987485%positive;5485676198033%positive;395289551557455399771264122857%positive;92035520718772838377%positive;96506244151734932528823967%positive;86890067004746519077322729%positive;395289576045616243870191315455%positive;395289576045508157479134423551%positive;1472550408361321037469%positive;1272356869486641675967%positive;20364736985982012145641%positive;356478197192193354998930857961%positive;395284740351453071140850237085%positive;5439425987881799326886367%positive;356478221541895532089555020255%positive;86815892718883795727810207%positive;79524556147012878315%positive;86890067112832910134214633%positive;6031566472647875933759967%positive;395284740351525128597623269855%positive;395284716001822951506999107561%positive;87030809861357281091903465%positive;22469610942466335%positive;356478221541931561023838879389%positive;19316196576851263%positive;395289551557563486162321014761%positive;395289576045580215283451559583%positive;395284740351561157531907128989%positive;75385173311315%positive;96505057617614506801881065%positive;86815892646825991410805247%positive;86815892754912382467697151%positive]]
  | StD => [HRank [(356478221541823474632781987485%positive,0);(5752220401271370238%positive,0);(5485676198033%positive,1);(356478221541895532295539301886%positive,0);(395284740351525128803607551486%positive,0);(395289551557455399771264122857%positive,1);(87030815806108789221268990%positive,0);(96505063562366014931246590%positive,0);(92035520718772838377%positive,1);(1272356869692626299902%positive,0);(86890067004746519077322729%positive,1);(1472550408361321037469%positive,0);(309059144859841534%positive,0);(20364736985982012145641%positive,1);(395289576045616244011751088126%positive,0);(395284740351453071140850237085%positive,0);(86815892754912524027469822%positive,0);(356478197192193354998930857961%positive,1);(86890067112832910134214633%positive,1);(86815892646826132970577918%positive,0);(395284716001822951506999107561%positive,1);(87030809861357281091903465%positive,1);(356478221541931561023838879389%positive,0);(395289576045508157620694196222%positive,0);(395289551557563486162321014761%positive,1);(395284740351561157531907128989%positive,0);(96505057617614506801881065%positive,1)]]
  end.

Lemma cqh_h_00063 : iqh tmq_h_00063.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00063 StA 3 4 2 28 20000
                lsetq_h_00063 rsetq_h_00063 certq_h_00063 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00063); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00064 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StB)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StA)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00064 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00064 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition certq_h_00064 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 37 [(314652163455309742%positive,4);(356852788752799647%positive,4);(5445141436191%positive,4);(75791334364922%positive,2);(1212666493260527%positive,4);(4709410501563%positive,1);(356852788753168287%positive,4);(314652164210284282%positive,4);(75791334363887%positive,4);(321809154152691615%positive,4);(1212665738286842%positive,2);(1172076690%positive,4);(19665759941678842%positive,4);(1212666493261562%positive,2);(314652164210283247%positive,4);(4709410132923%positive,3);(321809154152322975%positive,4);(1212665738285807%positive,4);(19665759941677807%positive,4);(314652163455309562%positive,4);(75791334365102%positive,0);(4910418007839%positive,4);(314652164210284462%positive,4);(314652163455308527%positive,4);(1212665738287022%positive,0);(19665759941679022%positive,4);(1212666493261742%positive,0);(300075682094%positive,4)] [314652163455309742%positive;356852788752799647%positive;5445141436191%positive;75791334364922%positive;1212666493260527%positive;4709410501563%positive;314652164210284282%positive;75791334363887%positive;321809154152691615%positive;1212665738286842%positive;1172076690%positive;19665759941678842%positive;1212666493261562%positive;314652164210283247%positive;4709410132923%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;314652163455309562%positive;75791334365102%positive;4910418007839%positive;314652164210284462%positive;1212666493261742%positive;314652163455308527%positive;1212665738287022%positive;19665759941679022%positive;356852788753168287%positive;300075682094%positive]]
  | StC => [HMeas MRight 37 [(78566688125433%positive,1);(356852788752799647%positive,1);(321809154152690169%positive,1);(5445141436191%positive,1);(1212666493260527%positive,1);(321809154152321529%positive,1);(4709410501563%positive,1);(356852788753168287%positive,1);(75791334363887%positive,1);(21270083729%positive,1);(321809154152691615%positive,1);(314652164210283247%positive,1);(4709410132923%positive,0);(87122262979065%positive,1);(321809154152322975%positive,1);(1212665738285807%positive,1);(19665759941677807%positive,1);(356852788753166841%positive,1);(4910418007839%positive,1);(314652163455308527%positive,1);(356852788752798201%positive,1)] [78566688125433%positive;356852788752799647%positive;321809154152690169%positive;5445141436191%positive;1212666493260527%positive;321809154152321529%positive;4709410501563%positive;75791334363887%positive;21270083729%positive;321809154152691615%positive;314652164210283247%positive;4709410132923%positive;87122262979065%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;356852788753166841%positive;4910418007839%positive;314652163455308527%positive;356852788752798201%positive;356852788753168287%positive]]
  | StD => [HMeas MLeft 37 [(314652163455309742%positive,2);(78566688125433%positive,1);(321809154152690169%positive,1);(75791334364922%positive,2);(321809154152321529%positive,1);(314652164210284282%positive,0);(21270083729%positive,1);(1212665738286842%positive,2);(1172076690%positive,0);(19665759941678842%positive,0);(1212666493261562%positive,2);(87122262979065%positive,1);(314652163455309562%positive,0);(75791334365102%positive,2);(356852788753166841%positive,1);(314652164210284462%positive,2);(1212665738287022%positive,2);(19665759941679022%positive,2);(356852788752798201%positive,1);(1212666493261742%positive,2);(300075682094%positive,2)] [314652163455309742%positive;78566688125433%positive;321809154152690169%positive;75791334364922%positive;321809154152321529%positive;314652164210284282%positive;21270083729%positive;1212665738286842%positive;1172076690%positive;19665759941678842%positive;1212666493261562%positive;87122262979065%positive;314652163455309562%positive;75791334365102%positive;356852788753166841%positive;314652164210284462%positive;1212665738287022%positive;19665759941679022%positive;356852788752798201%positive;1212666493261742%positive;300075682094%positive]]
  end.

Lemma cqh_h_00064 : iqh tmq_h_00064.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00064 StA 9 2 2 34 20000
                lsetq_h_00064 rsetq_h_00064 certq_h_00064 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00064); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00065 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StB)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StA)
  | StC, S1 => Some (mkTrans S0 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Definition lsetq_h_00065 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)])]].

Definition rsetq_h_00065 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00065 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(96506244151734932528823967%positive,0);(395289576045616243870191315455%positive,0);(395289576045508157479134423551%positive,0);(1272356869486641675967%positive,0);(86815892754912382467697151%positive,0);(356478221541895532295539301886%positive,1);(356478221541895532089555020255%positive,0);(395284740351525128597623269855%positive,0);(395289576045616244011751088126%positive,1);(5439425987881799326886367%positive,0);(86815892718883795727810207%positive,0);(6031566472647875933759967%positive,0);(5752220401271370238%positive,1);(79524556147012878315%positive,1);(75385173311315%positive,2);(309059144859841534%positive,3);(395284740351525128803607551486%positive,1);(86815892646826132970577918%positive,1);(86815892646825991410805247%positive,0);(87030815806108789221268990%positive,1);(22469610942466335%positive,0);(395289576045508157620694196222%positive,1);(19316196576851263%positive,0);(1272356869692626299902%positive,1);(96505063562366014931246590%positive,1);(395289576045580215283451559583%positive,0);(86815892754912524027469822%positive,1)]]
  | StC => [HMeas MLeft 45 [(356478221541823474632781987485%positive,1);(5485676198033%positive,0);(395289551557455399771264122857%positive,0);(92035520718772838377%positive,0);(96506244151734932528823967%positive,1);(86890067004746519077322729%positive,0);(395289576045616243870191315455%positive,1);(395289576045508157479134423551%positive,1);(1472550408361321037469%positive,1);(1272356869486641675967%positive,1);(20364736985982012145641%positive,0);(395284740351453071140850237085%positive,1);(5439425987881799326886367%positive,1);(356478221541895532089555020255%positive,1);(356478197192193354998930857961%positive,0);(86815892718883795727810207%positive,1);(79524556147012878315%positive,0);(86890067112832910134214633%positive,0);(6031566472647875933759967%positive,1);(395284740351525128597623269855%positive,1);(395284716001822951506999107561%positive,0);(87030809861357281091903465%positive,0);(22469610942466335%positive,1);(356478221541931561023838879389%positive,1);(19316196576851263%positive,1);(395289551557563486162321014761%positive,0);(395289576045580215283451559583%positive,1);(395284740351561157531907128989%positive,1);(75385173311315%positive,1);(96505057617614506801881065%positive,0);(86815892646825991410805247%positive,1);(86815892754912382467697151%positive,1)] [356478221541823474632781987485%positive;5485676198033%positive;395289551557455399771264122857%positive;92035520718772838377%positive;96506244151734932528823967%positive;86890067004746519077322729%positive;395289576045616243870191315455%positive;395289576045508157479134423551%positive;1472550408361321037469%positive;1272356869486641675967%positive;20364736985982012145641%positive;356478197192193354998930857961%positive;395284740351453071140850237085%positive;5439425987881799326886367%positive;356478221541895532089555020255%positive;86815892718883795727810207%positive;79524556147012878315%positive;86890067112832910134214633%positive;6031566472647875933759967%positive;395284740351525128597623269855%positive;395284716001822951506999107561%positive;87030809861357281091903465%positive;22469610942466335%positive;356478221541931561023838879389%positive;19316196576851263%positive;395289551557563486162321014761%positive;395289576045580215283451559583%positive;395284740351561157531907128989%positive;75385173311315%positive;96505057617614506801881065%positive;86815892646825991410805247%positive;86815892754912382467697151%positive]]
  | StD => [HRank [(356478221541823474632781987485%positive,0);(5752220401271370238%positive,0);(5485676198033%positive,1);(356478221541895532295539301886%positive,0);(395284740351525128803607551486%positive,0);(395289551557455399771264122857%positive,1);(87030815806108789221268990%positive,0);(96505063562366014931246590%positive,0);(92035520718772838377%positive,1);(1272356869692626299902%positive,0);(86890067004746519077322729%positive,1);(1472550408361321037469%positive,0);(309059144859841534%positive,0);(20364736985982012145641%positive,1);(395289576045616244011751088126%positive,0);(395284740351453071140850237085%positive,0);(86815892754912524027469822%positive,0);(356478197192193354998930857961%positive,1);(86890067112832910134214633%positive,1);(86815892646826132970577918%positive,0);(395284716001822951506999107561%positive,1);(87030809861357281091903465%positive,1);(356478221541931561023838879389%positive,0);(395289576045508157620694196222%positive,0);(395289551557563486162321014761%positive,1);(395284740351561157531907128989%positive,0);(96505057617614506801881065%positive,1)]]
  end.

Lemma cqh_h_00065 : iqh tmq_h_00065.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00065 StA 3 4 2 28 20000
                lsetq_h_00065 rsetq_h_00065 certq_h_00065 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00065); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00066 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StA)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00066 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StA,S1);(StC,S0)]);(S1,[(StC,S0)])]].

Definition rsetq_h_00066 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StD,S1);(StA,S1);(StC,S0)]);(S1,[(StA,S1);(StC,S0);(StD,S0);(StC,S1)])];
   [(S0,[(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StC,S1);(StC,S0)]);(S0,[(StC,S1);(StD,S1);(StA,S1);(StC,S0)])];
   [(S0,[(StD,S0);(StC,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S1);(StC,S0);(StD,S0);(StB,S0)])];
   [(S0,[(StD,S0);(StC,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S1);(StC,S0);(StD,S0);(StC,S1)])];
   [(S1,[(StA,S1);(StC,S0);(StD,S0);(StB,S0)]);(S0,[(StD,S0)])];
   [(S1,[(StA,S1);(StC,S0);(StD,S0);(StC,S1)]);(S0,[(StD,S0);(StC,S1);(StD,S1);(StA,S1)])]].

Definition certq_h_00066 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(22898819688870160045953961963%positive,0);(365791779881754879274682%positive,1);(5581539610011988715%positive,0);(4784548194450%positive,1);(21802889101609262%positive,2);(85304750833174785278%positive,3);(313560150571578063%positive,2);(299964774546%positive,3)]]
  | StB => []
  | StC => [HRank [(5852669107275019760888748%positive,0);(22898819688870160045953961963%positive,1);(1224844338170156%positive,0);(5581539610011988715%positive,1);(313560150571578063%positive,0)]]
  | StD => [HRank [(365791779881754879274682%positive,0);(4784548194450%positive,0);(21802889101609262%positive,1);(85304750833174785278%positive,2);(5852669107275019760888748%positive,3);(299964774546%positive,0);(1224844338170156%positive,1)]]
  end.

Lemma cqh_h_00066 : iqh tmq_h_00066.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00066 StB 1 4 2 26 20000
                lsetq_h_00066 rsetq_h_00066 certq_h_00066 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00066); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00067 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StA)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Definition lsetq_h_00067 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])]].

Definition rsetq_h_00067 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StC,S1)]);(S1,[(StA,S1);(StD,S1)])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S1,[(StA,S1);(StD,S1)])];
   [(S1,[(StA,S1);(StD,S1)]);(S0,[(StD,S0);(StD,S0)])]].

Definition certq_h_00067 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(78571922617067%positive,0);(21370742930%positive,1);(306921572654%positive,2);(20114412226999995%positive,0);(87538656703183%positive,1);(20791900306%positive,2)]]
  | StB => []
  | StC => [HRank [(341947877676%positive,0);(78571922617067%positive,1);(87535435478268%positive,0);(20114412226999995%positive,1);(87538656703183%positive,2)]]
  | StD => [HRank [(21370742930%positive,0);(306921572654%positive,1);(20791900306%positive,0);(87535435478268%positive,2);(341947877676%positive,1)]]
  end.

Lemma cqh_h_00067 : iqh tmq_h_00067.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00067 StB 1 2 2 26 20000
                lsetq_h_00067 rsetq_h_00067 certq_h_00067 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00067); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00068 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S0 DR StC)
  end.

Definition lsetq_h_00068 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])]].

Definition rsetq_h_00068 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StC,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StA,S1);(StC,S0)])]].

Definition certq_h_00068 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(85197983412971%positive,0);(18686388370%positive,1);(294402225131%positive,0);(296261088506%positive,1);(294400808638%positive,2);(299297764047%positive,3);(21810683792159723%positive,0);(76540520527098%positive,1);(332804622638%positive,2);(21810683790743230%positive,2);(76543557202639%positive,3);(20800288914%positive,4)]]
  | StB => []
  | StC => [HRank [(299297764047%positive,0);(298998270252%positive,0);(85197983412971%positive,1);(76543557202639%positive,0);(76543557203884%positive,0);(299297765292%positive,0);(21810683792159723%positive,1);(294402225131%positive,1)]]
  | StD => [HRank [(18686388370%positive,0);(76540520527098%positive,0);(332804622638%positive,1);(296261088506%positive,0);(294400808638%positive,1);(20800288914%positive,0);(298998270252%positive,1);(76543557203884%positive,2);(299297765292%positive,2);(21810683790743230%positive,1)]]
  end.

Lemma cqh_h_00068 : iqh tmq_h_00068.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00068 StB 1 2 2 26 20000
                lsetq_h_00068 rsetq_h_00068 certq_h_00068 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00068); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00069 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S1 DR StA)
  end.

Definition lsetq_h_00069 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])]].

Definition rsetq_h_00069 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StD,S1)]);(S1,[(StA,S1);(StD,S0)])];
   [(S1,[(StA,S1);(StD,S0)]);(S0,[])];
   [(S1,[(StA,S1);(StD,S0)]);(S0,[(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S1)])]].

Definition certq_h_00069 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(78743838749419%positive,0);(21429463186%positive,1);(307593120046%positive,2);(87776037532926%positive,3);(87779191648975%positive,0);(20800288914%positive,1)]]
  | StB => []
  | StC => [HRank [(342887467308%positive,0);(78743838749419%positive,1);(20158422756882108%positive,0);(87779191648975%positive,1)]]
  | StD => [HRank [(20800288914%positive,0);(342887467308%positive,1);(21429463186%positive,0);(307593120046%positive,1);(87776037532926%positive,2);(20158422756882108%positive,3)]]
  end.

Lemma cqh_h_00069 : iqh tmq_h_00069.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00069 StB 1 2 2 26 20000
                lsetq_h_00069 rsetq_h_00069 certq_h_00069 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00069); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00070 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Definition lsetq_h_00070 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StA,S1);(StC,S0)]);(S1,[(StC,S0)])]].

Definition rsetq_h_00070 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StD,S1);(StA,S1);(StC,S0)]);(S1,[(StA,S1);(StD,S1);(StD,S0);(StC,S1)])];
   [(S1,[(StA,S1);(StD,S1);(StD,S0);(StB,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StA,S1);(StD,S1);(StD,S0);(StC,S1)]);(S1,[(StD,S0);(StC,S1);(StD,S1);(StA,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1);(StC,S0)]);(S0,[(StC,S1);(StD,S1);(StA,S1);(StC,S0)])];
   [(S1,[(StD,S0);(StC,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S1);(StD,S1);(StD,S0);(StB,S0)])];
   [(S1,[(StD,S0);(StC,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S1);(StD,S1);(StD,S0);(StC,S1)])]].

Definition certq_h_00070 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(5584354359779095275%positive,0);(4784548194450%positive,1);(21813884217887022%positive,2);(22898857490860453095294554091%positive,0);(365976247322491974790847%positive,1);(313560150588355279%positive,2);(299973163154%positive,3);(85304891656562486526%positive,3)]]
  | StB => []
  | StC => [HRank [(1224844338235692%positive,0);(5584354359779095275%positive,1);(5855620586344405475191804%positive,0);(22898857490860453095294554091%positive,1);(365976247322491974790847%positive,2);(313560150588355279%positive,3)]]
  | StD => [HRank [(4784548194450%positive,0);(21813884217887022%positive,1);(85304891656562486526%positive,2);(5855620586344405475191804%positive,3);(299973163154%positive,0);(1224844338235692%positive,1)]]
  end.

Lemma cqh_h_00070 : iqh tmq_h_00070.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00070 StB 1 4 2 26 20000
                lsetq_h_00070 rsetq_h_00070 certq_h_00070 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00070); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00071 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S0 DL StA)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00071 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S1)]);(S0,[(StC,S1);(StD,S1)])];
   [(S0,[(StC,S1);(StD,S1)]);(S1,[(StC,S0)])];
   [(S0,[(StC,S1);(StD,S1)]);(S1,[(StC,S0);(StC,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S1)]);(S1,[(StC,S0);(StC,S1)])]].

Definition rsetq_h_00071 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0)]);(S0,[])]].

Definition certq_h_00071 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(18408775027%positive,0);(18408447347%positive,0);(294736524602%positive,1);(75770399511246%positive,2);(20067435737871614%positive,3);(294653689658%positive,1);(75771724264143%positive,2);(20067434413118698%positive,3);(1254214399382762%positive,3)]]
  | StB => []
  | StC => [HRank [(75770397979564%positive,0);(18408775027%positive,1);(75771723338668%positive,0);(18408447347%positive,1);(75771724264143%positive,0)]]
  | StD => [HRank [(294736524602%positive,0);(75770399511246%positive,1);(20067435737871614%positive,2);(75770397979564%positive,3);(20067434413118698%positive,0);(1254214399382762%positive,0);(75771723338668%positive,1);(294653689658%positive,0)]]
  end.

Lemma cqh_h_00071 : iqh tmq_h_00071.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00071 StB 1 2 2 26 20000
                lsetq_h_00071 rsetq_h_00071 certq_h_00071 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00071); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00072 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StA)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00072 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StA,S1);(StC,S0)]);(S1,[(StC,S0)])]].

Definition rsetq_h_00072 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StD,S1);(StA,S1);(StC,S0)]);(S1,[(StA,S1);(StC,S0);(StD,S0);(StC,S1)])];
   [(S0,[(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StC,S1);(StC,S0)]);(S0,[(StC,S1);(StD,S1);(StA,S1);(StC,S0)])];
   [(S0,[(StD,S0);(StC,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S1);(StC,S0);(StD,S0)])];
   [(S0,[(StD,S0);(StC,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S1);(StC,S0);(StD,S0);(StC,S1)])];
   [(S1,[(StA,S1);(StC,S0);(StD,S0)]);(S0,[(StD,S0)])];
   [(S1,[(StA,S1);(StC,S0);(StD,S0);(StC,S1)]);(S0,[(StD,S0);(StC,S1);(StD,S1);(StA,S1)])]].

Definition certq_h_00072 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(22898819688870160045953961963%positive,0);(365791779881754879274682%positive,1);(5581539610011988715%positive,0);(4784548194450%positive,1);(21802889101609262%positive,2);(85304750833174785278%positive,3);(313560150571578063%positive,2);(299964774546%positive,3)]]
  | StB => []
  | StC => [HRank [(5852669107275019760888748%positive,0);(22898819688870160045953961963%positive,1);(1224844338170156%positive,0);(5581539610011988715%positive,1);(313560150571578063%positive,0)]]
  | StD => [HRank [(365791779881754879274682%positive,0);(4784548194450%positive,0);(21802889101609262%positive,1);(85304750833174785278%positive,2);(5852669107275019760888748%positive,3);(299964774546%positive,0);(1224844338170156%positive,1)]]
  end.

Lemma cqh_h_00072 : iqh tmq_h_00072.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00072 StB 1 4 2 26 20000
                lsetq_h_00072 rsetq_h_00072 certq_h_00072 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00072); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00073 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StA)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Definition lsetq_h_00073 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])]].

Definition rsetq_h_00073 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StC,S1)]);(S1,[(StA,S1);(StD,S1)])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S1,[(StA,S1);(StD,S1)])];
   [(S1,[(StA,S1);(StD,S1)]);(S0,[(StD,S0);(StD,S0)])]].

Definition certq_h_00073 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(78571922617067%positive,0);(21370742930%positive,1);(306921572654%positive,2);(20114412226999995%positive,0);(87538656703183%positive,1);(20791900306%positive,2)]]
  | StB => []
  | StC => [HRank [(341947877676%positive,0);(78571922617067%positive,1);(87535435478268%positive,0);(20114412226999995%positive,1);(87538656703183%positive,2)]]
  | StD => [HRank [(21370742930%positive,0);(306921572654%positive,1);(20791900306%positive,0);(87535435478268%positive,2);(341947877676%positive,1)]]
  end.

Lemma cqh_h_00073 : iqh tmq_h_00073.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00073 StB 1 2 2 26 20000
                lsetq_h_00073 rsetq_h_00073 certq_h_00073 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00073); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00074 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S0 DR StC)
  end.

Definition lsetq_h_00074 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])]].

Definition rsetq_h_00074 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StC,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StA,S1);(StC,S0)])]].

Definition certq_h_00074 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(85197983412971%positive,0);(18686388370%positive,1);(294402225131%positive,0);(296261088506%positive,1);(294400808638%positive,2);(299297764047%positive,3);(21810683792159723%positive,0);(76540520527098%positive,1);(332804622638%positive,2);(21810683790743230%positive,2);(76543557202639%positive,3);(20800288914%positive,4)]]
  | StB => []
  | StC => [HRank [(299297764047%positive,0);(298998270252%positive,0);(85197983412971%positive,1);(76543557202639%positive,0);(76543557203884%positive,0);(299297765292%positive,0);(21810683792159723%positive,1);(294402225131%positive,1)]]
  | StD => [HRank [(18686388370%positive,0);(76540520527098%positive,0);(332804622638%positive,1);(296261088506%positive,0);(294400808638%positive,1);(20800288914%positive,0);(298998270252%positive,1);(76543557203884%positive,2);(299297765292%positive,2);(21810683790743230%positive,1)]]
  end.

Lemma cqh_h_00074 : iqh tmq_h_00074.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00074 StB 1 2 2 26 20000
                lsetq_h_00074 rsetq_h_00074 certq_h_00074 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00074); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00075 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S1 DR StA)
  end.

Definition lsetq_h_00075 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])]].

Definition rsetq_h_00075 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StD,S1)]);(S1,[(StA,S1);(StD,S0)])];
   [(S1,[(StA,S1);(StD,S0)]);(S0,[])];
   [(S1,[(StA,S1);(StD,S0)]);(S0,[(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S1)])]].

Definition certq_h_00075 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(78743838749419%positive,0);(21429463186%positive,1);(307593120046%positive,2);(87776037532926%positive,3);(87779191648975%positive,0);(20800288914%positive,1)]]
  | StB => []
  | StC => [HRank [(342887467308%positive,0);(78743838749419%positive,1);(20158422756882108%positive,0);(87779191648975%positive,1)]]
  | StD => [HRank [(20800288914%positive,0);(342887467308%positive,1);(21429463186%positive,0);(307593120046%positive,1);(87776037532926%positive,2);(20158422756882108%positive,3)]]
  end.

Lemma cqh_h_00075 : iqh tmq_h_00075.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00075 StB 1 2 2 26 20000
                lsetq_h_00075 rsetq_h_00075 certq_h_00075 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00075); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00076 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Definition lsetq_h_00076 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StA,S1);(StC,S0)]);(S1,[(StC,S0)])]].

Definition rsetq_h_00076 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StD,S1);(StA,S1);(StC,S0)]);(S1,[(StA,S1);(StD,S1);(StD,S0);(StC,S1)])];
   [(S1,[(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StA,S1);(StD,S1);(StD,S0);(StC,S1)]);(S1,[(StD,S0);(StC,S1);(StD,S1);(StA,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1);(StC,S0)]);(S0,[(StC,S1);(StD,S1);(StA,S1);(StC,S0)])];
   [(S1,[(StD,S0);(StC,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S1);(StD,S1);(StD,S0)])];
   [(S1,[(StD,S0);(StC,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S1);(StD,S1);(StD,S0);(StC,S1)])]].

Definition certq_h_00076 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(5584354359779095275%positive,0);(4784548194450%positive,1);(21813884217887022%positive,2);(22898857490860453095294554091%positive,0);(365976247322491974790847%positive,1);(313560150588355279%positive,2);(299973163154%positive,3);(85304891656562486526%positive,3)]]
  | StB => []
  | StC => [HRank [(1224844338235692%positive,0);(5584354359779095275%positive,1);(5855620586344405475191804%positive,0);(22898857490860453095294554091%positive,1);(365976247322491974790847%positive,2);(313560150588355279%positive,3)]]
  | StD => [HRank [(4784548194450%positive,0);(21813884217887022%positive,1);(85304891656562486526%positive,2);(5855620586344405475191804%positive,3);(299973163154%positive,0);(1224844338235692%positive,1)]]
  end.

Lemma cqh_h_00076 : iqh tmq_h_00076.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00076 StB 1 4 2 26 20000
                lsetq_h_00076 rsetq_h_00076 certq_h_00076 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00076); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00077 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S0 DL StA)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Definition lsetq_h_00077 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StA,S0)]);(S0,[])];
   [(S0,[(StC,S1);(StA,S1)]);(S0,[(StC,S1);(StD,S1)])];
   [(S0,[(StC,S1);(StD,S1)]);(S1,[(StC,S0);(StB,S0)])];
   [(S0,[(StC,S1);(StD,S1)]);(S1,[(StC,S0);(StC,S1)])];
   [(S1,[(StC,S0);(StB,S0)]);(S0,[(StA,S0)])];
   [(S1,[(StC,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S1)]);(S1,[(StC,S0);(StC,S1)])]].

Definition rsetq_h_00077 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0)]);(S0,[])]].

Definition certq_h_00077 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(18408775027%positive,0);(18408447347%positive,0);(294736524602%positive,1);(75770399511246%positive,2);(20067435737871614%positive,3);(294653689658%positive,1);(75771724264143%positive,2);(20067434413118698%positive,3);(20067429044409578%positive,3)]]
  | StB => []
  | StC => [HRank [(75770397979564%positive,0);(18408775027%positive,1);(75771723338668%positive,0);(18408447347%positive,1);(75771724264143%positive,0)]]
  | StD => [HRank [(294736524602%positive,0);(75770399511246%positive,1);(20067435737871614%positive,2);(75770397979564%positive,3);(20067434413118698%positive,0);(20067429044409578%positive,0);(75771723338668%positive,1);(294653689658%positive,0)]]
  end.

Lemma cqh_h_00077 : iqh tmq_h_00077.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00077 StB 1 2 2 26 20000
                lsetq_h_00077 rsetq_h_00077 certq_h_00077 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00077); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00078 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StA)
  | StC, S1 => Some (mkTrans S0 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StD)
  | StD, S1 => Some (mkTrans S1 DR StB)
  end.

Definition lsetq_h_00078 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)])]].

Definition rsetq_h_00078 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)])]].

Definition certq_h_00078 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(5121400252161856676293087%positive,0);(19315842251812639%positive,0);(336666231129655607476438428159%positive,0);(91865338864502422595960479%positive,0);(92221282669268254699%positive,1);(22514964547406143%positive,0);(396087353015353860671596390911%positive,0);(376280314747900420265453545951%positive,0);(376280314747971008911956765151%positive,0);(396087430838708343138374033406%positive,1);(1401753406032447798975%positive,0);(81942401319767723897912991%positive,0);(376280427989074121697149714079%positive,0);(82193904084370949397801471%positive,0);(81942401249170281318489598%positive,1);(1401753827888430836734%positive,1);(82193923084213352343707646%positive,1);(81942401319758927821708798%positive,1);(79152975685779%positive,2);(96701013919746499494275583%positive,0);(376280427989003524254570290686%positive,1);(376280427989074112901073509886%positive,1);(5121400181573210173073887%positive,0);(4934250293338501630%positive,1);(336666308953010089943216070654%positive,1);(96701032919588902440181758%positive,1);(360239385426826238%positive,3)]]
  | StC => [HMeas MRight 45 [(336666308953010081147139915421%positive,1);(82193923084213487265775593%positive,0);(5121400252161856676293087%positive,1);(19315842251812639%positive,1);(4715781263345%positive,0);(376280427989074112856781348841%positive,0);(1263168066298580172445%positive,1);(336666231129655607476438428159%positive,1);(396087430838637745695794658973%positive,1);(22428061246214901252073%positive,0);(92221282669268254699%positive,0);(22514964547406143%positive,1);(396087353015353860671596390911%positive,1);(336666308953010089898672259049%positive,0);(1401753406032447798975%positive,1);(81942401319767723897912991%positive,1);(376280427989074121697149714079%positive,1);(376280314747900420265453545951%positive,1);(96701032919589037362249705%positive,0);(376280314747971008911956765151%positive,1);(78948004690632056809%positive,0);(79152975685779%positive,1);(81942401249170237026328553%positive,0);(396087430838708343093830221801%positive,0);(396087430838708334342297878173%positive,1);(91865338864502422595960479%positive,1);(81942401319758883529547753%positive,0);(82193904084370949397801471%positive,1);(336666308952939492500636696221%positive,1);(376280427989003524210278129641%positive,0);(5121400181573210173073887%positive,1);(96701013919746499494275583%positive,1)] [336666308953010081147139915421%positive;82193923084213487265775593%positive;5121400252161856676293087%positive;19315842251812639%positive;4715781263345%positive;376280427989074112856781348841%positive;1263168066298580172445%positive;336666231129655607476438428159%positive;396087430838637745695794658973%positive;22428061246214901252073%positive;92221282669268254699%positive;22514964547406143%positive;396087353015353860671596390911%positive;336666308953010089898672259049%positive;1401753406032447798975%positive;81942401319767723897912991%positive;376280427989074121697149714079%positive;376280314747900420265453545951%positive;96701032919589037362249705%positive;376280314747971008911956765151%positive;78948004690632056809%positive;79152975685779%positive;5121400181573210173073887%positive;81942401249170237026328553%positive;396087430838708343093830221801%positive;396087430838708334342297878173%positive;91865338864502422595960479%positive;81942401319758883529547753%positive;82193904084370949397801471%positive;336666308952939492500636696221%positive;376280427989003524210278129641%positive;96701013919746499494275583%positive]]
  | StD => [HRank [(336666308953010081147139915421%positive,0);(1401753827888430836734%positive,0);(82193923084213487265775593%positive,1);(4934250293338501630%positive,0);(4715781263345%positive,1);(396087430838708343138374033406%positive,0);(376280427989074112856781348841%positive,1);(1263168066298580172445%positive,0);(396087430838637745695794658973%positive,0);(360239385426826238%positive,0);(22428061246214901252073%positive,1);(376280427989003524254570290686%positive,0);(376280427989074112901073509886%positive,0);(336666308953010089898672259049%positive,1);(81942401249170281318489598%positive,0);(96701032919589037362249705%positive,1);(82193923084213352343707646%positive,0);(81942401319758927821708798%positive,0);(78948004690632056809%positive,1);(81942401249170237026328553%positive,1);(396087430838708343093830221801%positive,1);(396087430838708334342297878173%positive,0);(336666308953010089943216070654%positive,0);(81942401319758883529547753%positive,1);(336666308952939492500636696221%positive,0);(96701032919588902440181758%positive,0);(376280427989003524210278129641%positive,1)]]
  end.

Lemma cqh_h_00078 : iqh tmq_h_00078.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00078 StA 3 4 2 28 20000
                lsetq_h_00078 rsetq_h_00078 certq_h_00078 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00078); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00079 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StA)
  | StC, S1 => Some (mkTrans S0 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Definition lsetq_h_00079 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)])]].

Definition rsetq_h_00079 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)])]].

Definition certq_h_00079 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(96506244151734932528823967%positive,0);(395289576045616243870191315455%positive,0);(395289576045508157479134423551%positive,0);(1272356869486641675967%positive,0);(86815892754912382467697151%positive,0);(356478221541895532295539301886%positive,1);(356478221541895532089555020255%positive,0);(395284740351525128597623269855%positive,0);(395289576045616244011751088126%positive,1);(5439425987881799326886367%positive,0);(86815892718883795727810207%positive,0);(6031566472647875933759967%positive,0);(5752220401271370238%positive,1);(79524556147012878315%positive,1);(75385173311315%positive,2);(309059144859841534%positive,3);(395284740351525128803607551486%positive,1);(86815892646826132970577918%positive,1);(86815892646825991410805247%positive,0);(87030815806108789221268990%positive,1);(22469610942466335%positive,0);(395289576045508157620694196222%positive,1);(19316196576851263%positive,0);(1272356869692626299902%positive,1);(96505063562366014931246590%positive,1);(395289576045580215283451559583%positive,0);(86815892754912524027469822%positive,1)]]
  | StC => [HMeas MLeft 45 [(356478221541823474632781987485%positive,1);(5485676198033%positive,0);(395289551557455399771264122857%positive,0);(92035520718772838377%positive,0);(96506244151734932528823967%positive,1);(86890067004746519077322729%positive,0);(395289576045616243870191315455%positive,1);(395289576045508157479134423551%positive,1);(1472550408361321037469%positive,1);(1272356869486641675967%positive,1);(20364736985982012145641%positive,0);(395284740351453071140850237085%positive,1);(5439425987881799326886367%positive,1);(356478221541895532089555020255%positive,1);(356478197192193354998930857961%positive,0);(86815892718883795727810207%positive,1);(79524556147012878315%positive,0);(86890067112832910134214633%positive,0);(6031566472647875933759967%positive,1);(395284740351525128597623269855%positive,1);(395284716001822951506999107561%positive,0);(87030809861357281091903465%positive,0);(22469610942466335%positive,1);(356478221541931561023838879389%positive,1);(19316196576851263%positive,1);(395289551557563486162321014761%positive,0);(395289576045580215283451559583%positive,1);(395284740351561157531907128989%positive,1);(75385173311315%positive,1);(96505057617614506801881065%positive,0);(86815892646825991410805247%positive,1);(86815892754912382467697151%positive,1)] [356478221541823474632781987485%positive;5485676198033%positive;395289551557455399771264122857%positive;92035520718772838377%positive;96506244151734932528823967%positive;86890067004746519077322729%positive;395289576045616243870191315455%positive;395289576045508157479134423551%positive;1472550408361321037469%positive;1272356869486641675967%positive;20364736985982012145641%positive;356478197192193354998930857961%positive;395284740351453071140850237085%positive;5439425987881799326886367%positive;356478221541895532089555020255%positive;86815892718883795727810207%positive;79524556147012878315%positive;86890067112832910134214633%positive;6031566472647875933759967%positive;395284740351525128597623269855%positive;395284716001822951506999107561%positive;87030809861357281091903465%positive;22469610942466335%positive;356478221541931561023838879389%positive;19316196576851263%positive;395289551557563486162321014761%positive;395289576045580215283451559583%positive;395284740351561157531907128989%positive;75385173311315%positive;96505057617614506801881065%positive;86815892646825991410805247%positive;86815892754912382467697151%positive]]
  | StD => [HRank [(356478221541823474632781987485%positive,0);(5752220401271370238%positive,0);(5485676198033%positive,1);(356478221541895532295539301886%positive,0);(395284740351525128803607551486%positive,0);(395289551557455399771264122857%positive,1);(87030815806108789221268990%positive,0);(96505063562366014931246590%positive,0);(92035520718772838377%positive,1);(1272356869692626299902%positive,0);(86890067004746519077322729%positive,1);(1472550408361321037469%positive,0);(309059144859841534%positive,0);(20364736985982012145641%positive,1);(395289576045616244011751088126%positive,0);(395284740351453071140850237085%positive,0);(86815892754912524027469822%positive,0);(356478197192193354998930857961%positive,1);(86890067112832910134214633%positive,1);(86815892646826132970577918%positive,0);(395284716001822951506999107561%positive,1);(87030809861357281091903465%positive,1);(356478221541931561023838879389%positive,0);(395289576045508157620694196222%positive,0);(395289551557563486162321014761%positive,1);(395284740351561157531907128989%positive,0);(96505057617614506801881065%positive,1)]]
  end.

Lemma cqh_h_00079 : iqh tmq_h_00079.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00079 StA 5 4 2 30 20000
                lsetq_h_00079 rsetq_h_00079 certq_h_00079 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 30) 2000 tmq_h_00079); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00080 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => None
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00080 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StA,S0)]);(S0,[])]].

Definition rsetq_h_00080 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S0)]);(S0,[])];
   [(S0,[(StD,S1);(StA,S1)]);(S1,[(StD,S0);(StC,S0)])];
   [(S0,[(StD,S1);(StA,S1)]);(S1,[(StD,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StB,S1)]);(S0,[(StD,S1);(StA,S1)])];
   [(S1,[(StA,S1);(StB,S1)]);(S1,[(StD,S0);(StD,S1)])];
   [(S1,[(StD,S0);(StC,S0)]);(S0,[(StB,S0)])];
   [(S1,[(StD,S0);(StD,S1)]);(S0,[(StD,S1);(StA,S1)])]].

Definition certq_h_00080 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(341407140107%positive,0);(19559480825935355%positive,0);(317651323147%positive,0);(87399338628063%positive,1);(20818082337322447%positive,2);(87400227819709%positive,3);(22374230593041915%positive,0);(81318738677949%positive,1)]]
  | StB => [HRank [(20296431760%positive,0);(341407140107%positive,1);(81320634504156%positive,2);(19559480825935355%positive,3);(20388706448%positive,0);(317651323147%positive,1);(22374230593041915%positive,3);(87399338628063%positive,2);(20818082337322447%positive,3)]]
  | StC => []
  | StD => [HRank [(87400227819709%positive,0);(81320634504156%positive,0);(81318738677949%positive,0);(20296431760%positive,1);(20388706448%positive,1)]]
  end.

Lemma cqh_h_00080 : iqh tmq_h_00080.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00080 StC 2 2 2 27 20000
                lsetq_h_00080 rsetq_h_00080 certq_h_00080 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 27) 2000 tmq_h_00080); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00081 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => None
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00081 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StA,S0)]);(S0,[])];
   [(S0,[(StA,S0);(StD,S1);(StA,S1);(StB,S1)]);(S1,[(StB,S1);(StD,S0);(StA,S0)])];
   [(S0,[(StA,S0);(StD,S1);(StA,S1);(StB,S1)]);(S1,[(StB,S1);(StD,S0);(StA,S0);(StD,S1)])];
   [(S0,[(StA,S0);(StD,S1);(StD,S0)]);(S0,[(StD,S1);(StA,S1);(StB,S1);(StD,S0)])];
   [(S0,[(StD,S1);(StA,S1);(StB,S1);(StD,S0)]);(S1,[(StB,S1);(StD,S0);(StA,S0);(StD,S1)])];
   [(S1,[(StB,S1);(StD,S0);(StA,S0)]);(S0,[(StA,S0)])];
   [(S1,[(StB,S1);(StD,S0);(StA,S0);(StD,S1)]);(S0,[(StA,S0);(StD,S1);(StA,S1);(StB,S1)])]].

Definition rsetq_h_00081 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StB,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0)]);(S0,[])]].

Definition certq_h_00081 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(4711432232915%positive,0);(19314225162648895%positive,1);(294471769843%positive,0);(339114827455564108087179%positive,0);(79522097303043128783%positive,2);(5425837239289092645320893%positive,3);(1206126651622717%positive,1)]]
  | StB => [HRank [(4970253216930845688%positive,0);(4711432232915%positive,1);(19314225162648895%positive,2);(22198068690745280788138548472%positive,0);(339114827455564108087179%positive,1);(310624627321492444%positive,2);(294471769843%positive,3);(79522097303043128783%positive,3)]]
  | StC => []
  | StD => [HRank [(1206126651622717%positive,0);(4970253216930845688%positive,1);(310624627321492444%positive,0);(5425837239289092645320893%positive,0);(22198068690745280788138548472%positive,1)]]
  end.

Lemma cqh_h_00081 : iqh tmq_h_00081.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00081 StC 2 4 2 27 20000
                lsetq_h_00081 rsetq_h_00081 certq_h_00081 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 27) 2000 tmq_h_00081); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00082 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => None
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00082 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StA,S0)]);(S0,[])]].

Definition rsetq_h_00082 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StA,S1)]);(S1,[(StD,S0)])];
   [(S0,[(StD,S1);(StA,S1)]);(S1,[(StD,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StB,S1)]);(S0,[(StD,S1);(StA,S1)])];
   [(S1,[(StA,S1);(StB,S1)]);(S1,[(StD,S0);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StD,S1)]);(S0,[(StD,S1);(StA,S1)])]].

Definition certq_h_00082 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(341407140107%positive,0);(317651323147%positive,0);(87399338628063%positive,1);(20818082337322447%positive,2);(87400227819709%positive,3);(22374230593041915%positive,0);(1263607339742715%positive,0);(81318738677949%positive,1)]]
  | StB => [HRank [(20296431760%positive,0);(341407140107%positive,1);(20388706448%positive,0);(317651323147%positive,1);(81320634504156%positive,2);(22374230593041915%positive,3);(87399338628063%positive,2);(20818082337322447%positive,3);(1263607339742715%positive,3)]]
  | StC => []
  | StD => [HRank [(87400227819709%positive,0);(81320634504156%positive,0);(81318738677949%positive,0);(20296431760%positive,1);(20388706448%positive,1)]]
  end.

Lemma cqh_h_00082 : iqh tmq_h_00082.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00082 StC 2 2 2 27 20000
                lsetq_h_00082 rsetq_h_00082 certq_h_00082 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 27) 2000 tmq_h_00082); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00083 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => None
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00083 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StA,S0)]);(S0,[])];
   [(S0,[(StA,S0);(StD,S1);(StA,S1);(StB,S1)]);(S1,[(StB,S1);(StD,S0);(StA,S0);(StC,S0)])];
   [(S0,[(StA,S0);(StD,S1);(StA,S1);(StB,S1)]);(S1,[(StB,S1);(StD,S0);(StA,S0);(StD,S1)])];
   [(S0,[(StA,S0);(StD,S1);(StD,S0)]);(S0,[(StD,S1);(StA,S1);(StB,S1);(StD,S0)])];
   [(S0,[(StD,S1);(StA,S1);(StB,S1);(StD,S0)]);(S1,[(StB,S1);(StD,S0);(StA,S0);(StD,S1)])];
   [(S1,[(StB,S1);(StD,S0);(StA,S0);(StC,S0)]);(S0,[(StA,S0)])];
   [(S1,[(StB,S1);(StD,S0);(StA,S0);(StD,S1)]);(S0,[(StA,S0);(StD,S1);(StA,S1);(StB,S1)])]].

Definition rsetq_h_00083 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StB,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0)]);(S0,[])]].

Definition certq_h_00083 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(4711432232915%positive,0);(19314225162648895%positive,1);(294471769843%positive,0);(339114827455564108087179%positive,0);(79522097303043128783%positive,2);(5425837239289092645320893%positive,3);(1206126651622717%positive,1)]]
  | StB => [HRank [(4970253216930845688%positive,0);(4711432232915%positive,1);(19314225162648895%positive,2);(22198068690745280788138548472%positive,0);(339114827455564108087179%positive,1);(310624627321492444%positive,2);(294471769843%positive,3);(79522097303043128783%positive,3)]]
  | StC => []
  | StD => [HRank [(1206126651622717%positive,0);(4970253216930845688%positive,1);(310624627321492444%positive,0);(5425837239289092645320893%positive,0);(22198068690745280788138548472%positive,1)]]
  end.

Lemma cqh_h_00083 : iqh tmq_h_00083.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00083 StC 2 4 2 27 20000
                lsetq_h_00083 rsetq_h_00083 certq_h_00083 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 27) 2000 tmq_h_00083); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00084 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => None
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00084 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StA,S0)]);(S0,[])]].

Definition rsetq_h_00084 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StA,S1)]);(S1,[(StD,S0);(StC,S0)])];
   [(S0,[(StD,S1);(StA,S1)]);(S1,[(StD,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StB,S1)]);(S0,[(StD,S1);(StA,S1)])];
   [(S1,[(StA,S1);(StB,S1)]);(S1,[(StD,S0);(StD,S1)])];
   [(S1,[(StD,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StD,S1)]);(S0,[(StD,S1);(StA,S1)])]].

Definition certq_h_00084 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(341407140107%positive,0);(19559480825935355%positive,0);(317651323147%positive,0);(87399338628063%positive,1);(20818082337322447%positive,2);(87400227819709%positive,3);(22374230593041915%positive,0);(81318738677949%positive,1)]]
  | StB => [HRank [(20296431760%positive,0);(341407140107%positive,1);(81320634504156%positive,2);(19559480825935355%positive,3);(20388706448%positive,0);(317651323147%positive,1);(22374230593041915%positive,3);(87399338628063%positive,2);(20818082337322447%positive,3)]]
  | StC => []
  | StD => [HRank [(87400227819709%positive,0);(81320634504156%positive,0);(81318738677949%positive,0);(20296431760%positive,1);(20388706448%positive,1)]]
  end.

Lemma cqh_h_00084 : iqh tmq_h_00084.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00084 StC 2 2 2 27 20000
                lsetq_h_00084 rsetq_h_00084 certq_h_00084 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 27) 2000 tmq_h_00084); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00085 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => None
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00085 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StA,S0)]);(S0,[])];
   [(S0,[(StA,S0);(StD,S1);(StA,S1);(StB,S1)]);(S1,[(StB,S1);(StD,S0);(StA,S0);(StA,S0)])];
   [(S0,[(StA,S0);(StD,S1);(StA,S1);(StB,S1)]);(S1,[(StB,S1);(StD,S0);(StA,S0);(StD,S1)])];
   [(S0,[(StA,S0);(StD,S1);(StD,S0)]);(S0,[(StD,S1);(StA,S1);(StB,S1);(StD,S0)])];
   [(S0,[(StD,S1);(StA,S1);(StB,S1);(StD,S0)]);(S1,[(StB,S1);(StD,S0);(StA,S0);(StD,S1)])];
   [(S1,[(StB,S1);(StD,S0);(StA,S0);(StA,S0)]);(S0,[(StA,S0)])];
   [(S1,[(StB,S1);(StD,S0);(StA,S0);(StD,S1)]);(S0,[(StA,S0);(StD,S1);(StA,S1);(StB,S1)])]].

Definition rsetq_h_00085 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StB,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0)]);(S0,[])]].

Definition certq_h_00085 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(4711432232915%positive,0);(19314225162648895%positive,1);(294471769843%positive,0);(339114827455564108087179%positive,0);(79522097303043128783%positive,2);(5425837239289092645320893%positive,3);(1206126651622717%positive,1)]]
  | StB => [HRank [(4970253216930845688%positive,0);(4711432232915%positive,1);(19314225162648895%positive,2);(22198068690745280788138548472%positive,0);(339114827455564108087179%positive,1);(310624627321492444%positive,2);(294471769843%positive,3);(79522097303043128783%positive,3)]]
  | StC => []
  | StD => [HRank [(1206126651622717%positive,0);(4970253216930845688%positive,1);(310624627321492444%positive,0);(5425837239289092645320893%positive,0);(22198068690745280788138548472%positive,1)]]
  end.

Lemma cqh_h_00085 : iqh tmq_h_00085.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00085 StC 2 4 2 27 20000
                lsetq_h_00085 rsetq_h_00085 certq_h_00085 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 27) 2000 tmq_h_00085); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00086 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => None
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00086 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StA,S0)]);(S0,[])]].

Definition rsetq_h_00086 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StA,S1)]);(S1,[(StD,S0)])];
   [(S0,[(StD,S1);(StA,S1)]);(S1,[(StD,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StB,S1)]);(S0,[(StD,S1);(StA,S1)])];
   [(S1,[(StA,S1);(StB,S1)]);(S1,[(StD,S0);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StD,S1)]);(S0,[(StD,S1);(StA,S1)])]].

Definition certq_h_00086 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(341407140107%positive,0);(317651323147%positive,0);(87399338628063%positive,1);(20818082337322447%positive,2);(87400227819709%positive,3);(22374230593041915%positive,0);(1263607339742715%positive,0);(81318738677949%positive,1)]]
  | StB => [HRank [(20296431760%positive,0);(341407140107%positive,1);(20388706448%positive,0);(317651323147%positive,1);(81320634504156%positive,2);(22374230593041915%positive,3);(87399338628063%positive,2);(20818082337322447%positive,3);(1263607339742715%positive,3)]]
  | StC => []
  | StD => [HRank [(87400227819709%positive,0);(81320634504156%positive,0);(81318738677949%positive,0);(20296431760%positive,1);(20388706448%positive,1)]]
  end.

Lemma cqh_h_00086 : iqh tmq_h_00086.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00086 StC 2 2 2 27 20000
                lsetq_h_00086 rsetq_h_00086 certq_h_00086 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 27) 2000 tmq_h_00086); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00087 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => None
  | StD, S0 => Some (mkTrans S1 DL StA)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00087 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StA,S0)]);(S0,[])];
   [(S0,[(StA,S0);(StB,S0)]);(S0,[(StA,S0)])];
   [(S0,[(StA,S0);(StD,S1);(StA,S1);(StB,S1)]);(S1,[(StB,S1);(StD,S0);(StA,S0);(StC,S0)])];
   [(S0,[(StA,S0);(StD,S1);(StA,S1);(StB,S1)]);(S1,[(StB,S1);(StD,S0);(StA,S0);(StD,S1)])];
   [(S0,[(StA,S0);(StD,S1);(StD,S0)]);(S0,[(StD,S1);(StA,S1);(StB,S1);(StD,S0)])];
   [(S0,[(StD,S1);(StA,S1);(StB,S1);(StD,S0)]);(S1,[(StB,S1);(StD,S0);(StA,S0);(StD,S1)])];
   [(S1,[(StB,S1);(StD,S0);(StA,S0);(StC,S0)]);(S0,[(StA,S0);(StB,S0)])];
   [(S1,[(StB,S1);(StD,S0);(StA,S0);(StD,S1)]);(S0,[(StA,S0);(StD,S1);(StA,S1);(StB,S1)])]].

Definition rsetq_h_00087 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StB,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S0)]);(S0,[])]].

Definition certq_h_00087 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(4711432232915%positive,0);(19314225162648895%positive,1);(294471769843%positive,0);(339114827455564108087179%positive,0);(79522097303043128783%positive,2);(5425837239289092645320893%positive,3);(1206126651622717%positive,1)]]
  | StB => [HRank [(4970253216930845688%positive,0);(4711432232915%positive,1);(19314225162648895%positive,2);(22198068690745280788138548472%positive,0);(339114827455564108087179%positive,1);(310624627321492444%positive,2);(294471769843%positive,3);(79522097303043128783%positive,3)]]
  | StC => []
  | StD => [HRank [(1206126651622717%positive,0);(4970253216930845688%positive,1);(310624627321492444%positive,0);(5425837239289092645320893%positive,0);(22198068690745280788138548472%positive,1)]]
  end.

Lemma cqh_h_00087 : iqh tmq_h_00087.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00087 StC 2 4 2 27 20000
                lsetq_h_00087 rsetq_h_00087 certq_h_00087 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 27) 2000 tmq_h_00087); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00088 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StA)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00088 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00088 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S1,[(StA,S1);(StC,S1)])];
   [(S1,[(StA,S1);(StC,S1)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition certq_h_00088 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 48 [(349537950172698542%positive,0);(21846121564329902%positive,0);(314652163455309742%positive,4);(349537949417722607%positive,4);(356852788752799647%positive,4);(321826196582552507%positive,3);(5445141436191%positive,4);(349537949417723822%positive,0);(75791334364922%positive,2);(321826196582921147%positive,1);(1212666493260527%positive,4);(356852788753168287%positive,4);(4709410501563%positive,1);(314652164210284282%positive,4);(75791334363887%positive,4);(321809154152691615%positive,4);(1212665738286842%positive,2);(19665759941678842%positive,4);(1172076690%positive,4);(1212666493261562%positive,2);(314652164210283247%positive,4);(4709410132923%positive,3);(321809154152322975%positive,4);(1212665738285807%positive,4);(19665759941677807%positive,4);(349537949417723642%positive,2);(349537950172698362%positive,2);(314652163455309562%positive,4);(75791334365102%positive,0);(21846121564329722%positive,2);(4910418007839%positive,4);(314652164210284462%positive,4);(349537950172697327%positive,4);(314652163455308527%positive,4);(1212665738287022%positive,0);(21846121564328687%positive,4);(19665759941679022%positive,4);(1212666493261742%positive,0);(300075682094%positive,4)] [349537950172698542%positive;349537949417722607%positive;314652163455309742%positive;21846121564329902%positive;356852788752799647%positive;321826196582552507%positive;5445141436191%positive;349537949417723822%positive;75791334364922%positive;321826196582921147%positive;1212666493260527%positive;4709410501563%positive;314652164210284282%positive;75791334363887%positive;321809154152691615%positive;1212665738286842%positive;19665759941678842%positive;1172076690%positive;1212666493261562%positive;314652164210283247%positive;4709410132923%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;349537949417723642%positive;349537950172698362%positive;314652163455309562%positive;75791334365102%positive;21846121564329722%positive;4910418007839%positive;314652164210284462%positive;349537950172697327%positive;1212666493261742%positive;314652163455308527%positive;1212665738287022%positive;21846121564328687%positive;19665759941679022%positive;356852788753168287%positive;300075682094%positive]]
  | StC => [HMeas MRight 48 [(78566688125433%positive,1);(349537949417722607%positive,1);(356852788752799647%positive,1);(321826196582552507%positive,0);(321809154152690169%positive,1);(5445141436191%positive,1);(321826196582921147%positive,1);(321809154152321529%positive,1);(1212666493260527%positive,1);(356852788753168287%positive,1);(4709410501563%positive,1);(75791334363887%positive,1);(21270083729%positive,1);(321809154152691615%positive,1);(314652164210283247%positive,1);(4709410132923%positive,0);(87122262979065%positive,1);(321809154152322975%positive,1);(1212665738285807%positive,1);(19665759941677807%positive,1);(4910418007839%positive,1);(356852788753166841%positive,1);(349537950172697327%positive,1);(314652163455308527%positive,1);(21846121564328687%positive,1);(356852788752798201%positive,1)] [349537949417722607%positive;78566688125433%positive;356852788752799647%positive;321826196582552507%positive;321809154152690169%positive;5445141436191%positive;321826196582921147%positive;321809154152321529%positive;1212666493260527%positive;4709410501563%positive;75791334363887%positive;21270083729%positive;321809154152691615%positive;314652164210283247%positive;4709410132923%positive;87122262979065%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;356852788753166841%positive;4910418007839%positive;349537950172697327%positive;314652163455308527%positive;21846121564328687%positive;356852788752798201%positive;356852788753168287%positive]]
  | StD => [HMeas MLeft 48 [(349537950172698542%positive,2);(21846121564329902%positive,2);(314652163455309742%positive,2);(78566688125433%positive,1);(321809154152690169%positive,1);(349537949417723822%positive,2);(75791334364922%positive,2);(321809154152321529%positive,1);(314652164210284282%positive,0);(21270083729%positive,1);(1212665738286842%positive,2);(19665759941678842%positive,0);(1172076690%positive,0);(1212666493261562%positive,2);(87122262979065%positive,1);(349537949417723642%positive,2);(349537950172698362%positive,2);(314652163455309562%positive,0);(75791334365102%positive,2);(21846121564329722%positive,2);(356852788753166841%positive,1);(314652164210284462%positive,2);(1212665738287022%positive,2);(19665759941679022%positive,2);(356852788752798201%positive,1);(1212666493261742%positive,2);(300075682094%positive,2)] [349537950172698542%positive;21846121564329902%positive;314652163455309742%positive;78566688125433%positive;321809154152690169%positive;349537949417723822%positive;75791334364922%positive;321809154152321529%positive;314652164210284282%positive;21270083729%positive;1212665738286842%positive;19665759941678842%positive;1172076690%positive;1212666493261562%positive;87122262979065%positive;349537950172698362%positive;314652163455309562%positive;75791334365102%positive;21846121564329722%positive;356852788753166841%positive;314652164210284462%positive;1212666493261742%positive;1212665738287022%positive;19665759941679022%positive;356852788752798201%positive;349537949417723642%positive;300075682094%positive]]
  end.

Lemma cqh_h_00088 : iqh tmq_h_00088.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00088 StA 9 2 2 34 20000
                lsetq_h_00088 rsetq_h_00088 certq_h_00088 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00088); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00089 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Definition lsetq_h_00089 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition rsetq_h_00089 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition certq_h_00089 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MRight 37 [(314652163455309742%positive,4);(356852788752799647%positive,4);(5445141436191%positive,4);(75791334364922%positive,2);(1212666493260527%positive,4);(4709410501563%positive,1);(356852788753168287%positive,4);(314652164210284282%positive,4);(75791334363887%positive,4);(321809154152691615%positive,4);(1212665738286842%positive,2);(1172076690%positive,4);(19665759941678842%positive,4);(1212666493261562%positive,2);(314652164210283247%positive,4);(4709410132923%positive,3);(321809154152322975%positive,4);(1212665738285807%positive,4);(19665759941677807%positive,4);(314652163455309562%positive,4);(75791334365102%positive,0);(4910418007839%positive,4);(314652164210284462%positive,4);(314652163455308527%positive,4);(1212665738287022%positive,0);(19665759941679022%positive,4);(1212666493261742%positive,0);(300075682094%positive,4)] [314652163455309742%positive;356852788752799647%positive;5445141436191%positive;75791334364922%positive;1212666493260527%positive;4709410501563%positive;314652164210284282%positive;75791334363887%positive;321809154152691615%positive;1212665738286842%positive;1172076690%positive;19665759941678842%positive;1212666493261562%positive;314652164210283247%positive;4709410132923%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;314652163455309562%positive;75791334365102%positive;4910418007839%positive;314652164210284462%positive;1212666493261742%positive;314652163455308527%positive;1212665738287022%positive;19665759941679022%positive;356852788753168287%positive;300075682094%positive]]
  | StC => [HMeas MRight 37 [(78566688125433%positive,1);(356852788752799647%positive,1);(321809154152690169%positive,1);(5445141436191%positive,1);(1212666493260527%positive,1);(321809154152321529%positive,1);(4709410501563%positive,1);(356852788753168287%positive,1);(75791334363887%positive,1);(21270083729%positive,1);(321809154152691615%positive,1);(314652164210283247%positive,1);(4709410132923%positive,0);(87122262979065%positive,1);(321809154152322975%positive,1);(1212665738285807%positive,1);(19665759941677807%positive,1);(356852788753166841%positive,1);(4910418007839%positive,1);(314652163455308527%positive,1);(356852788752798201%positive,1)] [78566688125433%positive;356852788752799647%positive;321809154152690169%positive;5445141436191%positive;1212666493260527%positive;321809154152321529%positive;4709410501563%positive;75791334363887%positive;21270083729%positive;321809154152691615%positive;314652164210283247%positive;4709410132923%positive;87122262979065%positive;321809154152322975%positive;1212665738285807%positive;19665759941677807%positive;356852788753166841%positive;4910418007839%positive;314652163455308527%positive;356852788752798201%positive;356852788753168287%positive]]
  | StD => [HMeas MLeft 37 [(314652163455309742%positive,2);(78566688125433%positive,1);(321809154152690169%positive,1);(75791334364922%positive,2);(321809154152321529%positive,1);(314652164210284282%positive,0);(21270083729%positive,1);(1212665738286842%positive,2);(1172076690%positive,0);(19665759941678842%positive,0);(1212666493261562%positive,2);(87122262979065%positive,1);(314652163455309562%positive,0);(75791334365102%positive,2);(356852788753166841%positive,1);(314652164210284462%positive,2);(1212665738287022%positive,2);(19665759941679022%positive,2);(356852788752798201%positive,1);(1212666493261742%positive,2);(300075682094%positive,2)] [314652163455309742%positive;78566688125433%positive;321809154152690169%positive;75791334364922%positive;321809154152321529%positive;314652164210284282%positive;21270083729%positive;1212665738286842%positive;1172076690%positive;19665759941678842%positive;1212666493261562%positive;87122262979065%positive;314652163455309562%positive;75791334365102%positive;356852788753166841%positive;314652164210284462%positive;1212665738287022%positive;19665759941679022%positive;356852788752798201%positive;1212666493261742%positive;300075682094%positive]]
  end.

Lemma cqh_h_00089 : iqh tmq_h_00089.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00089 StA 9 2 2 34 20000
                lsetq_h_00089 rsetq_h_00089 certq_h_00089 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00089); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00090 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StA)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S0 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00090 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition rsetq_h_00090 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition certq_h_00090 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 37 [(357411547841885946%positive,4);(351078360865895151%positive,4);(1396138856798126%positive,0);(306064359855454111%positive,4);(4670218605499%positive,1);(306064355677927327%positive,4);(76724903465711%positive,4);(357411547841884911%positive,4);(1150007538%positive,4);(351078360865896366%positive,4);(76724903466926%positive,0);(19641575789098746%positive,4);(4722827818783%positive,4);(294402117422%positive,4);(4722566723359%positive,4);(357411547841886126%positive,4);(19641575789097711%positive,4);(19641575789098926%positive,4);(1371399845172986%positive,2);(306067452231907231%positive,4);(306067448054380447%positive,4);(1396138856797946%positive,2);(1371399845171951%positive,4);(4670171419579%positive,3);(1396138856796911%positive,4);(351078360865896186%positive,4);(1371399845173166%positive,0);(76724903466746%positive,2)] [357411547841885946%positive;351078360865895151%positive;1396138856798126%positive;306064359855454111%positive;4670218605499%positive;306064355677927327%positive;76724903465711%positive;357411547841884911%positive;1150007538%positive;351078360865896366%positive;76724903466926%positive;19641575789098746%positive;4722827818783%positive;294402117422%positive;4722566723359%positive;357411547841886126%positive;19641575789097711%positive;19641575789098926%positive;1371399845172986%positive;306067452231907231%positive;306067448054380447%positive;1396138856797946%positive;1371399845171951%positive;4670171419579%positive;1396138856796911%positive;351078360865896186%positive;1371399845173166%positive;76724903466746%positive]]
  | StC => [HMeas MLeft 37 [(351078360865895151%positive,1);(306064359855454111%positive,1);(4670218605499%positive,1);(306064355677927327%positive,1);(76724903465711%positive,1);(357411547841884911%positive,1);(4722827818783%positive,1);(4722566723359%positive,1);(306067448054379001%positive,1);(18419783537%positive,1);(19641575789097711%positive,1);(306067452231905785%positive,1);(306067452231907231%positive,1);(306067448054380447%positive,1);(75561067573753%positive,1);(75565245100537%positive,1);(1371399845171951%positive,1);(4670171419579%positive,0);(306064355677925881%positive,1);(1396138856796911%positive,1);(306064359855452665%positive,1)] [351078360865895151%positive;306064359855454111%positive;4670218605499%positive;306064355677927327%positive;76724903465711%positive;357411547841884911%positive;4722827818783%positive;4722566723359%positive;306067448054379001%positive;18419783537%positive;19641575789097711%positive;306067452231905785%positive;306067452231907231%positive;306067448054380447%positive;75561067573753%positive;75565245100537%positive;1371399845171951%positive;4670171419579%positive;306064355677925881%positive;1396138856796911%positive;306064359855452665%positive]]
  | StD => [HMeas MRight 37 [(357411547841885946%positive,0);(1396138856798126%positive,2);(1150007538%positive,0);(351078360865896366%positive,2);(76724903466926%positive,2);(19641575789098746%positive,0);(294402117422%positive,2);(357411547841886126%positive,2);(306067448054379001%positive,1);(18419783537%positive,1);(306067452231905785%positive,1);(19641575789098926%positive,2);(1371399845172986%positive,2);(75561067573753%positive,1);(75565245100537%positive,1);(1396138856797946%positive,2);(306064355677925881%positive,1);(306064359855452665%positive,1);(351078360865896186%positive,0);(1371399845173166%positive,2);(76724903466746%positive,2)] [357411547841885946%positive;1396138856798126%positive;1150007538%positive;351078360865896366%positive;76724903466926%positive;19641575789098746%positive;294402117422%positive;357411547841886126%positive;306067448054379001%positive;18419783537%positive;306067452231905785%positive;19641575789098926%positive;1371399845172986%positive;75561067573753%positive;75565245100537%positive;1396138856797946%positive;306064355677925881%positive;351078360865896186%positive;306064359855452665%positive;1371399845173166%positive;76724903466746%positive]]
  end.

Lemma cqh_h_00090 : iqh tmq_h_00090.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00090 StA 9 2 2 34 20000
                lsetq_h_00090 rsetq_h_00090 certq_h_00090 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00090); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00091 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StB)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StA)
  | StC, S1 => Some (mkTrans S0 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StD)
  | StD, S1 => Some (mkTrans S1 DR StB)
  end.

Definition lsetq_h_00091 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StB,S1);(StB,S0);(StC,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StB,S0);(StC,S1);(StD,S1)]);(S1,[(StD,S0);(StC,S1);(StD,S1);(StD,S0)])]].

Definition rsetq_h_00091 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S0)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StD,S1);(StD,S1)]);(S1,[(StB,S0);(StC,S1);(StD,S1);(StB,S1)])]].

Definition certq_h_00091 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HRank [(5121400252161856676293087%positive,0);(19315842251812639%positive,0);(336666231129655607476438428159%positive,0);(91865338864502422595960479%positive,0);(92221282669268254699%positive,1);(22514964547406143%positive,0);(396087353015353860671596390911%positive,0);(376280314747900420265453545951%positive,0);(376280314747971008911956765151%positive,0);(396087430838708343138374033406%positive,1);(1401753406032447798975%positive,0);(81942401319767723897912991%positive,0);(376280427989074121697149714079%positive,0);(82193904084370949397801471%positive,0);(81942401249170281318489598%positive,1);(1401753827888430836734%positive,1);(82193923084213352343707646%positive,1);(81942401319758927821708798%positive,1);(79152975685779%positive,2);(96701013919746499494275583%positive,0);(376280427989003524254570290686%positive,1);(376280427989074112901073509886%positive,1);(5121400181573210173073887%positive,0);(4934250293338501630%positive,1);(336666308953010089943216070654%positive,1);(96701032919588902440181758%positive,1);(360239385426826238%positive,3)]]
  | StC => [HMeas MRight 45 [(336666308953010081147139915421%positive,1);(82193923084213487265775593%positive,0);(5121400252161856676293087%positive,1);(19315842251812639%positive,1);(4715781263345%positive,0);(376280427989074112856781348841%positive,0);(1263168066298580172445%positive,1);(336666231129655607476438428159%positive,1);(396087430838637745695794658973%positive,1);(22428061246214901252073%positive,0);(92221282669268254699%positive,0);(22514964547406143%positive,1);(396087353015353860671596390911%positive,1);(336666308953010089898672259049%positive,0);(1401753406032447798975%positive,1);(81942401319767723897912991%positive,1);(376280427989074121697149714079%positive,1);(376280314747900420265453545951%positive,1);(96701032919589037362249705%positive,0);(376280314747971008911956765151%positive,1);(78948004690632056809%positive,0);(79152975685779%positive,1);(81942401249170237026328553%positive,0);(396087430838708343093830221801%positive,0);(396087430838708334342297878173%positive,1);(91865338864502422595960479%positive,1);(81942401319758883529547753%positive,0);(82193904084370949397801471%positive,1);(336666308952939492500636696221%positive,1);(376280427989003524210278129641%positive,0);(5121400181573210173073887%positive,1);(96701013919746499494275583%positive,1)] [336666308953010081147139915421%positive;82193923084213487265775593%positive;5121400252161856676293087%positive;19315842251812639%positive;4715781263345%positive;376280427989074112856781348841%positive;1263168066298580172445%positive;336666231129655607476438428159%positive;396087430838637745695794658973%positive;22428061246214901252073%positive;92221282669268254699%positive;22514964547406143%positive;396087353015353860671596390911%positive;336666308953010089898672259049%positive;1401753406032447798975%positive;81942401319767723897912991%positive;376280427989074121697149714079%positive;376280314747900420265453545951%positive;96701032919589037362249705%positive;376280314747971008911956765151%positive;78948004690632056809%positive;79152975685779%positive;5121400181573210173073887%positive;81942401249170237026328553%positive;396087430838708343093830221801%positive;396087430838708334342297878173%positive;91865338864502422595960479%positive;81942401319758883529547753%positive;82193904084370949397801471%positive;336666308952939492500636696221%positive;376280427989003524210278129641%positive;96701013919746499494275583%positive]]
  | StD => [HRank [(336666308953010081147139915421%positive,0);(1401753827888430836734%positive,0);(82193923084213487265775593%positive,1);(4934250293338501630%positive,0);(4715781263345%positive,1);(396087430838708343138374033406%positive,0);(376280427989074112856781348841%positive,1);(1263168066298580172445%positive,0);(396087430838637745695794658973%positive,0);(360239385426826238%positive,0);(22428061246214901252073%positive,1);(376280427989003524254570290686%positive,0);(376280427989074112901073509886%positive,0);(336666308953010089898672259049%positive,1);(81942401249170281318489598%positive,0);(96701032919589037362249705%positive,1);(82193923084213352343707646%positive,0);(81942401319758927821708798%positive,0);(78948004690632056809%positive,1);(81942401249170237026328553%positive,1);(396087430838708343093830221801%positive,1);(396087430838708334342297878173%positive,0);(336666308953010089943216070654%positive,0);(81942401319758883529547753%positive,1);(336666308952939492500636696221%positive,0);(96701032919588902440181758%positive,0);(376280427989003524210278129641%positive,1)]]
  end.

Lemma cqh_h_00091 : iqh tmq_h_00091.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00091 StA 3 4 2 28 20000
                lsetq_h_00091 rsetq_h_00091 certq_h_00091 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 28) 2000 tmq_h_00091); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00092 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StB)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StA)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S0 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Definition lsetq_h_00092 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StD,S1)]);(S1,[(StC,S1);(StC,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S0,[(StD,S0);(StD,S0)])];
   [(S1,[(StC,S1);(StC,S0)]);(S1,[(StB,S0);(StD,S1)])]].

Definition rsetq_h_00092 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S1);(StB,S0)]);(S0,[(StD,S1);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0)])];
   [(S0,[(StD,S1);(StB,S0)]);(S1,[(StC,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S1)]);(S0,[(StD,S1);(StB,S0)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S0)])]].

Definition certq_h_00092 (q:St) : list hcomp :=
  match q with
  | StA => []
  | StB => [HMeas MLeft 37 [(357411547841885946%positive,4);(351078360865895151%positive,4);(1396138856798126%positive,0);(306064359855454111%positive,4);(4670218605499%positive,1);(306064355677927327%positive,4);(76724903465711%positive,4);(357411547841884911%positive,4);(1150007538%positive,4);(351078360865896366%positive,4);(76724903466926%positive,0);(19641575789098746%positive,4);(4722827818783%positive,4);(294402117422%positive,4);(4722566723359%positive,4);(357411547841886126%positive,4);(19641575789097711%positive,4);(19641575789098926%positive,4);(1371399845172986%positive,2);(306067452231907231%positive,4);(306067448054380447%positive,4);(1396138856797946%positive,2);(1371399845171951%positive,4);(4670171419579%positive,3);(351078360865896186%positive,4);(1396138856796911%positive,4);(1371399845173166%positive,0);(76724903466746%positive,2)] [357411547841885946%positive;351078360865895151%positive;1396138856798126%positive;306064359855454111%positive;4670218605499%positive;306064355677927327%positive;76724903465711%positive;357411547841884911%positive;1150007538%positive;351078360865896366%positive;76724903466926%positive;19641575789098746%positive;4722827818783%positive;294402117422%positive;4722566723359%positive;357411547841886126%positive;19641575789097711%positive;19641575789098926%positive;1371399845172986%positive;306067452231907231%positive;306067448054380447%positive;1396138856797946%positive;1371399845171951%positive;4670171419579%positive;351078360865896186%positive;1396138856796911%positive;1371399845173166%positive;76724903466746%positive]]
  | StC => [HMeas MLeft 37 [(351078360865895151%positive,1);(306064359855454111%positive,1);(4670218605499%positive,1);(306064355677927327%positive,1);(76724903465711%positive,1);(357411547841884911%positive,1);(4722827818783%positive,1);(4722566723359%positive,1);(306067448054379001%positive,1);(18419783537%positive,1);(19641575789097711%positive,1);(306067452231905785%positive,1);(306067452231907231%positive,1);(306067448054380447%positive,1);(75561067573753%positive,1);(75565245100537%positive,1);(1371399845171951%positive,1);(4670171419579%positive,0);(306064355677925881%positive,1);(306064359855452665%positive,1);(1396138856796911%positive,1)] [351078360865895151%positive;306064359855454111%positive;4670218605499%positive;306064355677927327%positive;76724903465711%positive;357411547841884911%positive;4722827818783%positive;4722566723359%positive;306067448054379001%positive;18419783537%positive;19641575789097711%positive;306067452231905785%positive;306067452231907231%positive;306067448054380447%positive;75561067573753%positive;75565245100537%positive;1371399845171951%positive;4670171419579%positive;306064355677925881%positive;1396138856796911%positive;306064359855452665%positive]]
  | StD => [HMeas MRight 37 [(357411547841885946%positive,0);(1396138856798126%positive,2);(1150007538%positive,0);(351078360865896366%positive,2);(76724903466926%positive,2);(19641575789098746%positive,0);(294402117422%positive,2);(357411547841886126%positive,2);(306067448054379001%positive,1);(18419783537%positive,1);(306067452231905785%positive,1);(19641575789098926%positive,2);(1371399845172986%positive,2);(75561067573753%positive,1);(75565245100537%positive,1);(1396138856797946%positive,2);(306064355677925881%positive,1);(351078360865896186%positive,0);(306064359855452665%positive,1);(1371399845173166%positive,2);(76724903466746%positive,2)] [357411547841885946%positive;1396138856798126%positive;1150007538%positive;351078360865896366%positive;76724903466926%positive;19641575789098746%positive;294402117422%positive;357411547841886126%positive;306067448054379001%positive;18419783537%positive;306067452231905785%positive;19641575789098926%positive;1371399845172986%positive;75561067573753%positive;75565245100537%positive;1396138856797946%positive;306064355677925881%positive;351078360865896186%positive;306064359855452665%positive;1371399845173166%positive;76724903466746%positive]]
  end.

Lemma cqh_h_00092 : iqh tmq_h_00092.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00092 StA 9 2 2 34 20000
                lsetq_h_00092 rsetq_h_00092 certq_h_00092 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 34) 2000 tmq_h_00092); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00093 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StC)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DR StA)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Definition lsetq_h_00093 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0)]);(S0,[])]].

Definition rsetq_h_00093 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S1)]);(S0,[(StC,S1);(StD,S1)])];
   [(S0,[(StC,S1);(StD,S1)]);(S1,[(StC,S0);(StB,S0)])];
   [(S0,[(StC,S1);(StD,S1)]);(S1,[(StC,S0);(StC,S1)])];
   [(S1,[(StC,S0);(StB,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S1)]);(S1,[(StC,S0);(StC,S1)])]].

Definition certq_h_00093 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(19860994195%positive,0);(332276926778%positive,1);(87779124564687%positive,2);(18962154155046122%positive,3);(19819051155%positive,0);(342879799610%positive,1);(85066030633678%positive,2);(22471455968490750%positive,3);(21776903922152682%positive,3)]]
  | StB => []
  | StC => [HRank [(85062893294508%positive,0);(87777228739500%positive,0);(19819051155%positive,1);(19860994195%positive,1);(87779124564687%positive,0)]]
  | StD => [HRank [(342879799610%positive,0);(85066030633678%positive,1);(22471455968490750%positive,2);(85062893294508%positive,3);(21776903922152682%positive,0);(18962154155046122%positive,0);(87777228739500%positive,1);(332276926778%positive,0)]]
  end.

Lemma cqh_h_00093 : iqh tmq_h_00093.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00093 StB 1 2 2 26 20000
                lsetq_h_00093 rsetq_h_00093 certq_h_00093 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00093); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00094 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StC)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S0 DR StA)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Definition lsetq_h_00094 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StD,S1);(StA,S1);(StC,S0)]);(S1,[(StA,S1);(StC,S0);(StD,S0);(StC,S1)])];
   [(S0,[(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StC,S1);(StC,S0)]);(S0,[(StC,S1);(StD,S1);(StA,S1);(StC,S0)])];
   [(S0,[(StD,S0);(StC,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S1);(StC,S0);(StD,S0)])];
   [(S0,[(StD,S0);(StC,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S1);(StC,S0);(StD,S0);(StC,S1)])];
   [(S1,[(StA,S1);(StC,S0);(StD,S0)]);(S0,[(StD,S0)])];
   [(S1,[(StA,S1);(StC,S0);(StD,S0);(StC,S1)]);(S0,[(StD,S0);(StC,S1);(StD,S1);(StA,S1)])]].

Definition rsetq_h_00094 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StA,S1);(StC,S0)]);(S1,[(StC,S0)])]].

Definition certq_h_00094 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(21547646746469607060788137963%positive,0);(329592559599171151408826%positive,1);(309494104947282639%positive,2);(294401250930%positive,3);(4952181351617876715%positive,0);(4710303700818%positive,1);(19310633487430958%positive,2);(79232948558050569470%positive,3)]]
  | StB => []
  | StC => [HRank [(5273480953586813425085356%positive,0);(21547646746469607060788137963%positive,1);(1205837747412268%positive,0);(4952181351617876715%positive,1);(309494104947282639%positive,0)]]
  | StD => [HRank [(329592559599171151408826%positive,0);(294401250930%positive,0);(1205837747412268%positive,1);(4710303700818%positive,0);(19310633487430958%positive,1);(79232948558050569470%positive,2);(5273480953586813425085356%positive,3)]]
  end.

Lemma cqh_h_00094 : iqh tmq_h_00094.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00094 StB 1 4 2 26 20000
                lsetq_h_00094 rsetq_h_00094 certq_h_00094 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00094); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00095 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StC)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S0 DR StA)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Definition lsetq_h_00095 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0);(StC,S1)]);(S1,[(StA,S1);(StD,S1)])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StD,S0)]);(S1,[(StA,S1);(StD,S1)])];
   [(S1,[(StA,S1);(StD,S1)]);(S0,[(StD,S0);(StD,S0)])]].

Definition rsetq_h_00095 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])]].

Definition certq_h_00095 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(19654839503845051%positive,0);(75565448417999%positive,1);(18416047730%positive,2);(75561070129899%positive,0);(18420569938%positive,1);(294455600942%positive,2)]]
  | StB => []
  | StC => [HRank [(75565446845692%positive,0);(19654839503845051%positive,1);(75565448417999%positive,2);(294729243948%positive,0);(75561070129899%positive,1)]]
  | StD => [HRank [(18416047730%positive,0);(294729243948%positive,1);(18420569938%positive,0);(294455600942%positive,1);(75565446845692%positive,2)]]
  end.

Lemma cqh_h_00095 : iqh tmq_h_00095.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00095 StB 1 2 2 26 20000
                lsetq_h_00095 rsetq_h_00095 certq_h_00095 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00095); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00096 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StC)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DR StA)
  | StD, S1 => Some (mkTrans S0 DL StC)
  end.

Definition lsetq_h_00096 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StA,S1);(StC,S0)]);(S1,[(StD,S0);(StC,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1)]);(S1,[(StA,S1);(StC,S0)])]].

Definition rsetq_h_00096 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])]].

Definition certq_h_00096 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(19666662489224171%positive,0);(75560078234874%positive,1);(19654774019749566%positive,2);(75560079717071%positive,3);(75564305511147%positive,0);(18399598418%positive,1);(300089381867%positive,0);(295155225850%positive,1);(299907978942%positive,2);(295156708047%positive,3);(18416113266%positive,4);(294657812270%positive,2)]]
  | StB => []
  | StC => [HRank [(295156709292%positive,0);(75560079717071%positive,0);(294393700140%positive,0);(300089381867%positive,1);(75564305511147%positive,1);(75560079718316%positive,0);(295156708047%positive,0);(19666662489224171%positive,1)]]
  | StD => [HRank [(18399598418%positive,0);(294657812270%positive,1);(295156709292%positive,2);(75560078234874%positive,0);(19654774019749566%positive,1);(18416113266%positive,0);(294393700140%positive,1);(75560079718316%positive,2);(295155225850%positive,0);(299907978942%positive,1)]]
  end.

Lemma cqh_h_00096 : iqh tmq_h_00096.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00096 StB 1 2 2 26 20000
                lsetq_h_00096 rsetq_h_00096 certq_h_00096 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00096); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00097 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StC)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DR StA)
  | StD, S1 => Some (mkTrans S1 DL StA)
  end.

Definition lsetq_h_00097 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StD,S1)]);(S1,[(StA,S1);(StD,S0)])];
   [(S1,[(StA,S1);(StD,S0)]);(S0,[])];
   [(S1,[(StA,S1);(StD,S0)]);(S0,[(StC,S1);(StD,S1)])];
   [(S1,[(StD,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S1)])]].

Definition rsetq_h_00097 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])]].

Definition certq_h_00097 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(75561154073323%positive,0);(18421028690%positive,1);(294460847406%positive,2);(75565564327166%positive,3);(75565565866703%positive,0);(18416113266%positive,1)]]
  | StB => []
  | StC => [HRank [(294736584492%positive,0);(75561154073323%positive,1);(19654839587788476%positive,0);(75565565866703%positive,1)]]
  | StD => [HRank [(18421028690%positive,0);(294460847406%positive,1);(75565564327166%positive,2);(18416113266%positive,0);(294736584492%positive,1);(19654839587788476%positive,3)]]
  end.

Lemma cqh_h_00097 : iqh tmq_h_00097.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00097 StB 1 2 2 26 20000
                lsetq_h_00097 rsetq_h_00097 certq_h_00097 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00097); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00098 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StC)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DR StA)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Definition lsetq_h_00098 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StD,S1);(StA,S1);(StC,S0)]);(S1,[(StA,S1);(StD,S1);(StD,S0);(StC,S1)])];
   [(S1,[(StA,S1);(StD,S1);(StD,S0)]);(S1,[(StD,S0)])];
   [(S1,[(StA,S1);(StD,S1);(StD,S0);(StC,S1)]);(S1,[(StD,S0);(StC,S1);(StD,S1);(StA,S1)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StC,S1);(StC,S0)]);(S0,[(StC,S1);(StD,S1);(StA,S1);(StC,S0)])];
   [(S1,[(StD,S0);(StC,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S1);(StD,S1);(StD,S0)])];
   [(S1,[(StD,S0);(StC,S1);(StD,S1);(StA,S1)]);(S1,[(StA,S1);(StD,S1);(StD,S0);(StC,S1)])]].

Definition rsetq_h_00098 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StD,S1);(StA,S1);(StC,S0)]);(S1,[(StC,S0)])]].

Definition certq_h_00098 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(4952182726007411435%positive,0);(4710303700818%positive,1);(19310719386776878%positive,2);(21547646769528038253107793899%positive,0);(329592559621161383964351%positive,1);(309494104947290831%positive,2);(294401316466%positive,3);(79232948626811989246%positive,3)]]
  | StB => []
  | StC => [HRank [(5273480953938657148070908%positive,0);(21547646769528038253107793899%positive,1);(329592559621161383964351%positive,2);(309494104947290831%positive,3);(1205837747412780%positive,0);(4952182726007411435%positive,1)]]
  | StD => [HRank [(4710303700818%positive,0);(19310719386776878%positive,1);(79232948626811989246%positive,2);(5273480953938657148070908%positive,3);(294401316466%positive,0);(1205837747412780%positive,1)]]
  end.

Lemma cqh_h_00098 : iqh tmq_h_00098.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00098 StB 1 4 2 26 20000
                lsetq_h_00098 rsetq_h_00098 certq_h_00098 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00098); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition tmq_h_00099 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StC)
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DR StA)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Definition lsetq_h_00099 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0)]);(S0,[])]].

Definition rsetq_h_00099 : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S1)]);(S0,[(StC,S1);(StD,S1)])];
   [(S0,[(StC,S1);(StD,S1)]);(S1,[(StC,S0)])];
   [(S0,[(StC,S1);(StD,S1)]);(S1,[(StC,S0);(StC,S1)])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StC,S1)]);(S0,[(StC,S1);(StD,S1)])];
   [(S1,[(StD,S1);(StA,S1)]);(S1,[(StC,S0);(StC,S1)])]].

Definition certq_h_00099 (q:St) : list hcomp :=
  match q with
  | StA => [HRank [(19819051155%positive,0);(342879799610%positive,1);(85066030633678%positive,2);(22471455968490750%positive,3);(19860994195%positive,0);(332276926778%positive,1);(87779124564687%positive,2);(1229230622274794%positive,3);(21776903922152682%positive,3)]]
  | StB => []
  | StC => [HRank [(85062893294508%positive,0);(87777228739500%positive,0);(19819051155%positive,1);(19860994195%positive,1);(87779124564687%positive,0)]]
  | StD => [HRank [(342879799610%positive,0);(85066030633678%positive,1);(22471455968490750%positive,2);(85062893294508%positive,3);(1229230622274794%positive,0);(21776903922152682%positive,0);(87777228739500%positive,1);(332276926778%positive,0)]]
  end.

Lemma cqh_h_00099 : iqh tmq_h_00099.
Proof.
  unfold iqh.
  pose proof (ngramhist_check_qhbound_lex_sound tmq_h_00099 StB 1 2 2 26 20000
                lsetq_h_00099 rsetq_h_00099 certq_h_00099 ltac:(vm_compute; reflexivity))
    as (Hnh & Hb & Hqh).
  split; [exact Hnh | split;
    [ apply (qhbound_mono (S 26) 2000 tmq_h_00099); [lia | exact Hb] | exact Hqh ] ].
Qed.

Definition nghw_00 : list TM :=
  [tmq_h_00000;
   tmq_h_00001;
   tmq_h_00002;
   tmq_h_00003;
   tmq_h_00004;
   tmq_h_00005;
   tmq_h_00006;
   tmq_h_00007;
   tmq_h_00008;
   tmq_h_00009;
   tmq_h_00010;
   tmq_h_00011;
   tmq_h_00012;
   tmq_h_00013;
   tmq_h_00014;
   tmq_h_00015;
   tmq_h_00016;
   tmq_h_00017;
   tmq_h_00018;
   tmq_h_00019;
   tmq_h_00020;
   tmq_h_00021;
   tmq_h_00022;
   tmq_h_00023;
   tmq_h_00024;
   tmq_h_00025;
   tmq_h_00026;
   tmq_h_00027;
   tmq_h_00028;
   tmq_h_00029;
   tmq_h_00030;
   tmq_h_00031;
   tmq_h_00032;
   tmq_h_00033;
   tmq_h_00034;
   tmq_h_00035;
   tmq_h_00036;
   tmq_h_00037;
   tmq_h_00038;
   tmq_h_00039;
   tmq_h_00040;
   tmq_h_00041;
   tmq_h_00042;
   tmq_h_00043;
   tmq_h_00044;
   tmq_h_00045;
   tmq_h_00046;
   tmq_h_00047;
   tmq_h_00048;
   tmq_h_00049;
   tmq_h_00050;
   tmq_h_00051;
   tmq_h_00052;
   tmq_h_00053;
   tmq_h_00054;
   tmq_h_00055;
   tmq_h_00056;
   tmq_h_00057;
   tmq_h_00058;
   tmq_h_00059;
   tmq_h_00060;
   tmq_h_00061;
   tmq_h_00062;
   tmq_h_00063;
   tmq_h_00064;
   tmq_h_00065;
   tmq_h_00066;
   tmq_h_00067;
   tmq_h_00068;
   tmq_h_00069;
   tmq_h_00070;
   tmq_h_00071;
   tmq_h_00072;
   tmq_h_00073;
   tmq_h_00074;
   tmq_h_00075;
   tmq_h_00076;
   tmq_h_00077;
   tmq_h_00078;
   tmq_h_00079;
   tmq_h_00080;
   tmq_h_00081;
   tmq_h_00082;
   tmq_h_00083;
   tmq_h_00084;
   tmq_h_00085;
   tmq_h_00086;
   tmq_h_00087;
   tmq_h_00088;
   tmq_h_00089;
   tmq_h_00090;
   tmq_h_00091;
   tmq_h_00092;
   tmq_h_00093;
   tmq_h_00094;
   tmq_h_00095;
   tmq_h_00096;
   tmq_h_00097;
   tmq_h_00098;
   tmq_h_00099].

Lemma nghw_00_all : Forall iqh nghw_00.

Proof. unfold nghw_00. exact (Forall_cons _ cqh_h_00000 (Forall_cons _ cqh_h_00001 (Forall_cons _ cqh_h_00002 (Forall_cons _ cqh_h_00003 (Forall_cons _ cqh_h_00004 (Forall_cons _ cqh_h_00005 (Forall_cons _ cqh_h_00006 (Forall_cons _ cqh_h_00007 (Forall_cons _ cqh_h_00008 (Forall_cons _ cqh_h_00009 (Forall_cons _ cqh_h_00010 (Forall_cons _ cqh_h_00011 (Forall_cons _ cqh_h_00012 (Forall_cons _ cqh_h_00013 (Forall_cons _ cqh_h_00014 (Forall_cons _ cqh_h_00015 (Forall_cons _ cqh_h_00016 (Forall_cons _ cqh_h_00017 (Forall_cons _ cqh_h_00018 (Forall_cons _ cqh_h_00019 (Forall_cons _ cqh_h_00020 (Forall_cons _ cqh_h_00021 (Forall_cons _ cqh_h_00022 (Forall_cons _ cqh_h_00023 (Forall_cons _ cqh_h_00024 (Forall_cons _ cqh_h_00025 (Forall_cons _ cqh_h_00026 (Forall_cons _ cqh_h_00027 (Forall_cons _ cqh_h_00028 (Forall_cons _ cqh_h_00029 (Forall_cons _ cqh_h_00030 (Forall_cons _ cqh_h_00031 (Forall_cons _ cqh_h_00032 (Forall_cons _ cqh_h_00033 (Forall_cons _ cqh_h_00034 (Forall_cons _ cqh_h_00035 (Forall_cons _ cqh_h_00036 (Forall_cons _ cqh_h_00037 (Forall_cons _ cqh_h_00038 (Forall_cons _ cqh_h_00039 (Forall_cons _ cqh_h_00040 (Forall_cons _ cqh_h_00041 (Forall_cons _ cqh_h_00042 (Forall_cons _ cqh_h_00043 (Forall_cons _ cqh_h_00044 (Forall_cons _ cqh_h_00045 (Forall_cons _ cqh_h_00046 (Forall_cons _ cqh_h_00047 (Forall_cons _ cqh_h_00048 (Forall_cons _ cqh_h_00049 (Forall_cons _ cqh_h_00050 (Forall_cons _ cqh_h_00051 (Forall_cons _ cqh_h_00052 (Forall_cons _ cqh_h_00053 (Forall_cons _ cqh_h_00054 (Forall_cons _ cqh_h_00055 (Forall_cons _ cqh_h_00056 (Forall_cons _ cqh_h_00057 (Forall_cons _ cqh_h_00058 (Forall_cons _ cqh_h_00059 (Forall_cons _ cqh_h_00060 (Forall_cons _ cqh_h_00061 (Forall_cons _ cqh_h_00062 (Forall_cons _ cqh_h_00063 (Forall_cons _ cqh_h_00064 (Forall_cons _ cqh_h_00065 (Forall_cons _ cqh_h_00066 (Forall_cons _ cqh_h_00067 (Forall_cons _ cqh_h_00068 (Forall_cons _ cqh_h_00069 (Forall_cons _ cqh_h_00070 (Forall_cons _ cqh_h_00071 (Forall_cons _ cqh_h_00072 (Forall_cons _ cqh_h_00073 (Forall_cons _ cqh_h_00074 (Forall_cons _ cqh_h_00075 (Forall_cons _ cqh_h_00076 (Forall_cons _ cqh_h_00077 (Forall_cons _ cqh_h_00078 (Forall_cons _ cqh_h_00079 (Forall_cons _ cqh_h_00080 (Forall_cons _ cqh_h_00081 (Forall_cons _ cqh_h_00082 (Forall_cons _ cqh_h_00083 (Forall_cons _ cqh_h_00084 (Forall_cons _ cqh_h_00085 (Forall_cons _ cqh_h_00086 (Forall_cons _ cqh_h_00087 (Forall_cons _ cqh_h_00088 (Forall_cons _ cqh_h_00089 (Forall_cons _ cqh_h_00090 (Forall_cons _ cqh_h_00091 (Forall_cons _ cqh_h_00092 (Forall_cons _ cqh_h_00093 (Forall_cons _ cqh_h_00094 (Forall_cons _ cqh_h_00095 (Forall_cons _ cqh_h_00096 (Forall_cons _ cqh_h_00097 (Forall_cons _ cqh_h_00098 (Forall_cons _ cqh_h_00099 (Forall_nil iqh))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))). Qed.
