(* wave-6 NGramHist corruption tests -- MUST-fail controls.
   UNTRUSTED-generated; the Coq kernel re-checks every claim. *)
From Coq Require Import List ZArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import NGram NGramHist.
Import ListNotations.

Definition tm_counter : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StA)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => None
  | StD, S0 => Some (mkTrans S1 DR StA)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.
Definition tm_qh : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DR StC)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S0 DL StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.
Definition tm_halt : TM := fun q s =>
  match q, s with StA, S0 => Some (mkTrans S1 DR StB) | _, _ => None end.

Definition lset_c : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StA,S0);(StC,S0)]);(S0,[(StB,S1);(StD,S1)])];
   [(S0,[(StA,S0);(StC,S0)]);(S1,[(StD,S0)])];
   [(S0,[(StA,S0);(StC,S0)]);(S1,[(StD,S0);(StB,S1)])];
   [(S0,[(StB,S1);(StD,S1)]);(S0,[(StA,S0);(StC,S0)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1)]);(S0,[(StA,S0);(StC,S0)])]].
Definition rset_c : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S0);(StB,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StA,S0)]);(S0,[(StB,S0);(StB,S0)])];
   [(S0,[(StC,S0);(StA,S0)]);(S1,[(StD,S1);(StD,S0)])];
   [(S1,[(StD,S1);(StD,S0)]);(S0,[(StC,S0);(StA,S0)])]].
Definition lset_c_mut : hgset :=
  [[(S0,[(StA,S0);(StC,S0)]);(S0,[(StB,S1);(StD,S1)])];
   [(S0,[(StA,S0);(StC,S0)]);(S1,[(StD,S0)])];
   [(S0,[(StA,S0);(StC,S0)]);(S1,[(StD,S0);(StB,S1)])];
   [(S0,[(StB,S1);(StD,S1)]);(S0,[(StA,S0);(StC,S0)])];
   [(S1,[(StD,S0)]);(S0,[])];
   [(S1,[(StD,S0);(StB,S1)]);(S0,[(StA,S0);(StC,S0)])]].
Definition cert_c (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 35 [(17537431698%positive,1);(18916180841748443%positive,0);(4713451114905%positive,2);(324191733436142589%positive,2);(324191733436143039%positive,2);(294229279963533962%positive,1);(302658895452853245%positive,2);(302658895452853695%positive,2);(302658895452854235%positive,0);(20261983074145277%positive,2);(71833320288906%positive,1);(20261983074145727%positive,2);(294229279962428042%positive,1);(4715716039065%positive,2);(1207740563%positive,0);(20261983074146267%positive,0);(302658897717778395%positive,0);(324191731171218429%positive,2);(324191731171218879%positive,2);(18916180841747903%positive,2);(302658897717777405%positive,2);(302658897717777855%positive,2);(1203315127800458%positive,1);(324191731171219419%positive,0);(18916180841747453%positive,2);(1203315126694538%positive,1);(309173324095%positive,2);(324191733436143579%positive,0)] [17537431698%positive;18916180841748443%positive;4713451114905%positive;324191733436142589%positive;324191733436143039%positive;294229279963533962%positive;302658895452853245%positive;302658895452853695%positive;302658895452854235%positive;20261983074145277%positive;71833320288906%positive;20261983074145727%positive;294229279962428042%positive;4715716039065%positive;20261983074146267%positive;302658897717778395%positive;324191731171218429%positive;324191731171218879%positive;18916180841747903%positive;302658897717777405%positive;302658897717777855%positive;1203315127800458%positive;324191731171219419%positive;324191733436143579%positive;18916180841747453%positive;1203315126694538%positive;309173324095%positive;1207740563%positive]]
  | StB => [HMeas MLeft 35 [(17537431698%positive,37);(1203315127799976%positive,38);(18916180841748443%positive,37);(324191733436143039%positive,38);(294229279963533962%positive,37);(294229279962427560%positive,0);(302658895452853695%positive,38);(302658895452854235%positive,37);(71833320288906%positive,37);(20261983074145727%positive,38);(294229279962428042%positive,37);(1207740563%positive,36);(20261983074146267%positive,36);(302658897717778395%positive,37);(294229279963533480%positive,38);(324191731171218879%positive,38);(1203315126694056%positive,1);(18916180841747903%positive,38);(302658897717777855%positive,38);(1203315127800458%positive,38);(324191731171219419%positive,36);(4489582518056%positive,0);(1203315126694538%positive,38);(309173324095%positive,38);(324191733436143579%positive,36)] [17537431698%positive;1203315127799976%positive;18916180841748443%positive;324191733436143039%positive;294229279963533962%positive;294229279962427560%positive;302658895452853695%positive;302658895452854235%positive;71833320288906%positive;20261983074145727%positive;294229279962428042%positive;20261983074146267%positive;302658897717778395%positive;294229279963533480%positive;324191731171218879%positive;1203315126694056%positive;18916180841747903%positive;302658897717777855%positive;1203315127800458%positive;324191731171219419%positive;324191733436143579%positive;4489582518056%positive;1203315126694538%positive;309173324095%positive;1207740563%positive]]
  | StC => [HMeas MRight 35 [(1203315127799976%positive,1);(18916180841748443%positive,2);(4713451114905%positive,0);(324191733436142589%positive,2);(324191733436143039%positive,2);(294229279962427560%positive,1);(302658895452853245%positive,2);(302658895452853695%positive,2);(302658895452854235%positive,2);(20261983074145277%positive,2);(20261983074145727%positive,2);(4715716039065%positive,0);(1207740563%positive,2);(20261983074146267%positive,2);(302658897717778395%positive,2);(294229279963533480%positive,1);(324191731171218429%positive,2);(324191731171218879%positive,2);(1203315126694056%positive,1);(18916180841747903%positive,2);(302658897717777405%positive,2);(302658897717777855%positive,2);(324191731171219419%positive,2);(18916180841747453%positive,2);(4489582518056%positive,1);(309173324095%positive,2);(324191733436143579%positive,2)] [1203315127799976%positive;18916180841748443%positive;4713451114905%positive;324191733436142589%positive;324191733436143039%positive;294229279962427560%positive;302658895452853245%positive;302658895452853695%positive;302658895452854235%positive;20261983074145277%positive;20261983074145727%positive;4715716039065%positive;20261983074146267%positive;302658897717778395%positive;294229279963533480%positive;324191731171218429%positive;324191731171218879%positive;1203315126694056%positive;18916180841747903%positive;302658897717777405%positive;302658897717777855%positive;324191731171219419%positive;324191733436143579%positive;18916180841747453%positive;4489582518056%positive;309173324095%positive;1207740563%positive]]
  | StD => [HMeas MRight 35 [(17537431698%positive,3);(1203315127799976%positive,2);(4713451114905%positive,2);(324191733436142589%positive,3);(294229279963533962%positive,3);(294229279962427560%positive,3);(302658895452853245%positive,3);(20261983074145277%positive,3);(71833320288906%positive,3);(294229279962428042%positive,3);(4715716039065%positive,1);(294229279963533480%positive,2);(324191731171218429%positive,3);(1203315126694056%positive,3);(302658897717777405%positive,3);(1203315127800458%positive,0);(18916180841747453%positive,3);(4489582518056%positive,3);(1203315126694538%positive,1)] [17537431698%positive;1203315127799976%positive;4713451114905%positive;324191733436142589%positive;294229279963533962%positive;294229279962427560%positive;302658895452853245%positive;20261983074145277%positive;71833320288906%positive;294229279962428042%positive;4715716039065%positive;294229279963533480%positive;324191731171218429%positive;1203315126694056%positive;302658897717777405%positive;1203315127800458%positive;18916180841747453%positive;4489582518056%positive;1203315126694538%positive]]
  end.
Definition lset_qh : hgset :=
  [[(S0,[]);(S0,[])];
   [(S1,[(StC,S0)]);(S0,[])];
   [(S1,[(StC,S0);(StB,S0)]);(S1,[(StC,S0)])];
   [(S1,[(StC,S0);(StD,S0)]);(S1,[(StC,S0);(StB,S0)])];
   [(S1,[(StC,S0);(StD,S1)]);(S1,[(StC,S0);(StD,S0)])];
   [(S1,[(StC,S0);(StD,S1)]);(S1,[(StC,S0);(StD,S1)])]].
Definition rset_qh : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StD,S0)]);(S0,[(StD,S1);(StC,S0)])];
   [(S0,[(StD,S0);(StD,S0)]);(S0,[])];
   [(S0,[(StD,S1);(StC,S0)]);(S0,[(StD,S1);(StC,S0)])];
   [(S0,[(StD,S1);(StC,S0)]);(S1,[(StB,S1);(StC,S1)])];
   [(S1,[(StB,S1);(StC,S1)]);(S0,[(StD,S0);(StD,S0)])]].
(* --- Control 4: plain NGram MISSES; NGramHist CATCHES (history load-bearing) --- *)
Example ctl_plain_misses : ngram_check_neverqh tm_counter 2 40 100000 200 = false.
Proof. vm_compute. reflexivity. Qed.

Example ctl_hist_closes : ngramhist_closed tm_counter 2 2 40 100000 lset_c rset_c = true.
Proof. vm_compute. reflexivity. Qed.

Example ctl_hist_boards : ngramhist_check_neverqh_lex tm_counter 2 2 40 100000 lset_c rset_c cert_c = true.
Proof. vm_compute. reflexivity. Qed.

(* --- Control 1: quasihalter CLOSES (NonHalt) but never-QH REJECTS (the trap) --- *)
Example qh_closes : ngramhist_closed tm_qh 2 2 40 100000 lset_qh rset_qh = true.
Proof. vm_compute. reflexivity. Qed.

Example qh_rejected : ngramhist_check_neverqh_lex tm_qh 2 2 40 100000 lset_qh rset_qh (fun _ => []) = false.
Proof. vm_compute. reflexivity. Qed.

(* --- Control 2: halter rejected --- *)
Example halt_rejected : ngramhist_check_neverqh_lex tm_halt 2 2 40 100000 [] [] (fun _ => []) = false.
Proof. vm_compute. reflexivity. Qed.

(* --- Control 3: mutated closure (one window dropped) rejected --- *)
Example mut_rejected : ngramhist_check_neverqh_lex tm_counter 2 2 40 100000 lset_c_mut rset_c cert_c = false.
Proof. vm_compute. reflexivity. Qed.

