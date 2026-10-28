From Coq Require Import List NArith.
From BBB24 Require Import Statement StatementTr CTape Census WeightedCensus WeightedState.
Import ListNotations.

Definition ws_loop : TM := fun _ _ => Some (mkTrans S0 DR StA).
Definition ws_nodes : list cconf := [(StA,([S0],S0,[S0]))].
Definition ws_choose_zero (_:St) := S0.
Definition ws_no_certificate (_:Instr) : option WCert := None.

Example recurrent_instruction_suffices :
  ws_graph_check 0 ws_loop 1 0 ws_nodes ws_choose_zero ws_no_certificate = true.
Proof. vm_compute; reflexivity. Qed.
Example absent_instruction_is_not_a_recurrence_witness :
  ws_graph_check 0 ws_loop 1 0 ws_nodes (fun _=>S1) ws_no_certificate = false.
Proof. vm_compute; reflexivity. Qed.
Example missing_seed_rejected :
  ws_graph_check 0 ws_loop 1 0 [] ws_choose_zero ws_no_certificate = false.
Proof. vm_compute; reflexivity. Qed.
Example missing_successor_rejected :
  ws_graph_check 0 (fun _ _=>Some(mkTrans S0 DR StB)) 1 0
    ws_nodes ws_choose_zero ws_no_certificate = false.
Proof. vm_compute; reflexivity. Qed.
Example halt_rejected :
  ws_graph_check 0 empty 1 0 ws_nodes ws_choose_zero ws_no_certificate = false.
Proof. vm_compute; reflexivity. Qed.
Example late_prefix_rejected :
  ws_graph_check 0 ws_loop 1 1 ws_nodes ws_choose_zero ws_no_certificate = false.
Proof. vm_compute; reflexivity. Qed.
Example zero_width_rejected :
  ws_graph_check 0 ws_loop 0 0 ws_nodes ws_choose_zero ws_no_certificate = false.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions ws_graph_check_sound.
