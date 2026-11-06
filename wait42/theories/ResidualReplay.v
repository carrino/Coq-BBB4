(** Source residual SHA256: 42b11b973e9628e12f40b3f7beb5d8976a797679d84c80a30d2a8d575a58a2c5. *)
(** Generated from deterministic hash-sample nominations. Every check below
    independently recomputes the seed, finite closure and quantitative ranks. *)
From Coq Require Import Arith Lia.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import TNF_QH.
From BBBWait42 Require Import Spec RepeatedWord.
(** Source residual index 217415; sample index 42; 1RB0RD_1RC0LB_0RD1RA_1LD1LB. *)
Definition residual_217415 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S1 DR StB)
| StA, S1 => Some (mkTrans S0 DR StD)
| StB, S0 => Some (mkTrans S1 DR StC)
| StB, S1 => Some (mkTrans S0 DL StB)
| StC, S0 => Some (mkTrans S0 DR StD)
| StC, S1 => Some (mkTrans S1 DR StA)
| StD, S0 => Some (mkTrans S1 DL StD)
| StD, S1 => Some (mkTrans S1 DL StB)
end.
Example residual_217415_checked : repwl_ranked_search residual_217415 4 2 64 0 538 266 = true.
Proof. native_compute. reflexivity. Qed.
Theorem residual_217415_completion : forall tm' B, 0 <= B -> TM_le residual_217415 tm' -> WindowBound tm' B 266.
Proof. intros tm' B HB Hle. eapply (repwl_ranked_search_completion residual_217415 4 2 64 0 538 266 B); [exact HB|exact residual_217415_checked|exact Hle]. Qed.
(** Source residual index 100501; sample index 75; 1RB1LB_0LC1RD_1RA1LA_0RB0RA. *)
Definition residual_100501 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S1 DR StB)
| StA, S1 => Some (mkTrans S1 DL StB)
| StB, S0 => Some (mkTrans S0 DL StC)
| StB, S1 => Some (mkTrans S1 DR StD)
| StC, S0 => Some (mkTrans S1 DR StA)
| StC, S1 => Some (mkTrans S1 DL StA)
| StD, S0 => Some (mkTrans S0 DR StB)
| StD, S1 => Some (mkTrans S0 DR StA)
end.
Example residual_100501_checked : repwl_ranked_search residual_100501 3 2 64 0 384 189 = true.
Proof. native_compute. reflexivity. Qed.
Theorem residual_100501_completion : forall tm' B, 0 <= B -> TM_le residual_100501 tm' -> WindowBound tm' B 189.
Proof. intros tm' B HB Hle. eapply (repwl_ranked_search_completion residual_100501 3 2 64 0 384 189 B); [exact HB|exact residual_100501_checked|exact Hle]. Qed.
(** Source residual index 9731; sample index 81; 0RB0LB_0LC1RD_1LA0RD_1RC1RC. *)
Definition residual_9731 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S0 DR StB)
| StA, S1 => Some (mkTrans S0 DL StB)
| StB, S0 => Some (mkTrans S0 DL StC)
| StB, S1 => Some (mkTrans S1 DR StD)
| StC, S0 => Some (mkTrans S1 DL StA)
| StC, S1 => Some (mkTrans S0 DR StD)
| StD, S0 => Some (mkTrans S1 DR StC)
| StD, S1 => Some (mkTrans S1 DR StC)
end.
Example residual_9731_checked : repwl_ranked_search residual_9731 3 2 64 0 1074 534 = true.
Proof. native_compute. reflexivity. Qed.
Theorem residual_9731_completion : forall tm' B, 0 <= B -> TM_le residual_9731 tm' -> WindowBound tm' B 534.
Proof. intros tm' B HB Hle. eapply (repwl_ranked_search_completion residual_9731 3 2 64 0 1074 534 B); [exact HB|exact residual_9731_checked|exact Hle]. Qed.
(** Source residual index 171511; sample index 98; 1RB0LD_0RC1RA_0LC1LA_0RA0LA. *)
Definition residual_171511 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S1 DR StB)
| StA, S1 => Some (mkTrans S0 DL StD)
| StB, S0 => Some (mkTrans S0 DR StC)
| StB, S1 => Some (mkTrans S1 DR StA)
| StC, S0 => Some (mkTrans S0 DL StC)
| StC, S1 => Some (mkTrans S1 DL StA)
| StD, S0 => Some (mkTrans S0 DR StA)
| StD, S1 => Some (mkTrans S0 DL StA)
end.
Example residual_171511_checked : repwl_ranked_search residual_171511 3 2 64 0 302 148 = true.
Proof. native_compute. reflexivity. Qed.
Theorem residual_171511_completion : forall tm' B, 0 <= B -> TM_le residual_171511 tm' -> WindowBound tm' B 148.
Proof. intros tm' B HB Hle. eapply (repwl_ranked_search_completion residual_171511 3 2 64 0 302 148 B); [exact HB|exact residual_171511_checked|exact Hle]. Qed.
(** Source residual index 110519; sample index 146; 1RB0LD_0LC0RA_1RD1LC_1LA1RA. *)
Definition residual_110519 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S1 DR StB)
| StA, S1 => Some (mkTrans S0 DL StD)
| StB, S0 => Some (mkTrans S0 DL StC)
| StB, S1 => Some (mkTrans S0 DR StA)
| StC, S0 => Some (mkTrans S1 DR StD)
| StC, S1 => Some (mkTrans S1 DL StC)
| StD, S0 => Some (mkTrans S1 DL StA)
| StD, S1 => Some (mkTrans S1 DR StA)
end.
Example residual_110519_checked : repwl_ranked_search residual_110519 3 2 64 0 654 324 = true.
Proof. native_compute. reflexivity. Qed.
Theorem residual_110519_completion : forall tm' B, 0 <= B -> TM_le residual_110519 tm' -> WindowBound tm' B 324.
Proof. intros tm' B HB Hle. eapply (repwl_ranked_search_completion residual_110519 3 2 64 0 654 324 B); [exact HB|exact residual_110519_checked|exact Hle]. Qed.
(** Source residual index 184440; sample index 148; 1RB0LA_0RC1LC_1RD1LA_1LA0RA. *)
Definition residual_184440 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S1 DR StB)
| StA, S1 => Some (mkTrans S0 DL StA)
| StB, S0 => Some (mkTrans S0 DR StC)
| StB, S1 => Some (mkTrans S1 DL StC)
| StC, S0 => Some (mkTrans S1 DR StD)
| StC, S1 => Some (mkTrans S1 DL StA)
| StD, S0 => Some (mkTrans S1 DL StA)
| StD, S1 => Some (mkTrans S0 DR StA)
end.
Example residual_184440_checked : repwl_ranked_search residual_184440 3 2 64 0 1486 740 = true.
Proof. native_compute. reflexivity. Qed.
Theorem residual_184440_completion : forall tm' B, 0 <= B -> TM_le residual_184440 tm' -> WindowBound tm' B 740.
Proof. intros tm' B HB Hle. eapply (repwl_ranked_search_completion residual_184440 3 2 64 0 1486 740 B); [exact HB|exact residual_184440_checked|exact Hle]. Qed.
(** Source residual index 66593; sample index 232; 1RB1LA_0LA1RC_0LA1RD_0RC0RC. *)
Definition residual_66593 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S1 DR StB)
| StA, S1 => Some (mkTrans S1 DL StA)
| StB, S0 => Some (mkTrans S0 DL StA)
| StB, S1 => Some (mkTrans S1 DR StC)
| StC, S0 => Some (mkTrans S0 DL StA)
| StC, S1 => Some (mkTrans S1 DR StD)
| StD, S0 => Some (mkTrans S0 DR StC)
| StD, S1 => Some (mkTrans S0 DR StC)
end.
Example residual_66593_checked : repwl_ranked_search residual_66593 3 2 64 0 542 268 = true.
Proof. native_compute. reflexivity. Qed.
Theorem residual_66593_completion : forall tm' B, 0 <= B -> TM_le residual_66593 tm' -> WindowBound tm' B 268.
Proof. intros tm' B HB Hle. eapply (repwl_ranked_search_completion residual_66593 3 2 64 0 542 268 B); [exact HB|exact residual_66593_checked|exact Hle]. Qed.
(** Source residual index 69624; sample index 249; 1RB1LC_0LA1RD_0RB0LD_1RB0LA. *)
Definition residual_69624 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S1 DR StB)
| StA, S1 => Some (mkTrans S1 DL StC)
| StB, S0 => Some (mkTrans S0 DL StA)
| StB, S1 => Some (mkTrans S1 DR StD)
| StC, S0 => Some (mkTrans S0 DR StB)
| StC, S1 => Some (mkTrans S0 DL StD)
| StD, S0 => Some (mkTrans S1 DR StB)
| StD, S1 => Some (mkTrans S0 DL StA)
end.
Example residual_69624_checked : repwl_ranked_search residual_69624 4 2 64 0 434 214 = true.
Proof. native_compute. reflexivity. Qed.
Theorem residual_69624_completion : forall tm' B, 0 <= B -> TM_le residual_69624 tm' -> WindowBound tm' B 214.
Proof. intros tm' B HB Hle. eapply (repwl_ranked_search_completion residual_69624 4 2 64 0 434 214 B); [exact HB|exact residual_69624_checked|exact Hle]. Qed.
(** Source residual index 204174; sample index 301; 1RB0LA_1RC0LD_1LC0RD_1RA1LA. *)
Definition residual_204174 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S1 DR StB)
| StA, S1 => Some (mkTrans S0 DL StA)
| StB, S0 => Some (mkTrans S1 DR StC)
| StB, S1 => Some (mkTrans S0 DL StD)
| StC, S0 => Some (mkTrans S1 DL StC)
| StC, S1 => Some (mkTrans S0 DR StD)
| StD, S0 => Some (mkTrans S1 DR StA)
| StD, S1 => Some (mkTrans S1 DL StA)
end.
Example residual_204174_checked : repwl_ranked_search residual_204174 4 2 64 0 554 274 = true.
Proof. native_compute. reflexivity. Qed.
Theorem residual_204174_completion : forall tm' B, 0 <= B -> TM_le residual_204174 tm' -> WindowBound tm' B 274.
Proof. intros tm' B HB Hle. eapply (repwl_ranked_search_completion residual_204174 4 2 64 0 554 274 B); [exact HB|exact residual_204174_checked|exact Hle]. Qed.
(** Source residual index 58659; sample index 329; 0RB1LC_1RC0RB_1LD0LA_1RB1LB. *)
Definition residual_58659 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S0 DR StB)
| StA, S1 => Some (mkTrans S1 DL StC)
| StB, S0 => Some (mkTrans S1 DR StC)
| StB, S1 => Some (mkTrans S0 DR StB)
| StC, S0 => Some (mkTrans S1 DL StD)
| StC, S1 => Some (mkTrans S0 DL StA)
| StD, S0 => Some (mkTrans S1 DR StB)
| StD, S1 => Some (mkTrans S1 DL StB)
end.
Example residual_58659_checked : repwl_ranked_search residual_58659 4 2 64 0 972 483 = true.
Proof. native_compute. reflexivity. Qed.
Theorem residual_58659_completion : forall tm' B, 0 <= B -> TM_le residual_58659 tm' -> WindowBound tm' B 483.
Proof. intros tm' B HB Hle. eapply (repwl_ranked_search_completion residual_58659 4 2 64 0 972 483 B); [exact HB|exact residual_58659_checked|exact Hle]. Qed.
(** Source residual index 95720; sample index 401; 1RB0LA_1LB0RC_1RD1LA_1LD0LC. *)
Definition residual_95720 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S1 DR StB)
| StA, S1 => Some (mkTrans S0 DL StA)
| StB, S0 => Some (mkTrans S1 DL StB)
| StB, S1 => Some (mkTrans S0 DR StC)
| StC, S0 => Some (mkTrans S1 DR StD)
| StC, S1 => Some (mkTrans S1 DL StA)
| StD, S0 => Some (mkTrans S1 DL StD)
| StD, S1 => Some (mkTrans S0 DL StC)
end.
Example residual_95720_checked : repwl_ranked_search residual_95720 4 2 64 0 786 390 = true.
Proof. native_compute. reflexivity. Qed.
Theorem residual_95720_completion : forall tm' B, 0 <= B -> TM_le residual_95720 tm' -> WindowBound tm' B 390.
Proof. intros tm' B HB Hle. eapply (repwl_ranked_search_completion residual_95720 4 2 64 0 786 390 B); [exact HB|exact residual_95720_checked|exact Hle]. Qed.
(** Source residual index 212079; sample index 430; 1RB1LA_1RC0RC_1LD0RD_0LA1RB. *)
Definition residual_212079 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S1 DR StB)
| StA, S1 => Some (mkTrans S1 DL StA)
| StB, S0 => Some (mkTrans S1 DR StC)
| StB, S1 => Some (mkTrans S0 DR StC)
| StC, S0 => Some (mkTrans S1 DL StD)
| StC, S1 => Some (mkTrans S0 DR StD)
| StD, S0 => Some (mkTrans S0 DL StA)
| StD, S1 => Some (mkTrans S1 DR StB)
end.
Example residual_212079_checked : repwl_ranked_search residual_212079 3 2 64 64 1418 706 = true.
Proof. native_compute. reflexivity. Qed.
Theorem residual_212079_completion : forall tm' B, 64 <= B -> TM_le residual_212079 tm' -> WindowBound tm' B 706.
Proof. intros tm' B HB Hle. eapply (repwl_ranked_search_completion residual_212079 3 2 64 64 1418 706 B); [exact HB|exact residual_212079_checked|exact Hle]. Qed.
(** Source residual index 164328; sample index 463; 1RB1LB_1LC0LB_0LA0RD_1RC1RD. *)
Definition residual_164328 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S1 DR StB)
| StA, S1 => Some (mkTrans S1 DL StB)
| StB, S0 => Some (mkTrans S1 DL StC)
| StB, S1 => Some (mkTrans S0 DL StB)
| StC, S0 => Some (mkTrans S0 DL StA)
| StC, S1 => Some (mkTrans S0 DR StD)
| StD, S0 => Some (mkTrans S1 DR StC)
| StD, S1 => Some (mkTrans S1 DR StD)
end.
Example residual_164328_checked : repwl_ranked_search residual_164328 4 2 64 0 540 267 = true.
Proof. native_compute. reflexivity. Qed.
Theorem residual_164328_completion : forall tm' B, 0 <= B -> TM_le residual_164328 tm' -> WindowBound tm' B 267.
Proof. intros tm' B HB Hle. eapply (repwl_ranked_search_completion residual_164328 4 2 64 0 540 267 B); [exact HB|exact residual_164328_checked|exact Hle]. Qed.
(** Source residual index 177808; sample index 490; 1RB0LD_0RC1RA_0LD1LA_1LD1LB. *)
Definition residual_177808 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S1 DR StB)
| StA, S1 => Some (mkTrans S0 DL StD)
| StB, S0 => Some (mkTrans S0 DR StC)
| StB, S1 => Some (mkTrans S1 DR StA)
| StC, S0 => Some (mkTrans S0 DL StD)
| StC, S1 => Some (mkTrans S1 DL StA)
| StD, S0 => Some (mkTrans S1 DL StD)
| StD, S1 => Some (mkTrans S1 DL StB)
end.
Example residual_177808_checked : repwl_ranked_search residual_177808 4 2 64 0 682 338 = true.
Proof. native_compute. reflexivity. Qed.
Theorem residual_177808_completion : forall tm' B, 0 <= B -> TM_le residual_177808 tm' -> WindowBound tm' B 338.
Proof. intros tm' B HB Hle. eapply (repwl_ranked_search_completion residual_177808 4 2 64 0 682 338 B); [exact HB|exact residual_177808_checked|exact Hle]. Qed.
(** Source residual index 21868; sample index 495; 0RB1RB_1LC0RC_1RA0LD_0LB0LC. *)
Definition residual_21868 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S0 DR StB)
| StA, S1 => Some (mkTrans S1 DR StB)
| StB, S0 => Some (mkTrans S1 DL StC)
| StB, S1 => Some (mkTrans S0 DR StC)
| StC, S0 => Some (mkTrans S1 DR StA)
| StC, S1 => Some (mkTrans S0 DL StD)
| StD, S0 => Some (mkTrans S0 DL StB)
| StD, S1 => Some (mkTrans S0 DL StC)
end.
Example residual_21868_checked : repwl_ranked_search residual_21868 4 2 64 0 786 390 = true.
Proof. native_compute. reflexivity. Qed.
Theorem residual_21868_completion : forall tm' B, 0 <= B -> TM_le residual_21868 tm' -> WindowBound tm' B 390.
Proof. intros tm' B HB Hle. eapply (repwl_ranked_search_completion residual_21868 4 2 64 0 786 390 B); [exact HB|exact residual_21868_checked|exact Hle]. Qed.
(** Source residual index 40788; sample index 547; 0RB1LB_0RC1LD_1LA1RC_1LB0LD. *)
Definition residual_40788 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S0 DR StB)
| StA, S1 => Some (mkTrans S1 DL StB)
| StB, S0 => Some (mkTrans S0 DR StC)
| StB, S1 => Some (mkTrans S1 DL StD)
| StC, S0 => Some (mkTrans S1 DL StA)
| StC, S1 => Some (mkTrans S1 DR StC)
| StD, S0 => Some (mkTrans S1 DL StB)
| StD, S1 => Some (mkTrans S0 DL StD)
end.
Example residual_40788_checked : repwl_ranked_search residual_40788 4 2 64 0 434 214 = true.
Proof. native_compute. reflexivity. Qed.
Theorem residual_40788_completion : forall tm' B, 0 <= B -> TM_le residual_40788 tm' -> WindowBound tm' B 214.
Proof. intros tm' B HB Hle. eapply (repwl_ranked_search_completion residual_40788 4 2 64 0 434 214 B); [exact HB|exact residual_40788_checked|exact Hle]. Qed.
