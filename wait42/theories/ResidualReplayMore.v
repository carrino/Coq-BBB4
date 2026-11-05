(** Source residual SHA256: 42b11b973e9628e12f40b3f7beb5d8976a797679d84c80a30d2a8d575a58a2c5. *)
(** Generated from deterministic hash-sample nominations. Every check below
    independently recomputes the seed, finite closure and quantitative ranks. *)
From Coq Require Import Arith Lia.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import TNF_QH.
From BBBWait42 Require Import Spec RepeatedWord.
(** Source residual index 184475; sample index 553; 1RB0LA_0RC0LD_1RD1LD_1LA1RB. *)
Definition residual_184475 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S1 DR StB)
| StA, S1 => Some (mkTrans S0 DL StA)
| StB, S0 => Some (mkTrans S0 DR StC)
| StB, S1 => Some (mkTrans S0 DL StD)
| StC, S0 => Some (mkTrans S1 DR StD)
| StC, S1 => Some (mkTrans S1 DL StD)
| StD, S0 => Some (mkTrans S1 DL StA)
| StD, S1 => Some (mkTrans S1 DR StB)
end.
Example residual_184475_checked : repwl_ranked_search residual_184475 3 2 64 0 1286 640 = true.
Proof. native_compute. reflexivity. Qed.
Theorem residual_184475_completion : forall tm' B, 0 <= B -> TM_le residual_184475 tm' -> WindowBound tm' B 640.
Proof. intros tm' B HB Hle. eapply (repwl_ranked_search_completion residual_184475 3 2 64 0 1286 640 B); [exact HB|exact residual_184475_checked|exact Hle]. Qed.
(** Source residual index 163817; sample index 712; 1RB0LA_1LC0RC_0LA0RD_1LA1LD. *)
Definition residual_163817 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S1 DR StB)
| StA, S1 => Some (mkTrans S0 DL StA)
| StB, S0 => Some (mkTrans S1 DL StC)
| StB, S1 => Some (mkTrans S0 DR StC)
| StC, S0 => Some (mkTrans S0 DL StA)
| StC, S1 => Some (mkTrans S0 DR StD)
| StD, S0 => Some (mkTrans S1 DL StA)
| StD, S1 => Some (mkTrans S1 DL StD)
end.
Example residual_163817_checked : repwl_ranked_search residual_163817 3 2 64 0 726 360 = true.
Proof. native_compute. reflexivity. Qed.
Theorem residual_163817_completion : forall tm' B, 0 <= B -> TM_le residual_163817 tm' -> WindowBound tm' B 360.
Proof. intros tm' B HB Hle. eapply (repwl_ranked_search_completion residual_163817 3 2 64 0 726 360 B); [exact HB|exact residual_163817_checked|exact Hle]. Qed.
(** Source residual index 16439; sample index 758; 0RB1RD_1LC1RA_1LA0RB_1LC0LD. *)
Definition residual_16439 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S0 DR StB)
| StA, S1 => Some (mkTrans S1 DR StD)
| StB, S0 => Some (mkTrans S1 DL StC)
| StB, S1 => Some (mkTrans S1 DR StA)
| StC, S0 => Some (mkTrans S1 DL StA)
| StC, S1 => Some (mkTrans S0 DR StB)
| StD, S0 => Some (mkTrans S1 DL StC)
| StD, S1 => Some (mkTrans S0 DL StD)
end.
Example residual_16439_checked : repwl_ranked_search residual_16439 4 2 64 0 1748 871 = true.
Proof. native_compute. reflexivity. Qed.
Theorem residual_16439_completion : forall tm' B, 0 <= B -> TM_le residual_16439 tm' -> WindowBound tm' B 871.
Proof. intros tm' B HB Hle. eapply (repwl_ranked_search_completion residual_16439 4 2 64 0 1748 871 B); [exact HB|exact residual_16439_checked|exact Hle]. Qed.
(** Source residual index 186886; sample index 835; 1RB1LA_1RC1RC_0LA0RD_1RC0RA. *)
Definition residual_186886 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S1 DR StB)
| StA, S1 => Some (mkTrans S1 DL StA)
| StB, S0 => Some (mkTrans S1 DR StC)
| StB, S1 => Some (mkTrans S1 DR StC)
| StC, S0 => Some (mkTrans S0 DL StA)
| StC, S1 => Some (mkTrans S0 DR StD)
| StD, S0 => Some (mkTrans S1 DR StC)
| StD, S1 => Some (mkTrans S0 DR StA)
end.
Example residual_186886_checked : repwl_ranked_search residual_186886 3 2 64 0 626 310 = true.
Proof. native_compute. reflexivity. Qed.
Theorem residual_186886_completion : forall tm' B, 0 <= B -> TM_le residual_186886 tm' -> WindowBound tm' B 310.
Proof. intros tm' B HB Hle. eapply (repwl_ranked_search_completion residual_186886 3 2 64 0 626 310 B); [exact HB|exact residual_186886_checked|exact Hle]. Qed.
(** Source residual index 158020; sample index 859; 1RB0RB_1LC1RA_0LD1LD_1RA1LB. *)
Definition residual_158020 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S1 DR StB)
| StA, S1 => Some (mkTrans S0 DR StB)
| StB, S0 => Some (mkTrans S1 DL StC)
| StB, S1 => Some (mkTrans S1 DR StA)
| StC, S0 => Some (mkTrans S0 DL StD)
| StC, S1 => Some (mkTrans S1 DL StD)
| StD, S0 => Some (mkTrans S1 DR StA)
| StD, S1 => Some (mkTrans S1 DL StB)
end.
Example residual_158020_checked : repwl_ranked_search residual_158020 3 2 64 0 342 168 = true.
Proof. native_compute. reflexivity. Qed.
Theorem residual_158020_completion : forall tm' B, 0 <= B -> TM_le residual_158020 tm' -> WindowBound tm' B 168.
Proof. intros tm' B HB Hle. eapply (repwl_ranked_search_completion residual_158020 3 2 64 0 342 168 B); [exact HB|exact residual_158020_checked|exact Hle]. Qed.
(** Source residual index 19734; sample index 863; 0RB0LB_1LC1RD_1LA1LD_1LB0RD. *)
Definition residual_19734 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S0 DR StB)
| StA, S1 => Some (mkTrans S0 DL StB)
| StB, S0 => Some (mkTrans S1 DL StC)
| StB, S1 => Some (mkTrans S1 DR StD)
| StC, S0 => Some (mkTrans S1 DL StA)
| StC, S1 => Some (mkTrans S1 DL StD)
| StD, S0 => Some (mkTrans S1 DL StB)
| StD, S1 => Some (mkTrans S0 DR StD)
end.
Example residual_19734_checked : repwl_ranked_search residual_19734 4 2 64 0 618 306 = true.
Proof. native_compute. reflexivity. Qed.
Theorem residual_19734_completion : forall tm' B, 0 <= B -> TM_le residual_19734 tm' -> WindowBound tm' B 306.
Proof. intros tm' B HB Hle. eapply (repwl_ranked_search_completion residual_19734 4 2 64 0 618 306 B); [exact HB|exact residual_19734_checked|exact Hle]. Qed.
(** Source residual index 91369; sample index 899; 1RB0LC_1LB1LA_1RC1RD_1LA0RD. *)
Definition residual_91369 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S1 DR StB)
| StA, S1 => Some (mkTrans S0 DL StC)
| StB, S0 => Some (mkTrans S1 DL StB)
| StB, S1 => Some (mkTrans S1 DL StA)
| StC, S0 => Some (mkTrans S1 DR StC)
| StC, S1 => Some (mkTrans S1 DR StD)
| StD, S0 => Some (mkTrans S1 DL StA)
| StD, S1 => Some (mkTrans S0 DR StD)
end.
Example residual_91369_checked : repwl_ranked_search residual_91369 4 2 64 0 624 309 = true.
Proof. native_compute. reflexivity. Qed.
Theorem residual_91369_completion : forall tm' B, 0 <= B -> TM_le residual_91369 tm' -> WindowBound tm' B 309.
Proof. intros tm' B HB Hle. eapply (repwl_ranked_search_completion residual_91369 4 2 64 0 624 309 B); [exact HB|exact residual_91369_checked|exact Hle]. Qed.
(** Source residual index 10170; sample index 940; 0RB0RD_0LC1RA_1RB1LC_0RA1RB. *)
Definition residual_10170 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S0 DR StB)
| StA, S1 => Some (mkTrans S0 DR StD)
| StB, S0 => Some (mkTrans S0 DL StC)
| StB, S1 => Some (mkTrans S1 DR StA)
| StC, S0 => Some (mkTrans S1 DR StB)
| StC, S1 => Some (mkTrans S1 DL StC)
| StD, S0 => Some (mkTrans S0 DR StA)
| StD, S1 => Some (mkTrans S1 DR StB)
end.
Example residual_10170_checked : repwl_ranked_search residual_10170 3 2 64 0 438 216 = true.
Proof. native_compute. reflexivity. Qed.
Theorem residual_10170_completion : forall tm' B, 0 <= B -> TM_le residual_10170 tm' -> WindowBound tm' B 216.
Proof. intros tm' B HB Hle. eapply (repwl_ranked_search_completion residual_10170 3 2 64 0 438 216 B); [exact HB|exact residual_10170_checked|exact Hle]. Qed.
(** Source residual index 119411; sample index 992; 1RB1LB_0LC0RC_1LA0RD_1LB1RC. *)
Definition residual_119411 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S1 DR StB)
| StA, S1 => Some (mkTrans S1 DL StB)
| StB, S0 => Some (mkTrans S0 DL StC)
| StB, S1 => Some (mkTrans S0 DR StC)
| StC, S0 => Some (mkTrans S1 DL StA)
| StC, S1 => Some (mkTrans S0 DR StD)
| StD, S0 => Some (mkTrans S1 DL StB)
| StD, S1 => Some (mkTrans S1 DR StC)
end.
Example residual_119411_checked : repwl_ranked_search residual_119411 4 2 64 0 1346 670 = true.
Proof. native_compute. reflexivity. Qed.
Theorem residual_119411_completion : forall tm' B, 0 <= B -> TM_le residual_119411 tm' -> WindowBound tm' B 670.
Proof. intros tm' B HB Hle. eapply (repwl_ranked_search_completion residual_119411 4 2 64 0 1346 670 B); [exact HB|exact residual_119411_checked|exact Hle]. Qed.
