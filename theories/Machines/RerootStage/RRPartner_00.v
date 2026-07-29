(** * RRPartner_00: 0RB1LC_1LA1RB_0LD0LA_1RA0RA never quasihalts, by RE-ROOT TRANSPORT.

    A0 writes the blank, so after a 1-step all-blank prefix this machine
    IS its re-root [TM_swap StA StB] started fresh (Census/Reroot.v).
    The re-root is (up to mirror) the already-boarded
    never-quasihalter [1RB1LA_0LA1RC_0RD0RB_1LB0LB], so no new machine analysis
    is needed: [neverqh_reroot] carries the partner theorem across the
    prefix, with the four [Visited] witnesses at steps [0, 1, 5, 6].
    Suggested by the bbchallenge community 0RB observation. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From BBB4.Census Require Import TNF_QH Decide Reroot.
Require BBB4.Machines.Counters.NLAP_1RB1LA_0LA1RC_0RD0RB_1LB0LB.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 0RB1LC_1LA1RB_0LD0LA_1RA0RA *)
Definition tm_0RB1LC_1LA1RB_0LD0LA_1RA0RA : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S0 DR StB
  | StA, S1 => mk S1 DL StC
  | StB, S0 => mk S1 DL StA
  | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S0 DL StD
  | StC, S1 => mk S0 DL StA
  | StD, S0 => mk S1 DR StA
  | StD, S1 => mk S0 DR StA
  end.

Local Notation tm := tm_0RB1LC_1LA1RB_0LD0LA_1RA0RA.
Local Notation core := (TM_swap StA StB tm).

(** the four visit witnesses on the re-root, by [vm_compute] *)
Lemma rr_vis_A : VisitsAt core StA 0.
Proof.
  assert (E : csteps core 0 c0 = Some (StA, ([], S0, [])))
    by (vm_compute; reflexivity).
  eexists. split.
  - rewrite <- lift_c0. exact (csteps_lift core 0 c0 _ E).
  - reflexivity.
Qed.

Lemma rr_vis_B : VisitsAt core StB 1.
Proof.
  assert (E : csteps core 1 c0 = Some (StB, ([], S0, [S1])))
    by (vm_compute; reflexivity).
  eexists. split.
  - rewrite <- lift_c0. exact (csteps_lift core 1 c0 _ E).
  - reflexivity.
Qed.

Lemma rr_vis_C : VisitsAt core StC 5.
Proof.
  assert (E : csteps core 5 c0 = Some (StC, ([], S0, [S1; S1])))
    by (vm_compute; reflexivity).
  eexists. split.
  - rewrite <- lift_c0. exact (csteps_lift core 5 c0 _ E).
  - reflexivity.
Qed.

Lemma rr_vis_D : VisitsAt core StD 6.
Proof.
  assert (E : csteps core 6 c0 = Some (StD, ([], S0, [S0; S1; S1])))
    by (vm_compute; reflexivity).
  eexists. split.
  - rewrite <- lift_c0. exact (csteps_lift core 6 c0 _ E).
  - reflexivity.
Qed.

Theorem nqh_0RB1LC_1LA1RB_0LD0LA_1RA0RA : NeverQuasiHaltsSt tm.
Proof.
  apply (neverqh_reroot tm StB 1).
  - apply prefix_ok_sound. vm_compute. reflexivity.
  - apply mirror_never_qh.
    assert (Heq : mirror_tm core = BBB4.Machines.Counters.NLAP_1RB1LA_0LA1RC_0RD0RB_1LB0LB.tm_1RB1LA_0LA1RC_0RD0RB_1LB0LB)
      by (apply tm_eqb_eq; vm_compute; reflexivity).
    rewrite Heq. exact BBB4.Machines.Counters.NLAP_1RB1LA_0LA1RC_0RD0RB_1LB0LB.nqh_1RB1LA_0LA1RC_0RD0RB_1LB0LB.
  - intro q. destruct q.
    + exists 0. exact rr_vis_A.
    + exists 1. exact rr_vis_B.
    + exists 5. exact rr_vis_C.
    + exists 6. exact rr_vis_D.
Qed.

Print Assumptions nqh_0RB1LC_1LA1RB_0LD0LA_1RA0RA.
