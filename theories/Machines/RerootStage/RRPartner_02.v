(** * RRPartner_02: 0RB1RC_0LC---_0LD0RA_1RA1LD never quasihalts, by RE-ROOT TRANSPORT.

    A0 writes the blank, so after a 1-step all-blank prefix this machine
    IS its re-root [TM_swap StA StD] started fresh (Census/Reroot.v).
    The re-root is (up to state swaps) the already-boarded
    never-quasihalter [1RB1LA_0RC1RD_0LD____0LA0RB], so no new machine analysis
    is needed: [neverqh_reroot] carries the partner theorem across the
    prefix, with the four [Visited] witnesses at steps [0, 1, 2, 3].
    Suggested by the bbchallenge community 0RB observation. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From BBB4.Census Require Import TNF_QH Decide Reroot.
From BBB4.Closeout Require Import CloseoutKit.
Require BBB4.Machines.Counters.NLAP_1RB1LA_0RC1RD_0LD____0LA0RB.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 0RB1RC_0LC---_0LD0RA_1RA1LD *)
Definition tm_0RB1RC_0LC_____0LD0RA_1RA1LD : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S0 DR StB
  | StA, S1 => mk S1 DR StC
  | StB, S0 => mk S0 DL StC
  | StB, S1 => None
  | StC, S0 => mk S0 DL StD
  | StC, S1 => mk S0 DR StA
  | StD, S0 => mk S1 DR StA
  | StD, S1 => mk S1 DL StD
  end.

Local Notation tm := tm_0RB1RC_0LC_____0LD0RA_1RA1LD.
Local Notation core := (TM_swap StA StD tm).

(** the four visit witnesses on the re-root, by [vm_compute] *)
Lemma rr_vis_A : VisitsAt core StA 0.
Proof.
  assert (E : csteps core 0 c0 = Some (StA, ([], S0, [])))
    by (vm_compute; reflexivity).
  eexists. split.
  - rewrite <- lift_c0. exact (csteps_lift core 0 c0 _ E).
  - reflexivity.
Qed.

Lemma rr_vis_D : VisitsAt core StD 1.
Proof.
  assert (E : csteps core 1 c0 = Some (StD, ([S1], S0, [])))
    by (vm_compute; reflexivity).
  eexists. split.
  - rewrite <- lift_c0. exact (csteps_lift core 1 c0 _ E).
  - reflexivity.
Qed.

Lemma rr_vis_B : VisitsAt core StB 2.
Proof.
  assert (E : csteps core 2 c0 = Some (StB, ([S0; S1], S0, [])))
    by (vm_compute; reflexivity).
  eexists. split.
  - rewrite <- lift_c0. exact (csteps_lift core 2 c0 _ E).
  - reflexivity.
Qed.

Lemma rr_vis_C : VisitsAt core StC 3.
Proof.
  assert (E : csteps core 3 c0 = Some (StC, ([S1], S0, [S0])))
    by (vm_compute; reflexivity).
  eexists. split.
  - rewrite <- lift_c0. exact (csteps_lift core 3 c0 _ E).
  - reflexivity.
Qed.

Theorem nqh_0RB1RC_0LC_____0LD0RA_1RA1LD : NeverQuasiHaltsSt tm.
Proof.
  apply (neverqh_reroot tm StD 3).
  - apply prefix_ok_sound. vm_compute. reflexivity.
  - apply (never_qh_unswap StC StD);
      [intro Hx; discriminate Hx | intro Hx; discriminate Hx |].
    apply (never_qh_unswap StB StC);
      [intro Hx; discriminate Hx | intro Hx; discriminate Hx |].
    assert (Heq : TM_swap StB StC (TM_swap StC StD core) = BBB4.Machines.Counters.NLAP_1RB1LA_0RC1RD_0LD____0LA0RB.tm_1RB1LA_0RC1RD_0LD____0LA0RB)
      by (apply tm_eqb_eq; vm_compute; reflexivity).
    rewrite Heq. exact BBB4.Machines.Counters.NLAP_1RB1LA_0RC1RD_0LD____0LA0RB.nqh_1RB1LA_0RC1RD_0LD____0LA0RB.
  - intro q. destruct q.
    + exists 0. exact rr_vis_A.
    + exists 2. exact rr_vis_B.
    + exists 3. exact rr_vis_C.
    + exists 1. exact rr_vis_D.
Qed.

Print Assumptions nqh_0RB1RC_0LC_____0LD0RA_1RA1LD.
