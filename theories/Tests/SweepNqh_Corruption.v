(** * Tests/SweepNqh_Corruption: negative controls for the never-QH
    sweep glue [SweepGlueNeverTr.sweep_nqh_check].

    The DN sweep counters (SCOPING_INSTR.md 7.4.SW) are boarded as
    [NeverQuasiHaltsTr] through a CYCLE of anchor families.  The two
    features that are new over [SweepGlueTr] get controls here, on a real
    two-family certificate (the block grows by one cell a round, its units
    are two cells, so the rounds alternate between [Rpost = [1]] and
    [Rpost = []]):

    - the GROWTH gate: the families must be listed so that family 0
      grows the block ([1 <= e_0 + d_0]).  The same certificate with the
      two families swapped (and every index renamed to match) is otherwise
      intact and must be rejected, since the reachability argument counts
      rounds of family 0;
    - the cross-family OUTER lap: a wrong grow step [d] must be rejected;
    - the inner lap's SIDE ([f_behind]): the same chain read as the other
      kind of lap must be rejected;
    - pinning a LIVE instruction (the pins are claimed never to fire) must
      be rejected, as must an empty fire list;
    - the unmirrored machine and a one-transition mutant must be rejected.

    Every control is closed by [vm_compute]; a regression that made the
    checker accept any of them BREAKS THIS FILE. *)

From Coq Require Import List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement Mirror.
From BBB4.Census Require Import Deferred_Defs.
From BBB4.Checkers Require Import LapDecider.
From BBB4.Counters Require Import SweepGlueNeverTr.
Import ListNotations.

(** 0RB1LA_1LC1RB_0RC1LD_0RA0LA ([CBT_SW_00]): the hole moves left, so
    the certificate is for the mirror *)
Definition tm_sw2 : TM := row_to_tm [t0RB;t1LA;t1LC;t1RB;t0RC;t1LD;t0RA;t0LA].

Definition fam0 : swfam :=
  mkF StB S0 [] [S1;S1] [] [] [S1;S1] [S1] false 1 0
      [(SWin 2); (SRotR 1); (SWin 1); (SCycR 2); (SWinR 2); (SCycL 2 0); (SWin 1); (SUnrotR 1)]
      []
      0 0 [(SWin 1); (SWinR 5); (SCycL 2 0); (SWinL 1); (SRotR 1); (SFoldR 1)] 0 1.

Definition fam1 : swfam :=
  mkF StB S0 [] [S1;S1] [] [] [S1;S1] [] false 1 1
      [(SWin 2); (SRotR 1); (SWin 1); (SCycR 2); (SWin 1); (SWinR 3); (SCycL 2 0); (SWin 1); (SRotR 1); (SFoldR 1)]
      [[(SWin 2); (SWinR 2)]]
      0 0 [(SWinR 6); (SCycL 2 0); (SWinL 1); (SUnrotR 1)] 0 0.

Definition fires_sw2 (a b : nat) : list (nat * bool * list lstep) :=
  [(a, false, [(SWin 2); (SRotR 1); (SWin 1); (SCycR 2); (SWinR 1)]);
   (a, false, [(SWin 2); (SRotR 1); (SWin 1)]); (a, false, []);
   (a, false, [(SWin 2); (SRotR 1); (SWin 1); (SCycR 2); (SWinR 2)]);
   (b, true, [(SWinR 1)]); (a, false, [(SWin 1)]);
   (a, true, [(SWin 1); (SWinR 1)]); (a, false, [(SWin 2)])].

Definition w_sw2 : swncert := mkSWN [] [fam0; fam1] 0 (fires_sw2 0 1) 1 1 0 0.

(** positive control: the certificate the batch uses *)
Example sw2_ok : sweep_nqh_check (mirror_tm tm_sw2) w_sw2 = true.
Proof. vm_compute. reflexivity. Qed.

(** the growth gate: family 0 no longer grows the block *)
Example sw2_swapped : sweep_nqh_check (mirror_tm tm_sw2)
  (mkSWN [] [fam1; fam0] 0 (fires_sw2 1 0) 1 0 0 0) = false.
Proof. vm_compute. reflexivity. Qed.

(** a wrong grow step on the cross-family outer lap *)
Example sw2_bad_d : sweep_nqh_check (mirror_tm tm_sw2)
  (mkSWN [] [fam0; mkF (f_q fam1) (f_h fam1) (f_Lpre fam1) (f_uL fam1)
                       (f_Lpost fam1) (f_Rpre fam1) (f_uR fam1) (f_Rpost fam1)
                       (f_behind fam1) (f_na fam1) (f_nb fam1) (f_chi fam1)
                       (f_base fam1) (f_ma fam1) (f_mb fam1) (f_cho fam1) 0 1]
         0 (fires_sw2 0 1) 1 1 0 0) = false.
Proof. vm_compute. reflexivity. Qed.

(** the ahead inner lap read as a behind one *)
Example sw2_behind : sweep_nqh_check (mirror_tm tm_sw2)
  (mkSWN [] [mkF (f_q fam0) (f_h fam0) (f_Lpre fam0) (f_uL fam0)
                 (f_Lpost fam0) (f_Rpre fam0) (f_uR fam0) (f_Rpost fam0)
                 true (f_na fam0) (f_nb fam0) (f_chi fam0)
                 (f_base fam0) (f_ma fam0) (f_mb fam0) (f_cho fam0) 0 1; fam1]
         0 (fires_sw2 0 1) 1 1 0 0) = false.
Proof. vm_compute. reflexivity. Qed.

(** a live instruction claimed never to fire *)
Example sw2_pin_live : sweep_nqh_check (mirror_tm tm_sw2)
  (mkSWN [(StA, S0)] [fam0; fam1] 0 (fires_sw2 0 1) 1 1 0 0) = false.
Proof. vm_compute. reflexivity. Qed.

(** no fire witnesses *)
Example sw2_no_fires : sweep_nqh_check (mirror_tm tm_sw2)
  (mkSWN [] [fam0; fam1] 0 [] 1 1 0 0) = false.
Proof. vm_compute. reflexivity. Qed.

(** the machine itself, not its mirror *)
Example sw2_unmirrored : sweep_nqh_check tm_sw2 w_sw2 = false.
Proof. vm_compute. reflexivity. Qed.

(** a one-transition mutant (D1: 0LA -> 1LA) *)
Example sw2_mutant : sweep_nqh_check
  (mirror_tm (row_to_tm [t0RB;t1LA;t1LC;t1RB;t0RC;t1LD;t0RA;t1LA])) w_sw2 = false.
Proof. vm_compute. reflexivity. Qed.
