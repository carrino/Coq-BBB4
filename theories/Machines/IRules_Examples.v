(** * IRules_Examples: inductive-rules machine theorems.

    Two geometric sweepers from the BBB harness's v1 [irules]
    certificate set (results/certs_irules), parameters straight from
    their certificates.  Each [vm_compute] validates the rules by
    fresh-variable replay, closes the symbolic meta-cycle
    [C(k) ->* C(a*k + b)], re-simulates the ~1.2M-step and ~1.8M-step
    prefixes to the anchors, and checks the prefix-visited states
    against the cycle's fired set (a few seconds each).

    - [tm_ir1] = 1RB1RD_1RC1RB_1LC1LA_0RC0RD
      template C(k) = [C] reading 0 with 1^k on the left; meta map
      k -> 3k + 1, kmin 3, anchor step 1,245,560 at k0 = 1822; one
      rule C(1^u | 1 | 1^w) ->* C(1^(u-1) | 1 | 1^(w+3)).  All eight
      transitions fire in the cycle: never quasihalts.

    - [tm_ir2] = 1RB0RC_0RC0RB_1LC1LD_1RA1RB
      template D(k) = [D] reading 0 with 1^k on the right; meta map
      k -> 3k, kmin 3, anchor step 1,799,057 at k0 = 2187; two rules.
      Its certificate claims transition-level quasihalting (A0 fires
      exactly once, at step 1), but at state level -- BBB proper --
      state A recurs through A1, so the machine never quasihalts:
      the checker's state-level classification covers claim-T
      certificates like this one uniformly. *)

From Coq Require Import ZArith List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta.
Import ListNotations.
Open Scope Z_scope.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** ** 1RB1RD_1RC1RB_1LC1LA_0RC0RD *)

Definition tm_ir1 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DR StD
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S1 DL StC | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S0 DR StC | StD, S1 => mk S0 DR StD
  end.

Definition cert_ir1 : IRCert := mkIRCert
  1245560%nat  (* anchor step *)
  1822         (* k0 *)
  3            (* kmin *)
  3 1          (* meta map k -> 3k + 1 *)
  StC S0       (* template state, head symbol *)
  [(S1, 1, 0)] (* left:  1^(1k+0) *)
  []           (* right: empty *)
  [mkRule StC S1 [(S1, RV (-1) 2)] [(S1, RV 3 1)]].

Theorem tm_ir1_never_quasihalts : NeverQuasiHaltsSt tm_ir1.
Proof.
  apply (irules_check_neverqh_sound tm_ir1 cert_ir1 300000).
  vm_compute. reflexivity.
Qed.

Theorem tm_ir1_nonhalt : NonHalt tm_ir1.
Proof. apply never_qh_nonhalt, tm_ir1_never_quasihalts. Qed.

(** ** 1RB0RC_0RC0RB_1LC1LD_1RA1RB *)

Definition tm_ir2 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DR StC
  | StB, S0 => mk S0 DR StC | StB, S1 => mk S0 DR StB
  | StC, S0 => mk S1 DL StC | StC, S1 => mk S1 DL StD
  | StD, S0 => mk S1 DR StA | StD, S1 => mk S1 DR StB
  end.

Definition cert_ir2 : IRCert := mkIRCert
  1799057%nat 2187 3 3 0 StD S0
  []
  [(S1, 1, 0)]
  [mkRule StA S1 [(S1, RV 1 1)] [(S1, RV (-1) 2)];
   mkRule StC S0 [(S0, RV 3 1); (S1, RV (-1) 3)] []].

Theorem tm_ir2_never_quasihalts : NeverQuasiHaltsSt tm_ir2.
Proof.
  apply (irules_check_neverqh_sound tm_ir2 cert_ir2 300000).
  vm_compute. reflexivity.
Qed.

Theorem tm_ir2_nonhalt : NonHalt tm_ir2.
Proof. apply never_qh_nonhalt, tm_ir2_never_quasihalts. Qed.
