(** * LadderLazyFib_Corruption: negative controls for the LAZY fibonacci ladder.

    BBB corruption-test tradition: every computable ingredient of
    [LadderCheck] section 3d and section 12's boards must REJECT mutated
    inputs.  What those boards rest on is

    - the MEMBERSHIP predicate [fiblazb] -- LSB-first, [d0 = 1], no two
      zeros adjacent, top digit [1] -- which is the only thing separating
      the lazy representative of the fibonacci numeration from the greedy
      one [fibokb] picks;
    - the DECODER [fiblaz], which must invert [fibval] on the members of a
      width and only there ([fam_lo] is the guard that keeps it from being
      asked below a width's floor);
    - the two CLASS laws and the FILL [lazfill], each of which must move the
      value by exactly one;
    - and per row, the boot landing at its exact index.

    So those are what is attacked here.  The load-bearing control is the
    THIRD block: the greedy decode and the lazy one disagree, and each is
    rejected by the other's membership -- without which section 3d would be
    section 3c under another name and the six rows it boards would have
    boarded four waves ago.

    Everything is decided by [vm_compute]/[reflexivity]; a regression that
    made any of these pass would be a soundness alarm. *)

From Coq Require Import Arith Bool List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import LadderFam LadderCheck.
From BBB4.Machines.Ladder Require Import LDR_1RB____0LC1RD_1LB1RC_1LB0RD.
Import ListNotations.

(** ** 1. Membership accepts exactly the lazy strings

    Width 5's members are the five strings below and nothing else; they are
    what [tools/ladder/fiblazy.py] reads off all six machines. *)

Example laz_mem_ok :
  map fiblazb [[1];[1;1];[1;0;1];[1;1;1];[1;1;0;1];[1;0;1;1];[1;1;1;1];
               [1;0;1;0;1];[1;1;1;0;1];[1;1;0;1;1];[1;0;1;1;1];[1;1;1;1;1]]
  = repeat true 12.
Proof. vm_compute. reflexivity. Qed.

(** The three ways to fail, one per clause of the predicate. *)
Example laz_mem_low0  : fiblazb [0;1;1] = false.       (* [d0] is not 1 *)
Proof. vm_compute. reflexivity. Qed.
Example laz_mem_two0  : fiblazb [1;0;0;1] = false.     (* two zeros adjacent *)
Proof. vm_compute. reflexivity. Qed.
Example laz_mem_top0  : fiblazb [1;1;0] = false.       (* the top digit is 0 *)
Proof. vm_compute. reflexivity. Qed.
Example laz_mem_nil   : fiblazb [] = false.            (* no width is 0 *)
Proof. vm_compute. reflexivity. Qed.

(** ** 2. The decoder inverts the fold on a width's members, and nowhere else

    Width 5 spells exactly [fibw 5 = 8] up to [fibsum 5 = 12], consecutively.
    Below the floor there is no width-5 member at all, which is why
    [fam_of_value] carries [fam_lo]: [fiblaz 5 true 7] is NOT worth 7. *)

Example laz_dec_range :
  map (fun v => fibval (fiblaz 5 true v)) [8;9;10;11;12] = [8;9;10;11;12].
Proof. vm_compute. reflexivity. Qed.

Example laz_dec_strings :
  map (fiblaz 5 true) [8;9;10;11;12]
  = [[1;0;1;0;1];[1;1;1;0;1];[1;1;0;1;1];[1;0;1;1;1];[1;1;1;1;1]].
Proof. vm_compute. reflexivity. Qed.

Example laz_dec_below_floor : Nat.eqb (fibval (fiblaz 5 true 7)) 7 = false.
Proof. vm_compute. reflexivity. Qed.

(** ** 3. The two representatives are DIFFERENT, and each rejects the other

    This is the whole content of section 3d.  [fibdec] and [fiblaz] agree on
    the value and disagree on the string, and neither string satisfies the
    other's membership -- so a board that used section 3c's law on one of
    these six rows would state a false equation, not a weaker one. *)

Example laz_vs_greedy_string :
  (fiblaz 4 true 5, fibdec 4 false 5) = ([1;1;0;1], [0;0;1;1]).
Proof. vm_compute. reflexivity. Qed.

Example laz_vs_greedy_value :
  (fibval (fiblaz 4 true 5), fibval (fibdec 4 false 5)) = (5, 5).
Proof. vm_compute. reflexivity. Qed.

Example greedy_is_not_lazy : fiblazb (fibdec 5 false 8) = false.
Proof. vm_compute. reflexivity. Qed.

Example lazy_is_not_greedy : fibokb false (fiblaz 5 true 8) = false.
Proof. vm_compute. reflexivity. Qed.

(** ** 4. The class laws move the value by exactly one, and the parities are
    not interchangeable

    [flc 0] is the EVEN class and [flc 1] the odd one; running either at the
    other's run shape gives a string whose value is not one more. *)

Definition dv (i n : nat) (rest : list nat) : nat :=
  fibval (clsW_rhs (flc i) n rest).
Definition sv (i n : nat) (rest : list nat) : nat :=
  fibval (clsW_lhs (flc i) n rest).

Example laz_cls_step0 :
  map (fun n => Nat.eqb (dv 0 n [1;1]) (S (sv 0 n [1;1]))) [0;1;2;3]
  = repeat true 4.
Proof. vm_compute. reflexivity. Qed.

Example laz_cls_step1 :
  map (fun n => Nat.eqb (dv 1 n [1;1]) (S (sv 1 n [1;1]))) [0;1;2;3]
  = repeat true 4.
Proof. vm_compute. reflexivity. Qed.

(** The corruption: the alternating run [(1 0)^m] the increment leaves is not
    a run of ZEROS, which is what every earlier code's class writes. *)
Example laz_cls_not_zero_run :
  Nat.eqb (fibval ([] ++ repeat 0 4 ++ [1] ++ [1;1]))
          (S (sv 0 2 [1;1])) = false.
Proof. vm_compute. reflexivity. Qed.

(** And the two classes really are two: swap the parity and the law breaks. *)
Example laz_cls_parity_matters :
  Nat.eqb (dv 1 2 [1;1]) (S (sv 0 2 [1;1])) = false.
Proof. vm_compute. reflexivity. Qed.

(** ** 5. The fill is the smallest string of the next width

    [lazfill k] is alternating, its length is [S k], its value is
    [S (fibsum k)] -- the top of width [k] plus one -- and it is a member. *)

Example laz_fill_shape :
  map lazfill [1;2;3;4;5]
  = [[1;1]; [1;0;1]; [1;1;0;1]; [1;0;1;0;1]; [1;1;0;1;0;1]].
Proof. vm_compute. reflexivity. Qed.

Example laz_fill_value :
  map (fun k => Nat.eqb (fibval (lazfill k)) (S (fibsum k))) [1;2;3;4;5;6;7]
  = repeat true 7.
Proof. vm_compute. reflexivity. Qed.

Example laz_fill_member :
  map (fun k => fiblazb (lazfill k)) [1;2;3;4;5;6;7] = repeat true 7.
Proof. vm_compute. reflexivity. Qed.

(** The corruption: one cell wider, or the alternation started at the wrong
    end, and the value is no longer the top's successor. *)
Example laz_fill_not_wider :
  Nat.eqb (fibval (lazfill 4 ++ [0])) (S (fibsum 4)) = true
  /\ fiblazb (lazfill 4 ++ [0]) = false.
Proof. vm_compute. split; reflexivity. Qed.

Example laz_fill_not_flipped :
  Nat.eqb (fibval [0;1;0;1;1]) (S (fibsum 4)) = false.
Proof. vm_compute. reflexivity. Qed.

(** ** 6. The board's boot lands at its exact index and nowhere adjacent *)

Local Notation tm := tm_1RB____0LC1RD_1LB1RC_1LB0RD.
Local Notation FAM := fam_1RB____0LC1RD_1LB1RC_1LB0RD.

Example laz_boot_4 :
  match csteps tm 4 c0 with
  | Some c => ceqb c (fam_cfg FAM ([1], 0, 0)) | None => false end = true.
Proof. vm_compute. reflexivity. Qed.

Example laz_boot_not_3 :
  match csteps tm 3 c0 with
  | Some c => ceqb c (fam_cfg FAM ([1], 0, 0)) | None => false end = false.
Proof. vm_compute. reflexivity. Qed.

Example laz_boot_not_5 :
  match csteps tm 5 c0 with
  | Some c => ceqb c (fam_cfg FAM ([1], 0, 0)) | None => false end = false.
Proof. vm_compute. reflexivity. Qed.

(** The boot string is a MEMBER -- the base case of the invariant -- and a
    non-member at the same width is rejected. *)
Example laz_boot_member : fiblazb [1] = true /\ fiblazb [0] = false.
Proof. vm_compute. split; reflexivity. Qed.

(** ** 7. The family is the one the board names

    A wrong code, a wrong step or a wrong anchor would make section 12's
    hypotheses unprovable rather than the theorem wrong, but the check is
    cheap and it pins what the row was measured at. *)
Example laz_fam_fields :
  (fm_b FAM, fm_step FAM, fm_left FAM, fm_other FAM, fm_pre FAM)
  = (2, 1, false, @nil Sym, @nil Sym).
Proof. vm_compute. reflexivity. Qed.

Example laz_fam_code : match fm_code FAM with FibL => true | _ => false end = true.
Proof. vm_compute. reflexivity. Qed.

Example laz_fam_not_fib : match fm_code FAM with Fib => true | _ => false end = false.
Proof. vm_compute. reflexivity. Qed.
