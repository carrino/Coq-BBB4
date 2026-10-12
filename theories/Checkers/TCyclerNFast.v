(** * Avoid redundant prefix scans in binary-fuel state cycle proofs.

    The original implication scans the complete prefix before checking
    whether a state occurs in the repeating guarded lap. Check that
    consequent first, stopping at its first visit. If it holds, no prefix
    scan is needed. The equality below covers every input, including
    rejected certificates; the original soundness theorem is reused. *)
From Coq Require Import Arith Bool List NArith.
From BBB4 Require Import BBB4_Statement CTape GTape Mirror.
From BBB4.Checkers Require Import TCycler TCyclerN.
Import ListNotations.

Fixpoint gvisits_short (tm : TM) (g : cconf) (len : nat) (q : St) : bool :=
  match len with
  | 0 => false
  | S m =>
      if st_eqb (fst g) q then true
      else match gstep tm g with
           | Some g' => gvisits_short tm g' m q
           | None => false
           end
  end.

Lemma gvisits_short_eq : forall tm len g q,
  gvisits_short tm g len q = gvisits tm g len q.
Proof.
  intros tm len. induction len as [|len IH]; intros g q; [reflexivity|].
  cbn [gvisits_short gvisits]. destruct (st_eqb (fst g) q); [reflexivity|].
  destruct (gstep tm g); [apply IH|reflexivity].
Qed.

Definition tcycler_check_neverqh_N_fast (tm : TM) (n1 P : N) (W : nat) : bool :=
  (0 <? P)%N &&
  match cstepsN tm n1 c0 with
  | Some (q1, (l1, h1, r1)) =>
      let g1 : cconf := (q1, (firstn_pad W l1, h1, r1)) in
      let period := N.to_nat P in
      match gsteps tm period g1 with
      | Some g2 =>
          gmatch g1 g2 &&
          forallb (fun q =>
            if gvisits_short tm g1 period q then true
            else negb (cvisitsN tm c0 (n1 + P) q)) all_St
      | None => false
      end
  | None => false
  end.

Theorem tcycler_check_neverqh_N_fast_eq : forall tm n1 P W,
  tcycler_check_neverqh_N_fast tm n1 P W = tcycler_check_neverqh_N tm n1 P W.
Proof.
  intros tm n1 P W.
  unfold tcycler_check_neverqh_N_fast, tcycler_check_neverqh_N.
  destruct (cstepsN tm n1 c0) as [[q1 [[l1 h1] r1]]|]; [|reflexivity].
  destruct (gsteps tm (N.to_nat P) (q1, (firstn_pad W l1, h1, r1))) as [g2|];
    [|reflexivity].
  f_equal. f_equal.
  assert (H : forall qs,
    forallb (fun q => if gvisits_short tm (q1, (firstn_pad W l1, h1, r1))
                              (N.to_nat P) q then true
                     else negb (cvisitsN tm c0 (n1 + P) q)) qs =
    forallb (fun q => implb (cvisitsN tm c0 (n1 + P) q)
                     (gvisits tm (q1, (firstn_pad W l1, h1, r1)) (N.to_nat P) q)) qs).
  { induction qs as [|q qs IH]; [reflexivity|].
    cbn [forallb]. rewrite gvisits_short_eq, IH.
    destruct (gvisits tm (q1, (firstn_pad W l1, h1, r1)) (N.to_nat P) q),
             (cvisitsN tm c0 (n1 + P) q); reflexivity. }
  apply H.
Qed.

Theorem tcycler_check_neverqh_N_fast_sound : forall tm n1 P W,
  tcycler_check_neverqh_N_fast tm n1 P W = true -> NeverQuasiHaltsSt tm.
Proof.
  intros tm n1 P W. rewrite tcycler_check_neverqh_N_fast_eq.
  apply tcycler_check_neverqh_N_sound.
Qed.

Corollary tcycler_check_neverqh_N_fast_sound_L : forall tm n1 P W,
  tcycler_check_neverqh_N_fast (mirror_tm tm) n1 P W = true -> NeverQuasiHaltsSt tm.
Proof.
  intros tm n1 P W. rewrite tcycler_check_neverqh_N_fast_eq.
  apply tcycler_check_neverqh_N_sound_L.
Qed.
