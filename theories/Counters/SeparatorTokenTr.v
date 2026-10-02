(** * A base-four counter with a fixed separator and outer digit.

    The digit words are 010, 000, 011, 001. The inner successor carries
    through 001 words and creates 011 at an empty end. One outer digit
    uses the same cycle; its carry crosses a fixed 1 and increments the
    inner word. No numeric ranking or canonical representation is needed.

    [sep_g_run] proves the arbitrary-length inner carry by induction.
    [sep_counter] joins it to the outer digit. A supplied LapDecider
    sweep certificate grows the repeated 110 block, and seven checked
    sweep prefixes plus the initial D1 yield every instruction witness.
    The anchor retains one final blank so all lap endpoints are exact. *)
From Coq Require Import Arith Lia List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers Require Import LapDecider.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import WTape LapGlueTr.
Import ListNotations.

Inductive sep_digit := sd0 | sd1 | sd2 | sd3.
Definition sep_d d : list Sym :=
 match d with sd0=>[S0;S1;S0]|sd1=>[S0;S0;S0]|sd2=>[S0;S1;S1]|sd3=>[S0;S0;S1] end.
Fixpoint sep_e ds : list Sym :=
 match ds with []=>[]|d::xs=>sep_d d ++ sep_e xs end.
Fixpoint sep_inc ds : list sep_digit :=
 match ds with []=>[sd2]|sd0::xs=>sd1::xs|sd1::xs=>sd2::xs|sd2::xs=>sd3::xs|sd3::xs=>sd0::sep_inc xs end.
Fixpoint sep_gc ds : nat :=
 match ds with []=>6|sd0::_=>4|sd1::_=>6|sd2::_=>4|sd3::xs=>6+sep_gc xs end.
Definition sep_value := (sep_digit * list sep_digit)%type.
Definition sep_next (x:sep_value) : sep_value :=
 match x with (sd0,w)=>(sd1,w)|(sd1,w)=>(sd2,w)|(sd2,w)=>(sd3,w)|(sd3,w)=>(sd0,sep_inc w) end.
Definition sep_word (x:sep_value) := sep_d (fst x) ++ S1::sep_e (snd x).
Definition sep_cc (x:sep_value) :=
 match fst x with sd0|sd2=>8|sd1=>10|sd3=>12+sep_gc (snd x) end.
Definition sep_anchor n x : cconf :=
 (StB,(S1::S1::sep_word x,S0,rep [S1;S1;S0] n ++ [S1;S1;S0])).
Definition sep_mid n w : cconf :=
 (StA,(S0::S1::w,S0,rep [S1;S1;S0] n ++ [S1;S1;S0])).

Definition sep_sc := mkC StA (sflat [S0;S1]) S0
 (mkS [] [S1;S1;S0] 1 0 [S1;S1;S0]).
Definition sep_sd := mkC StB (sflat [S1;S1]) S0
 (mkS [] [S1;S1;S0] 1 1 [S1;S1;S0]).
Definition sep_sweep_chain :=
 [(SCycR 3); (SWin 2); (SWinR 6); (SCycL 3 0); (SWin 4);
  (SCycR 3); (SWin 4); (SWinR 6); (SCycL 3 0); (SWin 4);
  (SCycR 3); (SWin 5); (SWinR 7); (SCycL 3 0); (SRotR 3); (SFoldR 1)].

Section Separator.
Variable tm : TM.
Hypothesis HA0 : tm StA S0 = Some (mkTrans S1 DR StB).
Hypothesis HA1 : tm StA S1 = Some (mkTrans S0 DR StA).
Hypothesis HB0 : tm StB S0 = Some (mkTrans S0 DL StC).
Hypothesis HB1 : tm StB S1 = Some (mkTrans S0 DR StA).
Hypothesis HC0 : tm StC S0 = Some (mkTrans S1 DR StA).
Hypothesis HC1 : tm StC S1 = Some (mkTrans S1 DL StD).
Hypothesis HD0 : tm StD S0 = Some (mkTrans S1 DL StB).
Hypothesis HD1 : tm StD S1 = Some (mkTrans S0 DL StD).
Local Ltac sep_compute :=
 cbn [Nat.add csteps cstep ctape_move chd ctl t_next t_dir t_write];
 repeat (first [rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|
                rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
         cbn [Nat.add csteps cstep ctape_move chd ctl t_next t_dir t_write]);
 reflexivity.

Lemma sep_g_run : forall ds R,
 csteps tm (sep_gc ds) (StD,(ctl (sep_e ds),chd (sep_e ds),S1::S0::R)) =
 Some (StA,(S0::sep_e (sep_inc ds),S0,R)).
Proof.
 induction ds as [|d ds IH];intro R.
 - cbn [sep_gc sep_e sep_inc sep_d chd ctl app]. sep_compute.
 - destruct d;cbn [sep_gc sep_e sep_inc sep_d chd ctl app];try sep_compute.
   replace (6+sep_gc ds) with (3+(sep_gc ds+3)) by lia.
   rewrite csteps_add.
   assert (H : csteps tm 3 (StD,(S0::S1::sep_e ds,S0,S1::S0::R)) =
     Some (StD,(ctl (sep_e ds),chd (sep_e ds),S1::S0::S1::S1::S0::R))) by sep_compute.
   rewrite H,csteps_add,IH. sep_compute.
Qed.

Lemma sep_h_run : forall ds R,
 csteps tm (sep_gc ds+1) (StD,(ctl (sep_e ds),chd (sep_e ds),S0::S1::S0::R)) =
 Some (StA,(S0::S1::sep_e (sep_inc ds),S0,R)).
Proof.
 intros [|d ds] R.
 - cbn [sep_gc sep_e sep_inc sep_d chd ctl app]. sep_compute.
 - destruct d;cbn [sep_gc sep_e sep_inc sep_d chd ctl app];try sep_compute.
   replace (6+sep_gc ds+1) with (3+(sep_gc ds+4)) by lia.
   rewrite csteps_add.
   assert (H : csteps tm 3 (StD,(S0::S1::sep_e ds,S0,S0::S1::S0::R)) =
     Some (StD,(ctl (sep_e ds),chd (sep_e ds),S1::S0::S1::S0::S1::S0::R))) by sep_compute.
   rewrite H,csteps_add,sep_g_run. sep_compute.
Qed.

Lemma sep_counter : forall x R,
 csteps tm (sep_cc x) (StB,(S1::S1::sep_word x,S0,R)) =
 Some (StA,(S0::S1::sep_word (sep_next x),S0,R)).
Proof.
 intros [d ds] R. destruct d;cbn [sep_cc sep_word sep_next fst snd sep_d app];try sep_compute.
 replace (12+sep_gc ds) with (7+((sep_gc ds+1)+4)) by lia.
 rewrite csteps_add.
 assert (H : csteps tm 7 (StB,(S1::S1::S0::S0::S1::S1::sep_e ds,S0,R)) =
   Some (StD,(ctl (sep_e ds),chd (sep_e ds),S0::S1::S0::S1::S0::S1::S0::R))) by sep_compute.
 rewrite H,csteps_add,sep_h_run. sep_compute.
Qed.

Hypothesis Hsweep : srun tm false true sep_sweep_chain sep_sc = Some (sep_sd,18,38).

Lemma sep_sweep : forall n w,
 csteps tm (18*n+38) (sep_mid n w) =
 Some (StB,(S1::S1::w,S0,rep [S1;S1;S0] (S n) ++ [S1;S1;S0])).
Proof.
 intros n w.
 pose proof (srun_sound tm false true sep_sweep_chain sep_sc sep_sd 18 38 Hsweep
   w [] n ltac:(discriminate) ltac:(reflexivity)) as H.
 unfold cden, sden, sep_sc, sep_sd, sflat in H.
 cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post] in H.
 rewrite rep_nil in H. cbn [app] in H.
 replace (1*n+0) with n in H by lia.
 replace (1*n+1) with (S n) in H by lia.
 try rewrite !app_nil_r in H. exact H.
Qed.

Lemma sep_lap : forall n x,
 csteps tm (sep_cc x+18*n+38) (sep_anchor n x) =
 Some (sep_anchor (S n) (sep_next x)).
Proof.
 intros n x. replace (sep_cc x+18*n+38) with (sep_cc x+(18*n+38)) by lia.
 unfold sep_anchor. rewrite csteps_add,sep_counter. apply sep_sweep.
Qed.

Hypothesis Hfires : forall t, t<>(StD,S1) -> exists ch,
 srun_instr tm false true ch sep_sc = Some t.

Lemma sep_sweep_fire : forall n w t, t<>(StD,S1) -> exists j c,
 csteps tm j (sep_mid n w) = Some c /\ cinstr c = t.
Proof.
 intros n w t Ht. destruct (Hfires t Ht) as [ch Hch].
 apply (fire_of_run_instr tm (fun _ => sep_mid n w) false true ch sep_sc
   xH n w [] t Hch ltac:(discriminate) ltac:(reflexivity)).
 unfold sep_mid,cden,sden,sep_sc,sflat.
 cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
 rewrite rep_nil. cbn [app]. replace (1*n+0) with n by lia.
 try rewrite !app_nil_r. reflexivity.
Qed.

Lemma sep_fire : forall n x t, exists j c,
 csteps tm j (sep_anchor n x) = Some c /\ cinstr c = t.
Proof.
 intros n x t.
 assert (Ho : forall u, u<>(StD,S1) -> exists j c,
   csteps tm j (sep_anchor n x) = Some c /\ cinstr c = u).
 { intros u Hu. destruct (sep_sweep_fire n (sep_word (sep_next x)) u Hu) as (j & c & H & Hi).
   exists (sep_cc x+j),c. split.
   - unfold sep_anchor. rewrite csteps_add,sep_counter. exact H.
   - exact Hi. }
 destruct t as [q s]. destruct q,s;try (apply Ho;discriminate).
 exists 2,(StD,(sep_word x,S1,S1::S0::(rep [S1;S1;S0] n ++ [S1;S1;S0]))).
 split;[unfold sep_anchor;sep_compute|reflexivity].
Qed.
End Separator.
