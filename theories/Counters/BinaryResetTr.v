(** * Binary carries with a moving boundary at overflow.

    Ordinary carries use digit words 10 and 11. A short end marker changes
    phase once; overflow then converts the old sweep block into new zero
    digits. The value is an arbitrary finite word, not a numeral invariant. *)
From Coq Require Import Arith Lia List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers Require Import LapDecider.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import WTape LapGlueTr.
Import ListNotations.

Definition br_value := (list Sym * bool)%type.
Fixpoint br_word (w:list Sym) (top:bool) : list Sym :=
 match w with []=>if top then [S1] else []|d::w=>S1::d::br_word w top end.
Definition br_encode (v:br_value) := br_word (fst v) (snd v).
Fixpoint br_scan (w:list Sym) (top:bool) : option br_value :=
 match w with
 | []=>if top then Some ([S1],false) else None
 | S0::w=>Some (S1::w,top)
 | S1::w=>option_map (fun v => (S0::fst v,snd v)) (br_scan w top)
 end.
Fixpoint br_cost (w:list Sym) := match w with []=>4|S0::_=>4|S1::w=>4+br_cost w end.
Definition br_anchor (x:nat*br_value) : cconf :=
 let '(n,(w,b)) := x in (StD,(br_word w b,S1,rep [S1;S0] n++[S1])).
Definition br_reset k n : br_value := (repeat S0 (k+n)++[S1],true).

Definition br_sweep_s := mkC StA (sflat [S1]) S1 (mkS [] [S1;S0] 1 0 [S1]).
Definition br_sweep_e := mkC StD (sflat [S1]) S1 (mkS [] [S1;S0] 1 2 [S1]).
Definition br_sweep_ch := [(SRotR 1); (SWin 1); (SCycR 2); (SWinR 10);
 (SCycL 2 0); (SWin 3); (SRotR 1); (SRotR 2); (SFoldR 2)].
Definition br_reset_s := mkC StD (sflat []) S1 (mkS [] [S0;S1] 1 0 [S1]).
Definition br_reset_e := mkC StA (sflat [S1;S1;S1]) S1 (mkS [] [S0;S1] 1 0 []).
Definition br_reset_ch := [(SWinL 4); (SCycR 2); (SWin 2); (SCycL 2 0);
 (SWin 2); (SRotR 1); (SWin 1)].
Definition br_finish_s := mkC StA (sflat [S1;S1;S1]) S1 (mkS [] [S0;S1] 1 0 []).
Definition br_finish_e := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1;S1]) S1 (sflat [S1;S0;S1]).
Definition br_finish_ch := [(SCycR 2); (SWinR 8); (SRotL 1); (SWin 2); (SUnrotL 1)].

Section BinaryReset.
Variable tm : TM.
Hypothesis HA0 : tm StA S0 = Some (mkTrans S1 DR StB).
Hypothesis HA1 : tm StA S1 = Some (mkTrans S0 DR StC).
Hypothesis HB0 : tm StB S0 = Some (mkTrans S1 DL StC).
Hypothesis HB1 : tm StB S1 = Some (mkTrans S0 DL StD).
Hypothesis HC0 : tm StC S0 = Some (mkTrans S1 DR StA).
Hypothesis HC1 : tm StC S1 = Some (mkTrans S1 DR StD).
Hypothesis HD0 : tm StD S0 = Some (mkTrans S1 DR StC).
Hypothesis HD1 : tm StD S1 = Some (mkTrans S1 DL StB).
Local Ltac br_compute :=
 cbn [Nat.add csteps cstep ctape_move chd ctl t_next t_dir t_write];
 repeat (first [rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|
                rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
         cbn [Nat.add csteps cstep ctape_move chd ctl t_next t_dir t_write]);
 reflexivity.

Lemma br_scan_run : forall w b v R, br_scan w b = Some v ->
 csteps tm (br_cost w) (StD,(br_word w b,S1,R)) = Some (StA,(br_encode v,S1,R)).
Proof.
 induction w as [|d w IH];intros b v R E.
 - destruct b;[injection E as <-|discriminate]. cbn [br_cost br_word br_encode fst snd]. br_compute.
 - destruct d.
   + injection E as <-. cbn [br_cost br_word br_encode fst snd]. br_compute.
   + cbn [br_scan] in E. destruct (br_scan w b) as [[u c]|] eqn:Es;[|discriminate].
     injection E as <-. cbn [br_cost br_word br_encode fst snd].
     replace (4+br_cost w) with (2+(br_cost w+2)) by lia.
     rewrite csteps_add.
     assert (H : csteps tm 2 (StD,(S1::S1::br_word w b,S1,R)) =
       Some (StD,(br_word w b,S1,S0::S1::R))) by br_compute.
     rewrite H,csteps_add,(IH b (u,c) (S0::S1::R) Es).
     cbn [br_encode fst snd]. br_compute.
Qed.

Lemma br_scan_head : forall w b v, br_scan w b = Some v ->
 exists u, br_encode v = S1::u.
Proof.
 induction w as [|[] w IH];intros b v E;cbn [br_scan] in E.
 - destruct b;[injection E as <-;eexists;reflexivity|discriminate].
 - injection E as <-. eexists;reflexivity.
 - destruct (br_scan w b) as [[u c]|];[|discriminate]. injection E as <-.
   eexists;reflexivity.
Qed.
Lemma br_top_some : forall w, exists v, br_scan w true=Some v.
Proof.
 induction w as [|[] w IH];cbn [br_scan];try (eexists;reflexivity).
 destruct IH as [[u b] E]. rewrite E. eexists;reflexivity.
Qed.
Lemma br_empty_run : forall w b R, br_scan w b=None ->
 csteps tm (2*length w) (StD,(br_word w b,S1,R)) =
 Some (StD,([],S1,rep [S0;S1] (length w)++R)).
Proof.
 induction w as [|[] w IH];intros b R E.
 - destruct b;[discriminate|reflexivity].
 - discriminate.
 - cbn [br_scan] in E. destruct (br_scan w b) as [v|] eqn:Es;[discriminate|].
   cbn [length br_word]. replace (2*S(length w)) with (2+2*length w) by lia.
   rewrite csteps_add.
   assert (H : csteps tm 2 (StD,(S1::S1::br_word w b,S1,R)) =
     Some (StD,(br_word w b,S1,S0::S1::R))) by br_compute.
   rewrite H,(IH b (S0::S1::R) Es).
   change (Some (StD,(([]:list Sym),S1,rep [S0;S1] (length w)++([S0;S1]++R))) =
     Some (StD,([],S1,rep [S0;S1] (S(length w))++R))).
   rewrite app_assoc,rep_shift. reflexivity.
Qed.

Hypothesis Hsweep : srun tm false true br_sweep_ch br_sweep_s = Some (br_sweep_e,4,14).
Hypothesis Hreset : srun tm true false br_reset_ch br_reset_s = Some (br_reset_e,4,9).
Hypothesis Hfinish : srun tm true true br_finish_ch br_finish_s = Some (br_finish_e,2,10).
Local Ltac br_den n H :=
 unfold cden,sden,sflat,br_sweep_s,br_sweep_e,br_reset_s,br_reset_e,br_finish_s,br_finish_e in H;
 cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post] in H;
 rewrite !rep_nil in H;cbn [app] in H;
 repeat rewrite app_nil_r in H;
 replace (1*n+0) with n in H by lia;
 try replace (1*n+2) with (n+2) in H by lia.

Lemma br_sweep : forall n w,
 csteps tm (4*n+14) (StA,(S1::w,S1,rep [S1;S0] n++[S1])) =
 Some (StD,(S1::w,S1,rep [S1;S0] (n+2)++[S1])).
Proof.
 intros n w. pose proof (srun_sound tm false true br_sweep_ch br_sweep_s br_sweep_e
  4 14 Hsweep w [] n ltac:(discriminate) ltac:(reflexivity)) as H.
 br_den n H. exact H.
Qed.
Lemma br_reset_first : forall k R,
 csteps tm (4*k+9) (StD,([],S1,rep [S0;S1] k++S1::R)) =
 Some (StA,([S1;S1;S1],S1,rep [S0;S1] k++R)).
Proof.
 intros k R. pose proof (srun_sound tm true false br_reset_ch br_reset_s br_reset_e
  4 9 Hreset [] R k ltac:(reflexivity) ltac:(discriminate)) as H.
 br_den k H. exact H.
Qed.
Lemma br_reset_finish : forall n,
 csteps tm (2*n+10) (StA,([S1;S1;S1],S1,rep [S0;S1] n)) =
 Some (StD,(rep [S1;S0] n++[S1;S1;S1],S1,[S1;S0;S1])).
Proof.
 intro n. pose proof (srun_sound tm true true br_finish_ch br_finish_s br_finish_e
  2 10 Hfinish [] [] n ltac:(reflexivity) ltac:(reflexivity)) as H.
 br_den n H. exact H.
Qed.
Lemma br_ones_rotate : forall n, rep [S1;S0] n++[S1] = S1::rep [S0;S1] n.
Proof. induction n;cbn [rep app];[reflexivity|rewrite IHn;reflexivity]. Qed.
Lemma br_zero_word : forall n w b,
 br_word (repeat S0 n++w) b = rep [S1;S0] n++br_word w b.
Proof. induction n;intros;cbn [repeat app br_word rep];[reflexivity|rewrite IHn;reflexivity]. Qed.
Lemma br_overflow : forall k n,
 csteps tm (6*k+2*n+19) (StD,([],S1,rep [S0;S1] k++rep [S1;S0] n++[S1])) =
 Some (br_anchor (1,br_reset k n)).
Proof.
 intros k n. rewrite br_ones_rotate.
 replace (6*k+2*n+19) with ((4*k+9)+(2*(k+n)+10)) by lia.
 rewrite csteps_add,br_reset_first,<-rep_add,br_reset_finish.
 unfold br_anchor,br_reset. rewrite br_zero_word. reflexivity.
Qed.

Lemma br_reset_run : forall n w b, br_scan w b=None ->
 csteps tm (8*length w+2*n+19) (br_anchor (n,(w,b))) =
 Some (br_anchor (1,br_reset (length w) n)).
Proof.
 intros n w b E. unfold br_anchor at 1.
 replace (8*length w+2*n+19) with (2*length w+(6*length w+2*n+19)) by lia.
 rewrite csteps_add,(br_empty_run w b _ E).
 apply br_overflow.
Qed.
Lemma br_progress : forall n w b, exists m v k,
 0<k /\ csteps tm k (br_anchor (n,(w,b))) = Some (br_anchor (m,v)).
Proof.
 intros n w b. destruct (br_scan w b) as [[u c]|] eqn:E.
 - destruct (br_scan_head w b (u,c) E) as [L HL].
   exists (n+2),(u,c),(br_cost w+(4*n+14)). split;[lia|].
   unfold br_anchor. rewrite csteps_add,(br_scan_run w b (u,c) _ E).
   change (br_word u c=S1::L) in HL. unfold br_encode;cbn [fst snd].
   rewrite HL. apply br_sweep.
 - exists 1,(br_reset (length w) n),(8*length w+2*n+19).
   split;[lia|apply br_reset_run;exact E].
Qed.
Lemma br_find_sweep : forall n w b, exists k L m,
 csteps tm k (br_anchor (n,(w,b))) =
 Some (StA,(S1::L,S1,rep [S1;S0] m++[S1])).
Proof.
 intros n w b. destruct (br_scan w b) as [v|] eqn:E.
 - destruct (br_scan_head w b v E) as [L HL].
   exists (br_cost w),L,n. unfold br_anchor. rewrite (br_scan_run w b v _ E),HL. reflexivity.
 - destruct (br_top_some (repeat S0 (length w+n)++[S1])) as [v Ev].
   destruct (br_scan_head _ true v Ev) as [L HL].
   exists ((8*length w+2*n+19)+br_cost (repeat S0 (length w+n)++[S1])),L,1.
   rewrite csteps_add,(br_reset_run n w b E).
   unfold br_anchor,br_reset. rewrite (br_scan_run _ true v _ Ev),HL. reflexivity.
Qed.

Hypothesis Hfires : forall t, exists ch,
 srun_instr tm false true ch br_sweep_s = Some t.
Lemma br_fire : forall n w b t, exists j c,
 csteps tm j (br_anchor (n,(w,b))) = Some c /\ cinstr c=t.
Proof.
 intros n w b t. destruct (br_find_sweep n w b) as (k&L&m&Ek).
 destruct (Hfires t) as [ch Hch].
 assert (Hden : (StA,(S1::L,S1,rep [S1;S0] m++[S1])) = cden L [] m br_sweep_s).
 { unfold cden,sden,sflat,br_sweep_s.
   cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
   rewrite rep_nil. cbn [app]. replace (1*m+0) with m by lia. reflexivity. }
 destruct (fire_of_run_instr tm (fun _ => (StA,(S1::L,S1,rep [S1;S0] m++[S1])))
   false true ch br_sweep_s xH m L [] t Hch ltac:(discriminate) ltac:(reflexivity)
   Hden) as (j&c&Hj&Hi).
 exists (k+j),c. split;[rewrite csteps_add,Ek;exact Hj|exact Hi].
Qed.

Theorem binary_reset_neverqhtr :
 (exists T n w b, stepn tm T InitES = Some (lift (br_anchor (n,(w,b))))) ->
 NeverQuasiHaltsTr tm.
Proof.
 intro Boot.
 assert (Reach : forall N, exists T n w b, N<=T /\
   stepn tm T InitES = Some (lift (br_anchor (n,(w,b))))).
 { induction N as [|N IH].
   - destruct Boot as (T&n&w&b&E). exists T,n,w,b. split;[lia|exact E].
   - destruct IH as (T&n&w&b&HT&E).
     destruct (br_progress n w b) as (m&[u c]&k&Hk&Ek).
     exists (T+k),m,u,c. split;[lia|].
     rewrite stepn_add,E. apply csteps_lift. exact Ek. }
 intros t _ N. destruct (Reach N) as (T&n&w&b&HT&E).
 destruct (br_fire n w b t) as (k&c&Ek&Et).
 exists (T+k). split;[lia|]. exists (lift c). split.
 - rewrite stepn_add,E. apply csteps_lift. exact Ek.
 - rewrite cinstr_lift. exact Et.
Qed.
End BinaryReset.
