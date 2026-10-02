(** * Pair transfers with a stack of finite left blocks.

    The inner sweep removes two from the near left block and adds one
    to both the far left block and the right block.  An odd exit consumes
    a left block.  At the empty stack, odd rounds map [a] to [(a+3)/2].
    The invariant excludes the non-firing fixed point [a=3]: the farthest
    stored left block always has at least two ones.  The empty-stack
    values are 1, 2, or at least 4.

    D0 returns preserve this stack language.  Even right lengths halve
    before the next D0; odd lengths fire all instructions during the
    next exit.  Induction on right length therefore supplies all eight
    liveness witnesses.  Positive existential returns avoid choice. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import StackCubeTr TriReachTr WTape.
Import ListNotations.

Fixpoint pc_word (w : list nat) : list Sym :=
 match w with [] => [] | n::w => sc_ones n++S0::pc_word w end.
Definition pc_B a w r : cconf := (StB,(sc_ones a++S0::pc_word w,S1,sc_ones r)).
Definition pc_D w r : cconf := (StD,(pc_word w,S0,sc_ones r)).
Fixpoint pc_wf (w : list nat) : Prop :=
 match w with [] => False | [n] => 2<=n | _::w => pc_wf w end.
Definition pc_good a w r :=
 match w with [] => a=1 \/ a=2 \/ 4<=a | _::_ => pc_wf w /\ 0<a+r end.
Definition pc_found tm c := exists w r, pc_wf w /\ 0<r /\ sc_R tm c (pc_D w r).
Lemma pc_found_back : forall tm c d,
 sc_R tm c d -> pc_found tm d -> pc_found tm c.
Proof. intros tm c d E (w&r&W&P&F). exists w,r. repeat split; try assumption. eapply sc_R_trans;eauto. Qed.

Definition pc_inc k w := match w with [] => [k] | b::w => (k+b)::w end.
Lemma pc_inc_wf : forall w k, pc_wf w -> pc_wf (pc_inc k w).
Proof. intros [|b [|c w]] k H; cbn [pc_inc pc_wf] in *; lia || assumption. Qed.
Lemma pc_prepend_wf : forall w n, pc_wf w -> pc_wf (n::w).
Proof. intros [|b w] n H; cbn [pc_wf] in *; tauto. Qed.
Lemma pc_pop_good : forall k b w r, pc_wf (b::w) -> pc_good (k+b+2) w r.
Proof.
 intros k b [|c w] r H; cbn [pc_wf pc_good] in *.
 - right;right;lia.
 - split;[exact H|lia].
Qed.
Lemma pc_R_inc : forall tm q P k w h R,
 sc_R tm (q,(P++sc_ones k++pc_word w,h,R)) (q,(P++pc_word(pc_inc k w),h,R)).
Proof.
 intros tm q P k [|b w] h R; cbn [pc_word pc_inc].
 - rewrite app_nil_r,app_assoc. apply sc_R_padL.
 - rewrite sc_ones_add. apply sc_R_same;reflexivity.
Qed.

Lemma pc_ones_app : forall a b, sc_ones a++sc_ones b=sc_ones(a+b).
Proof. intros. unfold sc_ones. rewrite repeat_app. reflexivity. Qed.

Section PairStack.
Variable tm : TM.
Hypothesis HA0 : tm StA S0 = Some (mkTrans S1 DL StB).
Hypothesis HA1 : tm StA S1 = Some (mkTrans S1 DR StA).
Hypothesis HB0 : tm StB S0 = Some (mkTrans S1 DR StB).
Hypothesis HB1 : tm StB S1 = Some (mkTrans S0 DL StC).
Hypothesis HC0 : tm StC S0 = Some (mkTrans S1 DR StD).
Hypothesis HC1 : tm StC S1 = Some (mkTrans S1 DL StC).
Hypothesis HD0 : tm StD S0 = Some (mkTrans S0 DR StD).
Hypothesis HD1 : tm StD S1 = Some (mkTrans S0 DR StA).
Local Ltac pc_compute :=
 repeat (cbn [csteps cstep ctape_move chd ctl t_write t_dir t_next];
  first [rewrite HA0 | rewrite HA1 | rewrite HB0 | rewrite HB1 |
         rewrite HC0 | rewrite HC1 | rewrite HD0 | rewrite HD1]); reflexivity.

Lemma pc_C1_step : forall L R,
 csteps tm 1 (StC,(L,S1,R)) = Some (StC,(ctl L,chd L,S1::R)).
Proof. intros; pc_compute. Qed.
Lemma pc_C1_sweep : forall n L R,
 csteps tm n (StC,(ctl (sc_ones n++L),chd (sc_ones n++L),R)) =
 Some (StC,(ctl L,chd L,sc_ones n++R)).
Proof.
 induction n as [|n IH];intros L R;[reflexivity|].
 change (S n) with (1+n). rewrite csteps_add.
 cbn [Nat.add sc_ones repeat app chd ctl]. rewrite pc_C1_step,IH,sc_ones_push. reflexivity.
Qed.
Lemma pc_B1_enter : forall L R,
 csteps tm 1 (StB,(L,S1,R)) = Some (StC,(ctl L,chd L,S0::R)).
Proof. intros; pc_compute. Qed.
Lemma pc_C0_turn : forall L R,
 csteps tm 2 (StC,(L,S0,S1::R)) = Some (StA,(S0::S1::L,chd R,ctl R)).
Proof. intros; pc_compute. Qed.
Lemma pc_transfer : forall a L R,
 csteps tm (2*a+7) (StB,(sc_ones (a+2)++S0::L,S1,R)) =
 Some (StB,(sc_ones a++S0::S1::L,S1,S1::R)).
Proof.
 intros a L R. replace (2*a+7) with (1+((a+2)+(2+((a+1)+1)))) by lia.
 rewrite csteps_add,pc_B1_enter,csteps_add,pc_C1_sweep.
 cbn [chd ctl]. replace (a+2) with (S(S a)) by lia.
 rewrite csteps_add. cbn [sc_ones repeat app]. rewrite pc_C0_turn.
 replace (a+1) with (S a) by lia.
 change (csteps tm (S a+1)
  (StA,(S0::S1::L,chd(sc_ones (S a)++S0::R),ctl(sc_ones (S a)++S0::R))) =
 Some (StB,(sc_ones a++S0::S1::L,S1,S1::R))).
 rewrite csteps_add,(sc_A1_sweep tm HA1).
 replace (a+1) with (S a) by lia. cbn [sc_ones repeat app chd ctl].
 apply (sc_A0_turn tm HA0).
Qed.
Lemma pc_odd_exit : forall L R,
 csteps tm 6 (StB,(S1::S0::L,S1,R)) = Some (StB,(S1::S1::L,S1,R)).
Proof. intros; pc_compute. Qed.
Lemma pc_even_exit : forall L R,
 csteps tm 2 (StB,(S0::L,S1,R)) = Some (StD,(S1::L,S0,R)).
Proof. intros; pc_compute. Qed.
Lemma pc_D_short : forall L,
 csteps tm 4 (StD,(L,S0,[S1])) = Some (StB,(S1::S0::L,S1,[])).
Proof. intros; pc_compute. Qed.
Lemma pc_D_long : forall r L,
 csteps tm (r+4) (StD,(L,S0,sc_ones (r+2)++[S0])) =
 Some (StB,(sc_ones r++S0::S0::L,S1,[S1])).
Proof.
 intros r L. replace (r+2) with (S(S r)) by lia.
 assert (E : csteps tm 2 (StD,(L,S0,sc_ones (S(S r))++[S0])) =
  Some (StA,(S0::S0::L,S1,sc_ones r++[S0]))).
 { cbn [sc_ones repeat app];pc_compute. }
 replace (r+4) with (2+(S r+1)) by lia. rewrite csteps_add,E.
 change (csteps tm (S r+1)
  (StA,(S0::S0::L,chd(sc_ones(S r)++[S0]),ctl(sc_ones(S r)++[S0]))) =
 Some (StB,(sc_ones r++S0::S0::L,S1,[S1]))).
 rewrite csteps_add,(sc_A1_sweep tm HA1).
 cbn [sc_ones repeat app chd ctl]. apply (sc_A0_turn tm HA0).
Qed.

Lemma pc_R_loop : forall k a L R,
 sc_R tm (StB,(sc_ones(2*k+a)++S0::L,S1,R))
 (StB,(sc_ones a++S0::(sc_ones k++L),S1,sc_ones k++R)).
Proof.
 induction k as [|k IH];intros a L R.
 - cbn [Nat.mul Nat.add sc_ones repeat app]. apply sc_R_same;reflexivity.
 - replace (2*S k+a) with ((2*k+a)+2) by lia.
   eapply sc_R_trans;[eapply sc_R_steps;apply pc_transfer|].
   pose proof (IH a (S1::L) (S1::R)) as E.
   rewrite !sc_ones_push in E. exact E.
Qed.
Lemma pc_R_loop_B : forall k a w r,
 sc_R tm (pc_B (2*k+a) w r) (pc_B a (pc_inc k w) (k+r)).
Proof.
 intros. unfold pc_B. eapply sc_R_trans;[apply pc_R_loop|].
 rewrite <- (pc_ones_app k r).
 pose proof (pc_R_inc tm StB (sc_ones a++[S0]) k w S1 (sc_ones k++sc_ones r)) as E.
 rewrite <-!app_assoc in E. cbn [app] in E. exact E.
Qed.
Lemma pc_R_even : forall k w r,
 sc_R tm (pc_B (2*k) w r) (pc_D (pc_inc (k+1) w) (k+r)).
Proof.
 intros k w r. unfold pc_B. replace (2*k) with (2*k+0) by lia.
 eapply sc_R_trans;[apply pc_R_loop|].
 eapply sc_R_trans;[eapply sc_R_steps;apply pc_even_exit|].
 unfold pc_D. rewrite <- (pc_ones_app k r).
 replace (k+1) with (S k) by lia.
 apply (pc_R_inc tm StD [] (S k) w S0 (sc_ones k++sc_ones r)).
Qed.
Lemma pc_R_odd_empty : forall k r,
 sc_R tm (pc_B (2*k+1) [] r) (pc_B (k+2) [] (k+r)).
Proof.
 intros. eapply sc_R_trans;[apply pc_R_loop_B|].
 eapply sc_R_trans;[eapply sc_R_steps;apply pc_odd_exit|].
 unfold pc_B. cbn [pc_word pc_inc sc_ones repeat app].
 replace (k+2) with (S(S k)) by lia. cbn [sc_ones repeat app].
 apply sc_R_same;reflexivity.
Qed.
Lemma pc_R_odd_cons : forall k b w r,
 sc_R tm (pc_B (2*k+1) (b::w) r) (pc_B (k+b+2) w (k+r)).
Proof.
 intros. eapply sc_R_trans;[apply pc_R_loop_B|].
 eapply sc_R_trans;[eapply sc_R_steps;apply pc_odd_exit|].
 unfold pc_B. cbn [pc_word pc_inc].
 replace (k+b+2) with (S(S(k+b))) by lia.
 apply sc_R_same;reflexivity.
Qed.

Lemma pc_parity : forall a, exists k, a=2*k \/ a=2*k+1.
Proof.
 intro a. exists (a/2). pose proof (Nat.div_mod a 2 ltac:(lia)).
 pose proof (Nat.mod_upper_bound a 2 ltac:(lia)). lia.
Qed.
Lemma pc_even_found : forall k w r,
 (pc_wf w \/ (w=[] /\ 0<k)) -> 0<k+r -> pc_found tm (pc_B (2*k) w r).
Proof.
 intros k w r W P. exists (pc_inc (k+1) w),(k+r).
 split.
 - destruct W as [W|[->W]].
   + apply pc_inc_wf;exact W.
   + cbn [pc_inc pc_wf]. lia.
 - split;[exact P|apply pc_R_even].
Qed.
(** The exceptional terminal values 0 and 3 are never admitted. *)
Lemma pc_terminal_found : forall a r, pc_good a [] r -> pc_found tm (pc_B a [] r).
Proof.
 induction a as [a IH] using lt_wf_ind. intros r G.
 cbn [pc_good] in G. destruct (pc_parity a) as (k&[Ea|Ea]);subst a.
 - apply pc_even_found; [right;split;[reflexivity|lia]|lia].
 - destruct k as [|[|k]].
   + eapply pc_found_back;[apply (pc_R_odd_empty 0 r)|].
     change (pc_found tm (pc_B (2*1) [] (0+r))).
     apply pc_even_found;[right;split;[reflexivity|lia]|lia].
   + exfalso;lia.
   + eapply pc_found_back;[apply pc_R_odd_empty|].
     apply IH;[lia|]. cbn [pc_good]. right;right;lia.
Qed.
Lemma pc_all_found : forall w a r, pc_good a w r -> pc_found tm (pc_B a w r).
Proof.
 assert (E : forall n w, length w=n -> forall a r,
  pc_good a w r -> pc_found tm (pc_B a w r)).
 { induction n as [n IH] using lt_wf_ind. intros [|b w] En a r G.
   - apply pc_terminal_found;exact G.
   - destruct G as [W P]. destruct (pc_parity a) as (k&[Ea|Ea]);subst a.
     + apply pc_even_found;[left;exact W|lia].
     + eapply pc_found_back;[apply pc_R_odd_cons|].
       apply (IH (length w));[cbn [length] in En;lia|reflexivity|].
       apply pc_pop_good;exact W. }
 intros. exact (E (length w) w eq_refl a r H).
Qed.
Lemma pc_D_return : forall w r, pc_wf w -> 0<r -> exists a v s,
 pc_good a v s /\ sc_R tm (pc_D w r) (pc_B a v s).
Proof.
 intros w [|[|r]] W P;[lia| |].
 - exists 1,w,0. split.
   + destruct w;[contradiction|]. split;[exact W|lia].
   + apply sc_R_steps with(k:=4). apply pc_D_short.
 - exists r,(0::w),1. split.
   + split;[apply pc_prepend_wf;exact W|lia].
   + unfold pc_D. eapply sc_R_trans;[apply sc_R_padR|].
     replace (S(S r)) with (r+2) by lia.
     eapply sc_R_steps. apply pc_D_long.
Qed.

Lemma pc_odd_fire : forall L R t, t<>(StA,S1) -> t<>(StD,S0) ->
 tri_reaches_fire tm t (StB,(S1::S0::L,S1,R)).
Proof.
 intros L R [q h] EA ED; destruct q,h.
 - eapply (sc_fire_steps tm) with (n:=4) (d:=(StA,(S0::S1::L,S0,R)));
   [pc_compute|apply sc_fire_now].
 - contradiction.
 - eapply (sc_fire_steps tm) with (n:=5) (d:=(StB,(S1::L,S0,S1::R)));
   [pc_compute|apply sc_fire_now].
 - apply sc_fire_now.
 - eapply (sc_fire_steps tm) with (n:=2) (d:=(StC,(L,S0,S1::S0::R)));
   [pc_compute|apply sc_fire_now].
 - eapply (sc_fire_steps tm) with (n:=1) (d:=(StC,(S0::L,S1,S0::R)));
   [pc_compute|apply sc_fire_now].
 - contradiction.
 - eapply (sc_fire_steps tm) with (n:=3) (d:=(StD,(S1::L,S1,S0::R)));
   [pc_compute|apply sc_fire_now].
Qed.
Lemma pc_transfer_A1 : forall a L R,
 tri_reaches_fire tm (StA,S1) (StB,(sc_ones(a+2)++S0::L,S1,R)).
Proof.
 intros. eapply (sc_fire_steps tm);[apply pc_B1_enter|].
 eapply (sc_fire_steps tm);[apply pc_C1_sweep|]. cbn [ctl chd].
 replace (a+2) with (S(S a)) by lia. cbn [sc_ones repeat app].
 eapply (sc_fire_steps tm);[apply pc_C0_turn|apply sc_fire_now].
Qed.
Lemma pc_D_A1 : forall r L,
 tri_reaches_fire tm (StA,S1) (StD,(L,S0,sc_ones(r+2))).
Proof.
 intros. replace (r+2) with (S(S r)) by lia. cbn [sc_ones repeat].
 eapply (sc_fire_steps tm) with (n:=2) (d:=(StA,(S0::S0::L,S1,sc_ones r)));
 [pc_compute|apply sc_fire_now].
Qed.
Lemma pc_R_D_long : forall r w,
 sc_R tm (pc_D w (r+2)) (pc_B r (0::w) 1).
Proof.
 intros. unfold pc_D. eapply sc_R_trans;[apply sc_R_padR|].
 eapply sc_R_steps;apply pc_D_long.
Qed.
Lemma pc_R_D_even : forall k w,
 sc_R tm (pc_D w (2*k+2)) (pc_D ((k+1)::w) (k+1)).
Proof.
 intros. eapply sc_R_trans;[apply pc_R_D_long|].
 pose proof (pc_R_even k (0::w) 1) as E.
 cbn [pc_inc] in E. rewrite Nat.add_0_r in E. exact E.
Qed.
Lemma pc_R_D_odd : forall k w,
 sc_R tm (pc_D w (2*k+3)) (pc_B 1 (k::w) (k+1)).
Proof.
 intros. replace (2*k+3) with ((2*k+1)+2) by lia.
 eapply sc_R_trans;[apply pc_R_D_long|].
 pose proof (pc_R_loop_B k 1 (0::w) 1) as E.
 cbn [pc_inc] in E. rewrite Nat.add_0_r in E. exact E.
Qed.
Lemma pc_D_one_all : forall w t, pc_wf w -> tri_reaches_fire tm t (pc_D w 1).
Proof.
 intros w [q h] W. destruct q,h;
 try solve [apply sc_fire_now];
 try solve [eapply (sc_fire_steps tm);[apply pc_D_short|apply pc_odd_fire;discriminate]].
 destruct w as [|b w];[contradiction|].
 eapply (sc_fire_steps tm);[apply pc_D_short|].
 eapply (sc_fire_steps tm);[apply pc_odd_exit|].
 change (tri_reaches_fire tm (StA,S1)
  (StB,(sc_ones (S(S b))++S0::pc_word w,S1,[]))).
 replace (S(S b)) with (b+2) by lia. apply pc_transfer_A1.
Qed.
Lemma pc_D_odd_all : forall k w t, tri_reaches_fire tm t (pc_D w (2*k+3)).
Proof.
 intros k w [q h]. destruct q,h;
 try solve [apply sc_fire_now];
 try solve [eapply (sc_fire_R tm);[apply pc_R_D_odd|apply pc_odd_fire;discriminate]].
 replace (2*k+3) with ((2*k+1)+2) by lia. apply pc_D_A1.
Qed.
(** A non-firing even pass halves the right block; odd passes fire. *)
Lemma pc_D_all_fire : forall r w t, pc_wf w -> 0<r ->
 tri_reaches_fire tm t (pc_D w r).
Proof.
 induction r as [r IH] using lt_wf_ind. intros w t W P.
 destruct (pc_parity r) as (k&[Er|Er]);subst r.
 - destruct k as [|k];[lia|]. replace (2*S k) with (2*k+2) by lia.
   eapply (sc_fire_R tm);[apply pc_R_D_even|].
   apply IH;[lia|apply pc_prepend_wf;exact W|lia].
 - destruct k as [|k].
   + apply pc_D_one_all;exact W.
   + replace (2*S k+1) with (2*k+3) by lia. apply pc_D_odd_all.
Qed.
Lemma pc_D_progress : forall w r, pc_wf w -> 0<r -> exists v s k,
 pc_wf v /\ 0<s /\ 0<k /\
 stepn tm k (lift(pc_D w r))=Some(lift(pc_D v s)).
Proof.
 intros w r W P. destruct (pc_D_return w r W P) as (a&v&s&G&n&En).
 destruct (pc_all_found v a s G) as (u&t&U&Q&m&Em).
 assert (Hn : 0<n).
 { destruct n;[cbn [stepn pc_D pc_B lift] in En;discriminate|lia]. }
 exists u,t,(n+m). repeat split;try assumption;try lia.
 rewrite stepn_add,En. exact Em.
Qed.
Theorem pair_stack_neverqhtr :
 (exists T w r, pc_wf w /\ 0<r /\ stepn tm T InitES=Some(lift(pc_D w r))) ->
 NeverQuasiHaltsTr tm.
Proof.
 intro Boot.
 assert (Reach : forall N,exists T w r,N<=T /\ pc_wf w /\ 0<r /\
  stepn tm T InitES=Some(lift(pc_D w r))).
 { induction N as [|N IH].
   - destruct Boot as (T&w&r&W&P&E). exists T,w,r. repeat split;try assumption;lia.
   - destruct IH as (T&w&r&HT&W&P&E).
     destruct (pc_D_progress w r W P) as (v&s&k&V&Q&Hk&Ek).
     exists (T+k),v,s. repeat split;try assumption;try lia.
     rewrite stepn_add,E. exact Ek. }
 intros t _ N. destruct (Reach N) as (T&w&r&HT&W&P&E).
 destruct (pc_D_all_fire r w t W P) as (k&c&Ek&Et).
 exists (T+k). split;[lia|]. exists c. split;[|exact Et].
 rewrite stepn_add,E. exact Ek.
Qed.
End PairStack.
