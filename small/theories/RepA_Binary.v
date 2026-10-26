(** The remaining binary counter has a three-phase right wall.
    At each overflow the wall cycles [] -> [1;1] -> [1] -> [].
    The empty-wall overflow preserves width; the other two increase it.
    All three overflow runs and every ordinary increment are checked. *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From SmallBB Require Import Statement StatementTr CTape Size Bounds Mirror
 KnownCensus SwapSymbols Binary23Counter.
From SmallBB.Counters Require Import WTape MonoCounter JpCounter IXPGadgets
 LapCertGlue LapCertGlueLift NestedLap NestedLapLift LapGlueTr.
From SmallBB.Checkers Require Import LapDecider.
From SmallBB.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Definition ba_tm:TM:=machine_of_codes 2 3 [7;8;3;5;4;6].
Definition ba_C(p:positive)(wall:list Sym):cconf:=(StB,(bc23_E p,S1,wall)).
Definition ba_Z0:=mkC StB (mkS [S0;S1] [] 0 0 []) S1 (sflat []).
Definition ba_Z1:=mkC StB (mkS [S1;S1] [] 0 0 []) S1 (sflat []).
Definition ba_P0:=mkC StB (mkS [S1;S1] [S1;S1] 1 0 [S0;S1]) S1 (sflat []).
Definition ba_P1:=mkC StB (mkS [S0;S1] [S0;S1] 1 0 [S1;S1]) S1 (sflat []).
Definition ba_int_steps:list lstep:=[SWin 2;SCycL 2 0;SWin 2;SCycR 2;SWin 2].
Lemma ba_zero:srun ba_tm false false [SWin 2] ba_Z0=Some(ba_Z1,0,2).
Proof. vm_compute;reflexivity. Qed.
Lemma ba_pos:srun ba_tm false false ba_int_steps ba_P0=Some(ba_P1,4,6).
Proof. vm_compute;reflexivity. Qed.
Lemma ba_interior:forall wall p j q,cview p=(j,Some q)->
 exists n,0<n /\ csteps ba_tm n (ba_C p wall)=Some(ba_C(Pos.succ p)wall).
Proof.
 intros wall p j q H;destruct(bc23_some p j q H)as[H1 H2].
 destruct j as[|j].
 - exists 2;split;[lia|].
   assert(HC:ba_C p wall=cden(bc23_E q)wall 0 ba_Z0).
   { unfold ba_C;rewrite H1;reflexivity. }
   rewrite HC. etransitivity;[exact(srun_sound ba_tm false false [SWin 2] ba_Z0 ba_Z1 0 2
     ba_zero (bc23_E q)wall 0 ltac:(discriminate) ltac:(discriminate))|].
   unfold ba_C;rewrite H2;reflexivity.
 - exists(4*j+6);split;[lia|].
   assert(HC:ba_C p wall=cden(bc23_E q)wall j ba_P0).
   { unfold ba_C;rewrite H1. unfold cden,sden,ba_P0;cbn.
     repeat rewrite Nat.add_0_r. rewrite <-?app_assoc;reflexivity. }
   rewrite HC. etransitivity;[exact(srun_sound ba_tm false false ba_int_steps ba_P0 ba_P1 4 6
     ba_pos (bc23_E q)wall j ltac:(discriminate) ltac:(discriminate))|].
   unfold ba_C;rewrite H2. unfold cden,sden,ba_P1;cbn.
   repeat rewrite Nat.add_0_r. rewrite <-?app_assoc;reflexivity.
Qed.
Lemma ba_to_fill:forall p wall,exists n,
 stepn ba_tm n(lift(ba_C p wall))=Some(lift(ba_C(fill p)wall)).
Proof.
 intros p wall. apply(inner_to_fill_lift ba_tm(fun v=>ba_C v wall)).
 intros v i q H;destruct(ba_interior wall v i q H)as[n[Hn Hr]].
 exists n,(ba_C(Pos.succ v)wall);auto.
Qed.

Definition ba_base j wall:=ba_C(fill(pow2(S j)))wall.
Definition ba_O0(w:list Sym):=mkC StB (mkS [S1;S1] [S1;S1] 1 0 [S1]) S1 (sflat w).
Definition ba_Oplus:=mkC StB (mkS [S0;S1;S1;S1] [S0;S1] 1 0 [S1]) S1 (sflat []).
Definition ba_Oempty:=mkC StB (mkS [S1;S1] [S0;S1] 1 0 [S1]) S1 (sflat [S1;S1]).
Definition ba_plus_steps:list lstep:=
 [SWin 2;SCycL 2 0;SWin 1;SWinL 3;SCycR 2;SWin 7;SRotL 1].
Definition ba_empty_steps:list lstep:=
 [SWin 2;SCycL 2 0;SWin 1;SWinL 3;SCycR 2;SWin 6;SWinR 3;SRotL 1].
Lemma ba_plus:srun ba_tm true false ba_plus_steps(ba_O0 [S1])=Some(ba_Oplus,4,13).
Proof. vm_compute;reflexivity. Qed.
Lemma ba_empty:srun ba_tm true true ba_empty_steps(ba_O0 [])=Some(ba_Oempty,4,15).
Proof. vm_compute;reflexivity. Qed.
Lemma ba_base_shape:forall j w U,ba_base j(w++U)=cden [] U j(ba_O0 w).
Proof.
 intros j w U;unfold ba_base,ba_C;rewrite bc23_fill.
 unfold cden,sden,ba_O0,sflat;cbn. rewrite ?app_nil_r.
 repeat rewrite Nat.add_0_r;reflexivity.
Qed.
Lemma ba_plus_shape:forall j U,cden [] U j ba_Oplus=ba_C(bc23_jump j)U.
Proof.
 intros j U;unfold ba_C,bc23_jump;cbn[bc23_E];rewrite bc23_pow.
 unfold cden,sden,ba_Oplus,sflat;cbn. rewrite ?app_nil_r.
 repeat rewrite Nat.add_0_r;reflexivity.
Qed.
Definition ba_jump0 j:=xI(pow2 j).
Lemma ba_empty_shape:forall j,cden[][]j ba_Oempty=ba_C(ba_jump0 j)[S1;S1].
Proof.
 intro j;unfold ba_C,ba_jump0;cbn[bc23_E];rewrite bc23_pow.
 unfold cden,sden,ba_Oempty,sflat;cbn. rewrite ?app_nil_r.
 repeat rewrite Nat.add_0_r;reflexivity.
Qed.
Lemma ba_phase_plus:forall j U,exists n,0<n /\
 stepn ba_tm n(lift(ba_base j(S1::U)))=Some(lift(ba_base(S j)U)).
Proof.
 intros j U;destruct(ba_to_fill(bc23_jump j)U)as[n Hr].
 exists(4*j+13+n);split;[lia|].
 rewrite stepn_add. replace (S1::U) with ([S1]++U) by reflexivity.
 rewrite (ba_base_shape j [S1] U).
 rewrite(csteps_lift _ _ _ _(srun_sound ba_tm true false ba_plus_steps(ba_O0 [S1])ba_Oplus
   4 13 ba_plus [] U j ltac:(reflexivity)ltac:(discriminate))).
 rewrite ba_plus_shape. exact Hr.
Qed.
Lemma ba_phase_empty:forall j,exists n,0<n /\
 stepn ba_tm n(lift(ba_base j []))=Some(lift(ba_base j [S1;S1])).
Proof.
 intro j;destruct(ba_to_fill(ba_jump0 j)[S1;S1])as[n Hr].
 exists(4*j+15+n);split;[lia|].
 rewrite stepn_add.
 pose proof(ba_base_shape j [] [])as HC;cbn[app]in HC;rewrite HC.
 rewrite(csteps_lift _ _ _ _(srun_sound ba_tm true true ba_empty_steps(ba_O0 [])ba_Oempty
   4 15 ba_empty [][]j ltac:(reflexivity)ltac:(reflexivity))).
 rewrite ba_empty_shape. exact Hr.
Qed.
Lemma ba_cycle:forall j,exists n,0<n /\
 stepn ba_tm n(lift(ba_base j []))=Some(lift(ba_base(j+2)[])).
Proof.
 intro j;destruct(ba_phase_empty j)as[n0[H0 R0]].
 destruct(ba_phase_plus j [S1])as[n1[H1 R1]].
 destruct(ba_phase_plus(S j)[])as[n2[H2 R2]].
 exists(n0+(n1+n2));split;[lia|].
 rewrite stepn_add,R0,stepn_add,R1. replace(j+2)with(S(S j))by lia. exact R2.
Qed.
Definition ba_anchor j:=ba_base(2*j+2)[].
Lemma ba_anchor_step:forall j,exists n,0<n /\
 stepn ba_tm n(lift(ba_anchor j))=Some(lift(ba_anchor(S j))).
Proof.
 intro j;unfold ba_anchor. replace(2*S j+2)with((2*j+2)+2)by lia. apply ba_cycle.
Qed.
Lemma ba_boot:stepn ba_tm 76 InitES=Some(lift(ba_anchor 0)).
Proof. rewrite <-lift_c0;apply csteps_lift;vm_compute;reflexivity. Qed.
Lemma ba_reachable:forall j,exists n,j<=n /\
 stepn ba_tm n InitES=Some(lift(ba_anchor j)).
Proof.
 induction j as[|j[n[Hn Hr]]].
 - exists 76;split;[lia|exact ba_boot].
 - destruct(ba_anchor_step j)as[k[Hk Hs]].
   exists(n+k);split;[lia|]. rewrite stepn_add,Hr;exact Hs.
Qed.
Lemma ba_nonhalt:NonHalt ba_tm.
Proof.
 intros n Hn;destruct(ba_reachable n)as[T[HT Hr]].
 destruct(stepn_prefix ba_tm n T InitES _ HT Hr)as[c[Hc _]]. congruence.
Qed.
Definition ba_fire_steps(t:Instr):list lstep:=match t with
 |(StA,S0)=>[SWin 2;SCycL 2 0;SWin 1;SWinL 1]
 |(StA,S1)=>[SWin 1]
 |(StA,S2)=>[SWin 2;SCycL 2 0;SWin 1;SWinL 3]
 |(StB,S0)=>[SWin 2;SCycL 2 0;SWin 1;SWinL 3;SCycR 2;SWin 6;SWinR 1]
 |(StB,S1)=>[]
 |(StB,S2)=>[SWin 2;SCycL 2 0;SWin 1;SWinL 2]
 | _=>[] end.
Lemma ba_fire_check:forall q h,q<>StC->
 srun_instr ba_tm true true(ba_fire_steps(q,h))(ba_O0 [])=Some(q,h).
Proof. destruct q,h;intro H;try contradiction;vm_compute;reflexivity. Qed.
Lemma ba_anchor_fires:forall q h j,q<>StC->
 exists k c,csteps ba_tm k(ba_anchor j)=Some c /\ cinstr c=(q,h).
Proof.
 intros q h j Hq.
 exact(fire_of_run_instr ba_tm (fun _=>ba_anchor j) true true
   (ba_fire_steps(q,h)) (ba_O0 []) xH (2*j+2) [][] (q,h)
   (ba_fire_check q h Hq) ltac:(reflexivity)ltac:(reflexivity)
   (ba_base_shape(2*j+2)[][])).
Qed.
Lemma ba_recurrence:forall q h,q<>StC->forall N,
 exists n,N<=n /\ FiresAt ba_tm(q,h)n.
Proof.
 intros q h Hq N;destruct(ba_reachable N)as[T[HT Hr]].
 destruct(ba_anchor_fires q h N Hq)as[k[c[Hc He]]].
 exists(T+k);split;[lia|]. exists(lift c);split.
 - rewrite stepn_add,Hr;exact(csteps_lift _ _ _ _ Hc).
 - rewrite cinstr_lift;exact He.
Qed.
Theorem ba_never_quasihalts:NeverQuasiHaltsTr ba_tm.
Proof.
 intros[q h] Hf N;destruct q.
 - apply ba_recurrence;discriminate.
 - apply ba_recurrence;discriminate.
 - destruct Hf as[n[c[Hr Hi]]].
   assert(Hhalt:stepn ba_tm(n+1)InitES=None).
   { rewrite stepn_add,Hr. destruct c as[p tp].
     unfold instr_of in Hi;cbn in Hi;injection Hi as Hp He;subst p.
     cbn[stepn step fst snd]. unfold ba_tm,machine_of_codes;reflexivity. }
   exfalso;exact(ba_nonhalt _ Hhalt).
Qed.
Theorem binary23_rep1_bound:QHBoundTr 67(machine_of_codes 2 3 [5;10;1;7;6;4]).
Proof.
 apply mirror_qhbound.
 assert(E:mirror_tm(machine_of_codes 2 3 [5;10;1;7;6;4])=ba_tm).
 { apply same_table_sound;reflexivity. }
 rewrite E;intros t s [Hf Hquiet].
 destruct(ba_never_quasihalts t (ex_intro _ s Hf)(S s))as[n[Hn Hfire]].
 exfalso;apply(Hquiet n);[lia|exact Hfire].
Qed.
Print Assumptions binary23_rep1_bound.
