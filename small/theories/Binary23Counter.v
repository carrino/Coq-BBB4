(** The mirrored machine [1RB2LA0RB_2LB1LA1RA] is a binary counter.
    At an anchor the state/head are B/1, the right wall is [2;2], and the
    left tape encodes a positive number with low bit first: 0 -> [0;1],
    1 -> [1;1], and a terminal [1].

    Interior laps increment this number. An overflow starting at
    [2^(j+2)-1] reaches [2^(j+2)+2] in [4*j+17] steps. Interior laps then
    reach the next all-ones anchor. The proof uses [inner_to_fill_lift]
    for this finite sequence of increments; it never expands its length.

    Every active instruction occurs during each overflow. The final
    theorem transports the instruction bound back by tape reflection. *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From SmallBB Require Import Statement StatementTr CTape Size Bounds Mirror KnownCensus SwapSymbols.
From SmallBB.Counters Require Import WTape MonoCounter JpCounter IXPGadgets
 LapCertGlue LapCertGlueLift NestedLap NestedLapLift LapGlueTr.
From SmallBB.Checkers Require Import LapDecider.
From SmallBB.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Definition bc23_tm:TM:=machine_of_codes 2 3 [7;8;3;9;4;6].
Fixpoint bc23_E(p:positive):list Sym:=match p with
 |xH=>[S1]|xO q=>[S0;S1]++bc23_E q|xI q=>[S1;S1]++bc23_E q end.
Definition bc23_C(p:positive):cconf:=(StB,(bc23_E p,S1,[S2;S2])).
Lemma bc23_some:forall p j q,cview p=(j,Some q)->
 bc23_E p=rep [S1;S1] j++[S0;S1]++bc23_E q /\
 bc23_E(Pos.succ p)=rep [S0;S1] j++[S1;S1]++bc23_E q.
Proof.
 induction p;intros j q H;simpl in H.
 - destruct(cview p)as[j' r]eqn:E;inversion H;subst j r.
   destruct(IHp j' q eq_refl)as[H1 H2];split;simpl;[rewrite H1|rewrite H2];reflexivity.
 - inversion H;subst j q;split;reflexivity.
 - discriminate.
Qed.
Definition bc23_Z0:=mkC StB (mkS [S0;S1] [] 0 0 []) S1 (mkS [S2;S2] [] 0 0 []).
Definition bc23_Z1:=mkC StB (mkS [S1;S1] [] 0 0 []) S1 (mkS [S2;S2] [] 0 0 []).
Definition bc23_P0:=mkC StB (mkS [S1;S1] [S1;S1] 1 0 [S0;S1]) S1 (mkS [S2;S2] [] 0 0 []).
Definition bc23_P1:=mkC StB (mkS [S0;S1] [S0;S1] 1 0 [S1;S1]) S1 (mkS [S2;S2] [] 0 0 []).
Definition bc23_int_steps:list lstep:=[SWin 2;SCycL 2 0;SWin 2;SCycR 2;SWin 2].
Lemma bc23_zero:srun bc23_tm false true [SWin 2] bc23_Z0=Some(bc23_Z1,0,2).
Proof. vm_compute;reflexivity. Qed.
Lemma bc23_pos:srun bc23_tm false true bc23_int_steps bc23_P0=Some(bc23_P1,4,6).
Proof. vm_compute;reflexivity. Qed.
Lemma bc23_interior:forall p j q,cview p=(j,Some q)->
 exists n,0<n /\ csteps bc23_tm n (bc23_C p)=Some(bc23_C(Pos.succ p)).
Proof.
 intros p j q H;destruct(bc23_some p j q H)as[H1 H2].
 destruct j as[|j].
 - exists 2;split;[lia|].
   assert(HC:bc23_C p=cden(bc23_E q)[] 0 bc23_Z0).
   { unfold bc23_C;rewrite H1;reflexivity. }
   rewrite HC. etransitivity;[exact(srun_sound bc23_tm false true [SWin 2] bc23_Z0 bc23_Z1 0 2
     bc23_zero (bc23_E q)[] 0 ltac:(discriminate) ltac:(reflexivity))|].
   unfold bc23_C;rewrite H2;reflexivity.
 - exists(4*j+6);split;[lia|].
   assert(HC:bc23_C p=cden(bc23_E q)[] j bc23_P0).
   { unfold bc23_C;rewrite H1. unfold cden,sden,bc23_P0;cbn.
     repeat rewrite Nat.add_0_r. rewrite <-?app_assoc;reflexivity. }
   rewrite HC. etransitivity;[exact(srun_sound bc23_tm false true bc23_int_steps bc23_P0 bc23_P1 4 6
     bc23_pos (bc23_E q)[] j ltac:(discriminate) ltac:(reflexivity))|].
   unfold bc23_C;rewrite H2. unfold cden,sden,bc23_P1;cbn.
   repeat rewrite Nat.add_0_r. rewrite <-?app_assoc;reflexivity.
Qed.

Definition bc23_O0:=mkC StB (mkS [S1;S1] [S1;S1] 1 0 [S1]) S1 (mkS [S2;S2] [] 0 0 []).
Definition bc23_O1:=mkC StB (mkS [S0;S1;S1;S1] [S0;S1] 1 0 [S1]) S1 (mkS [S2;S2] [] 0 0 []).
Definition bc23_over_steps:list lstep:=[SWin 2;SCycL 2 0;SWin 1;SWinL 3;SCycR 2;SWin 8;SWinR 3;SRotL 1].
Lemma bc23_over:srun bc23_tm true true bc23_over_steps bc23_O0=Some(bc23_O1,4,17).
Proof. vm_compute;reflexivity. Qed.
Definition bc23_anchor j:=bc23_C(fill(pow2(S j))).
Definition bc23_jump j:positive:=xO(xI(pow2 j)).
Lemma bc23_pow:forall j,bc23_E(pow2 j)=rep [S0;S1] j++[S1].
Proof. induction j;cbn;[reflexivity|rewrite IHj;reflexivity]. Qed.
Lemma bc23_fill:forall j,bc23_E(fill(pow2 j))=rep [S1;S1] j++[S1].
Proof. induction j;cbn;[reflexivity|rewrite IHj;reflexivity]. Qed.
Lemma bc23_anchor_shape:forall j,bc23_anchor j=cden[][]j bc23_O0.
Proof.
 intro j;unfold bc23_anchor,bc23_C;rewrite bc23_fill.
 unfold cden,sden,bc23_O0;cbn. rewrite ?app_nil_r.
 repeat rewrite Nat.add_0_r;reflexivity.
Qed.
Lemma bc23_jump_shape:forall j,cden[][]j bc23_O1=bc23_C(bc23_jump j).
Proof.
 intro j;unfold bc23_C,bc23_jump;cbn[bc23_E];rewrite bc23_pow.
 unfold cden,sden,bc23_O1;cbn. rewrite ?app_nil_r.
 repeat rewrite Nat.add_0_r;reflexivity.
Qed.
Lemma bc23_jump_fill:forall j,bc23_C(fill(bc23_jump j))=bc23_anchor(S j).
Proof. intro j;unfold bc23_jump,bc23_anchor;reflexivity. Qed.
Lemma bc23_anchor_step:forall j,exists n,0<n /\
 stepn bc23_tm n(lift(bc23_anchor j))=Some(lift(bc23_anchor(S j))).
Proof.
 intro j.
 assert(Hin:forall v i q,cview v=(i,Some q)->exists n c,0<n /\
   csteps bc23_tm n(bc23_C v)=Some c /\ lift c=lift(bc23_C(Pos.succ v))).
 { intros v i q H;destruct(bc23_interior v i q H)as[n[Hn Hr]].
   exists n,(bc23_C(Pos.succ v));auto. }
 destruct(inner_to_fill_lift bc23_tm bc23_C Hin (bc23_jump j))as[n Hn].
 exists(4*j+17+n);split;[lia|].
 rewrite stepn_add,bc23_anchor_shape.
 rewrite(csteps_lift _ _ _ _(srun_sound bc23_tm true true bc23_over_steps bc23_O0 bc23_O1 4 17 bc23_over [][]j ltac:(reflexivity)ltac:(reflexivity))).
 rewrite bc23_jump_shape in *. rewrite bc23_jump_fill in Hn;exact Hn.
Qed.

Lemma bc23_boot:stepn bc23_tm 20 InitES=Some(lift(bc23_anchor 0)).
Proof. rewrite <-lift_c0;apply csteps_lift;vm_compute;reflexivity. Qed.
Lemma bc23_reachable:forall j,exists n,j<=n /\
 stepn bc23_tm n InitES=Some(lift(bc23_anchor j)).
Proof.
 induction j as[|j[n[Hn Hr]]].
 - exists 20;split;[lia|exact bc23_boot].
 - destruct(bc23_anchor_step j)as[k[Hk Hs]].
   exists(n+k);split;[lia|]. rewrite stepn_add,Hr;exact Hs.
Qed.
Lemma bc23_nonhalt:NonHalt bc23_tm.
Proof.
 intros n Hn;destruct(bc23_reachable n)as[T[HT Hr]].
 destruct(stepn_prefix bc23_tm n T InitES _ HT Hr)as[c[Hc _]].
 congruence.
Qed.
Definition bc23_fire_steps(t:Instr):list lstep:=match t with
 |(StA,S0)=>[SWin 2;SCycL 2 0;SWin 1;SWinL 1]
 |(StA,S1)=>[SWin 1]
 |(StA,S2)=>[SWin 2;SCycL 2 0;SWin 1;SWinL 3]
 |(StB,S0)=>[SWin 2;SCycL 2 0;SWin 1;SWinL 3;SCycR 2;SWin 8;SWinR 1]
 |(StB,S1)=>[]
 |(StB,S2)=>[SWin 2;SCycL 2 0;SWin 1;SWinL 2]
 | _=>[] end.
Lemma bc23_fire_check:forall q h,q<>StC->
 srun_instr bc23_tm true true(bc23_fire_steps(q,h))bc23_O0=Some(q,h).
Proof. destruct q,h;intro H;try contradiction;vm_compute;reflexivity. Qed.
Lemma bc23_anchor_fires:forall q h j,q<>StC->
 exists k c,csteps bc23_tm k(bc23_anchor j)=Some c /\ cinstr c=(q,h).
Proof.
 intros q h j Hq.
 exact(fire_of_run_instr bc23_tm (fun _=>bc23_anchor j) true true
   (bc23_fire_steps(q,h)) bc23_O0 xH j [][] (q,h)
   (bc23_fire_check q h Hq) ltac:(reflexivity)ltac:(reflexivity)
   (bc23_anchor_shape j)).
Qed.
Lemma bc23_recurrence:forall q h,q<>StC->forall N,
 exists n,N<=n /\ FiresAt bc23_tm(q,h)n.
Proof.
 intros q h Hq N;destruct(bc23_reachable N)as[T[HT Hr]].
 destruct(bc23_anchor_fires q h N Hq)as[k[c[Hc He]]].
 exists(T+k);split;[lia|]. exists(lift c);split.
 - rewrite stepn_add,Hr;exact(csteps_lift _ _ _ _ Hc).
 - rewrite cinstr_lift;exact He.
Qed.
Theorem bc23_never_quasihalts:NeverQuasiHaltsTr bc23_tm.
Proof.
 intros[q h] Hf N;destruct q.
 - apply bc23_recurrence;discriminate.
 - apply bc23_recurrence;discriminate.
 - destruct Hf as[n[c[Hr Hi]]].
   assert(Hhalt:stepn bc23_tm(n+1)InitES=None).
   { rewrite stepn_add,Hr. destruct c as[p tp].
     unfold instr_of in Hi;cbn in Hi;injection Hi as Hp He;subst p.
     cbn[stepn step fst snd]. unfold bc23_tm,machine_of_codes;reflexivity. }
   exfalso;exact(bc23_nonhalt _ Hhalt).
Qed.
Theorem binary23_rep2_bound:QHBoundTr 67(machine_of_codes 2 3 [5;10;1;11;6;4]).
Proof.
 apply mirror_qhbound.
 assert(E:mirror_tm(machine_of_codes 2 3 [5;10;1;11;6;4])=bc23_tm).
 { apply same_table_sound;reflexivity. }
 rewrite E;intros t s [Hf Hquiet].
 destruct(bc23_never_quasihalts t (ex_intro _ s Hf)(S s))as[n[Hn Hfire]].
 exfalso;apply(Hquiet n);[lia|exact Hfire].
Qed.
Print Assumptions binary23_rep2_bound.
