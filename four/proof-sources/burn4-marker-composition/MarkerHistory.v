(** Compose independent proofs of A and B recurrence. The marker invariant
    covers reachable A returns; a closed history graph supplies only B ranks. *)
From Coq Require Import List Arith Lia Bool NArith.
From BBB24 Require Import Statement Spec CTape PosEnc Closure HistCensus HistRankSearch
  OneStateReach MarkerState MarkerPotential TotalCompletion.
From BBB24.Checkers Require Import NGramHist.
From BBB24Burn3RelaxedMarker Require Import RelaxedMarker.
Import ListNotations.

Definition mh_history_target tm goal k n t fuel rounds :=
 if 1<=?n then match hcsteps tm k t hcconf0 with
 |None=>false
 |Some cc=>let '(q,(l,h,r)):=cc in
   let a0:=hng_start n cc in
   let '(ls,rs):=hn_grow tm k n a0 fuel rounds(hseed_side n l)(hseed_side n r)in
   let Sl:=hn_explore tm k n ls rs fuel [] PositiveSet.empty[a0]in
   hseed_ok n ls rs cc &&
   (closed_b hcconf hctx_enc(hng_succs tm k n ls rs)Sl &&
   (mem hcconf hctx_enc a0 Sl &&
   rank_ok hcconf(fun a=>fst(hainstr a))(hng_succs tm k n ls rs)Sl goal
    (compute_ranks hcconf hctx_enc(fun a=>fst(hainstr a))(hng_succs tm k n ls rs)Sl goal)))
 end else false.

Theorem mh_history_target_recur : forall tm goal k n t fuel rounds,
 mh_history_target tm goal k n t fuel rounds=true ->
 forall N,exists j,N<=j /\ VisitsAt tm goal j.
Proof.
 intros tm goal k n t fuel rounds H N;unfold mh_history_target in H.
 destruct(1<=?n)eqn:Hn;[apply Nat.leb_le in Hn|discriminate].
 destruct(hcsteps tm k t hcconf0)as[[q[[l h]r]]|]eqn:Et;[|discriminate].
 match type of H with(let '(_,_) := ?G in _)=true=>destruct G as[ls rs]end.
 cbv beta iota zeta in H;repeat rewrite andb_true_iff in H.
 destruct H as[Hseed[Hcl[Hmem Hr]]].
 set(a0:=hng_start n(q,(l,h,r)))in *.
 set(Sl:=hn_explore tm k n ls rs fuel [] PositiveSet.empty[a0])in *.
 assert(Hin:In a0 Sl)by(eapply mem_In;[exact hctx_enc_inj|exact Hmem]).
 assert(Hcov:hcovers n ls rs a0(lift(hproj(q,(l,h,r))))).
 {exists(q,(l,h,r));split;[reflexivity|]. apply hng_start_covers;exact Hseed. }
 assert(Hstate:forall a c,hcovers n ls rs a c -> fst(hainstr a)=fst c).
 {intros a c Hc;rewrite(hcovers_instr n ls rs a c Hc);reflexivity. }
 assert(Hsucc:forall a c,hcovers n ls rs a c ->
  match hng_succs tm k n ls rs a with
  |Some xs=>match step tm c with
    |Some c'=>exists a',In a' xs /\ hcovers n ls rs a' c'|None=>False end
  |None=>True end).
 {intros a c Hc;apply hng_succs_sound;assumption. }
 destruct(closure_invariant tm hcconf hctx_enc(hng_succs tm k n ls rs)
  (hcovers n ls rs)hctx_enc_inj Hsucc Sl Hcl a0 _ Hin Hcov N)
  as(cN&aN&EN&HinN&HcovN).
 assert(Eprefix:stepn tm t InitES=Some(lift(hproj(q,(l,h,r))))).
 {rewrite <-lift_c0;eapply csteps_lift. rewrite <-hproj_hcconf0;eapply hcsteps_proj;exact Et. }
 assert(Er:stepn tm(t+N)InitES=Some cN)by(rewrite stepn_add,Eprefix;exact EN).
 set(rank:=compute_ranks hcconf hctx_enc(fun a=>fst(hainstr a))(hng_succs tm k n ls rs)Sl goal)in *.
 destruct(rank_find tm hcconf hctx_enc(fun a=>fst(hainstr a))(hng_succs tm k n ls rs)
  (hcovers n ls rs)hctx_enc_inj Hstate Hsucc Sl goal rank Hcl Hr
  (S(rank aN))aN cN(t+N)(Nat.lt_succ_diag_r _)HinN HcovN Er)as(j&Hj&Hv).
 exists j;split;[lia|exact Hv].
Qed.

Definition mh_marker_A tm mask w1 w2 w3 :=
 let mark:=ms_mark mask in let weight:=mp_weights w1 w2 w3 in
 negb(mark S0) &&(rmp_preserve tm mark &&(ms_blank tm &&mp_rank_check tm weight)).
Lemma mh_marker_A_recur : forall tm mask w1 w2 w3,
 mh_marker_A tm mask w1 w2 w3=true ->
 NonHalt tm /\ forall N,exists n,N<=n /\ VisitsAt tm StA n.
Proof.
 intros tm mask w1 w2 w3 H;unfold mh_marker_A in H;cbv zeta in H.
 repeat rewrite andb_true_iff in H;destruct H as[Hm[Hp[Hb Hr]]].
 assert(Htotal:Total tm)by(eapply rmp_preserve_total;exact Hp).
 split;[apply ore_total_nonhalt;exact Htotal|].
 set(weight:=mp_weights w1 w2 w3).
 assert(Hz:weight S0=0)by reflexivity.
 intro N;destruct(ore_total_csteps tm Htotal N c0)as(cc&Eprefix).
 assert(Hi:ms_inv(ms_mark mask)cc)by(eapply rmp_inv_steps;[exact Hp|apply ms_inv_initial|exact Eprefix]).
 set(padded:=mp_pad(S(mp_weight weight cc))cc).
 assert(Hpi:ms_inv(ms_mark mask)padded)by(apply mp_pad_inv;exact Hi).
 assert(Hpc:mp_capacity weight padded)by(apply mp_padded_capacity;exact Hz).
 destruct(rmp_reaches_A tm(ms_mark mask)weight Hz Hp Hr padded Hpi Hpc)as(k&cc'&Etail&Hstate).
 exists(N+k);split;[lia|]. exists(lift cc');split;[|exact Hstate].
 rewrite stepn_add.
 pose proof(csteps_lift tm N c0 cc Eprefix)as Hprefix.
 rewrite lift_c0 in Hprefix;rewrite Hprefix.
 pose proof(csteps_lift tm k padded cc' Etail)as Htail.
 unfold padded in Htail;rewrite mp_pad_lift in Htail;exact Htail.
Qed.
Definition mh_check tm mask w1 w2 w3 k n t fuel rounds :=
 mh_marker_A tm mask w1 w2 w3 &&mh_history_target tm StB k n t fuel rounds.
Theorem mh_check_sound : forall tm mask w1 w2 w3 k n t fuel rounds,
 mh_check tm mask w1 w2 w3 k n t fuel rounds=true -> NonHalt tm /\ QHBound 0 tm.
Proof.
 intros tm mask w1 w2 w3 k n t fuel rounds H;apply andb_true_iff in H as[HA HB].
 destruct(mh_marker_A_recur tm mask w1 w2 w3 HA)as[Hnh HAr].
 pose proof(mh_history_target_recur tm StB k n t fuel rounds HB)as HBr.
 split;[exact Hnh|]. intros q s[_ Hquiet];destruct q.
 - destruct(HAr(S s))as(j&Hj&Hv);exfalso;apply(Hquiet j);[lia|exact Hv].
 - destruct(HBr(S s))as(j&Hj&Hv);exfalso;apply(Hquiet j);[lia|exact Hv].
Qed.
Print Assumptions mh_check_sound.
