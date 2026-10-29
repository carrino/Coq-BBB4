(** A closed original run is established before importing a completion's
    state bound. Completion recurrence alone says nothing about a partial run. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape PosEnc Closure HistCensus HistRankSearch
 Census OneStateConditional.
From BBB24.Checkers Require Import NGram NGramHist.
Import ListNotations.

Definition ct_nonhalt_check tm k n t fuel rounds :=
 (1<=?n) && match hcsteps tm k t hcconf0 with
 |None=>false
 |Some cc=>let '(_, (l,_,r)):=cc in
  let a0:=hng_start n cc in
  let '(ls,rs):=hn_grow tm k n a0 fuel rounds(hseed_side n l)(hseed_side n r)in
  let Sl:=hn_explore tm k n ls rs fuel [] PositiveSet.empty[a0]in
  hseed_ok n ls rs cc &&
  (closed_b hcconf hctx_enc(hng_succs tm k n ls rs)Sl &&
   mem hcconf hctx_enc a0 Sl)
 end.

Theorem ct_nonhalt_check_sound : forall tm k n t fuel rounds,
 ct_nonhalt_check tm k n t fuel rounds=true -> NonHalt tm.
Proof.
 intros tm k n t fuel rounds H;unfold ct_nonhalt_check in H.
 apply andb_true_iff in H as[Hn H];apply Nat.leb_le in Hn.
 destruct(hcsteps tm k t hcconf0)as[[q[[l h]r]]|]eqn:Et;[|discriminate].
 match type of H with(let '(_,_) := ?G in _)=true=>destruct G as[ls rs]end.
 cbv beta iota zeta in H;repeat rewrite andb_true_iff in H.
 destruct H as[Hseed[Hclosed Hmem]].
 set(cc0:=hproj(q,(l,h,r)))in *;set(a0:=hng_start n(q,(l,h,r)))in *.
 set(Sl:=hn_explore tm k n ls rs fuel [] PositiveSet.empty[a0])in *.
 assert(Hin:In a0 Sl)by(eapply mem_In;[exact hctx_enc_inj|exact Hmem]).
 assert(Hcov:hcovers n ls rs a0(lift cc0)).
 {exists(q,(l,h,r));split;[reflexivity|];apply hng_start_covers;exact Hseed. }
 assert(Eprefix:stepn tm t InitES=Some(lift cc0)).
 {rewrite <-lift_c0;eapply csteps_lift;rewrite <-hproj_hcconf0;eapply hcsteps_proj;exact Et. }
 assert(Hsucc:forall a c,hcovers n ls rs a c ->
  match hng_succs tm k n ls rs a with
  |Some xs=>match step tm c with
   |Some c'=>exists a',In a' xs /\ hcovers n ls rs a' c'|None=>False end
  |None=>True end).
 {intros;apply hng_succs_sound;assumption. }
 assert(Hinv:forall N,exists cc a,csteps tm N cc0=Some cc /\ In a Sl /\ hcovers n ls rs a(lift cc)).
 {intro N;eapply closure_invariant_c;[exact hctx_enc_inj|exact Hsucc|exact Hclosed|exact Hin|exact Hcov]. }
 intros j Hj;destruct(le_lt_dec t j).
 - destruct(Hinv(j-t))as(cc&a&EN&_).
   replace j with(t+(j-t))in Hj by lia;rewrite stepn_add,Eprefix in Hj.
   rewrite(csteps_lift tm(j-t)cc0 cc EN)in Hj;discriminate.
 - destruct(stepn_prefix tm j t InitES(lift cc0)ltac:(lia)Eprefix)as(c&E&_);congruence.
Qed.

Theorem ct_state_bound_back : forall tm completion B,
 NonHalt tm -> TM_le tm completion -> QHBound B completion -> QHBound B tm.
Proof.
 intros tm completion B Hnh Hle Hb.
 assert(Hv:forall q n,VisitsAt completion q n <-> VisitsAt tm q n).
 {intros q n;unfold VisitsAt;rewrite(extend_run tm completion Hnh Hle n);tauto. }
 intros q s[Hq Hquiet];apply(Hb q s);split.
 - apply Hv;exact Hq.
 - intros n Hn Hqn;apply(Hquiet n Hn);apply Hv;exact Hqn.
Qed.
Print Assumptions ct_nonhalt_check_sound.
Print Assumptions ct_state_bound_back.
