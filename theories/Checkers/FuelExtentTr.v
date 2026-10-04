(** Natural measures from the normalized finite half-tape extent. *)
From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import NGram FuelClass FuelWide.
From BBB4.Checkers Require Import PatternComplementTr.
Import ListNotations.
Definition xe_reg(side:bool):ngreg:=if side then RgL else RgR.
Definition xe_val(side:bool)(cc:cconf):nat:=
 let '(_,(L,_,R)):=cc in pc_extent(if side then L else R).
Definition xe_live(f:fclass):bool:=match f with F0=>false|_=>true end.
Definition xe_delta(tm:TM)(side:bool)(a:fcconf):Z:=
 let '((q,(_,h,_)),(fl,fr)):=a in
 match tm q h with
 | None=>0%Z
 | Some tr=>
   let has:=xe_live(if side then fl else fr)in
   match side,t_dir tr with
   | true,DR|false,DL=>zind(has||sym_eqb(t_write tr)S1)
   | _,_ =>(-zind has)%Z
   end
 end.
Lemma xe_class_live:forall xs,xe_live(class_of_list xs)=(Nat.ltb 0 (count1 xs)).
Proof. intros. unfold class_of_list,class_of_count. destruct(count1 xs)as[|[|n]];reflexivity. Qed.
Lemma xe_extent_ctl:forall xs,
 Z.of_nat(pc_extent(ctl xs))=(Z.of_nat(pc_extent xs)-zind(Nat.ltb 0 (count1 xs)))%Z.
Proof. intros[|x xs];[reflexivity|apply pc_extent_pop]. Qed.
Lemma xe_exact_base:forall tm n ls rs side a cc cc',
 ng_covers n ls rs(fst a)(lift cc)->
 (let '(_,(L,_,R)):=cc in snd a=(class_of_list L,class_of_list R))->
 cstep tm cc=Some cc' ->
 Z.of_nat(xe_val side cc')=(Z.of_nat(xe_val side cc)+xe_delta tm side a)%Z.
Proof.
 intros tm n ls rs side [[q[[lw h]rw]][fl fr]][qc[[L hc]R]]cc' Hcov Hclass Hstep.
 cbn in Hclass;injection Hclass as -> ->.
 destruct Hcov as(Hq&Hh&Hl&Hr&Hrest);cbn in Hq,Hh;subst qc hc.
 unfold cstep in Hstep;cbn[fst snd]in Hstep.
 destruct(tm q h)as[tr|]eqn:Et;[|discriminate]. injection Hstep as <-.
 unfold xe_val,xe_delta;cbn[fst snd]. rewrite Et.
 destruct side;destruct(t_dir tr);cbn[ctape_move];rewrite xe_class_live.
 - rewrite xe_extent_ctl. lia.
 - rewrite pc_extent_push,Nat2Z.inj_add. unfold zind. destruct((Nat.ltb 0 (count1 L))||sym_eqb(t_write tr)S1);reflexivity.
 - rewrite pc_extent_push,Nat2Z.inj_add. unfold zind. destruct((Nat.ltb 0 (count1 R))||sym_eqb(t_write tr)S1);reflexivity.
 - rewrite xe_extent_ctl. lia.
Qed.
Definition xe_complement_val(side:bool)(p:list Sym)(cc:cconf):nat:=
 xe_val side cc-pm_val p(xe_reg side)cc.
Lemma xe_pattern_bound:forall p side cc,In S1 p ->pm_val p(xe_reg side)cc<=xe_val side cc.
Proof.
 intros p side[q[[L h]R]]H.
 pose proof(pm_val_pattern_bound p(xe_reg side)(q,(L,h,R))H)as E.
 destruct side;unfold xe_reg,xe_val in *.
 - rewrite pc_pm_one_L in E. exact(Nat.le_trans _ _ _ E(pc_count1_extent L)).
 - rewrite pc_pm_one_R in E. exact(Nat.le_trans _ _ _ E(pc_count1_extent R)).
Qed.
Lemma xe_complement_exact_base:forall tm n ls rs side p a cc (a':fcconf) cc',
 pm_ok n p(xe_reg side)=true ->
 ng_covers n ls rs(fst a)(lift cc)->
 (let '(_,(L,_,R)):=cc in snd a=(class_of_list L,class_of_list R))->
 cstep tm cc=Some cc' ->
 Z.of_nat(xe_complement_val side p cc')=
 (Z.of_nat(xe_complement_val side p cc)+xe_delta tm side a-
  pm_delta tm p(xe_reg side)(fst a)(fst a'))%Z.
Proof.
 intros tm n ls rs side p a cc a' cc' Hok Hcov Hclass Hstep.
 assert(Hone:In S1 p).
 { unfold pm_ok in Hok. apply andb_prop in Hok as[Hone _].
   apply existsb_exists in Hone as(x&Hxin&Hx). apply sym_eqb_spec in Hx;subst x;exact Hxin. }
 assert(Ep:Z.of_nat(pm_val p(xe_reg side)cc')=
  (Z.of_nat(pm_val p(xe_reg side)cc)+pm_delta tm p(xe_reg side)(fst a)(fst a'))%Z).
 { eapply pm_exact;eauto. unfold pm_ok in Hok;apply andb_prop in Hok as[_ Hl].
   destruct side;apply Nat.leb_le;exact Hl. }
 pose proof(xe_exact_base tm n ls rs side a cc cc' Hcov Hclass Hstep)as Ee.
 unfold xe_complement_val. rewrite !Nat2Z.inj_sub by(apply xe_pattern_bound;exact Hone).
 rewrite Ee,Ep. lia.
Qed.
