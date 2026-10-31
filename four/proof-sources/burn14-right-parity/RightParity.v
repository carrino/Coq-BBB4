(** A graph coloring tracks parity on the entire concrete right tape.
    The finite windows and the parity share the same actual [hcconf]. *)
From Coq Require Import List Arith Lia Bool Wf_nat NArith.
From BBB24 Require Import Statement Spec CTape PosEnc Closure HistCensus HistRankSearch
 OneStateReach OneStateConditional MarkerState MarkerPotential.
From BBB24.Checkers Require Import NGram NGramHist.
From BBB24Burn12HistoryMarker Require Import HistoryMarker.
Import ListNotations.

Definition rp_mark (mask:N)(s:Sym) := N.testbit mask
 (match s with S0=>0|S1=>1|S2=>2|S3=>3 end)%N.
Definition rp_nonzero (cell:hsym) := negb(sym_eqb(hbit cell)S0).
Fixpoint rp_parity (mark:Sym->bool)(cells:list hsym) :=
 match cells with []=>false|h::r=>xorb(mark(hbit h))(rp_parity mark r)end.
Definition rp_right mark(cc:hcconf) := let '(_,(_,_,r)):=cc in rp_parity mark r.
Definition rp_inv mark (color:hcconf->bool) a cc := rp_right mark cc=color a.
Definition rp_node (color:hcconf->bool)(a:hcconf) :=
 st_eqb(fst a)StA || (hm_known rp_nonzero a || color a).
Definition rp_edge tm mark (color:hcconf->bool) a a' :=
 match tm(fst a)(hbit(hm_head a))with
 |None=>false
 |Some tr=>Bool.eqb(color a')
   (xorb(color a)(match t_dir tr with
    |DL=>mark(t_write tr)|DR=>mark(hbit(hm_head a'))end))
 end.
Definition rp_edges tm k n ls rs mark color Sl :=
 forallb(fun a=>match hng_succs tm k n ls rs a with
 |None=>false|Some xs=>forallb(rp_edge tm mark color a)xs end)Sl.
Fixpoint rp_color_set (Sl:list hcconf)(bits:N) := match Sl with
 |[]=>PositiveSet.empty
 |a::rest=>let set:=rp_color_set rest(N.div2 bits)in
   if N.odd bits then PositiveSet.add(hctx_enc a)set else set
 end.
Definition rp_colors Sl bits :=
 let colored:=rp_color_set Sl bits in
 fun a=>PositiveSet.mem(hctx_enc a)colored.

Lemma rp_nonzero_blank : rp_nonzero hblank=false.
Proof. reflexivity. Qed.
Lemma rp_parity_marker : forall mark r,
 mark S0=false -> rp_parity mark r=true -> hm_has rp_nonzero r.
Proof.
 intros mark r Hz;induction r as[|h r IH];intro H;[discriminate|].
 cbn[rp_parity]in H;destruct(mark(hbit h))eqn:Eh.
 - exists h;split;[left;reflexivity|].
   unfold rp_nonzero;destruct(hbit h);cbn;try reflexivity;congruence.
 - cbn in H;destruct(IH H)as(x&Hin&Hm);exists x;split;[right;exact Hin|exact Hm].
Qed.
Lemma rp_node_sound : forall mark color n ls rs a cc,
 mark S0=false -> hng_covers n ls rs a cc ->
 rp_node color a=true -> rp_inv mark color a cc -> hm_inv rp_nonzero cc.
Proof.
 intros mark color n ls rs a[q[[l h]r]]Hz Hcov Hnode Hinv;destruct q;[exact I|].
 unfold rp_node in Hnode;apply orb_true_iff in Hnode as[HA|Hnode].
 - apply st_eqb_spec in HA;pose proof(hng_covers_state _ _ _ _ _ Hcov)as Hs.
   unfold ha_state in Hs;cbn in Hs;congruence.
 - apply orb_true_iff in Hnode as[Hknown|Hcolor].
   + exact(hm_known_sound _ _ _ _ _ _ rp_nonzero_blank Hcov Hknown).
   + change(rp_parity mark r=color a)in Hinv;rewrite Hcolor in Hinv.
     destruct(rp_parity_marker mark r Hz Hinv)as(x&Hin&Hm).
     exists x;split;[right;exact Hin|exact Hm].
Qed.
Lemma rp_step_update : forall tm k mark cc cc' tr,
 mark S0=false -> tm(fst cc)(hbit(hm_head cc))=Some tr ->
 hcstep tm k cc=Some cc' ->
 rp_right mark cc'=xorb(rp_right mark cc)
  (match t_dir tr with DL=>mark(t_write tr)|DR=>mark(hbit(hm_head cc'))end).
Proof.
 intros tm k mark[q[[l h]r]]cc' tr Hz Et E.
 cbn[fst hm_head]in Et;cbn[hcstep]in E;rewrite Et in E;injection E as <-.
 destruct(t_dir tr);cbn[hctape_move rp_right hm_head rp_parity hbit].
 - apply xorb_comm.
 - destruct r as[|b r];cbn[hchd hctl hm_head rp_right rp_parity hbit].
   + change(false=xorb false(mark S0));rewrite Hz;reflexivity.
   + destruct(mark(hbit b)),(rp_parity mark r);reflexivity.
Qed.
Lemma rp_pad_inv : forall mark color a cc padding,
 rp_inv mark color a cc -> rp_inv mark color a(hm_pad padding cc).
Proof. intros mark color a[q[[l h]r]]padding H;exact H. Qed.

Section Graph.
Variables (tm:TM)(k n:nat)(ls rs:hgset)(Sl:list hcconf)
 (mark:Sym->bool)(color:hcconf->bool).
Hypothesis Hn:1<=n.
Hypothesis Hz:mark S0=false.
Hypothesis Hclosed:closed_b hcconf hctx_enc(hng_succs tm k n ls rs)Sl=true.
Hypothesis Hnodes:forallb(rp_node color)Sl=true.
Hypothesis Hedges:rp_edges tm k n ls rs mark color Sl=true.

Lemma rp_preserve_step : forall a cc cc',
 In a Sl -> hng_covers n ls rs a cc -> rp_inv mark color a cc ->
 hcstep tm k cc=Some cc' ->
 exists a',In a' Sl /\ hng_covers n ls rs a' cc' /\ rp_inv mark color a' cc'.
Proof.
 intros a cc cc' Hin Hcov Hi E.
 destruct(hm_closed_step tm k n ls rs Sl Hn Hclosed a cc Hin Hcov)
  as(c'&xs&a'&Es&Ex&Hix&Hin'&Hcov').
 rewrite E in Es;injection Es as <-.
 exists a';split;[exact Hin'|];split;[exact Hcov'|].
 assert(He:rp_edge tm mark color a a'=true).
 {unfold rp_edges in Hedges;apply forallb_forall with(x:=a)in Hedges;[|exact Hin].
  rewrite Ex in Hedges;apply forallb_forall with(x:=a')in Hedges;assumption. }
 unfold rp_edge in He;destruct(tm(fst a)(hbit(hm_head a)))as[tr|]eqn:Et;[|discriminate].
 apply Bool.eqb_prop in He.
 assert(Etc:tm(fst cc)(hbit(hm_head cc))=Some tr).
 {rewrite(hm_head_sound _ _ _ _ _ Hcov)in Et.
  pose proof(hng_covers_state _ _ _ _ _ Hcov)as Hs;unfold ha_state in Hs.
  rewrite Hs in Et;destruct cc as[q[[l h]r]];exact Et. }
 unfold rp_inv;rewrite(rp_step_update tm k mark cc cc' tr Hz Etc E).
 unfold rp_inv in Hi;rewrite Hi,He.
 rewrite(hm_head_sound _ _ _ _ _ Hcov');destruct cc' as[q[[l h]r]];reflexivity.
Qed.

Lemma rp_run : forall t cc a,
 In a Sl -> hng_covers n ls rs a cc -> rp_inv mark color a cc ->
 exists cc' a',hcsteps tm k t cc=Some cc' /\ In a' Sl /\
 hng_covers n ls rs a' cc' /\ rp_inv mark color a' cc'.
Proof.
 induction t;intros cc a Hin Hcov Hi.
 - exists cc,a;repeat split;try assumption;reflexivity.
 - destruct(hm_closed_step tm k n ls rs Sl Hn Hclosed a cc Hin Hcov)as(c1&xs&a1&E&_).
   destruct(rp_preserve_step a cc c1 Hin Hcov Hi E)as(b&Hb&Hcb&Hib).
   destruct(IHt c1 b Hb Hcb Hib)as(c2&b2&E2&Hb2&Hcb2&Hib2).
   exists c2,b2;repeat split;try assumption;cbn[hcsteps];rewrite E;exact E2.
Qed.

Lemma rp_reaches_A : forall weight,
 weight S0=0 -> mp_rank_check tm weight=true ->
 forall cc a,In a Sl -> hng_covers n ls rs a cc -> rp_inv mark color a cc ->
 mp_capacity weight(hproj cc) -> ore_reaches tm StA(hproj cc).
Proof.
 intros weight Hzero Hr.
 apply(well_founded_induction_type(well_founded_ltof hcconf(fun cc=>mp_measure weight(hproj cc)))
  (fun cc=>forall a,In a Sl -> hng_covers n ls rs a cc -> rp_inv mark color a cc ->
   mp_capacity weight(hproj cc) -> ore_reaches tm StA(hproj cc))).
 intros[q[[l h]r]]IH a Hin Hcov Hi Hcap;destruct q.
 - exists 0,(hproj(StA,(l,h,r)));split;reflexivity.
 - destruct(hm_B_defined tm weight(hbit h)Hr)as(tr&Et).
   set(w:=(t_write tr,firstn k((StB,hbit h)::snd h)):hsym).
   assert(E:hcstep tm k(StB,(l,h,r))=Some(t_next tr,hctape_move(t_dir tr)w(l,h,r))).
   {cbn[hcstep];rewrite Et;reflexivity. }
   pose proof(hcstep_proj_some tm k _ _ E)as Ep.
   destruct(t_next tr)eqn:En.
   + eapply ore_reaches_step;[exact Ep|];exists 0;eexists;split;
     [reflexivity|rewrite hproj_state;reflexivity].
   + destruct(rp_preserve_step _ _ _ Hin Hcov Hi E)as(a'&Hin'&Hcov'&Hi').
     assert(Hnode:rp_node color a'=true)by(eapply forallb_forall in Hnodes;eauto).
     pose proof(rp_node_sound mark color n ls rs _ _ Hz Hcov' Hnode Hi')as Hmarker.
     pose proof(mp_checked_delta tm weight(hbit h)tr Hr Et En)as Hd.
     pose proof(mp_capacity_move weight StB StB(hproj_side l)(hbit h)(hproj_side r)
       (t_dir tr)(t_write tr)Hzero Hcap Hd)as Hcap'.
     destruct(t_dir tr)eqn:Ed;cbn[hctape_move]in E,Ep,Hcov',Hi',Hmarker.
     * destruct l as[|b l];cbn[hchd hctl]in E,Ep,Hcov',Hi',Hmarker.
       -- unfold mp_capacity,mp_left_length,hproj,hproj_side in Hcap;cbn in Hcap;lia.
       -- eapply ore_reaches_step;[exact Ep|];eapply IH with(a:=a');try assumption.
          ++ unfold ltof,mp_measure,ore_mirror_cc;cbn[hproj hproj_side hbit w].
             apply ore_right_drop;change(weight(t_write tr)<weight(hbit h));lia.
     * destruct r as[|b r];cbn[hchd hctl]in E,Ep,Hcov',Hi',Hmarker.
       -- change(hm_has rp_nonzero[hblank])in Hmarker.
          pose proof(hm_has_single rp_nonzero hblank Hmarker);discriminate.
       -- eapply ore_reaches_step;[exact Ep|];eapply IH with(a:=a');try assumption.
          ++ unfold ltof,mp_measure,ore_mirror_cc;cbn[hproj hproj_side hbit w].
             apply ore_left_drop;eapply mp_checked_bound;exact Hr.
Qed.
End Graph.

Definition rp_check tm mask bits w1 w2 w3 k n t fuel rounds :=
 let mark:=rp_mark mask in let weight:=mp_weights w1 w2 w3 in
 negb(mark S0) && (mp_rank_check tm weight &&
 (ore_auto_goal(orc_fill_goal tm StB)StB && ((1<=?n) &&
 match hcsteps tm k t hcconf0 with
 |None=>false
 |Some cc=>let '(_, (l,_,r)):=cc in
  let a0:=hng_start n cc in
  let '(ls,rs):=hn_grow tm k n a0 fuel rounds(hseed_side n l)(hseed_side n r)in
  let Sl:=hn_explore tm k n ls rs fuel [] PositiveSet.empty[a0]in
  let color:=rp_colors Sl bits in
  Bool.eqb(rp_right mark cc)(color a0) && (hseed_ok n ls rs cc &&
  (closed_b hcconf hctx_enc(hng_succs tm k n ls rs)Sl &&
  (mem hcconf hctx_enc a0 Sl &&
   (forallb(rp_node color)Sl && rp_edges tm k n ls rs mark color Sl))))
 end))).

Theorem rp_check_sound : forall tm mask bits w1 w2 w3 k n t fuel rounds,
 rp_check tm mask bits w1 w2 w3 k n t fuel rounds=true -> NonHalt tm /\ QHBound 0 tm.
Proof.
 intros tm mask bits w1 w2 w3 k n t fuel rounds H;unfold rp_check in H;cbv zeta in H.
 repeat rewrite andb_true_iff in H;destruct H as[Hz[Hr[HB[Hn H]]]].
 apply negb_true_iff in Hz;apply Nat.leb_le in Hn.
 destruct(hcsteps tm k t hcconf0)as[cc0|]eqn:Et;[|discriminate].
 destruct cc0 as[q[[l h]r]].
 match type of H with(let '(_,_) := ?G in _)=true=>destruct G as[ls rs]end.
 cbv beta iota zeta in H;repeat rewrite andb_true_iff in H.
 destruct H as[Hi[Hseed[Hclosed[Hmem[Hnodes Hedges]]]]].
 set(cc0:=(q,(l,h,r)))in *;set(a0:=hng_start n cc0)in *.
 set(Sl:=hn_explore tm k n ls rs fuel [] PositiveSet.empty[a0])in *.
 set(color:=rp_colors Sl bits)in *.
 assert(Hin:In a0 Sl)by(eapply mem_In;[exact hctx_enc_inj|exact Hmem]).
 assert(Hcov:hng_covers n ls rs a0 cc0)by(apply hng_start_covers;exact Hseed).
 apply Bool.eqb_prop in Hi;change(rp_inv(rp_mark mask)color a0 cc0)in Hi.
 assert(Eprefix:stepn tm t InitES=Some(lift(hproj cc0))).
 {rewrite <-lift_c0;eapply csteps_lift;rewrite <-hproj_hcconf0;eapply hcsteps_proj;exact Et. }
 assert(Hinv:forall N,exists cc a,hcsteps tm k N cc0=Some cc /\ In a Sl /\
   hng_covers n ls rs a cc /\ rp_inv(rp_mark mask)color a cc).
 {intro N;eapply rp_run;eauto. }
 assert(Hnh:NonHalt tm).
 {intros j Hj;destruct(le_lt_dec t j).
  - destruct(Hinv(j-t))as(cc&a&EN&_).
    replace j with(t+(j-t))in Hj by lia;rewrite stepn_add,Eprefix in Hj.
    rewrite(csteps_lift tm(j-t)(hproj cc0)(hproj cc)(hcsteps_proj tm k(j-t)cc0 cc EN))in Hj;discriminate.
  - destruct(stepn_prefix tm j t InitES(lift(hproj cc0))ltac:(lia)Eprefix)as(c&E&_);congruence. }
 assert(HAr:forall N,exists j,N<=j /\ VisitsAt tm StA j).
 {intro N;destruct(Hinv N)as(cc&a&EN&Ha&Hca&Hia).
  set(weight:=mp_weights w1 w2 w3);assert(Hw:weight S0=0)by reflexivity.
  set(padded:=hm_pad(S(mp_weight weight(hproj cc)))cc).
  assert(Hcp:hng_covers n ls rs a padded)by(apply hm_pad_covers;exact Hca).
  assert(Hip:rp_inv(rp_mark mask)color a padded)by(apply rp_pad_inv;exact Hia).
  assert(Hcapacity:mp_capacity weight(hproj padded)).
  {unfold padded;rewrite hm_pad_projection;apply mp_padded_capacity;exact Hw. }
  destruct(rp_reaches_A tm k n ls rs Sl(rp_mark mask)color Hn Hz Hclosed Hnodes Hedges
    weight Hw Hr padded a Ha Hcp Hip Hcapacity)as(j&cc'&Ej&Hstate).
  exists(t+N+j);split;[lia|];exists(lift cc');split;[|exact Hstate].
  rewrite !stepn_add,Eprefix.
  rewrite(csteps_lift tm N(hproj cc0)(hproj cc)(hcsteps_proj tm k N cc0 cc EN)).
  pose proof(csteps_lift tm j(hproj padded)cc' Ej)as Htail.
  unfold padded in Htail;rewrite hm_pad_projection,mp_pad_lift in Htail;exact Htail. }
 pose proof(orc_goal_recurs tm StB Hnh HB)as HBr.
 split;[exact Hnh|].
 intros state s[_ Hquiet];destruct state.
 - destruct(HAr(S s))as(j&Hj&Hv);exfalso;apply(Hquiet j);[lia|exact Hv].
 - destruct(HBr(S s))as(j&Hj&Hv);exfalso;apply(Hquiet j);[lia|exact Hv].
Qed.
Print Assumptions rp_check_sound.
