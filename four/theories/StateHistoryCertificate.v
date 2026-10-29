(** Supplied history certificates for STATE bounds only.

    Window sets, closure nodes and lexicographic ranks are untrusted inputs.
    The checker replays the concrete prefix and verifies seed coverage, full
    transition closure, membership, every required rank edge, and the state
    prefix bound. It performs no SCC or Bellman-Ford certificate search.

    Binary node codes and dictionary indices affect only parsing/storage:
    soundness holds for every decoded value, including malformed encodings. *)
From Coq Require Import NArith Arith Lia Bool List.
From BBB24 Require Import StatePipeline StateOnlyCloseout Census FiniteCensus HistCensus HistRankSearch Closure ClosureTr StateBounds AbstractCensus Bounds PosEnc CTape Statement StatementTr Spec.
From BBB24.Checkers Require Import NGram NGramHist.
Import ListNotations.
Definition sh_state (a:hcconf) := fst(hainstr a).
Definition sh_live tm k n ls rs Sl (ca cb:list hncomp) :=
 forallb (fun q=>if appears hcconf sh_state Sl q then
 lex_ok hcconf sh_state (hng_succs tm k n ls rs) Sl q
 (hn_components tm (match q with StA=>ca | StB=>cb end)) else true) all_St.
Definition sh_check bound tm k n t ls rs Sl ca cb :=
 if 1<=?n then match hcsteps tm k t hcconf0 with
 |None=>false
 |Some cc=>
 if hseed_ok n ls rs cc then
 if closed_tr_b hcconf hctx_enc(hng_succs tm k n ls rs)Sl then
 if mem_tr hcconf hctx_enc(hng_start n cc)Sl then
 if state_prefix_gate bound tm t(tail_states(labels hainstr Sl)) then
 sh_live tm k n ls rs Sl ca cb
 else false else false else false else false
 end else false.
Definition sh_sym (c:N) := match N.to_nat c with 0=>S0 | 1=>S1 | 2=>S2 | _=>S3 end.
Fixpoint sh_hist (k:nat)(c:N) : hrec := match k with
 |0=>[] |S j=>if N.eqb c 0 then [] else
 let d:=(c-1)%N in
 (if N.ltb (d mod 8) 4 then StA else StB,sh_sym(d mod 4))::sh_hist j(d/8)
 end.
Definition sh_cell k (c:N) : hsym := (sh_sym(c mod 4),sh_hist k(c/4)).
Fixpoint sh_cells k n (base c:N) : list hsym := match n with
 |0=>[] |S j=>sh_cell k(c mod base)::sh_cells k j base(c/base) end.
Definition sh_node k n (base c:N) : hcconf :=
 let cells:=sh_cells k (n+S n) base(c/2) in
 (if N.even c then StA else StB,(firstn n cells, hd hblank(skipn n cells),skipn(S n)cells)).
Fixpoint sh_table (p:positive)(nodes:list hcconf) : PositiveMap.tree hcconf :=
 match nodes with []=>PositiveMap.empty hcconf |a::tl=>PositiveMap.add p a(sh_table(Pos.succ p)tl) end.
Definition sh_get tab (i:N) := match PositiveMap.find (match N.succ i with Npos p=>p |N0=>1%positive end) tab with Some a=>a |None=>hcconf0 end.
Inductive sh_pcomp := ShRank (phi:list(N*N)) |ShMeas (m:ngmeas)(K:N)(phi:list(N*N))(gate:list N).
Definition sh_phi tab phi := map(fun '(i,r)=>(sh_get tab i,N.to_nat r))phi.
Definition sh_comp tab c := match c with
 |ShRank phi=>HnRank(sh_phi tab phi)
 |ShMeas m K phi gate=>HnMeas m(N.to_nat K)(sh_phi tab phi)(map(sh_get tab)gate) end.
Definition sh_pcheck bound machine k n t base nodes ls rs ca cb :=
 let Sl:=map(sh_node k n base)nodes in let tab:=sh_table 1%positive Sl in
 sh_check bound (stp_machine machine) k n t (map(sh_cells k n base)ls)(map(sh_cells k n base)rs) Sl
 (map(sh_comp tab)ca)(map(sh_comp tab)cb).
Lemma sh_live_imp : forall tm k n ls rs Sl ca cb,
 sh_live tm k n ls rs Sl ca cb=true ->
 live_lex_ok hcconf hctx_enc sh_state (hng_succs tm k n ls rs) Sl
 (fun q=>hn_components tm (match q with StA=>ca |StB=>cb end))=true.
Proof.
 intros tm k n ls rs Sl ca cb H.
 unfold sh_live,live_lex_ok in *. rewrite forallb_forall in *.
 intros q Hq. specialize(H q Hq).
 destruct(appears hcconf sh_state Sl q); [|reflexivity].
 destruct(rank_ok hcconf sh_state (hng_succs tm k n ls rs) Sl q
  (compute_ranks hcconf hctx_enc sh_state (hng_succs tm k n ls rs) Sl q)); auto.
Qed.
Theorem sh_check_sound : forall bound tm k n t ls rs Sl ca cb,
 sh_check bound tm k n t ls rs Sl ca cb=true ->
 NonHalt tm /\ QHBound (N.to_nat bound) tm.
Proof.
 intros bound tm k n t ls rs Sl ca cb H. unfold sh_check in H.
 destruct(1<=?n)eqn:Hn; [apply Nat.leb_le in Hn|discriminate].
 destruct(hcsteps tm k t hcconf0)as[cc|]eqn:Et;[|discriminate].
 destruct(hseed_ok n ls rs cc)eqn:Hseed;[|discriminate].
 destruct(closed_tr_b hcconf hctx_enc(hng_succs tm k n ls rs)Sl)eqn:Hcl;[|discriminate].
 destruct(mem_tr hcconf hctx_enc(hng_start n cc)Sl)eqn:Hmem;[|discriminate].
 destruct(state_prefix_gate bound tm t(tail_states(labels hainstr Sl)))eqn:Hpre;[|discriminate].
 assert(Eproj:csteps tm t c0=Some(hproj cc)).
 {rewrite <-hproj_hcconf0. eapply hcsteps_proj; exact Et. }
 apply sh_live_imp in H. rewrite fn_closed_equiv in Hcl.
 eapply(abstract_state_bound tm hcconf hctx_enc hainstr(hng_succs tm k n ls rs)(hcovers n ls rs));
 [exact hctx_enc_inj|apply hcovers_instr| |exact Eproj| |exact Hcl|exact Hmem| |exact H|exact Hpre].
 - intros a c Hc. apply hng_succs_sound; assumption.
 - exists cc;split;[reflexivity|apply hng_start_covers;exact Hseed].
 - intros; apply hn_components_exact; exact Hn.
Qed.
Theorem sh_pcheck_sound : forall bound machine k n t base nodes ls rs ca cb,
 sh_pcheck bound machine k n t base nodes ls rs ca cb=true ->
 NonHalt(stp_machine machine) /\ QHBound(N.to_nat bound)(stp_machine machine).
Proof. intros. eapply sh_check_sound;exact H. Qed.
Print Assumptions sh_pcheck_sound.

Record sh_data := SHData {
 sh_machine_code : N;
 sh_node_codes : list N;
 sh_left_codes : list N;
 sh_right_codes : list N;
 sh_cert_A : list sh_pcomp;
 sh_cert_B : list sh_pcomp
}.
Definition sh_data_check bound k n t base row :=
 sh_pcheck bound (sh_machine_code row) k n t base
 (sh_node_codes row)(sh_left_codes row)(sh_right_codes row)
 (sh_cert_A row)(sh_cert_B row).
Definition sh_batch_check bound k n t base rows :=
 forallb (sh_data_check bound k n t base) rows.
Definition sh_board rows := map(fun row=>stp_machine(sh_machine_code row))rows.
Theorem sh_batch_state_sound : forall bound k n t base rows,
 sh_batch_check bound k n t base rows=true ->
 StateBoardSound(N.to_nat bound)(sh_board rows).
Proof.
 intros bound k n t base rows H family Hin tm Hle.
 apply in_map_iff in Hin as(row&<-&Hin).
 apply forallb_forall with(x:=row)in H;[|exact Hin].
 destruct(sh_pcheck_sound _ _ _ _ _ _ _ _ _ _ _ H)as[Hnh Hb].
 eapply state_bound_extend;eauto.
Qed.
Theorem sh_batch_nonhalt : forall bound k n t base rows,
 sh_batch_check bound k n t base rows=true ->
 forall family,In family(sh_board rows)->NonHalt family.
Proof.
 intros bound k n t base rows H family Hin.
 apply in_map_iff in Hin as(row&<-&Hin).
 apply forallb_forall with(x:=row)in H;[|exact Hin].
 exact(proj1(sh_pcheck_sound _ _ _ _ _ _ _ _ _ _ _ H)).
Qed.
Print Assumptions sh_batch_state_sound.
