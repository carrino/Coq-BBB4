(** Reuse an already proved weighted graph without recomputing its rankings.
    The source proof establishes a reusable tail. Each target independently
    checks its prefix, seed coverage, and every recurring transition. *)
From Coq Require Import List Bool NArith Arith.
From BBB24 Require Import Statement StatementTr CTape PosEnc Bounds Census
 Closure ClosureTr NGramCensus WeightedCensus WeightedTail WeightedReuse
 Symmetry Mirror CycleCensus FamilyTransport Pipeline.
From BBB24.Checkers Require Import NGram.
Import ListNotations.

Definition prepared_tail source n t Sl cert :=
 match csteps source t c0 with
 | None=>weighted_tail source n gempty gempty Sl cert
 | Some(_, (l,h,r))=>
   let ls:=gadds(ng_seed_side n l ++ flat_map(fun c=>fst(ng_harvest source c))Sl)gempty in
   let rs:=gadds(ng_seed_side n r ++ flat_map(fun c=>snd(ng_harvest source c))Sl)gempty in
   weighted_tail source n ls rs Sl cert
 end.

Theorem graph_prepares_ready_tail : forall bs bi source n t Sl cert,
 wc_graph_check bs bi source n t Sl cert=true ->
 wt_ready(prepared_tail source n t Sl cert)=true.
Proof.
 intros bs bi source n t Sl cert H.
 unfold wc_graph_check in H;unfold prepared_tail.
 destruct(1<=?n)eqn:Hn;[|discriminate].
 destruct(csteps source t c0)as[[q[[l h]r]]|];[|discriminate].
 cbv beta iota zeta in H.
 unfold wt_ready;cbn[wt_source wt_width wt_left wt_right wt_nodes wt_cert].
 rewrite Hn.
 match type of H with (if ?b then _ else _)=true=>destruct b eqn:Hseed end;[|discriminate].
 match type of H with (if ?b then _ else _)=true=>destruct b eqn:Hclosed end;[|discriminate].
 match type of H with (if ?b then _ else _)=true=>destruct b eqn:Hmem end;[|discriminate].
 match type of H with (if ?b then _ else _)=true=>destruct b eqn:Hprefix end;[|discriminate].
 exact H.
Qed.

Record ReadyReuseRow := ready_reuse_row {
 rr_codes : list nat;
 rr_permutation : SymPerm;
 rr_mirrored : bool;
 rr_boot : nat
}.
Definition rr_tm row := machine_of_codes(rr_codes row).
Definition rr_actual row :=
 perm_tm(inverse_perm(rr_permutation row))
   (if rr_mirrored row then mirror_tm(rr_tm row)else rr_tm row).
Definition ready_reuse_check bs bi tail row :=
 wt_use_check bs bi tail(rr_actual row)(rr_boot row).
Theorem ready_reuse_sound : forall bs bi tail row,
 wt_ready tail=true -> ready_reuse_check bs bi tail row=true ->
 NonHalt(rr_tm row) /\ Bounds bs bi(rr_tm row).
Proof.
 intros bs bi tail row Hr H.
 destruct(wt_use_sound _ _ _ _ _ Hr H)as[Hnh Hb].
 unfold rr_actual in Hnh,Hb.
 apply perm_nonhalt in Hnh;apply perm_bounds in Hb.
 destruct(rr_mirrored row).
 - split;[apply mirror_nonhalt;exact Hnh|apply mirror_bounds;exact Hb].
 - split;assumption.
Qed.
Theorem ready_reuse_batch_sound : forall bs bi tail rows,
 wt_ready tail=true -> forallb(ready_reuse_check bs bi tail)rows=true ->
 StrongBoard bs bi(map rr_tm rows).
Proof.
 intros bs bi tail rows Hr H tm Hin.
 apply in_map_iff in Hin as[row[<- Hin]].
 apply forallb_forall with(x:=row)in H;[|exact Hin].
 eapply ready_reuse_sound;eassumption.
Qed.

Print Assumptions graph_prepares_ready_tail.
Print Assumptions ready_reuse_batch_sound.
