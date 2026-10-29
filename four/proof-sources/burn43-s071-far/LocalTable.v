(** Finite local dispatcher for the independently extracted S071 traces. *)
From Coq Require Import List Arith Lia Bool PArith.
From BBB24 Require Import Statement CTape.
From BBB24Burn43S071FAR Require Import Programs.
From BBB24Burn43S071FAR Require Import DataSchema.
From BBB24Burn43S071FAR Require Import BlockMicro.
Import ListNotations.
Definition c52_state(q:bool):St:=if q then StB else StA.
Definition c52_cells(w:positive):list Sym:=match w with
|1%positive=>[S0;S0]
|2%positive=>[S1;S0]
|3%positive=>[S3;S0]
|4%positive=>[S3;S1]
|5%positive=>[S2;S1]
|6%positive=>[S0;S1]
|7%positive=>[S1;S1]
|8%positive=>[S2;S2]
|9%positive=>[S3;S3]
|10%positive=>[S2;S0]
|11%positive=>[S1;S2]
|12%positive=>[S0;S3]
|13%positive=>[S1;S3]
|14%positive=>[S0;S2]
|_=>[S1;S1] end.
Lemma c52_cells_blank:forall w,all_blank(c52_cells w)=true->w=1%positive.
Proof.
 intros w H.
 do 4 (try(destruct w as[w|w|];cbn[c52_cells all_blank sym_eqb]in H;try discriminate;try reflexivity)).
Qed.
Definition c52_local_entry (w:positive)(q f:bool)(l r:list Sym):cconf:=
 if f then s71_front(c52_state q)l(c52_cells w++r)
 else s71_back(c52_state q)(c52_cells w++l)r.
Definition c52_local_exit (f:bool)(wn:positive)(qn back:bool)(l r:list Sym):cconf:=
 if Bool.eqb f back then s71_back(c52_state qn)l(c52_cells wn++r)
 else s71_front(c52_state qn)(c52_cells wn++l)r.
Record c52_row:=MicroRow{
 mw:positive; mq:bool; mf:bool; mbz:bool; mfz:bool;
 mo:localout; mk:nat }.
Definition c52_rows:list c52_row:=[
 MicroRow 1%positive false false false false (Out 2%positive false true) 5;
 MicroRow 1%positive false true true true (Out 2%positive true true) 1;
 MicroRow 1%positive true false false false (Out 1%positive true true) 1;
 MicroRow 1%positive true false false true (Out 1%positive true true) 1;
 MicroRow 2%positive false false false false (Out 10%positive false true) 1;
 MicroRow 2%positive false true true false (Out 6%positive false true) 3;
 MicroRow 2%positive false true true true (Out 6%positive false true) 3;
 MicroRow 2%positive true false false false (Out 2%positive false true) 3;
 MicroRow 2%positive true true true false (Out 3%positive true true) 1;
 MicroRow 2%positive true true true true (Out 3%positive true true) 1;
 MicroRow 3%positive false true true false (Out 14%positive true false) 2;
 MicroRow 3%positive true true true false (Out 4%positive true true) 3;
 MicroRow 3%positive true true true true (Out 4%positive true true) 3;
 MicroRow 4%positive false true true false (Out 12%positive false true) 3;
 MicroRow 4%positive true true true false (Out 5%positive false false) 2;
 MicroRow 4%positive true true true true (Out 5%positive false false) 2;
 MicroRow 5%positive false false false false (Out 8%positive true true) 3;
 MicroRow 5%positive true false false false (Out 6%positive false false) 4;
 MicroRow 5%positive true false false true (Out 6%positive false false) 4;
 MicroRow 6%positive false true true false (Out 7%positive true true) 1;
 MicroRow 6%positive false true true true (Out 7%positive true true) 1;
 MicroRow 6%positive true true true false (Out 2%positive false false) 4;
 MicroRow 7%positive false true true false (Out 8%positive false false) 2;
 MicroRow 7%positive false true true true (Out 8%positive false false) 2;
 MicroRow 7%positive true true true false (Out 4%positive true true) 1;
 MicroRow 8%positive false false false false (Out 9%positive false false) 2;
 MicroRow 8%positive true false false false (Out 3%positive false false) 2;
 MicroRow 8%positive true false false true (Out 3%positive false false) 2;
 MicroRow 9%positive false true true false (Out 11%positive false false) 2;
 MicroRow 9%positive true true true false (Out 5%positive true false) 2;
 MicroRow 10%positive false false false false (Out 13%positive true false) 2;
 MicroRow 10%positive true false false false (Out 2%positive true false) 2;
 MicroRow 11%positive false false false false (Out 8%positive false true) 1;
 MicroRow 11%positive true false false false (Out 12%positive false false) 2;
 MicroRow 12%positive false true true false (Out 13%positive true true) 1;
 MicroRow 12%positive true true true false (Out 2%positive false false) 2;
 MicroRow 13%positive false true true false (Out 8%positive true false) 2;
 MicroRow 13%positive true true true false (Out 9%positive true true) 1;
 MicroRow 14%positive false false false false (Out 6%positive false false) 2;
 MicroRow 14%positive true false false false (Out 14%positive true true) 1
].
Definition c52_match w q f bz fz row:=
 Pos.eqb w(mw row)&&Bool.eqb q(mq row)&&Bool.eqb f(mf row)&&
 Bool.eqb bz(mbz row)&&Bool.eqb fz(mfz row).
Definition c52_localfun:localfun:=fun w q f bz fz=>
 match find(c52_match w q f bz fz)c52_rows with
 |Some row=>Some(mo row)|None=>None end.
Lemma c52_match_spec:forall w q f bz fz row,
 c52_match w q f bz fz row=true ->
 w=mw row /\ q=mq row /\ f=mf row /\ bz=mbz row /\ fz=mfz row.
Proof.
 intros w q f bz fz row H;unfold c52_match in H.
 repeat rewrite andb_true_iff in H.
 destruct H as [[[[Hw Hq] Hf] Hb] Ha].
 apply Pos.eqb_eq in Hw.
 apply Bool.eqb_prop in Hq,Hf,Hb,Ha.
 auto.
Qed.
Lemma c52_row_sound:forall row,In row c52_rows->forall l r,
 c52_right_ok(if mf row then mfz row else mbz row)r ->
 csteps s71_tm(mk row)(c52_local_entry(mw row)(mq row)(mf row)l r)=
 Some(c52_local_exit(mf row)(ow(mo row))(oq(mo row))(ob(mo row))l r) /\
 c52_safe_before(mk row)(c52_local_entry(mw row)(mq row)(mf row)l r).
Proof.
 intros row H;cbn[c52_rows]in H.
 destruct H as[<-|H];[exact c52_trace_00|].
 destruct H as[<-|H];[exact c52_trace_01|].
 destruct H as[<-|H];[exact c52_trace_02|].
 destruct H as[<-|H];[exact c52_trace_03|].
 destruct H as[<-|H];[exact c52_trace_04|].
 destruct H as[<-|H];[exact c52_trace_05|].
 destruct H as[<-|H];[exact c52_trace_06|].
 destruct H as[<-|H];[exact c52_trace_07|].
 destruct H as[<-|H];[exact c52_trace_08|].
 destruct H as[<-|H];[exact c52_trace_09|].
 destruct H as[<-|H];[exact c52_trace_10|].
 destruct H as[<-|H];[exact c52_trace_11|].
 destruct H as[<-|H];[exact c52_trace_12|].
 destruct H as[<-|H];[exact c52_trace_13|].
 destruct H as[<-|H];[exact c52_trace_14|].
 destruct H as[<-|H];[exact c52_trace_15|].
 destruct H as[<-|H];[exact c52_trace_16|].
 destruct H as[<-|H];[exact c52_trace_17|].
 destruct H as[<-|H];[exact c52_trace_18|].
 destruct H as[<-|H];[exact c52_trace_19|].
 destruct H as[<-|H];[exact c52_trace_20|].
 destruct H as[<-|H];[exact c52_trace_21|].
 destruct H as[<-|H];[exact c52_trace_22|].
 destruct H as[<-|H];[exact c52_trace_23|].
 destruct H as[<-|H];[exact c52_trace_24|].
 destruct H as[<-|H];[exact c52_trace_25|].
 destruct H as[<-|H];[exact c52_trace_26|].
 destruct H as[<-|H];[exact c52_trace_27|].
 destruct H as[<-|H];[exact c52_trace_28|].
 destruct H as[<-|H];[exact c52_trace_29|].
 destruct H as[<-|H];[exact c52_trace_30|].
 destruct H as[<-|H];[exact c52_trace_31|].
 destruct H as[<-|H];[exact c52_trace_32|].
 destruct H as[<-|H];[exact c52_trace_33|].
 destruct H as[<-|H];[exact c52_trace_34|].
 destruct H as[<-|H];[exact c52_trace_35|].
 destruct H as[<-|H];[exact c52_trace_36|].
 destruct H as[<-|H];[exact c52_trace_37|].
 destruct H as[<-|H];[exact c52_trace_38|].
 destruct H as[<-|H];[exact c52_trace_39|].
 contradiction.
Qed.
Lemma c52_row_positive:forall row,In row c52_rows->0<mk row.
Proof.
 intros row H;cbn[c52_rows]in H.
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 destruct H as[<-|H];[cbn;lia|].
 contradiction.
Qed.
Theorem c52_localfun_micro:forall w q f bz fz wn qn back,
 c52_localfun w q f bz fz=Some(Out wn qn back)->forall l r,
 c52_right_ok(if f then fz else bz)r ->
 exists k,0<k /\
 csteps s71_tm k(c52_local_entry w q f l r)=
 Some(c52_local_exit f wn qn back l r) /\
 c52_safe_before k(c52_local_entry w q f l r).
Proof.
 intros w q f bz fz wn qn back H l r Hr.
 unfold c52_localfun in H.
 destruct(find(c52_match w q f bz fz)c52_rows)as[row|]eqn:E;[|discriminate].
 apply find_some in E as[Hin Hmatch].
 apply c52_match_spec in Hmatch as[Hw[Hq[Hf[Hb Ha]]]].
 injection H as Ho.
 subst w q f bz fz.
 exists(mk row);split;[now apply c52_row_positive|].
 pose proof(c52_row_sound row Hin l r Hr)as Hs.
 rewrite Ho in Hs;exact Hs.
Qed.
Print Assumptions c52_localfun_micro.
