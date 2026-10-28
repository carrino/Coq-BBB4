(** N-grams with explicit finite half-tape ends. Short windows retain the
    endpoint; full windows describe a prefix of a canonical finite list. *)
From Coq Require Import Arith Lia Bool List ZArith FunctionalExtensionality.
From BBB24 Require Import Statement StatementTr CTape PosEnc Closure ClosureTr.
From BBB24.Checkers Require Import NGram RepWL.
Import ListNotations.

Fixpoint fn_trim (l:list Sym) : list Sym :=
 match l with []=>[] |x::t=>let u:=fn_trim t in
   match x,u with S0,[]=>[] |_,_=>x::u end end.
Definition fn_push x l := match x,l with S0,[]=>[] |_,_=>x::l end.
Definition fn_norm l := l=[] \/ last l S0<>S0.
Lemma fn_trim_nth : forall l i, nthb (fn_trim l) i=nthb l i.
Proof.
 induction l as [|x l IH]; intro i; [reflexivity|].
 cbn [fn_trim]. specialize (IH (pred i)). destruct (fn_trim l) as [|y u] eqn:E;
 destruct x; destruct i; cbn [nthb] in *; auto.
 all: cbn [pred] in IH; rewrite ?nthb_nil in *; exact IH.
Qed.
Lemma fn_trim_lift : forall l, lift_side (fn_trim l)=lift_side l.
Proof. intro l; apply functional_extensionality; apply fn_trim_nth. Qed.
Lemma fn_push_lift : forall x l, lift_side (fn_push x l)=lift_side (x::l).
Proof. intros [] [|y l]; try reflexivity.
 apply lpad_eqb_lift; reflexivity. Qed.
Lemma fn_trim_norm : forall l, fn_norm (fn_trim l).
Proof.
 induction l as [|x l IH]; [left; reflexivity|].
 cbn [fn_trim]. destruct (fn_trim l) as [|y u] eqn:E.
 - destruct x; unfold fn_norm; cbn; auto; right; discriminate.
 - destruct x; cbn; right; destruct IH as [H|H]; [discriminate|exact H|discriminate|exact H|discriminate|exact H|discriminate|exact H].
Qed.
Lemma fn_norm_ctl : forall l, fn_norm l -> fn_norm (ctl l).
Proof. intros [|x [|y l]] H; try (left; reflexivity).
 right; destruct H as [H|H]; [discriminate|exact H]. Qed.
Lemma fn_norm_push : forall x l, fn_norm l -> fn_norm (fn_push x l).
Proof.
 intros x [|y l] H.
 - destruct x; cbn [fn_push]; unfold fn_norm; cbn; auto; right; discriminate.
 - destruct x; cbn [fn_push]; right; destruct H as [H|H]; try discriminate; exact H.
Qed.
Lemma fn_blank_last : forall l, word_blank l=true -> last l S0=S0.
Proof.
 induction l as [|x l IH]; intro H; [reflexivity|].
 unfold word_blank in H; cbn in H; apply andb_prop in H as [Hx Hl].
 destruct l as [|y l].
 - cbn; apply sym_eqb_spec; exact Hx.
 - apply IH; exact Hl.
Qed.
Lemma fn_norm_blank : forall l, fn_norm l -> (word_blank l=true <-> l=[]).
Proof.
 intros l Hnorm; split; [|intros ->; reflexivity].
 intro Hb; destruct Hnorm as [H|H]; [exact H|].
 exfalso; apply H; apply fn_blank_last; exact Hb.
Qed.
Lemma fn_firstn_empty : forall n (l:list Sym), 1<=n -> (firstn n l=[] <-> l=[]).
Proof. intros [|n] [|x l] H; cbn; try lia; split; congruence. Qed.
Lemma fn_firstn_chd : forall n l, 1<=n -> chd (firstn n l)=chd l.
Proof. intros [|n] [|x l] H; cbn; try lia; reflexivity. Qed.
Definition fn_push_window n x w :=
 if sym_eqb x S0 && match w with []=>true|_=>false end then []
 else firstn n (x::w).
Lemma fn_push_window_spec : forall n x l, 1<=n ->
 fn_push_window n x (firstn n l)=firstn n (fn_push x l).
Proof.
 intros [|n] x l H; [lia|]. destruct l as [|y l]; destruct x;
 unfold fn_push_window; cbn [fn_push firstn sym_eqb andb]; rewrite ?firstn_nil; try reflexivity.
 all: f_equal; change (firstn n (firstn (S n) (y::l))=firstn n (y::l));
 rewrite firstn_firstn; replace (Nat.min n (S n)) with n by lia; reflexivity.
Qed.
Lemma fn_firstn_pop : forall n l, 1<=n ->
 firstn n (ctl l)=tl(firstn n l)++firstn 1 (skipn n l).
Proof.
 intros n l H; revert l H. induction n as [|n IH]; intros [|x l] H; try lia; cbn; auto.
 destruct n as [|n]; [destruct l; reflexivity|]. cbn in *.
 destruct l as [|y l]; [reflexivity|]. cbn in *.
 f_equal. specialize (IH (y::l) ltac:(lia)); cbn in IH; exact IH.
Qed.
Definition fn_pops n gs w :=
 filter (fun v=>gmem v gs)
   (if length w <? n then [tl w]
    else [tl w;tl w++[S0];tl w++[S1];tl w++[S2];tl w++[S3]]).
Lemma fn_pops_sound : forall n gs l,
 1<=n -> gmem (firstn n (ctl l)) gs=true ->
 In (firstn n (ctl l)) (fn_pops n gs (firstn n l)).
Proof.
 intros n gs l Hn Hg. unfold fn_pops. apply filter_In; split; [|exact Hg].
 destruct (length (firstn n l) <? n) eqn:E.
 - apply Nat.ltb_lt in E. rewrite firstn_length in E.
   assert (Hl:length l<n) by lia. rewrite (firstn_all2 l (n:=n) ltac:(lia)).
   rewrite firstn_all2 by (destruct l; cbn in *; lia). left; reflexivity.
 - rewrite fn_firstn_pop by exact Hn.
   destruct (skipn n l) as [|x u]; cbn [firstn].
   + rewrite app_nil_r; left; reflexivity.
   + destruct x; cbn; tauto.
Qed.

Definition fn_side n gs w f := exists l,
 fn_norm l /\ f=lift_side l /\ w=firstn n l /\
 forall d, gmem (firstn n (skipn d l)) gs=true.
Definition fn_covers n ls rs (a:cconf) (c:ExecState) :=
 let '(q,(l,h,r)):=a in fst c=q /\ t_head(snd c)=h /\
 fn_side n ls l (t_left(snd c)) /\ fn_side n rs r (t_right(snd c)).
Definition fn_succs tm n ls rs (a:cconf) : option(list cconf) :=
 let '(q,(l,h,r)):=a in match tm q h with
 |None=>None
 |Some tr=>match t_dir tr with
   |DR=>let l':=fn_push_window n (t_write tr) l in
     if gmem l' ls then Some(map(fun r'=>(t_next tr,(l',chd r,r')))(fn_pops n rs r))else None
   |DL=>let r':=fn_push_window n (t_write tr) r in
     if gmem r' rs then Some(map(fun l'=>(t_next tr,(l',chd l,r')))(fn_pops n ls l))else None
   end end.
Lemma fn_side_push : forall n gs w f x,
 1<=n -> fn_side n gs w f -> gmem (fn_push_window n x w) gs=true ->
 fn_side n gs (fn_push_window n x w) (push_side x f).
Proof.
 intros n gs w f x Hn (l & Hnorm & -> & -> & Hgrams) Hg.
 rewrite fn_push_window_spec in * by exact Hn.
 exists (fn_push x l). split; [apply fn_norm_push; exact Hnorm|].
 split; [rewrite fn_push_lift; symmetry; apply lift_side_cons|]. split; [reflexivity|].
 intros [|d]; [exact Hg|]. destruct x; destruct l; cbn [fn_push skipn] in *; try exact Hg; apply Hgrams.
Qed.
Lemma fn_side_pop : forall n gs w f,
 1<=n -> fn_side n gs w f -> exists w',
 In w' (fn_pops n gs w) /\ fn_side n gs w' (tail_side f).
Proof.
 intros n gs w f Hn (l & Hnorm & -> & -> & Hgrams).
 exists (firstn n (ctl l)). split.
 - apply fn_pops_sound; [exact Hn|exact (Hgrams 1)].
 - exists (ctl l); split; [apply fn_norm_ctl; exact Hnorm|].
   split; [symmetry; apply lift_side_tl|]. split; [reflexivity|].
   intro d. replace (skipn d (ctl l)) with (skipn (S d) l) by (destruct l; cbn [ctl skipn]; rewrite ?skipn_nil; reflexivity).
   apply Hgrams.
Qed.
Lemma fn_side_head : forall n gs w f, 1<=n -> fn_side n gs w f -> chd w=f 0.
Proof. intros n gs w f Hn (l & _ & -> & -> & _).
 rewrite fn_firstn_chd by exact Hn. apply lift_side_hd. Qed.
Lemma fn_covers_instr : forall n ls rs a c, fn_covers n ls rs a c -> cinstr a=instr_of c.
Proof. intros n ls rs [q[[l h]r]] c (Hq & Hh & _).
 unfold cinstr,instr_of; simpl; congruence. Qed.
Lemma fn_succs_sound : forall tm n ls rs a c,
 1<=n -> fn_covers n ls rs a c ->
 match fn_succs tm n ls rs a,step tm c with
 |Some sl,Some c'=>exists a',In a' sl /\ fn_covers n ls rs a' c'
 |Some _,None=>False |None,_=>True end.
Proof.
 intros tm n ls rs [q[[l h]r]] [qc [L hc R]] Hn (Hq & Hh & HL & HR).
 cbn in Hq,Hh,HL,HR; subst qc hc. unfold fn_succs,step; cbn.
 destruct (tm q h) as [tr|] eqn:E; [|exact I].
 destruct (t_dir tr) eqn:Ed; cbn [tape_move].
 - destruct (gmem (fn_push_window n (t_write tr) r) rs) eqn:Eg; [|exact I].
   destruct (fn_side_pop n ls l L Hn HL) as (l' & Hin & Hcov).
   exists (t_next tr,(l',chd l,fn_push_window n (t_write tr) r)). split.
   + apply in_map_iff; exists l'; split; [reflexivity|exact Hin].
   + cbn [fn_covers fst snd t_head t_left t_right]. split; [reflexivity|].
     split; [symmetry; eapply fn_side_head; eauto|]. split; [exact Hcov|].
     eapply fn_side_push; eauto.
 - destruct (gmem (fn_push_window n (t_write tr) l) ls) eqn:Eg; [|exact I].
   destruct (fn_side_pop n rs r R Hn HR) as (r' & Hin & Hcov).
   exists (t_next tr,(fn_push_window n (t_write tr) l,chd r,r')). split.
   + apply in_map_iff; exists r'; split; [reflexivity|exact Hin].
   + cbn [fn_covers fst snd t_head t_left t_right]. split; [reflexivity|].
     split; [symmetry; eapply fn_side_head; eauto|]. split; [|exact Hcov].
     eapply fn_side_push; eauto.
Qed.

Definition fn_seed_side n l :=
 let u:=fn_trim l in map(fun d=>firstn n(skipn d u))(seq 0 (S(length u))).
Definition fn_seed_ok n ls rs (cc:cconf) :=
 let '(_,(l,_,r)):=cc in
 forallb(fun w=>gmem w ls)(fn_seed_side n l) && forallb(fun w=>gmem w rs)(fn_seed_side n r).
Definition fn_start n (cc:cconf) : cconf :=
 let '(q,(l,h,r)):=cc in(q,(firstn n(fn_trim l),h,firstn n(fn_trim r))).
Lemma fn_seed_side_sound : forall n gs l,
 forallb(fun w=>gmem w gs)(fn_seed_side n l)=true ->
 forall d,gmem(firstn n(skipn d(fn_trim l)))gs=true.
Proof.
 intros n gs l H d. unfold fn_seed_side in H; rewrite forallb_forall in H.
 destruct (le_lt_dec d (length(fn_trim l))) as [Hd|Hd].
 - apply H; apply in_map_iff; exists d; split; [reflexivity|apply in_seq; lia].
 - rewrite skipn_all2 by lia.
   specialize (H (firstn n(skipn(length(fn_trim l))(fn_trim l)))).
   rewrite skipn_all in H. apply H. apply in_map_iff; exists (length(fn_trim l)).
   split; [rewrite skipn_all; reflexivity|apply in_seq; lia].
Qed.
Lemma fn_start_covers : forall n ls rs cc,
 fn_seed_ok n ls rs cc=true -> fn_covers n ls rs (fn_start n cc)(lift cc).
Proof.
 intros n ls rs [q[[l h]r]] H; apply andb_prop in H as [HL HR].
 cbn [fn_start fn_covers lift lift_tape fst snd t_head t_left t_right].
 split; [reflexivity|]; split; [reflexivity|]; split.
 - exists (fn_trim l); split; [apply fn_trim_norm|]. split; [symmetry; apply fn_trim_lift|].
   split; [reflexivity|apply fn_seed_side_sound; exact HL].
 - exists (fn_trim r); split; [apply fn_trim_norm|]. split; [symmetry; apply fn_trim_lift|].
   split; [reflexivity|apply fn_seed_side_sound; exact HR].
Qed.

Definition fn_nb (w:list Sym) := match w with []=>false|_=>true end.
Lemma fn_word_blank_ext : forall l r,
 (forall i,nthb l i=nthb r i) -> word_blank l=word_blank r.
Proof.
 intros l r H. destruct (word_blank l) eqn:HL, (word_blank r) eqn:HR; try reflexivity.
 - assert (E:word_blank r=true).
   { apply all_blank_word; intro i; rewrite <-H; apply word_blank_nthb; exact HL. } congruence.
 - assert (E:word_blank l=true).
   { apply all_blank_word; intro i; rewrite H; apply word_blank_nthb; exact HR. } congruence.
Qed.
Lemma fn_side_nb : forall n gs w l,
 1<=n -> fn_side n gs w (lift_side l) -> fn_nb w=negb(word_blank l).
Proof.
 intros n gs w l Hn (u & Hnorm & Hlift & -> & _).
 assert (Hb:word_blank l=word_blank u).
 { apply fn_word_blank_ext; intro i; exact (f_equal(fun f=>f i)Hlift). }
 rewrite Hb. destruct n as [|n]; [lia|]. destruct u as [|x u]; [reflexivity|].
 assert (E:word_blank(x::u)=false).
 { destruct (word_blank(x::u)) eqn:E; [|reflexivity].
   apply (proj1(fn_norm_blank _ Hnorm)) in E; discriminate. }
 cbn [firstn fn_nb]; rewrite E; reflexivity.
Qed.
Definition fn_span l := count1 CN l+ibc l.
Lemma fn_span_cons : forall x l,
 fn_span(x::l)=fn_span l+(if negb(sym_eqb x S0) || negb(word_blank l) then 1 else 0).
Proof.
 intros x l. unfold fn_span; cbn [count1 ibc]. destruct x, (word_blank l); cbn [nc1 sym_eqb andb negb orb]; lia.
Qed.
Lemma fn_span_ctl : forall l,
 fn_span l=fn_span(ctl l)+(if negb(word_blank l) then 1 else 0).
Proof.
 intros [|x l]; [reflexivity|]. rewrite fn_span_cons.
 cbn [ctl]. f_equal.
 change ((if negb(sym_eqb x S0)||negb(word_blank l) then 1 else 0)=
 (if negb(sym_eqb x S0 && word_blank l) then 1 else 0)).
 destruct x, (word_blank l); reflexivity.
Qed.
Inductive fnmeas := FnCount (m:ngmeas) | FnSpanL | FnSpanR.
Definition fnm_val m cc := match m with
 |FnCount m=>ngm_val m cc
 |FnSpanL=>let '(_,(l,_,_)):=cc in fn_span l
 |FnSpanR=>let '(_,(_,_,r)):=cc in fn_span r end.
Definition fnm_delta tm m (a a':cconf) : Z :=
 let '(q,(l,h,r)):=a in match tm q h with
 |None=>0%Z
 |Some tr=>match m,t_dir tr with
   |FnCount m,_=>ngm_delta tm m a a'
   |FnSpanL,DL=> -zi(fn_nb l)
   |FnSpanR,DR=> -zi(fn_nb r)
   |FnSpanL,DR=>zi(negb(sym_eqb(t_write tr)S0)||fn_nb l)
   |FnSpanR,DL=>zi(negb(sym_eqb(t_write tr)S0)||fn_nb r)
   end end.
Lemma fnm_exact : forall tm n ls rs m a cc a' cc',
 1<=n -> fn_covers n ls rs a(lift cc) -> cstep tm cc=Some cc' ->
 Z.of_nat(fnm_val m cc')=(Z.of_nat(fnm_val m cc)+fnm_delta tm m a a')%Z.
Proof.
 intros tm n ls rs m [q[[lw h]rw]] [qc[[l hc]r]] a' cc' Hn (Hq & Hh & HL & HR) Hstep.
 cbn [lift lift_tape fst snd t_head t_left t_right] in Hq,Hh,HL,HR; subst qc hc.
 assert (EL:chd lw=chd l) by (rewrite (lift_side_hd l); eapply fn_side_head; eauto).
 assert (ER:chd rw=chd r) by (rewrite (lift_side_hd r); eapply fn_side_head; eauto).
 pose proof(fn_side_nb n ls lw l Hn HL) as NL.
 pose proof(fn_side_nb n rs rw r Hn HR) as NR.
 cbn [cstep] in Hstep. destruct (tm q h) as [tr|] eqn:E; [|discriminate].
 injection Hstep as <-. unfold fnm_delta; rewrite E.
 destruct m as [[col|col|col]| |]; destruct (t_dir tr) eqn:Ed;
 cbn [fnm_val ngm_val ctape_move]; try (unfold ngm_delta; rewrite E; rewrite ?Ed).
 all: rewrite ?EL,?ER,?NL,?NR.
 all: try (pose proof(countnb_hd col l); pose proof(countnb_hd col r);
   pose proof(countnb_cons col (t_write tr) l); pose proof(countnb_cons col (t_write tr) r);
   unfold countnb,zc in *; unfold zc1; rewrite ?Nat2Z.inj_add; lia).
 all: rewrite ?fn_span_cons; pose proof(fn_span_ctl l); pose proof(fn_span_ctl r);
 unfold zi; destruct (negb(word_blank l)),(negb(word_blank r)),(negb(sym_eqb(t_write tr)S0)); cbn [orb]; lia.
Qed.

Fixpoint fn_explore (tm : TM) (n : nat) (lset rset : gset)
    (fuel : nat) (seen : list cconf) (sp : PositiveSet.t)
    (todo : list cconf) : list cconf :=
  match fuel with
  | 0 => seen
  | S f =>
      match todo with
      | [] => seen
      | a :: todo' =>
          if pset_mem cconf cconf_enc a sp
          then fn_explore tm n lset rset f seen sp todo'
          else let sp' := pset_add cconf cconf_enc a sp in
               match fn_succs tm n lset rset a with
               | None => fn_explore tm n lset rset f (a :: seen) sp' todo'
               | Some l => fn_explore tm n lset rset f (a :: seen) sp'
                                      (l ++ todo')
               end
      end
  end.

Definition fn_harvest (tm : TM) (n : nat) (a : cconf)
  : (list (list Sym) * list (list Sym)) :=
  let '(q, (lw, s, rw)) := a in
  match tm q s with
  | Some tr => match t_dir tr with
               | DR => ([fn_push_window n (t_write tr) lw], [])
               | DL => ([], [fn_push_window n (t_write tr) rw])
               end
  | None => ([], [])
  end.

Fixpoint fn_grow (tm : TM) (n : nat) (a0 : cconf) (fuel rounds : nat)
    (lset rset : gset) : (gset * gset) :=
  match rounds with
  | 0 => (lset, rset)
  | S k =>
      let ctxs := fn_explore tm n lset rset fuel [] PositiveSet.empty [a0] in
      let sets' :=
        fold_left (fun p a =>
                     let '(ls, rs) := p in
                     let '(hl, hr) := fn_harvest tm n a in
                     (gadds hl ls, gadds hr rs))
                  ctxs (lset, rset) in
      let '(lset', rset') := sets' in
      if (PositiveSet.cardinal lset' =? PositiveSet.cardinal lset)
         && (PositiveSet.cardinal rset' =? PositiveSet.cardinal rset)
      then (lset, rset)
      else fn_grow tm n a0 fuel k lset' rset'
  end.

