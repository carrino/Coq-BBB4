(** Finite left barriers, with an arbitrary finite right context. *)
From Coq Require Import Arith Lia List Bool.
From SmallBB Require Import Statement StatementTr CTape ClosureTr.
Import ListNotations.

Fixpoint wall_word_eqb (a b : list Sym) : bool :=
  match a,b with [],[] => true | x::a,y::b => sym_eqb x y && wall_word_eqb a b | _,_ => false end.
Lemma wall_word_eq : forall a b, wall_word_eqb a b = true <-> a=b.
Proof. induction a; destruct b; cbn; try (split; congruence).
  rewrite andb_true_iff, sym_eqb_spec, IHa. split; [intros [-> ->]; reflexivity|intro E; injection E; auto]. Qed.
Definition wall_conf_eqb (a b : cconf) : bool :=
 let '(q,(L,h,R)):=a in let '(q',(L',h',R')):=b in
 st_eqb q q' && sym_eqb h h' && wall_word_eqb L L' && wall_word_eqb R R'.
Lemma wall_conf_eq : forall a b, wall_conf_eqb a b=true <-> a=b.
Proof. intros [q[[L h]R]] [q'[[L' h']R']]; cbn [wall_conf_eqb].
 rewrite !andb_true_iff, st_eqb_spec, sym_eqb_spec, !wall_word_eq.
 split; [intros [[[-> ->] ->] ->]; reflexivity|intro E; injection E; auto]. Qed.
Definition wall_wmem g G := existsb (wall_word_eqb g) G.
Definition wall_cmem c I := existsb (wall_conf_eqb c) I.
Lemma wall_wmem_spec : forall g G, wall_wmem g G=true <-> In g G.
Proof. intros; unfold wall_wmem; rewrite existsb_exists; split.
 - intros (w & Hw & E); apply wall_word_eq in E; subst; assumption.
 - intro H; exists g; split; [assumption|apply wall_word_eq; reflexivity]. Qed.
Lemma wall_cmem_spec : forall c I, wall_cmem c I=true <-> In c I.
Proof. intros; unfold wall_cmem; rewrite existsb_exists; split.
 - intros (w & Hw & E); apply wall_conf_eq in E; subst; assumption.
 - intro H; exists c; split; [assumption|apply wall_conf_eq; reflexivity]. Qed.
Definition wall_ext (c:cconf) (U:list Sym) : cconf := let '(q,(L,h,R)):=c in (q,(L,h,R++U)).
Definition wall_entry q g : cconf := (q,(ctl g,chd g,[])).
Inductive wall_inv (G:list(list Sym)) (I:list cconf) : cconf -> Prop :=
| wall_out : forall q L h R g, In g G -> wall_inv G I (q,(L++g,h,R))
| wall_in : forall c U, In c I -> wall_inv G I (wall_ext c U).
Definition wall_rule tm target G I (c:cconf) :=
 if instr_eqb (cinstr c) target then true else
 let '(q,(L,h,R)):=c in match tm q h with
 | None => false
 | Some tr => match t_dir tr with
   | DR => match R with [] => wall_wmem (t_write tr::L) G
           | _ => match cstep tm c with Some d=>wall_cmem d I |None=>false end end
   | DL => match L with []=>false
           | _=>match cstep tm c with Some d=>wall_cmem d I |None=>false end end
   end end.
Definition wall_check tm target entry G I :=
 forallb (fun g => match g with []=>false | _=>forallb (fun q=>wall_cmem (wall_entry q g) I) entry end) G
 && forallb (wall_rule tm target G I) I.
Lemma wall_entries : forall tm target entry G I, wall_check tm target entry G I=true ->
 forall g, In g G -> g<>[] /\ forall q, In q entry -> In (wall_entry q g) I.
Proof.
 intros tm target entry G I H g Hg. unfold wall_check in H; apply andb_true_iff in H as [H _].
 rewrite forallb_forall in H; specialize (H g Hg). destruct g; [discriminate|].
 split; [discriminate|]. intros q Hq; apply wall_cmem_spec. cbn in H; rewrite forallb_forall in H; auto.
Qed.
Lemma wall_rules : forall tm target entry G I, wall_check tm target entry G I=true ->
 forall c, In c I -> wall_rule tm target G I c=true.
Proof. intros tm target entry G I H; unfold wall_check in H; apply andb_true_iff in H as [_ H]; now rewrite forallb_forall in H. Qed.
Lemma wall_step : forall tm target entry G I,
 wall_check tm target entry G I=true ->
 (forall q h tr, (q,h)<>target -> tm q h=Some tr -> t_dir tr=DL -> In (t_next tr) entry) ->
 forall c d, wall_inv G I c -> cinstr c<>target -> cstep tm c=Some d -> wall_inv G I d.
Proof.
 intros tm target entry G I HC HE c d HI HN HS. inversion HI; subst.
 - cbn [cstep] in HS. destruct (tm q h) as [tr|] eqn:ET; [|discriminate].
   cbn [ctape_move] in HS. destruct (t_dir tr) eqn:ED.
   + destruct L as [|x L].
     * cbn [app] in HS; injection HS as <-. cbn [ctape_move].
       change (wall_inv G I (wall_ext (wall_entry (t_next tr) g) (t_write tr::R))).
       apply wall_in. apply (wall_entries _ _ _ _ _ HC _ H).
       apply HE with (q:=q)(h:=h)(tr:=tr); assumption.
     * injection HS as <-; cbn [ctape_move ctl chd app]; apply wall_out; assumption.
   + destruct R as [|x R]; injection HS as <-; cbn [ctape_move ctl chd];
       apply (wall_out G I _ (t_write tr::L) _ _ g); assumption.
 - destruct c0 as [q[[L h]R]]. cbn [wall_ext] in *.
   pose proof (wall_rules _ _ _ _ _ HC _ H) as HR.
   unfold wall_rule in HR. assert (EN:instr_eqb (cinstr (q,(L,h,R))) target=false).
   { destruct (instr_eqb _ _) eqn:E; [apply instr_eqb_spec in E; contradiction|reflexivity]. }
   unfold cinstr in EN,HR; cbn in EN,HR; rewrite EN in HR; cbn in HR. cbn [cstep] in HS.
   destruct (tm q h) as [tr|] eqn:ET; [|discriminate].
   cbn [ctape_move] in HS. destruct (t_dir tr) eqn:ED.
   + destruct L as [|x L]; [discriminate|].
     cbn [ctape_move chd ctl] in HR. apply wall_cmem_spec in HR. injection HS as <-.
     change (wall_inv G I (wall_ext (t_next tr,(L,x,t_write tr::R)) U)); apply wall_in; assumption.
   + destruct R as [|x R].
     * cbn in HR; apply wall_wmem_spec in HR. injection HS as <-.
       destruct U; cbn [ctape_move chd ctl app]; apply (wall_out G I _ [] _ _ (t_write tr::L)); assumption.
     * cbn [ctape_move chd ctl] in HR. apply wall_cmem_spec in HR. injection HS as <-.
       change (wall_inv G I (wall_ext (t_next tr,(t_write tr::L,x,R)) U)); apply wall_in; assumption.
Qed.
Lemma wall_left_nonempty : forall tm target entry G I,
 wall_check tm target entry G I=true ->
 forall q L h R tr, wall_inv G I (q,(L,h,R)) -> (q,h)<>target ->
 tm q h=Some tr -> t_dir tr=DL -> L<>[].
Proof.
 intros tm target entry G I HC q L h R tr HI HN ET ED. inversion HI; subst.
 - destruct (wall_entries _ _ _ _ _ HC _ H0) as [HG _].
   intro E; apply app_eq_nil in E as [_ E]; contradiction.
 - destruct c as [q'[[L' h']R']]; cbn [wall_ext] in H; injection H as <- <- <- <-.
   pose proof (wall_rules _ _ _ _ _ HC _ H0) as HR. unfold wall_rule in HR.
   assert (EN:instr_eqb (cinstr (q',(L',h',R'))) target=false).
   { destruct (instr_eqb _ _) eqn:E; [apply instr_eqb_spec in E; contradiction|reflexivity]. }
   unfold cinstr in EN,HR; cbn in EN,HR; rewrite EN in HR; cbn in HR; rewrite ET,ED in HR.
   destruct L'; discriminate.
Qed.
