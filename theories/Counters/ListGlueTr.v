(** * ListGlueTr: block-LIST glue -- TriGlue families with list TAILS whose
    items carry a neighbour recurrence.

    The rows of SCOPING_INSTR.md §7.4.BL piece (a) keep a list of blocks
    whose lengths follow a neighbour recurrence ([b_(i+1) = a b_i + d_i],
    the offset [d_i] a digit).  [TriGlueTr]'s families are whole symbolic
    tapes with a fixed number of blocks, so on these rows the family count
    grows without bound.  Here a family is a TriGlue family (the WINDOW)
    plus, on each side, an optional TAIL: a concrete list of ITEMS
    [pre ++ u^e], each tagged with the transition of a finite automaton it
    was read by.  A transition carries the relation of the item's exponent
    [e] to the exponent [p] of the item before it (the first item: to the
    family's REF, an affine expression over the family's variables):

      up    [e + dn = a * p + dp]
      down  [p + dn = a * e + dp]           ([a = 0]: also [e = 0])

    - A dispatch tree node may UNFOLD a side's first tail item: one kid per
      transition out of the current state (a kid the relation makes
      impossible in the region is VOID, checked), and one for the empty
      tail when the state is accepting.  The unfolded exponent is an affine
      expression, checked against the relation coefficient-wise.
    - A leaf runs ONE [LapDecider] chain on the window and the unfolded
      items; everything beyond is the chain's opaque rest, exactly as in
      [TriGlueTr].  Its target family may FOLD the outermost window items
      back into the tail; every relation is checked coefficient-wise.
    - A certified lower bound per state on the ref of any valid tail
      ([lc_mins]) makes a region whose ref is a smaller constant VOID.
    - Liveness: [TriGlueTr]'s (leaf, residue) nodes, with rankings that add,
      per node and per side, [alpha_t * e + beta_t] for every tail item read
      by transition [t]; a step checks the window part affinely and the
      weights of the untouched tail transition by transition.

    Everything is checked coefficient-wise, so the certificate is data and
    [lg_check] is one boolean.  Only axiom: [functional_extensionality_dep]
    (through [CTape]). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr Mirror.
From BBB4.Checkers Require Import WrapTr LapDecider.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Checkers Require Import TCyclerQHTr.
From BBB4.Counters Require Import WTape LapCertGlueLift LapGlueTr SweepGlueTr TriGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

(** ** Affine equality *)

Definition aeq (e1 e2 : aexp) : bool := ale e1 e2 && ale e2 e1.

Lemma aeq_sound : forall v e1 e2, aeq e1 e2 = true -> aeval v e1 = aeval v e2.
Proof.
  intros v e1 e2 H. unfold aeq in H. apply andb_prop in H as [H1 H2].
  pose proof (ale_sound v _ _ H1). pose proof (ale_sound v _ _ H2). lia.
Qed.

Definition anocoef (e : aexp) : bool := forallb (fun ka => snd ka =? 0) (a_t e).

Lemma anocoef_const : forall v e, anocoef e = true -> aeval v e = a_c e.
Proof.
  intros v [c t] H. unfold aeval, anocoef in *; cbn [a_c a_t] in *.
  enough (teval v t = 0) by lia.
  induction t as [|[k a] t IH]; cbn [teval]; [reflexivity|].
  cbn in H. apply andb_prop in H as [H1 H2]. apply Nat.eqb_eq in H1. subst a.
  rewrite IH by exact H2. lia.
Qed.

(** every coefficient divisible by [a] *)
Definition adiv (a : nat) (e : aexp) : bool := forallb (fun ka => snd ka mod a =? 0) (a_t e).

(** ** Relations, transitions, tails *)

Record ltrans := mkLT {
  lt_left : bool;       (** the side: true = lsd *)
  lt_src  : nat;
  lt_kind : nat;
  lt_dst  : nat;
  lt_up   : bool;
  lt_a    : nat;
  lt_dp   : nat;
  lt_dn   : nat
}.

Definition relsem (tr : ltrans) (p e : nat) : Prop :=
  if lt_up tr then e + lt_dn tr = lt_a tr * p + lt_dp tr
  else if lt_a tr =? 0 then p + lt_dn tr = lt_dp tr /\ e = 0
  else p + lt_dn tr = lt_a tr * e + lt_dp tr.

Lemma relsem_det : forall tr p e e', relsem tr p e -> relsem tr p e' -> e = e'.
Proof.
  intros tr p e e' H H'. unfold relsem in *.
  destruct (lt_up tr); [lia|].
  destruct (lt_a tr =? 0) eqn:E; [lia|]. apply Nat.eqb_neq in E. nia.
Qed.

(** the relation between two affine expressions, as an identity *)
Definition relchk (tr : ltrans) (p e : aexp) : bool :=
  if lt_up tr then aeq (aaddc e (lt_dn tr)) (aaddc (ascale (lt_a tr) p) (lt_dp tr))
  else if lt_a tr =? 0 then aeq (aaddc p (lt_dn tr)) (aconst (lt_dp tr)) && aeq e (aconst 0)
  else aeq (aaddc p (lt_dn tr)) (aaddc (ascale (lt_a tr) e) (lt_dp tr)).

Lemma relchk_sound : forall tr p e v, relchk tr p e = true -> relsem tr (aeval v p) (aeval v e).
Proof.
  intros tr p e v H. unfold relchk, relsem in *.
  destruct (lt_up tr).
  - apply (aeq_sound v) in H. rewrite !aeval_aaddc, aeval_ascale in H. exact H.
  - destruct (lt_a tr =? 0).
    + apply andb_prop in H as [H1 H2].
      apply (aeq_sound v) in H1, H2. rewrite aeval_aaddc in H1.
      unfold aeval, aconst in H1, H2; cbn in H1, H2. unfold aeval. lia.
    + apply (aeq_sound v) in H. rewrite !aeval_aaddc, aeval_ascale in H. exact H.
Qed.

Definition item (kinds : list (list Sym * list Sym)) (k e : nat) : list Sym :=
  match nth_error kinds k with Some (pre, u) => pre ++ rep u e | None => [] end.

Definition item_segs (kinds : list (list Sym * list Sym)) (k : nat) (e : aexp) : list seg :=
  match nth_error kinds k with Some (pre, u) => [SL pre; SB u e] | None => [] end.

Lemma item_segs_ok : forall kinds k e v,
  sided v (item_segs kinds k e) = item kinds k (aeval v e).
Proof.
  intros kinds k e v. unfold item_segs, item.
  destruct (nth_error kinds k) as [[pre u]|]; cbn; [|reflexivity].
  rewrite app_nil_r. reflexivity.
Qed.

Section Tails.

Variable kinds : list (list Sym * list Sym).
Variable trans : list ltrans.
Variable acc : list (bool * nat).

Definition tr_kind (t : nat) : nat :=
  match nth_error trans t with Some tr => lt_kind tr | None => 0 end.

(** a tail: items (transition index, exponent), nearest first *)
Fixpoint trend (T : list (nat * nat)) : list Sym :=
  match T with
  | [] => []
  | (t, e) :: T' => item kinds (tr_kind t) e ++ trend T'
  end.

Definition accb (lsd : bool) (s : nat) : bool :=
  existsb (fun bs => Bool.eqb (fst bs) lsd && (snd bs =? s)) acc.

Fixpoint tvalid (lsd : bool) (s r : nat) (T : list (nat * nat)) : Prop :=
  match T with
  | [] => accb lsd s = true
  | (t, e) :: T' =>
      exists tr, nth_error trans t = Some tr /\ lt_left tr = lsd /\ lt_src tr = s
                 /\ relsem tr r e /\ tvalid lsd (lt_dst tr) e T'
  end.

Definition relsemb (tr : ltrans) (p e : nat) : bool :=
  if lt_up tr then e + lt_dn tr =? lt_a tr * p + lt_dp tr
  else if lt_a tr =? 0 then (p + lt_dn tr =? lt_dp tr) && (e =? 0)
  else p + lt_dn tr =? lt_a tr * e + lt_dp tr.

Lemma relsemb_ok : forall tr p e, relsemb tr p e = true -> relsem tr p e.
Proof.
  intros tr p e H. unfold relsemb, relsem in *.
  destruct (lt_up tr); [apply Nat.eqb_eq; exact H|].
  destruct (lt_a tr =? 0).
  - apply andb_prop in H as [H1 H2]. apply Nat.eqb_eq in H1, H2. auto.
  - apply Nat.eqb_eq. exact H.
Qed.

Fixpoint tvalidb (lsd : bool) (s r : nat) (T : list (nat * nat)) : bool :=
  match T with
  | [] => accb lsd s
  | (t, e) :: T' =>
      match nth_error trans t with
      | Some tr => Bool.eqb (lt_left tr) lsd && (lt_src tr =? s) && relsemb tr r e
                   && tvalidb lsd (lt_dst tr) e T'
      | None => false
      end
  end.

Lemma tvalidb_ok : forall T lsd s r, tvalidb lsd s r T = true -> tvalid lsd s r T.
Proof.
  induction T as [|[t e] T IH]; intros lsd s r H; cbn in H |- *; [exact H|].
  destruct (nth_error trans t) as [tr|] eqn:Et; [|discriminate].
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2]. apply Bool.eqb_prop in H1. apply Nat.eqb_eq in H2.
  exists tr. repeat split; auto. apply relsemb_ok. exact H3.
Qed.

(** ** A lower bound on the ref of any valid tail, per state *)

Definition mget (mins : list (bool * nat * nat)) (lsd : bool) (s : nat) : nat :=
  match find (fun bsm => Bool.eqb (fst (fst bsm)) lsd && (snd (fst bsm) =? s)) mins with
  | Some bsm => snd bsm
  | None => 0
  end.

(** the least pred of an item that satisfies the transition's relation with
    an exponent [>= md] (a lower bound, [None]: no pred at all) *)
Definition rbound (tr : ltrans) (md : nat) : option nat :=
  if lt_up tr then
    if lt_a tr =? 0 then (if md + lt_dn tr <=? lt_dp tr then Some 0 else None)
    else Some ((md + lt_dn tr - lt_dp tr + lt_a tr - 1) / lt_a tr)
  else if lt_a tr =? 0 then (if md =? 0 then Some (lt_dp tr - lt_dn tr) else None)
  else Some (lt_a tr * md + lt_dp tr - lt_dn tr).

Definition mins_ok (mins : list (bool * nat * nat)) : bool :=
  forallb (fun tr => match rbound tr (mget mins (lt_left tr) (lt_dst tr)) with
                     | Some b => mget mins (lt_left tr) (lt_src tr) <=? b
                     | None => true
                     end) trans
  && forallb (fun bsm => negb (accb (fst (fst bsm)) (snd (fst bsm))) || (snd bsm =? 0)) mins.

Lemma rbound_ok : forall tr md p e, relsem tr p e -> md <= e ->
  match rbound tr md with Some b => b <= p | None => False end.
Proof.
  intros tr md p e H He. unfold rbound, relsem in *.
  destruct (lt_up tr).
  - destruct (lt_a tr =? 0) eqn:Ea.
    + apply Nat.eqb_eq in Ea. rewrite Ea in H.
      destruct (md + lt_dn tr <=? lt_dp tr) eqn:E; [lia|]. apply Nat.leb_gt in E. lia.
    + apply Nat.eqb_neq in Ea.
      apply Nat.le_trans with (m := (lt_a tr * p + lt_a tr - 1) / lt_a tr).
      * apply Nat.Div0.div_le_mono. lia.
      * replace (lt_a tr * p + lt_a tr - 1) with (lt_a tr - 1 + p * lt_a tr) by nia.
        rewrite Nat.div_add by exact Ea.
        rewrite Nat.div_small by lia. lia.
  - destruct (lt_a tr =? 0) eqn:Ea.
    + destruct H as [H1 H2]. subst e.
      destruct (md =? 0) eqn:Em; [lia|]. apply Nat.eqb_neq in Em. lia.
    + apply Nat.eqb_neq in Ea. nia.
Qed.

Lemma mins_sound : forall mins, mins_ok mins = true ->
  forall T lsd s r, tvalid lsd s r T -> mget mins lsd s <= r.
Proof.
  intros mins Hm T. unfold mins_ok in Hm. apply andb_prop in Hm as [Ht Ha].
  rewrite forallb_forall in Ht, Ha.
  induction T as [|[t e] T IH]; intros lsd s r H; cbn [tvalid] in H.
  - unfold mget.
    destruct (find (fun bsm => Bool.eqb (fst (fst bsm)) lsd && (snd (fst bsm) =? s)) mins)
      as [bsm|] eqn:E; [|lia].
    apply find_some in E as [Hin Hf]. specialize (Ha bsm Hin).
    apply andb_prop in Hf as [Hl Hs]. apply Bool.eqb_prop in Hl. apply Nat.eqb_eq in Hs.
    rewrite Hl, Hs, H in Ha. cbn in Ha. apply Nat.eqb_eq in Ha. lia.
  - destruct H as (tr & Htr & Hl & Hs & Hr & Hv).
    specialize (IH _ _ _ Hv).
    specialize (Ht tr (nth_error_In _ _ Htr)).
    pose proof (rbound_ok tr _ r e Hr IH) as Hb. rewrite Hl, Hs in Ht.
    destruct (rbound tr (mget mins lsd (lt_dst tr))) as [b|]; [|contradiction].
    apply Nat.leb_le in Ht. lia.
Qed.

End Tails.

(** ** Families, unfold nodes, leaves *)

(** unfold nodes, reached from a [TLeaf u] of a family's [TriGlueTr]
    dispatch tree.  [UUnf lsd endk kids]: the side's first tail item; a kid
    [(t, Some (e, u'))] takes the items read by transition [t], with the
    exponent [e] (affine in the region's parameters), [(t, None)] is void;
    [endk] takes the empty tail. *)
Inductive unode :=
| ULeaf (l : nat)
| UVoid (lsd : bool)
| UUnf (lsd : bool) (endk : option nat) (kids : list (nat * option (aexp * nat))).

Record lfam := mkLF {
  lf_q     : St;
  lf_h     : Sym;
  lf_L     : list seg;        (** the window, nearest-first *)
  lf_R     : list seg;
  lf_n     : nat;
  lf_tree  : list tnode;      (** TriGlue's dispatch tree; [TLeaf u]: unfold node [u] *)
  lf_utree : list unode;
  lf_tL    : option (nat * aexp);   (** tail: state, ref *)
  lf_tR    : option (nat * aexp)
}.

Record lleaf := mkLL {
  ll_f     : nat;
  ll_reg   : list (nat * nat);
  ll_g     : nat;
  ll_tgt   : list aexp;
  ll_c0    : sconf;
  ll_j     : nat;
  ll_el    : bool;
  ll_er    : bool;
  ll_nL    : nat;
  ll_nR    : nat;
  ll_chain : list lstep;
  ll_fL    : list (nat * aexp);     (** folded items, nearest first *)
  ll_fR    : list (nat * aexp);
  ll_uL    : list (nat * aexp);     (** the unfold path's items (checked) *)
  ll_uR    : list (nat * aexp)
}.

Fixpoint teqb' (t1 t2 : list (nat * nat)) : bool :=
  match t1, t2 with
  | [], [] => true
  | (k1, a1) :: r1, (k2, a2) :: r2 => (k1 =? k2) && (a1 =? a2) && teqb' r1 r2
  | _, _ => false
  end.

Definition aeqb' (e1 e2 : aexp) : bool := (a_c e1 =? a_c e2) && teqb' (a_t e1) (a_t e2).

Fixpoint ieqb (I1 I2 : list (nat * aexp)) : bool :=
  match I1, I2 with
  | [], [] => true
  | (t1, e1) :: r1, (t2, e2) :: r2 => (t1 =? t2) && aeqb' e1 e2 && ieqb r1 r2
  | _, _ => false
  end.

Lemma teqb'_eq : forall t1 t2, teqb' t1 t2 = true -> t1 = t2.
Proof.
  induction t1 as [|[k1 a1] r1 IH]; intros [|[k2 a2] r2] H; cbn in H; try discriminate;
    [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1, H2. subst. rewrite (IH _ H3). reflexivity.
Qed.

Lemma ieqb_eq : forall I1 I2, ieqb I1 I2 = true -> I1 = I2.
Proof.
  induction I1 as [|[t1 [c1 e1]] r1 IH]; intros [|[t2 [c2 e2]] r2] H; cbn in H; try discriminate;
    [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  unfold aeqb' in H2; cbn in H2. apply andb_prop in H2 as [H2 H4].
  apply Nat.eqb_eq in H1, H2. apply teqb'_eq in H4. subst. rewrite (IH _ H3). reflexivity.
Qed.

(** the state of one side along an unfold path: the tail from state [s]
    with ref [r] (affine in the region's parameters), or [None]: known
    empty *)
Definition pst := option (nat * aexp).

Definition isNone {A} (o : option A) : bool := match o with None => true | Some _ => false end.

Definition sp_subst (s : list aexp) (sp : option (nat * aexp)) : pst :=
  match sp with None => None | Some (st, r) => Some (st, asubst s r) end.

Section Check.

Variable tmw : TM.
Variable kinds : list (list Sym * list Sym).
Variable trans : list ltrans.
Variable acc : list (bool * nat).
Variable mins : list (bool * nat * nat).
Variable fams : list lfam.
Variable leaves : list lleaf.

Definition isegs (I : list (nat * aexp)) : list seg :=
  flat_map (fun te => item_segs kinds (tr_kind trans (fst te)) (snd te)) I.

Definition conc (z : list nat) (I : list (nat * aexp)) : list (nat * nat) :=
  map (fun te => (fst te, aeval z (snd te))) I.

Lemma trend_app : forall T1 T2, trend kinds trans (T1 ++ T2) = trend kinds trans T1 ++ trend kinds trans T2.
Proof.
  induction T1 as [|[t e] T1 IH]; intros T2; cbn; [reflexivity|].
  rewrite IH, app_assoc. reflexivity.
Qed.

Lemma isegs_ok : forall z I, sided z (isegs I) = trend kinds trans (conc z I).
Proof.
  intros z I. induction I as [|[t e] I IH]; cbn; [reflexivity|].
  unfold isegs in *. cbn [flat_map]. rewrite sided_app, IH, item_segs_ok. reflexivity.
Qed.

(** the relation has no solution anywhere in the region *)
Definition tvoid (tr : ltrans) (r : aexp) : bool :=
  if lt_up tr then anocoef r && (lt_a tr * a_c r + lt_dp tr <? lt_dn tr)
  else if lt_a tr =? 0 then anocoef r && negb (a_c r + lt_dn tr =? lt_dp tr)
  else (pdiv (lt_a tr) r && negb ((a_c r + lt_dn tr) mod lt_a tr =? lt_dp tr mod lt_a tr))
       || (anocoef r && (a_c r + lt_dn tr <? lt_dp tr)).

Lemma tvoid_ok : forall tr r, tvoid tr r = true -> forall z e, ~ relsem tr (aeval z r) e.
Proof.
  intros tr r H z e Hr. unfold tvoid, relsem in *.
  destruct (lt_up tr).
  - apply andb_prop in H as [H1 H2]. rewrite (anocoef_const z r H1) in Hr.
    apply Nat.ltb_lt in H2. lia.
  - destruct (lt_a tr =? 0) eqn:Ea.
    + apply andb_prop in H as [H1 H2]. rewrite (anocoef_const z r H1) in Hr.
      apply negb_true_iff, Nat.eqb_neq in H2. lia.
    + apply Nat.eqb_neq in Ea. apply orb_prop in H as [H | H].
      * apply andb_prop in H as [H1 H2]. apply negb_true_iff, Nat.eqb_neq in H2.
        apply H2. pose proof (pdiv_mod (lt_a tr) z r H1) as Hm.
        rewrite Nat.Div0.add_mod, <- Hm, <- Nat.Div0.add_mod, Hr.
        rewrite Nat.Div0.add_mod, Nat.mul_comm, Nat.Div0.mod_mul, Nat.add_0_l,
          Nat.Div0.mod_mod. reflexivity.
      * apply andb_prop in H as [H1 H2]. rewrite (anocoef_const z r H1) in Hr.
        apply Nat.ltb_lt in H2. lia.
Qed.

(** every transition out of [s] on this side has a kid *)
Definition cover (lsd : bool) (s : nat) (kids : list (nat * option (aexp * nat))) : bool :=
  forallb (fun it => negb (Bool.eqb (lt_left (snd it)) lsd && (lt_src (snd it) =? s))
                     || existsb (fun tk => fst tk =? fst it) kids)
          (combine (seq 0 (length trans)) trans).

Definition pside (lsd : bool) (pL pR : pst) : pst := if lsd then pL else pR.

Fixpoint uleaves (ut : list unode) (fuel u : nat) (pL pR : pst) (iL iR : list (nat * aexp))
  : option (list (nat * pst * pst * list (nat * aexp) * list (nat * aexp))) :=
  match fuel with
  | 0 => None
  | S fu =>
      match nth_error ut u with
      | Some (ULeaf l) => Some [(l, pL, pR, iL, iR)]
      | Some (UVoid lsd) =>
          match pside lsd pL pR with
          | Some (s, r) => if anocoef r && (a_c r <? mget mins lsd s) then Some [] else None
          | None => None
          end
      | Some (UUnf lsd endk kids) =>
          match pside lsd pL pR with
          | None => None
          | Some (s, r) =>
              if negb (cover lsd s kids) then None else
              let ek := if accb acc lsd s then
                          match endk with
                          | Some u' => if lsd then uleaves ut fu u' None pR iL iR
                                       else uleaves ut fu u' pL None iL iR
                          | None => None
                          end
                        else Some [] in
              ocat (ek :: map (fun tk =>
                match nth_error trans (fst tk) with
                | Some tr =>
                    if Bool.eqb (lt_left tr) lsd && (lt_src tr =? s) then
                      match snd tk with
                      | None => if tvoid tr r then Some [] else None
                      | Some (e, u') =>
                          if relchk tr r e then
                            if lsd then uleaves ut fu u' (Some (lt_dst tr, e)) pR (iL ++ [(fst tk, e)]) iR
                            else uleaves ut fu u' pL (Some (lt_dst tr, e)) iL (iR ++ [(fst tk, e)])
                          else None
                      end
                    else None
                | None => None
                end) kids)
          end
      | None => None
      end
  end.

(** the concrete walk: the anchor's tails pick the kids *)
Fixpoint uwalk (ut : list unode) (fuel u : nat) (TL TR : list (nat * nat))
  : option (nat * list (nat * nat) * list (nat * nat)) :=
  match fuel with
  | 0 => None
  | S fu =>
      match nth_error ut u with
      | Some (ULeaf l) => Some (l, TL, TR)
      | Some (UVoid _) => None
      | Some (UUnf lsd endk kids) =>
          match (if lsd then TL else TR) with
          | [] => match endk with Some u' => uwalk ut fu u' TL TR | None => None end
          | (t, _) :: T' =>
              match find (fun tk => fst tk =? t) kids with
              | Some (_, Some (_, u')) =>
                  if lsd then uwalk ut fu u' T' TR else uwalk ut fu u' TL T'
              | _ => None
              end
          end
      | None => None
      end
  end.

Definition sidec (lsd : bool) (z : list nat) (p : pst) (T : list (nat * nat)) : Prop :=
  match p with
  | None => T = []
  | Some (s, r) => tvalid trans acc lsd s (aeval z r) T
  end.

Hypothesis Hmins : mins_ok trans acc mins = true.

Lemma cover_ok : forall lsd s kids t tr, cover lsd s kids = true ->
  nth_error trans t = Some tr -> lt_left tr = lsd -> lt_src tr = s ->
  exists tk, find (fun tk => fst tk =? t) kids = Some tk.
Proof.
  intros lsd s kids t tr Hc Ht Hl Hs. unfold cover in Hc. rewrite forallb_forall in Hc.
  assert (Hin : In (t, tr) (combine (seq 0 (length trans)) trans)).
  { assert (H : forall s0 l i, nth_error l i = Some tr -> In (s0 + i, tr) (combine (seq s0 (length l)) l)).
    { clear. intros s0 l. revert s0. induction l as [|x l IH]; intros s0 [|i] H; cbn in H |- *;
        try discriminate.
      - injection H as ->. left. f_equal. lia.
      - right. rewrite <- Nat.add_succ_comm. apply IH. exact H. }
    exact (H 0 trans t Ht). }
  specialize (Hc _ Hin). cbn [fst snd] in Hc. rewrite Hl, Hs, Bool.eqb_reflx, Nat.eqb_refl in Hc.
  cbn in Hc. apply existsb_exists in Hc as (tk & Hk & He).
  destruct (find (fun tk => fst tk =? t) kids) as [tk'|] eqn:E; [exists tk'; reflexivity|].
  exfalso. pose proof (find_none _ _ E tk Hk) as Hn. cbn in Hn. rewrite He in Hn. discriminate.
Qed.

Lemma uwalk_ok : forall ut fuel u pL pR iL iR Ls z TL TR,
  uleaves ut fuel u pL pR iL iR = Some Ls ->
  sidec true z pL TL -> sidec false z pR TR ->
  exists l pL' pR' iL' iR' TL' TR',
    uwalk ut fuel u TL TR = Some (l, TL', TR')
    /\ In (l, pL', pR', iL', iR') Ls
    /\ sidec true z pL' TL' /\ sidec false z pR' TR'
    /\ conc z iL ++ TL = conc z iL' ++ TL' /\ conc z iR ++ TR = conc z iR' ++ TR'.
Proof.
  intros ut fuel. induction fuel as [|fu IH]; intros u pL pR iL iR Ls z TL TR H HL HR;
    cbn [uleaves] in H; [discriminate|].
  cbn [uwalk].
  destruct (nth_error ut u) as [[l|lsd|lsd endk kids]|]; [| | |discriminate].
  - injection H as <-. exists l, pL, pR, iL, iR, TL, TR.
    repeat split; auto. left. reflexivity.
  - exfalso. destruct (pside lsd pL pR) as [[s r]|] eqn:Ep; [|discriminate].
    destruct (anocoef r && (a_c r <? mget mins lsd s)) eqn:E; [|discriminate].
    apply andb_prop in E as [E1 E2]. apply Nat.ltb_lt in E2.
    assert (Hv : tvalid trans acc lsd s (aeval z r) (if lsd then TL else TR)).
    { destruct lsd; cbn in Ep; rewrite Ep in *; assumption. }
    pose proof (mins_sound trans acc mins Hmins _ _ _ _ Hv) as Hm.
    rewrite (anocoef_const z r E1) in Hm. lia.
  - destruct (pside lsd pL pR) as [[s r]|] eqn:Ep; [|discriminate].
    destruct (negb (cover lsd s kids)) eqn:Ec; [discriminate|].
    apply negb_false_iff in Ec.
    assert (Hv : tvalid trans acc lsd s (aeval z r) (if lsd then TL else TR)).
    { destruct lsd; cbn in Ep; rewrite Ep in *; assumption. }
    remember (if lsd then TL else TR) as T eqn:ET.
    destruct T as [|[t e] T'].
    + (* the empty tail *)
      cbn in Hv.
      rewrite Hv in H.
      destruct endk as [u'|]; [|cbn in H; discriminate].
      destruct lsd.
      * destruct (uleaves ut fu u' None pR iL iR) as [L1|] eqn:E1; [|cbn in H; discriminate].
        destruct (IH _ _ _ _ _ _ z TL TR E1 ltac:(cbn; exact (eq_sym ET)) HR)
          as (l & pL' & pR' & iL' & iR' & TL' & TR' & Hw & Hi & H1 & H2 & H3 & H4).
        exists l, pL', pR', iL', iR', TL', TR'. repeat split; auto.
        apply (ocat_in _ _ _ L1 H); [left; reflexivity | exact Hi].
      * destruct (uleaves ut fu u' pL None iL iR) as [L1|] eqn:E1; [|cbn in H; discriminate].
        destruct (IH _ _ _ _ _ _ z TL TR E1 HL ltac:(cbn; exact (eq_sym ET)))
          as (l & pL' & pR' & iL' & iR' & TL' & TR' & Hw & Hi & H1 & H2 & H3 & H4).
        exists l, pL', pR', iL', iR', TL', TR'. repeat split; auto.
        apply (ocat_in _ _ _ L1 H); [left; reflexivity | exact Hi].
    + destruct Hv as (tr & Htr & Hl & Hs & Hr & Hv').
      destruct (cover_ok lsd s kids t tr Ec Htr Hl Hs) as (tk & Hf).
      rewrite Hf.
      pose proof (find_some _ _ Hf) as [Hk Hkt]. apply Nat.eqb_eq in Hkt.
      destruct tk as [t0 ok]. cbn [fst] in Hkt. subst t0.
      assert (Hm := in_map (fun tk =>
                match nth_error trans (fst tk) with
                | Some tr =>
                    if Bool.eqb (lt_left tr) lsd && (lt_src tr =? s) then
                      match snd tk with
                      | None => if tvoid tr r then Some [] else None
                      | Some (e, u') =>
                          if relchk tr r e then
                            if lsd then uleaves ut fu u' (Some (lt_dst tr, e)) pR (iL ++ [(fst tk, e)]) iR
                            else uleaves ut fu u' pL (Some (lt_dst tr, e)) iL (iR ++ [(fst tk, e)])
                          else None
                      end
                    else None
                | None => None
                end) _ _ Hk).
      cbn [fst snd] in Hm. rewrite Htr, Hl, Hs, Bool.eqb_reflx, Nat.eqb_refl in Hm. cbn [andb] in Hm.
      destruct ok as [[e' u']|].
      2: { exfalso. destruct (tvoid tr r) eqn:Evd.
           - exact (tvoid_ok tr r Evd z e Hr).
           - destruct (ocat_some _ _ _ H (or_intror Hm)) as (ys & Hys). discriminate. }
      destruct (relchk tr r e') eqn:Erc.
      2: { exfalso. destruct (ocat_some _ _ _ H (or_intror Hm)) as (ys & Hys). discriminate. }
      pose proof (relchk_sound tr r e' z Erc) as Hr'.
      pose proof (relsem_det tr _ _ _ Hr Hr') as He. subst e.
      destruct lsd.
      * destruct (uleaves ut fu u' (Some (lt_dst tr, e')) pR (iL ++ [(t, e')]) iR) as [L1|] eqn:E1.
        2: { exfalso. destruct (ocat_some _ _ _ H (or_intror Hm)) as (ys & Hys). discriminate. }
        destruct (IH _ _ _ _ _ _ z T' TR E1 ltac:(cbn; exact Hv') HR)
          as (l & pL' & pR' & iL' & iR' & TL' & TR' & Hw & Hi & H1 & H2 & H3 & H4).
        exists l, pL', pR', iL', iR', TL', TR'. repeat split; auto.
        -- apply (ocat_in _ _ _ L1 H); [right; exact Hm | exact Hi].
        -- cbn in ET. rewrite <- H3, <- ET. unfold conc. rewrite map_app, <- app_assoc. reflexivity.
      * destruct (uleaves ut fu u' pL (Some (lt_dst tr, e')) iL (iR ++ [(t, e')])) as [L1|] eqn:E1.
        2: { exfalso. destruct (ocat_some _ _ _ H (or_intror Hm)) as (ys & Hys). discriminate. }
        destruct (IH _ _ _ _ _ _ z TL T' E1 HL ltac:(cbn; exact Hv'))
          as (l & pL' & pR' & iL' & iR' & TL' & TR' & Hw & Hi & H1 & H2 & H3 & H4).
        exists l, pL', pR', iL', iR', TL', TR'. repeat split; auto.
        -- apply (ocat_in _ _ _ L1 H); [right; exact Hm | exact Hi].
        -- cbn in ET. rewrite <- H4, <- ET. unfold conc. rewrite map_app, <- app_assoc. reflexivity.
Qed.


(** ** Folds: the target's tail *)

Fixpoint fchain (lsd : bool) (s : nat) (r : aexp) (F : list (nat * aexp)) : option (nat * aexp) :=
  match F with
  | [] => Some (s, r)
  | (t, e) :: F' =>
      match nth_error trans t with
      | Some tr =>
          if Bool.eqb (lt_left tr) lsd && (lt_src tr =? s) && relchk tr r e
          then fchain lsd (lt_dst tr) e F' else None
      | None => None
      end
  end.

(** the target's tail spec [sg] (substituted), the folded items [F], and
    the rest of the tail as the unfold path left it ([p]) *)
Definition tail_end_ok (lsd : bool) (sg : pst) (F : list (nat * aexp)) (p : pst) : bool :=
  match sg with
  | None => match F with [] => isNone p | _ => false end
  | Some (s0, r0) =>
      match fchain lsd s0 r0 F with
      | Some (s1, r1) =>
          match p with
          | None => accb acc lsd s1
          | Some (s', r') => (s1 =? s') && aeq r1 r'
          end
      | None => false
      end
  end.

Definition tail_bvalid (lsd : bool) (sp : option (nat * aexp)) (vals : list nat)
  (T : list (nat * nat)) : bool :=
  match sp with
  | None => match T with [] => true | _ => false end
  | Some (s, r) => tvalidb trans acc lsd s (aeval vals r) T
  end.

Definition tailok (lsd : bool) (sp : option (nat * aexp)) (vals : list nat) (T : list (nat * nat))
  : Prop :=
  match sp with
  | None => T = []
  | Some (s, r) => tvalid trans acc lsd s (aeval vals r) T
  end.

Lemma tail_bvalid_ok : forall lsd sp vals T, tail_bvalid lsd sp vals T = true ->
  tailok lsd sp vals T.
Proof.
  intros lsd [[s r]|] vals T H; cbn in H |- *.
  - apply tvalidb_ok. exact H.
  - destruct T; [reflexivity | discriminate].
Qed.

Lemma fchain_ok : forall lsd z F s r s1 r1 T, fchain lsd s r F = Some (s1, r1) ->
  tvalid trans acc lsd s1 (aeval z r1) T -> tvalid trans acc lsd s (aeval z r) (conc z F ++ T).
Proof.
  intros lsd z F. induction F as [|[t e] F IH]; intros s r s1 r1 T H HT; cbn in H.
  - injection H as <- <-. exact HT.
  - destruct (nth_error trans t) as [tr|] eqn:Et; [|discriminate].
    destruct (Bool.eqb (lt_left tr) lsd && (lt_src tr =? s) && relchk tr r e) eqn:E;
      [|discriminate].
    apply andb_prop in E as [E Er]. apply andb_prop in E as [El Es].
    apply Bool.eqb_prop in El. apply Nat.eqb_eq in Es.
    cbn [conc map app tvalid fst snd]. exists tr. repeat split; auto.
    + exact (relchk_sound tr r e z Er).
    + exact (IH _ _ _ _ _ H HT).
Qed.

Lemma tail_end_sound : forall lsd sp tgt F p z T,
  tail_end_ok lsd (sp_subst tgt sp) F p = true -> sidec lsd z p T ->
  tailok lsd sp (map (aeval z) tgt) (conc z F ++ T).
Proof.
  intros lsd sp tgt F p z T H HT. unfold tail_end_ok, sp_subst in H. unfold tailok.
  destruct sp as [[sg rg]|].
  - destruct (fchain lsd sg (asubst tgt rg) F) as [[s1 r1]|] eqn:Ef; [|discriminate].
    rewrite <- aeval_asubst. apply (fchain_ok lsd z F _ _ s1 r1 T Ef).
    destruct p as [[s' r']|]; cbn in HT.
    + apply andb_prop in H as [H1 H2]. apply Nat.eqb_eq in H1. subst s'.
      rewrite (aeq_sound z _ _ H2). exact HT.
    + subst T. cbn. exact H.
  - destruct F; [|discriminate]. destruct p; [discriminate|]. cbn in HT. subst T. reflexivity.
Qed.

(** ** Leaves *)

Definition side_ok (p : pst) (post rhs : list seg) : bool :=
  if isNone p then lsame_segs post rhs else same_segs post rhs.

Definition leaf_ok (F : lfam) (lf : lleaf) (pL pR : pst) (iL iR : list (nat * aexp)) : bool :=
  let sub := rsub (ll_reg lf) in
  let Lz := map (seg_subst sub) (lf_L F) ++ isegs iL in
  let Rz := map (seg_subst sub) (lf_R F) ++ isegs iR in
  let c0 := ll_c0 lf in
  match nth_error fams (ll_g lf), srun tmw (ll_el lf) (ll_er lf) (ll_chain lf) c0 with
  | Some G, Some (c1, _, cb) =>
      st_eqb (c_st c0) (lf_q F) && sym_eqb (c_h c0) (lf_h F)
      && same_segs (ss_segs (c_l c0) (ll_j lf) ++ skipn (ll_nL lf) Lz) Lz
      && same_segs (ss_segs (c_r c0) (ll_j lf) ++ skipn (ll_nR lf) Rz) Rz
      && (negb (ll_el lf) || ((length Lz <=? ll_nL lf) && isNone pL))
      && (negb (ll_er lf) || ((length Rz <=? ll_nR lf) && isNone pR))
      && st_eqb (c_st c1) (lf_q G) && sym_eqb (c_h c1) (lf_h G)
      && side_ok pL (ss_segs (c_l c1) (ll_j lf) ++ skipn (ll_nL lf) Lz)
                    (map (seg_subst (ll_tgt lf)) (lf_L G) ++ isegs (ll_fL lf))
      && side_ok pR (ss_segs (c_r c1) (ll_j lf) ++ skipn (ll_nR lf) Rz)
                    (map (seg_subst (ll_tgt lf)) (lf_R G) ++ isegs (ll_fR lf))
      && tail_end_ok true (sp_subst (ll_tgt lf) (lf_tL G)) (ll_fL lf) pL
      && tail_end_ok false (sp_subst (ll_tgt lf) (lf_tR G)) (ll_fR lf) pR
      && (0 <? cb) && (length (ll_tgt lf) =? lf_n G) && (length (ll_reg lf) =? lf_n F)
  | _, _ => false
  end.

Ltac andb_split :=
  repeat match goal with
         | H : (_ && _) = true |- _ => apply andb_prop in H as [? ?]
         end.

Lemma side_ok_lift : forall lsd p post rhs z T X, side_ok p post rhs = true ->
  sidec lsd z p T -> X = trend kinds trans T ->
  lift_side (sided z post ++ X) = lift_side (sided z rhs ++ X).
Proof.
  intros lsd p post rhs z T X H HT ->. unfold side_ok in H.
  destruct p as [[s r]|]; cbn in H.
  - rewrite (same_segs_ok z _ _ H). reflexivity.
  - cbn in HT. subst T. cbn. rewrite !app_nil_r. exact (lsame_segs_ok z _ _ H).
Qed.

(** ** Anchors *)

Record lanc := mkAn {
  an_f : nat;
  an_v : list nat;
  an_L : list (nat * nat);
  an_R : list (nat * nat)
}.

Definition tanc (a : lanc) : cconf :=
  match nth_error fams (an_f a) with
  | Some F => (lf_q F, (sided (an_v a) (lf_L F) ++ trend kinds trans (an_L a), lf_h F,
                        sided (an_v a) (lf_R F) ++ trend kinds trans (an_R a)))
  | None => c0
  end.

Definition Good (a : lanc) : Prop :=
  exists F, nth_error fams (an_f a) = Some F /\ length (an_v a) = lf_n F
            /\ tailok true (lf_tL F) (an_v a) (an_L a) /\ tailok false (lf_tR F) (an_v a) (an_R a).

Definition fleaves' (F : lfam) := tleaves (lf_tree F) (length (lf_tree F)) 0 (R0 (lf_n F)).

Definition fam_ok (fi : nat) (F : lfam) : bool :=
  match fleaves' F with
  | Some L =>
      forallb (fun uR =>
        match uleaves (lf_utree F) (length (lf_utree F)) (fst uR)
                (sp_subst (rsub (snd uR)) (lf_tL F)) (sp_subst (rsub (snd uR)) (lf_tR F)) [] [] with
        | Some Ls =>
            forallb (fun e =>
              match e with
              | (l, pL, pR, iL, iR) =>
                  match nth_error leaves l with
                  | Some lf => (ll_f lf =? fi) && regeqb (ll_reg lf) (snd uR)
                               && ieqb (ll_uL lf) iL && ieqb (ll_uR lf) iR
                               && leaf_ok F lf pL pR iL iR
                  | None => false
                  end
              end) Ls
        | None => false
        end) L
  | None => false
  end.

Definition fams_ok : bool :=
  forallb (fun fF => fam_ok (fst fF) (snd fF)) (combine (seq 0 (length fams)) fams).

Definition lwalk (a : lanc) : option (nat * list (nat * nat) * list nat * list (nat * nat) * list (nat * nat)) :=
  match nth_error fams (an_f a) with
  | Some F =>
      match twalk (lf_tree F) (length (lf_tree F)) 0 (R0 (lf_n F)) (an_v a) with
      | Some (u, R, z) =>
          match uwalk (lf_utree F) (length (lf_utree F)) u (an_L a) (an_R a) with
          | Some (l, TL, TR) => Some (l, R, z, TL, TR)
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Definition lnxt (a : lanc) : lanc :=
  match lwalk a with
  | Some (l, R, z, TL, TR) =>
      match nth_error leaves l with
      | Some lf => mkAn (ll_g lf) (map (aeval z) (ll_tgt lf))
                        (conc z (ll_fL lf) ++ TL) (conc z (ll_fR lf) ++ TR)
      | None => a
      end
  | None => a
  end.

Hypothesis Hfams : fams_ok = true.

Lemma lfam_ok_of : forall fi F, nth_error fams fi = Some F -> fam_ok fi F = true.
Proof.
  intros fi F H. unfold fams_ok in Hfams. rewrite forallb_forall in Hfams.
  apply (Hfams (fi, F)).
  assert (Hc : forall s0 l i, nth_error l i = Some F ->
            In (s0 + i, F) (combine (seq s0 (length l)) l)).
  { clear. intros s0 l. revert s0. induction l as [|x l IH]; intros s0 [|i] H; cbn in H |- *;
      try discriminate.
    - injection H as ->. left. f_equal. lia.
    - right. rewrite <- Nat.add_succ_comm. apply IH. exact H. }
  exact (Hc 0 fams fi H).
Qed.

Lemma rv_R0' : forall n vals k, length vals = n -> rv (R0 n) vals k = nth k vals 0.
Proof.
  intros n vals k Hl. unfold rv, R0.
  destruct (lt_dec k n) as [Hk | Hk].
  - rewrite nth_repeat_lt' by exact Hk. cbn. lia.
  - rewrite nth_overflow by (rewrite repeat_length; lia).
    rewrite nth_overflow by lia. reflexivity.
Qed.

Lemma twalk_len : forall nodes fuel i R z l R' z', twalk nodes fuel i R z = Some (l, R', z') ->
  length R' = length R.
Proof.
  intros nodes fuel. induction fuel as [|fu IH]; intros i R z l R' z' H; cbn [twalk] in H;
    [discriminate|].
  destruct (nth_error nodes i) as [[l0|k n p kids]|]; [| |discriminate].
  - inversion H. reflexivity.
  - destruct (nth k z 0 <? n).
    + destruct (nth_error kids (nth k z 0)) as [i'|]; [|discriminate].
      rewrite (IH _ _ _ _ _ _ H). apply replace_length.
    + destruct (nth_error kids (n + (nth k z 0 - n) mod p)) as [i'|]; [|discriminate].
      rewrite (IH _ _ _ _ _ _ H). apply replace_length.
Qed.

Lemma lwalk_leaf : forall a, Good a -> exists F lf l R z TL TR pL pR iL iR,
  nth_error fams (an_f a) = Some F /\ lwalk a = Some (l, R, z, TL, TR)
  /\ nth_error leaves l = Some lf /\ ll_f lf = an_f a /\ ll_reg lf = R
  /\ ll_uL lf = iL /\ ll_uR lf = iR
  /\ leaf_ok F lf pL pR iL iR = true /\ an_v a = map (aeval z) (rsub R)
  /\ length z = length R
  /\ sidec true z pL TL /\ sidec false z pR TR
  /\ an_L a = conc z iL ++ TL /\ an_R a = conc z iR ++ TR.
Proof.
  intros [fi vals TL0 TR0] (F & HF & Hl & HtL & HtR). cbn [an_f an_v an_L an_R] in *.
  pose proof (lfam_ok_of fi F HF) as Hok. unfold fam_ok in Hok.
  destruct (fleaves' F) as [L|] eqn:EL; [|discriminate].
  assert (Hzl : length vals = length (R0 (lf_n F))) by (unfold R0; rewrite repeat_length; exact Hl).
  destruct (twalk_total _ _ _ _ _ EL vals Hzl) as (u & R & z & Hw & Hin & Hrv & HzR).
  rewrite forallb_forall in Hok. specialize (Hok _ Hin). cbn [fst snd] in Hok.
  assert (Hv : vals = map (aeval z) (rsub R)).
  { pose proof (twalk_len _ _ _ _ _ _ _ _ Hw) as HRl.
    apply nth_ext with (d := 0) (d' := 0).
    - rewrite map_length, rsub_length. lia.
    - intros k Hk.
      rewrite rsub_nth by lia.
      rewrite <- Hrv. symmetry. apply rv_R0'. exact Hl. }
  destruct (uleaves (lf_utree F) (length (lf_utree F)) u (sp_subst (rsub R) (lf_tL F))
              (sp_subst (rsub R) (lf_tR F)) [] []) as [Ls|] eqn:EU; [|discriminate].
  assert (HsL : sidec true z (sp_subst (rsub R) (lf_tL F)) TL0).
  { unfold sidec, sp_subst, tailok in *. destruct (lf_tL F) as [[s r]|]; [|exact HtL].
    rewrite aeval_asubst, <- Hv. exact HtL. }
  assert (HsR : sidec false z (sp_subst (rsub R) (lf_tR F)) TR0).
  { unfold sidec, sp_subst, tailok in *. destruct (lf_tR F) as [[s r]|]; [|exact HtR].
    rewrite aeval_asubst, <- Hv. exact HtR. }
  destruct (uwalk_ok _ _ _ _ _ _ _ _ _ _ _ EU HsL HsR)
    as (l & pL & pR & iL & iR & TL & TR & HW & HinL & H1 & H2 & H3 & H4).
  rewrite forallb_forall in Hok. specialize (Hok _ HinL). cbn in Hok.
  destruct (nth_error leaves l) as [lf|] eqn:Elf; [|discriminate].
  apply andb_prop in Hok as [Hok Hlo]. apply andb_prop in Hok as [Hok HuR].
  apply andb_prop in Hok as [Hok HuL]. apply andb_prop in Hok as [Hf Hreg].
  apply Nat.eqb_eq in Hf. apply regeqb_eq in Hreg. apply ieqb_eq in HuL, HuR.
  exists F, lf, l, R, z, TL, TR, pL, pR, iL, iR.
  repeat split; auto.
  unfold lwalk. cbn [an_f an_v an_L an_R]. rewrite HF, Hw, HW. reflexivity.
Qed.

(** ** A step: the chain from the anchor to the next one *)

Lemma sided_rsub : forall z R l, sided (map (aeval z) (rsub R)) l = sided z (map (seg_subst (rsub R)) l).
Proof. intros. rewrite sided_subst. reflexivity. Qed.

Lemma lstep_ok : forall a, Good a ->
  (exists n c', csteps tmw n (tanc a) = Some c' /\ lift c' = lift (tanc (lnxt a)) /\ 0 < n)
  /\ Good (lnxt a).
Proof.
  intros a Ha.
  destruct (lwalk_leaf a Ha) as (F & lf & l & R & z & TL & TR & pL & pR & iL & iR & HF & Hw
    & Hlf & Hf & HR & HuL & HuR & Hok & Hv & HzR & HsL & HsR & HaL & HaR).
  unfold leaf_ok in Hok.
  destruct (nth_error fams (ll_g lf)) as [G|] eqn:HG; [|discriminate].
  destruct (srun tmw (ll_el lf) (ll_er lf) (ll_chain lf) (ll_c0 lf)) as [[[c1 ca] cb]|] eqn:Er;
    [|discriminate].
  apply andb_prop in Hok as [Hok Hlr]. apply andb_prop in Hok as [Hok Hlt].
  apply andb_prop in Hok as [Hok Hcb]. apply andb_prop in Hok as [Hok HtR].
  apply andb_prop in Hok as [Hok HtL]. apply andb_prop in Hok as [Hok HdR].
  apply andb_prop in Hok as [Hok HdL]. apply andb_prop in Hok as [Hok Hh1].
  apply andb_prop in Hok as [Hok Hq1]. apply andb_prop in Hok as [Hok Her].
  apply andb_prop in Hok as [Hok Hel]. apply andb_prop in Hok as [Hok Hs0R].
  apply andb_prop in Hok as [Hok Hs0L]. apply andb_prop in Hok as [Hq0 Hh0].
  set (Lz := map (seg_subst (rsub (ll_reg lf))) (lf_L F) ++ isegs iL) in *.
  set (Rz := map (seg_subst (rsub (ll_reg lf))) (lf_R F) ++ isegs iR) in *.
  assert (Hnx : lnxt a = mkAn (ll_g lf) (map (aeval z) (ll_tgt lf))
                             (conc z (ll_fL lf) ++ TL) (conc z (ll_fR lf) ++ TR)).
  { unfold lnxt. rewrite Hw, Hlf. reflexivity. }
  rewrite Hnx.
  split.
  2: { exists G. cbn [an_f an_v an_L an_R]. split; [exact HG|].
       split; [rewrite map_length; apply Nat.eqb_eq; exact Hlt|].
       split.
       - exact (tail_end_sound true (lf_tL G) (ll_tgt lf) (ll_fL lf) pL z TL HtL HsL).
       - exact (tail_end_sound false (lf_tR G) (ll_tgt lf) (ll_fR lf) pR z TR HtR HsR). }
  (* the anchor as the chain's start *)
  set (XL := sided z (skipn (ll_nL lf) Lz) ++ trend kinds trans TL).
  set (XR := sided z (skipn (ll_nR lf) Rz) ++ trend kinds trans TR).
  assert (HL0 : sided (an_v a) (lf_L F) ++ trend kinds trans (an_L a) = sided z Lz ++ trend kinds trans TL).
  { rewrite Hv, HaL, trend_app, <- isegs_ok, sided_rsub, <- HR, app_assoc.
    unfold Lz. rewrite sided_app. reflexivity. }
  assert (HR0 : sided (an_v a) (lf_R F) ++ trend kinds trans (an_R a) = sided z Rz ++ trend kinds trans TR).
  { rewrite Hv, HaR, trend_app, <- isegs_ok, sided_rsub, <- HR, app_assoc.
    unfold Rz. rewrite sided_app. reflexivity. }
  assert (Hst : tanc a = cden XL XR (nth (ll_j lf) z 0) (ll_c0 lf)).
  { unfold tanc. rewrite HF, HL0, HR0. unfold cden.
    apply st_eqb_spec in Hq0. apply sym_eqb_spec in Hh0. rewrite <- Hq0, <- Hh0.
    rewrite !ss_segs_ok. unfold XL, XR. rewrite !app_assoc, <- !sided_app.
    rewrite (same_segs_ok z _ _ Hs0L), (same_segs_ok z _ _ Hs0R).
    destruct (ll_c0 lf). reflexivity. }
  assert (HXL : ll_el lf = true -> XL = []).
  { intros He. rewrite He in Hel. cbn in Hel. apply andb_prop in Hel as [H19a H19b].
    apply Nat.leb_le in H19a. destruct pL; [discriminate|]. cbn in HsL. subst TL.
    unfold XL. rewrite skipn_all_le by exact H19a. reflexivity. }
  assert (HXR : ll_er lf = true -> XR = []).
  { intros He. rewrite He in Her. cbn in Her. apply andb_prop in Her as [H18a H18b].
    apply Nat.leb_le in H18a. destruct pR; [discriminate|]. cbn in HsR. subst TR.
    unfold XR. rewrite skipn_all_le by exact H18a. reflexivity. }
  exists (ca * nth (ll_j lf) z 0 + cb), (cden XL XR (nth (ll_j lf) z 0) c1).
  split; [| split; [| apply Nat.ltb_lt in Hcb; lia]].
  - rewrite Hst. exact (srun_sound _ _ _ _ _ _ _ _ Er _ _ _ HXL HXR).
  - unfold tanc. cbn [an_f an_v an_L an_R]. rewrite HG.
    apply st_eqb_spec in Hq1. apply sym_eqb_spec in Hh1.
    assert (EL : sided (map (aeval z) (ll_tgt lf)) (lf_L G) ++ trend kinds trans (conc z (ll_fL lf) ++ TL)
                 = sided z (map (seg_subst (ll_tgt lf)) (lf_L G) ++ isegs (ll_fL lf))
                   ++ trend kinds trans TL).
    { rewrite trend_app, <- isegs_ok, sided_app, <- sided_subst, app_assoc. reflexivity. }
    assert (ER : sided (map (aeval z) (ll_tgt lf)) (lf_R G) ++ trend kinds trans (conc z (ll_fR lf) ++ TR)
                 = sided z (map (seg_subst (ll_tgt lf)) (lf_R G) ++ isegs (ll_fR lf))
                   ++ trend kinds trans TR).
    { rewrite trend_app, <- isegs_ok, sided_app, <- sided_subst, app_assoc. reflexivity. }
    assert (EL1 : sden XL (nth (ll_j lf) z 0) (c_l c1)
                  = sided z (ss_segs (c_l c1) (ll_j lf) ++ skipn (ll_nL lf) Lz) ++ trend kinds trans TL).
    { rewrite ss_segs_ok. unfold XL. rewrite sided_app, app_assoc. reflexivity. }
    assert (ER1 : sden XR (nth (ll_j lf) z 0) (c_r c1)
                  = sided z (ss_segs (c_r c1) (ll_j lf) ++ skipn (ll_nR lf) Rz) ++ trend kinds trans TR).
    { rewrite ss_segs_ok. unfold XR. rewrite sided_app, app_assoc. reflexivity. }
    unfold cden, lift, lift_tape; cbn [fst snd]. rewrite <- Hq1, <- Hh1, EL, ER, EL1, ER1.
    rewrite (side_ok_lift true pL _ _ z TL _ HdL HsL eq_refl).
    rewrite (side_ok_lift false pR _ _ z TR _ HdR HsR eq_refl).
    reflexivity.
Qed.

(** ** Fires: every chain prefix of the anchor's leaf *)

Definition lleaf_fired (lf : lleaf) : list Instr :=
  flat_map (fun pr => match srun_instr tmw (ll_el lf) (ll_er lf) pr (ll_c0 lf) with
                      | Some t => [t]
                      | None => []
                      end) (prefs (ll_chain lf)).

Lemma lstart : forall a, Good a -> exists l R z TL TR lf XL XR,
  lwalk a = Some (l, R, z, TL, TR) /\ nth_error leaves l = Some lf
  /\ tanc a = cden XL XR (nth (ll_j lf) z 0) (ll_c0 lf)
  /\ (ll_el lf = true -> XL = []) /\ (ll_er lf = true -> XR = []).
Proof.
  intros a Ha.
  destruct (lwalk_leaf a Ha) as (F & lf & l & R & z & TL & TR & pL & pR & iL & iR & HF & Hw
    & Hlf & Hf & HR & HuL & HuR & Hok & Hv & HzR & HsL & HsR & HaL & HaR).
  unfold leaf_ok in Hok.
  destruct (nth_error fams (ll_g lf)) as [G|] eqn:HG; [|discriminate].
  destruct (srun tmw (ll_el lf) (ll_er lf) (ll_chain lf) (ll_c0 lf)) as [[[c1 ca] cb]|] eqn:Er;
    [|discriminate].
  apply andb_prop in Hok as [Hok Hlr]. apply andb_prop in Hok as [Hok Hlt].
  apply andb_prop in Hok as [Hok Hcb]. apply andb_prop in Hok as [Hok HtR].
  apply andb_prop in Hok as [Hok HtL]. apply andb_prop in Hok as [Hok HdR].
  apply andb_prop in Hok as [Hok HdL]. apply andb_prop in Hok as [Hok Hh1].
  apply andb_prop in Hok as [Hok Hq1]. apply andb_prop in Hok as [Hok Her].
  apply andb_prop in Hok as [Hok Hel]. apply andb_prop in Hok as [Hok Hs0R].
  apply andb_prop in Hok as [Hok Hs0L]. apply andb_prop in Hok as [Hq0 Hh0].
  set (Lz := map (seg_subst (rsub (ll_reg lf))) (lf_L F) ++ isegs iL) in *.
  set (Rz := map (seg_subst (rsub (ll_reg lf))) (lf_R F) ++ isegs iR) in *.
  set (XL := sided z (skipn (ll_nL lf) Lz) ++ trend kinds trans TL).
  set (XR := sided z (skipn (ll_nR lf) Rz) ++ trend kinds trans TR).
  exists l, R, z, TL, TR, lf, XL, XR. split; [exact Hw|]. split; [exact Hlf|].
  split; [| split].
  - assert (HL0 : sided (an_v a) (lf_L F) ++ trend kinds trans (an_L a) = sided z Lz ++ trend kinds trans TL).
    { rewrite Hv, HaL, trend_app, <- isegs_ok, sided_rsub, <- HR, app_assoc.
      unfold Lz. rewrite sided_app. reflexivity. }
    assert (HR0 : sided (an_v a) (lf_R F) ++ trend kinds trans (an_R a) = sided z Rz ++ trend kinds trans TR).
    { rewrite Hv, HaR, trend_app, <- isegs_ok, sided_rsub, <- HR, app_assoc.
      unfold Rz. rewrite sided_app. reflexivity. }
    unfold tanc. rewrite HF, HL0, HR0. unfold cden.
    apply st_eqb_spec in Hq0. apply sym_eqb_spec in Hh0. rewrite <- Hq0, <- Hh0.
    rewrite !ss_segs_ok. unfold XL, XR. rewrite !app_assoc, <- !sided_app.
    rewrite (same_segs_ok z _ _ Hs0L), (same_segs_ok z _ _ Hs0R).
    destruct (ll_c0 lf). reflexivity.
  - intros He. rewrite He in Hel. cbn in Hel. apply andb_prop in Hel as [Hel1 Hel2].
    apply Nat.leb_le in Hel1. destruct pL; [discriminate|]. cbn in HsL. subst TL.
    unfold XL. rewrite skipn_all_le by exact Hel1. reflexivity.
  - intros He. rewrite He in Her. cbn in Her. apply andb_prop in Her as [Her1 Her2].
    apply Nat.leb_le in Her1. destruct pR; [discriminate|]. cbn in HsR. subst TR.
    unfold XR. rewrite skipn_all_le by exact Her1. reflexivity.
Qed.

Lemma lleaf_fires : forall a l R z TL TR lf t, Good a -> lwalk a = Some (l, R, z, TL, TR) ->
  nth_error leaves l = Some lf -> In t (lleaf_fired lf) ->
  exists k c, csteps tmw k (tanc a) = Some c /\ cinstr c = t.
Proof.
  intros a l R z TL TR lf t Ha Hw Hlf Hin.
  destruct (lstart a Ha) as (l' & R' & z' & TL' & TR' & lf' & XL & XR & Hw' & Hlf' & Hst & HL & HR).
  rewrite Hw in Hw'. injection Hw' as <- <- <- <- <-. rewrite Hlf in Hlf'. injection Hlf' as <-.
  unfold lleaf_fired in Hin. apply in_flat_map in Hin as (pr & _ & Hpr).
  destruct (srun_instr tmw (ll_el lf) (ll_er lf) pr (ll_c0 lf)) as [t'|] eqn:E; [|destruct Hpr].
  destruct Hpr as [<- | []].
  exact (fire_of_run_instr tmw (fun _ => tanc a) (ll_el lf) (ll_er lf) pr (ll_c0 lf) xH
           (nth (ll_j lf) z 0) _ _ t' E HL HR Hst).
Qed.

(** ** Liveness: (leaf, residue) nodes and rankings with tail weights *)

(** a ranking entry: the window part, and per side the weights
    [(alpha, beta)] of the items read by each transition (the ones past the
    list: [(0, b)]) *)
Record lrk := mkRk {
  rk_V  : nat * list nat;
  rk_wL : list (nat * nat);
  rk_bL : nat;
  rk_wR : list (nat * nat);
  rk_bR : nat
}.

Definition rk0 : lrk := mkRk (0, []) [] 0 [] 0.

Definition wget (w : list (nat * nat)) (b t : nat) : nat * nat := nth t w (0, b).

Fixpoint twv (w : list (nat * nat)) (b : nat) (T : list (nat * nat)) : nat :=
  match T with
  | [] => 0
  | (t, e) :: T' => fst (wget w b t) * e + snd (wget w b t) + twv w b T'
  end.

Fixpoint twa (w : list (nat * nat)) (b : nat) (I : list (nat * aexp)) : aexp :=
  match I with
  | [] => aconst 0
  | (t, e) :: I' => aadd (aaddc (ascale (fst (wget w b t)) e) (snd (wget w b t))) (twa w b I')
  end.

Lemma twa_ok : forall w b z I, aeval z (twa w b I) = twv w b (conc z I).
Proof.
  intros w b z I. induction I as [|[t e] I IH]; cbn [twa twv conc map fst snd]; [reflexivity|].
  rewrite aeval_aadd, aeval_aaddc, aeval_ascale, IH. reflexivity.
Qed.

Lemma twv_app : forall w b T1 T2, twv w b (T1 ++ T2) = twv w b T1 + twv w b T2.
Proof. intros w b T1 T2. induction T1 as [|[t e] T1 IH]; cbn; [reflexivity|]. rewrite IH. lia. Qed.

Definition wle (w1 : list (nat * nat)) (b1 : nat) (w2 : list (nat * nat)) (b2 : nat) : bool :=
  (b1 <=? b2)
  && forallb (fun k => (fst (wget w1 b1 k) <=? fst (wget w2 b2 k))
                       && (snd (wget w1 b1 k) <=? snd (wget w2 b2 k)))
             (seq 0 (Nat.max (length w1) (length w2))).

Lemma wle_ok : forall w1 b1 w2 b2 T, wle w1 b1 w2 b2 = true -> twv w1 b1 T <= twv w2 b2 T.
Proof.
  intros w1 b1 w2 b2 T H. unfold wle in H. apply andb_prop in H as [Hb H].
  apply Nat.leb_le in Hb. rewrite forallb_forall in H.
  assert (Hk : forall k, fst (wget w1 b1 k) <= fst (wget w2 b2 k)
                         /\ snd (wget w1 b1 k) <= snd (wget w2 b2 k)).
  { intros k. destruct (lt_dec k (Nat.max (length w1) (length w2))) as [Hl|Hl].
    - specialize (H k (proj2 (in_seq _ _ _) (conj (Nat.le_0_l k) Hl))).
      apply andb_prop in H as [H1 H2]. apply Nat.leb_le in H1, H2. lia.
    - unfold wget. rewrite !nth_overflow by lia. cbn. lia. }
  induction T as [|[t e] T IH]; cbn; [lia|].
  destruct (Hk t) as [H1 H2]. pose proof (Nat.mul_le_mono_r _ _ e H1). lia.
Qed.

Variable pins : list Instr.
Variable P : nat.
Variable S : list (nat * list nat).
Variable rk : list (Instr * list lrk).

Definition lrank_of (t : Instr) : list lrk :=
  match find (fun p => instr_eqb (fst p) t) rk with Some p => snd p | None => [] end.

Definition isub (sub : list aexp) (I : list (nat * aexp)) : list (nat * aexp) :=
  map (fun te => (fst te, asubst sub (snd te))) I.

Definition lnode_ok (fired : list (list Instr)) (i : nat) (lr : nat * list nat) : bool :=
  match nth_error leaves (fst lr) with
  | None => false
  | Some lf =>
      let fl := nth (fst lr) fired [] in
      forallb (fun s =>
        let sub := zsub P s in
        let src := map (asubst sub) (rsub (ll_reg lf)) in
        let tgt := map (asubst sub) (ll_tgt lf) in
        let uL := isub sub (ll_uL lf) in
        let uR := isub sub (ll_uR lf) in
        let fL := isub sub (ll_fL lf) in
        let fR := isub sub (ll_fR lf) in
        let rho' := map (fun e => a_c e mod P) tgt in
        forallb (pdiv P) tgt
        && forallb (fun l' =>
             match nth_error leaves l' with
             | None => true
             | Some lf' =>
                 if (ll_f lf' =? ll_g lf) && compat P (ll_reg lf') tgt then
                   match nidx S l' rho' with
                   | None => false
                   | Some i' =>
                       let fl' := nth l' fired [] in
                       forallb (fun t =>
                         tr_inb t pins || tr_inb t fl || tr_inb t fl'
                         || (let r := nth i (lrank_of t) rk0 in
                             let r' := nth i' (lrank_of t) rk0 in
                             ale (aaddc (aadd (veval (rk_V r') tgt)
                                              (aadd (twa (rk_wL r') (rk_bL r') fL)
                                                    (twa (rk_wR r') (rk_bR r') fR))) 1)
                                 (aadd (veval (rk_V r) src)
                                       (aadd (twa (rk_wL r) (rk_bL r) uL)
                                             (twa (rk_wR r) (rk_bR r) uR)))
                             && wle (rk_wL r') (rk_bL r') (rk_wL r) (rk_bL r)
                             && wle (rk_wR r') (rk_bR r') (rk_wR r) (rk_bR r)))
                         all_Instr
                   end
                 else true
             end) (seq 0 (length leaves)))
        (sassign P (ll_reg lf) (snd lr))
  end.

Definition llive_ok : bool :=
  let fired := map lleaf_fired leaves in
  (0 <? P)
  && forallb (fun ilr => lnode_ok fired (fst ilr) (snd ilr)) (combine (seq 0 (length S)) S).

Hypothesis Hlive : llive_ok = true.

Lemma lHP : 0 < P.
Proof. unfold llive_ok in Hlive. apply andb_prop in Hlive as [H _]. apply Nat.ltb_lt, H. Qed.

Lemma lnode : forall i lr, nth_error S i = Some lr -> lnode_ok (map lleaf_fired leaves) i lr = true.
Proof.
  intros i lr H. unfold llive_ok in Hlive. apply andb_prop in Hlive as [_ Hl].
  rewrite forallb_forall in Hl. apply (Hl (i, lr)).
  assert (Hc : forall s0 l i, nth_error l i = Some lr ->
            In (s0 + i, lr) (combine (seq s0 (length l)) l)).
  { clear. intros s0 l. revert s0. induction l as [|x l IH]; intros s0 [|i] H; cbn in H |- *;
      try discriminate.
    - injection H as ->. left. f_equal. lia.
    - right. rewrite <- Nat.add_succ_comm. apply IH. exact H. }
  exact (Hc 0 S i H).
Qed.

Definition lnodeidx (a : lanc) : option nat :=
  match lwalk a with
  | Some (l, _, _, _, _) => nidx S l (modl P (an_v a))
  | None => None
  end.

Definition GoodS (a : lanc) : Prop := Good a /\ lnodeidx a <> None.

Definition lfires_at (a : lanc) (t : Instr) : bool :=
  match lwalk a with
  | Some (l, _, _, _, _) =>
      match nth_error leaves l with Some lf => tr_inb t (lleaf_fired lf) | None => false end
  | None => false
  end.

Definition lrval (t : Instr) (a : lanc) : nat :=
  match lnodeidx a with
  | Some i => let r := nth i (lrank_of t) rk0 in
              vval (rk_V r) (an_v a) + twv (rk_wL r) (rk_bL r) (an_L a)
              + twv (rk_wR r) (rk_bR r) (an_R a)
  | None => 0
  end.

Lemma isub_conc : forall z' sub z I, (forall e, aeval z' (asubst sub e) = aeval z e) ->
  conc z' (isub sub I) = conc z I.
Proof.
  intros z' sub z I H. induction I as [|[t e] I IH]; cbn [conc isub map fst snd]; [reflexivity|].
  rewrite H. unfold conc, isub in IH. rewrite IH. reflexivity.
Qed.

Lemma lmodl_rsub : forall R z, length z = length R ->
  modl P (map (aeval z) (rsub R))
  = map (fun Mz => (fst (fst Mz) * snd Mz + snd (fst Mz)) mod P) (combine R z).
Proof.
  intros R z Hl. apply nth_ext with (d := 0) (d' := 0).
  - unfold modl. rewrite !map_length, rsub_length, combine_length. lia.
  - intros k Hk. unfold modl in Hk |- *. rewrite !map_length, rsub_length in Hk.
    rewrite (nth_map_lt _ _ _ 0 0) by (rewrite map_length, rsub_length; exact Hk).
    rewrite rsub_nth by exact Hk.
    rewrite (nth_map_lt _ _ _ ((0, 0), 0) 0) by (rewrite combine_length; lia).
    rewrite combine_nth by lia. reflexivity.
Qed.

Lemma lnext_ok : forall a, GoodS a ->
  GoodS (lnxt a)
  /\ forall t, ~ In t pins -> lfires_at a t = false -> lfires_at (lnxt a) t = false ->
       lrval t (lnxt a) + 1 <= lrval t a.
Proof.
  intros a [Ha Hn].
  destruct (lwalk_leaf a Ha) as (F & lf & l & R & z & TL & TR & pL & pR & iL & iR & HF & Hw
    & Hlf & Hf & HR & HuL & HuR & Hok & Hv & HzR & HsL & HsR & HaL & HaR).
  unfold lnodeidx in Hn. rewrite Hw in Hn.
  destruct (nidx S l (modl P (an_v a))) as [i|] eqn:Ei; [|contradiction].
  pose proof (nidx_ok _ _ _ _ Ei) as HSi.
  pose proof (lnode _ _ HSi) as Hln.
  unfold lnode_ok in Hln. cbn [fst snd] in Hln. rewrite Hlf in Hln.
  rewrite forallb_forall in Hln.
  set (s := modl P z).
  assert (Hs : In s (sassign P (ll_reg lf) (modl P (an_v a)))).
  { rewrite HR, Hv, lmodl_rsub by exact HzR. apply sassign_in; [exact lHP | exact HzR]. }
  specialize (Hln s Hs). cbv zeta in Hln. apply andb_prop in Hln as [Hdiv Hln].
  rewrite forallb_forall in Hln.
  destruct (lstep_ok a Ha) as (_ & Ha').
  assert (Hnx : lnxt a = mkAn (ll_g lf) (map (aeval z) (ll_tgt lf))
                             (conc z (ll_fL lf) ++ TL) (conc z (ll_fR lf) ++ TR)).
  { unfold lnxt. rewrite Hw, Hlf. reflexivity. }
  destruct (lwalk_leaf _ Ha') as (G & lf' & l' & R' & z2 & TL2 & TR2 & pL2 & pR2 & iL2 & iR2
    & HG & Hw' & Hlf' & Hf' & HR' & _ & _ & _ & Hv' & HzR' & _ & _ & _ & _).
  rewrite Hnx in HG, Hw', Hf', Hv'. cbn [an_f an_v an_L an_R] in HG, Hw', Hf', Hv'.
  set (z' := map (fun x => x / P) z).
  assert (Hzs : forall e, aeval z' (asubst (zsub P s) e) = aeval z e).
  { intros e. subst z' s. apply aeval_zsub. exact lHP. }
  set (tgt := map (asubst (zsub P s)) (ll_tgt lf)) in *.
  set (src := map (asubst (zsub P s)) (rsub (ll_reg lf))) in *.
  assert (Htgt : map (aeval z') tgt = map (aeval z) (ll_tgt lf)).
  { subst tgt. rewrite map_map. apply map_ext. exact Hzs. }
  assert (Hsrc : map (aeval z') src = an_v a).
  { subst src. rewrite map_map, Hv, <- HR. apply map_ext. exact Hzs. }
  assert (Hl' : In l' (seq 0 (length leaves))).
  { apply in_seq. split; [lia|]. apply nth_error_Some. rewrite Hlf'. discriminate. }
  specialize (Hln l' Hl'). rewrite Hlf' in Hln.
  assert (HlenR' : length R' = length (ll_tgt lf)).
  { pose proof (f_equal (@length nat) Hv') as E. rewrite !map_length, rsub_length in E. lia. }
  assert (Hcomp : compat P (ll_reg lf') tgt = true).
  { apply (compat_ok P z' (ll_reg lf') tgt z2 Hdiv).
    - subst tgt. rewrite map_length, HR'. lia.
    - intros k Hk. rewrite HR' in Hk |- *.
      assert (Hk2 : k < length tgt) by (subst tgt; rewrite map_length; lia).
      rewrite <- (nth_map_lt (aeval z') tgt k (aconst 0) 0 Hk2), Htgt, Hv'.
      apply rsub_nth. exact Hk. }
  rewrite Hf', Nat.eqb_refl, Hcomp in Hln. cbn [andb] in Hln.
  assert (Hrho : map (fun e => a_c e mod P) tgt = modl P (map (aeval z) (ll_tgt lf))).
  { rewrite <- Htgt. unfold modl. rewrite map_map. apply map_ext_in. intros e He.
    rewrite forallb_forall in Hdiv. symmetry. apply pdiv_mod. exact (Hdiv e He). }
  rewrite Hrho in Hln.
  destruct (nidx S l' (modl P (map (aeval z) (ll_tgt lf)))) as [i'|] eqn:Ei'; [|discriminate].
  assert (Hn' : lnodeidx (lnxt a) = Some i').
  { unfold lnodeidx. rewrite Hnx. cbn [an_v]. rewrite Hw'. exact Ei'. }
  split.
  - split; [exact Ha' | rewrite Hn'; discriminate].
  - intros t Hpin Hfa Hfa'.
    unfold lfires_at in Hfa, Hfa'. rewrite Hw, Hlf in Hfa. rewrite Hnx in Hfa'.
    rewrite Hw', Hlf' in Hfa'.
    rewrite forallb_forall in Hln. specialize (Hln t (all_Instr_complete t)).
    assert (Hpin' : tr_inb t pins = false).
    { destruct (tr_inb t pins) eqn:E; [|reflexivity].
      exfalso. apply Hpin. apply tr_inb_spec. exact E. }
    assert (Hfl : nth l (map lleaf_fired leaves) [] = lleaf_fired lf).
    { apply nth_error_nth. apply map_nth_error. exact Hlf. }
    assert (Hfl2 : nth l' (map lleaf_fired leaves) [] = lleaf_fired lf').
    { apply nth_error_nth. apply map_nth_error. exact Hlf'. }
    rewrite Hpin', Hfl, Hfl2, Hfa, Hfa' in Hln. cbn [orb] in Hln.
    apply andb_prop in Hln as [Hln HwR]. apply andb_prop in Hln as [Hln HwL].
    pose proof (ale_sound z' _ _ Hln) as Hle.
    rewrite aeval_aaddc, !aeval_aadd, !veval_ok, !twa_ok, Htgt, Hsrc in Hle.
    rewrite !(isub_conc z' (zsub P s) z) in Hle by exact Hzs.
    unfold lrval. rewrite Hn'. unfold lnodeidx. rewrite Hw, Ei.
    rewrite Hnx. cbn [an_v an_L an_R].
    rewrite HaL, HaR, !twv_app. rewrite HuL, HuR in Hle.
    pose proof (wle_ok _ _ _ _ TL HwL). pose proof (wle_ok _ _ _ _ TR HwR). lia.
Qed.

Lemma lfires_rank : forall t, ~ In t pins -> forall n a, GoodS a -> lrval t a <= n ->
  exists k e, stepn tmw k (lift (tanc a)) = Some e /\ instr_of e = t.
Proof.
  intros t Hpin n. induction n as [|n IH]; intros a Ha Hr.
  all: assert (Hfire : forall a, GoodS a -> lfires_at a t = true ->
                 exists k e, stepn tmw k (lift (tanc a)) = Some e /\ instr_of e = t)
         by (intros b [Hb _] Hf; unfold lfires_at in Hf;
             destruct (lwalk b) as [[[[[l R] z] TL] TR]|] eqn:Ew; [|discriminate];
             destruct (nth_error leaves l) as [lf|] eqn:El; [|discriminate];
             apply tr_inb_spec in Hf;
             destruct (lleaf_fires b l R z TL TR lf t Hb Ew El Hf) as (k & c & Hk & Hc);
             exists k, (lift c); split; [apply csteps_lift; exact Hk | rewrite cinstr_lift; exact Hc]).
  all: destruct (lfires_at a t) eqn:Ef; [exact (Hfire a Ha Ef)|].
  all: destruct (lstep_ok a (proj1 Ha)) as ((m & c' & Hm & Hl & _) & _).
  all: destruct (lnext_ok a Ha) as (Ha' & Hrk).
  all: assert (Hback : forall t', (exists k e, stepn tmw k (lift (tanc (lnxt a))) = Some e
                                                /\ instr_of e = t') ->
                                  exists k e, stepn tmw k (lift (tanc a)) = Some e /\ instr_of e = t')
         by (intros t' (k & e & Hk & He); exists (m + k), e;
             split; [rewrite stepn_add, (csteps_lift _ _ _ _ Hm), Hl; exact Hk | exact He]).
  all: apply Hback.
  all: destruct (lfires_at (lnxt a) t) eqn:Ef'; [exact (Hfire _ Ha' Ef')|].
  - pose proof (Hrk t Hpin Ef Ef'). lia.
  - apply (IH _ Ha'). pose proof (Hrk t Hpin Ef Ef'). lia.
Qed.

Lemma lreach : forall a0 t0, GoodS a0 -> stepn tmw t0 InitES = Some (lift (tanc a0)) ->
  forall N, exists T a, N <= T /\ GoodS a /\ stepn tmw T InitES = Some (lift (tanc a)).
Proof.
  intros a0 t0 H0 Hb N. induction N as [|N (T & a & HT & Ha & Hs)].
  - exists t0, a0. split; [lia|]. split; assumption.
  - destruct (lstep_ok a (proj1 Ha)) as ((m & c' & Hm & Hl & Hpos) & _).
    destruct (lnext_ok a Ha) as (Ha' & _).
    exists (T + m), (lnxt a). split; [lia|]. split; [exact Ha'|].
    rewrite stepn_add, Hs, (csteps_lift _ _ _ _ Hm), Hl. reflexivity.
Qed.

End Check.

(** ** The certificate and the checker *)

Record lcert := mkLC {
  lc_pins   : list Instr;               (** claimed never to fire *)
  lc_kinds  : list (list Sym * list Sym);
  lc_trans  : list ltrans;
  lc_acc    : list (bool * nat);
  lc_mins   : list (bool * nat * nat);
  lc_fams   : list lfam;
  lc_leaves : list lleaf;
  lc_P      : nat;
  lc_S      : list (nat * list nat);
  lc_rank   : list (Instr * list lrk);
  lc_t0     : nat;                      (** boot, on the wrapped machine *)
  lc_a0     : lanc
}.

Definition lboot_ok (tmw : TM) (w : lcert) : bool :=
  let a0 := lc_a0 w in
  match nth_error (lc_fams w) (an_f a0), csteps tmw (lc_t0 w) c0 with
  | Some F, Some c =>
      ceqb c (tanc (lc_kinds w) (lc_trans w) (lc_fams w) a0)
      && (length (an_v a0) =? lf_n F)
      && tail_bvalid (lc_trans w) (lc_acc w) true (lf_tL F) (an_v a0) (an_L a0)
      && tail_bvalid (lc_trans w) (lc_acc w) false (lf_tR F) (an_v a0) (an_R a0)
      && match lnodeidx (lc_fams w) (lc_P w) (lc_S w) a0 with Some _ => true | None => false end
  | _, _ => false
  end.

Definition lg_check (tm : TM) (w : lcert) : bool :=
  let tmw := tm_wrap_trs tm (lc_pins w) in
  mins_ok (lc_trans w) (lc_acc w) (lc_mins w)
  && fams_ok tmw (lc_kinds w) (lc_trans w) (lc_acc w) (lc_mins w) (lc_fams w) (lc_leaves w)
  && llive_ok tmw (lc_leaves w) (lc_pins w) (lc_P w) (lc_S w) (lc_rank w)
  && lboot_ok tmw w.

(** ** Soundness *)

Theorem lg_sound : forall tm w, lg_check tm w = true -> NeverQuasiHaltsTr tm.
Proof.
  intros tm w H. unfold lg_check in H.
  set (tmw := tm_wrap_trs tm (lc_pins w)) in *.
  apply andb_prop in H as [H Hb]. apply andb_prop in H as [H Hl].
  apply andb_prop in H as [Hm Hf].
  set (a0 := lc_a0 w) in *.
  (* the boot *)
  unfold lboot_ok in Hb. fold a0 in Hb.
  destruct (nth_error (lc_fams w) (an_f a0)) as [F|] eqn:EF; [|discriminate].
  destruct (csteps tmw (lc_t0 w) c0) as [c|] eqn:Ec; [|discriminate].
  apply andb_prop in Hb as [Hb Hn]. apply andb_prop in Hb as [Hb HtR].
  apply andb_prop in Hb as [Hb HtL]. apply andb_prop in Hb as [Hc Hlen].
  apply Nat.eqb_eq in Hlen.
  assert (H0 : GoodS (lc_trans w) (lc_acc w) (lc_fams w) (lc_P w) (lc_S w) a0).
  { split.
    - exists F. split; [exact EF|]. split; [exact Hlen|].
      split; apply tail_bvalid_ok; assumption.
    - destruct (lnodeidx (lc_fams w) (lc_P w) (lc_S w) a0); discriminate. }
  assert (Hboot : stepn tmw (lc_t0 w) InitES
                  = Some (lift (tanc (lc_kinds w) (lc_trans w) (lc_fams w) a0))).
  { rewrite <- lift_c0, (csteps_lift _ _ _ _ Ec). f_equal. exact (ceqb_lift _ _ Hc). }
  pose proof (lreach tmw _ _ _ _ _ _ Hm Hf _ _ _ _ Hl a0 (lc_t0 w) H0 Hboot) as Hreach.
  assert (Hnh : forall n, stepn tmw n InitES <> None).
  { intros n. destruct (Hreach n) as (T & a & HT & _ & Hs).
    destruct (stepn_prefix tmw n T InitES _ HT Hs) as (cm & Hcm & _).
    rewrite Hcm. discriminate. }
  pose proof (wrap_trs_agree tm (lc_pins w) InitES Hnh) as Hagree.
  intros t (n & c1 & Hc1 & Ht) N.
  assert (Hnp : ~ In t (lc_pins w)).
  { destruct (Hagree n) as [_ Hnot]. rewrite <- Ht. exact (Hnot c1 Hc1). }
  destruct (Hreach N) as (T & a & HT & Ha & Hs).
  destruct (lfires_rank tmw _ _ _ _ _ _ Hm Hf _ _ _ _ Hl t Hnp _ a Ha (le_n _))
    as (k & e & Hk & He).
  exists (T + k). split; [lia|].
  exists e. split; [| exact He].
  destruct (Hagree (T + k)) as [Heq _]. rewrite <- Heq. fold tmw.
  rewrite stepn_add, Hs. exact Hk.
Qed.

(** the anchors are mirrored: certify the mirror *)
Theorem lg_sound_mirror : forall tm w, lg_check (mirror_tm tm) w = true -> NeverQuasiHaltsTr tm.
Proof.
  intros tm w H. apply neverqhtr_mirror. exact (lg_sound _ w H).
Qed.
