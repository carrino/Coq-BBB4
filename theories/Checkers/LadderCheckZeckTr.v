(** * Checkers.LadderCheckZeckTr: the ZECKENDORF counter (SCOPING_INSTR 7.4.LE3).

    valfam reads seven open rows ([1RB1RA_0LC1LB_0RC1LD_0RA0LD], ...) as a
    one-cell binary string [x] with weights [1, 2, 3, 5, 8, ...] (its
    "fibonacci(shifted)" numeration) and no two adjacent [1]s -- the
    Zeckendorf representation -- followed by a fixed terminator, counting by
    one per anchor visit: [0000 01, 1000 01, 0100 01, 0010 01, 1010 01, ...]
    (LSB nearest the head).  [LadderFam]'s [Fib] code has the weights
    [1, 1, 2, 3, ...] and [LadderCheck] states its greedy and lazy
    representatives; the Zeckendorf one is neither, so it is stated here.

    The successor is DIGIT-WISE and total, [zinc]:

      zinc []            = [0]          zinc [0]          = [1]
      zinc (0 :: 0 :: r) = 1 :: 0 :: r  zinc (0 :: 1 :: t) = 0 :: 0 :: zinc t
      zinc (1 :: t)      = 0 :: zinc t

    and a Zeckendorf string is [u ++ (01)^k ++ s] with [u] one of [[]] or
    [[1]] (the maximal alternating prefix ending in a [1]) and [s] one of
    [0 :: 0 :: r], [[0]] or [[]].  So there are three arm classes, each in
    two kinds ([u]) and indexed by [k] in [LadderCheck]'s arm scheme over the
    two-cell word [01]:

    - interior: [u (01)^k 0 0 X -> 0^|u| (00)^k 1 0 X], [X] opaque;
    - end:      [u (01)^k 0 T  -> 0^|u| (00)^k 1 T], both tails known empty;
    - top:      [u (01)^k T    -> 0^|u| (00)^k 0 T], both tails known empty
                (the top of a width; [x] grows by one digit).

    Liveness: inside a width the value [fibvl 1 x] rises by one at every
    interior and end step and stays below [fibw (|x| + 1)] ([zbound]), so
    the tops recur, and the fires are witnessed from the top arms' anchors.
    The family is a [Fam] (digit words, prefix, the one terminator, the
    anchor); the configurations are [fam_cfg F (x, 0, 0)].

    Nothing landed is modified.  Axiom footprint: [functional_extensionality_dep],
    via [CTape.lift]. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr.
From BBB4.Counters Require Import WTape LapCertGlueLift.
From BBB4.Checkers Require Import WrapTr LapDecider LadderKernel LadderFam LadderCheck LadderCheckTr LadderNest LadderCheckNestTr TCyclerQHTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

(** ** 1. The Zeckendorf increment *)

Fixpoint zinc (x : list nat) : list nat :=
  match x with
  | [] => [0]
  | 0 :: t =>
      match t with
      | [] => [1]
      | 0 :: r => 1 :: 0 :: r
      | _ :: t' => 0 :: 0 :: zinc t'
      end
  | _ :: t => 0 :: zinc t
  end.

(** canonical: digits below 2, no two adjacent [1]s *)
Fixpoint zok (x : list nat) : bool :=
  match x with
  | [] => true
  | d :: t =>
      (d <? 2) && zok t
      && match t with
         | e :: _ => negb ((d =? 1) && (e =? 1))
         | [] => true
         end
  end.

Definition zval (x : list nat) : nat := fibvl 1 x.

Definition zu (i : nat) : list nat := if i =? 0 then [] else [1].
Definition zu0 (i : nat) : list nat := if i =? 0 then [] else [0].

Lemma wrep_cons01 : forall k s, wrep [0;1] (S k) ++ s = 0 :: 1 :: (wrep [0;1] k ++ s).
Proof. reflexivity. Qed.

Lemma zinc_alt : forall k s, 0 < k ->
  zinc (wrep [0;1] k ++ s) = wrep [0;0] k ++ zinc s.
Proof.
  induction k as [|k IH]; intros s Hk; [lia|].
  rewrite wrep_cons01. cbn [zinc wrep app].
  destruct k as [|k]; [reflexivity|].
  rewrite IH by lia. reflexivity.
Qed.

Lemma zinc_alt0 : forall k s,
  (match s with 0 :: _ => True | [] => True | _ => False end) ->
  zinc (wrep [0;1] k ++ s) = wrep [0;0] k ++ zinc s.
Proof.
  intros [|k] s Hs; [reflexivity|]. apply zinc_alt. lia.
Qed.

Lemma zinc_u : forall i k s, i < 2 ->
  (match s with 0 :: _ => True | [] => True | _ => False end) ->
  zinc (zu i ++ wrep [0;1] k ++ s) = zu0 i ++ wrep [0;0] k ++ zinc s.
Proof.
  intros [|[|i]] k s Hi Hs; [| |lia]; cbn [zu zu0 Nat.eqb app].
  - apply zinc_alt0. exact Hs.
  - destruct k as [|k].
    + cbn [wrep app]. destruct s as [|[|e] s]; try contradiction; reflexivity.
    + cbn [zinc]. rewrite zinc_alt by lia. reflexivity.
Qed.

(** ** 2. Values *)

Lemma fibvl_zeros : forall m j s, fibvl j (repeat 0 m ++ s) = fibvl (j + m) s.
Proof.
  induction m as [|m IH]; intros j s; cbn [repeat app fibvl].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IH. replace (j + S m) with (S j + m) by lia. lia.
Qed.

Lemma wrep00 : forall k, wrep [0;0] k = repeat 0 (2 * k).
Proof.
  induction k as [|k IH]; [reflexivity|].
  replace (2 * S k) with (S (S (2 * k))) by lia. cbn [wrep repeat app].
  rewrite IH. reflexivity.
Qed.

Lemma zval_alt : forall k, S (fibvl 1 (wrep [0;1] k)) = fibw (S (2 * k)).
Proof.
  induction k as [|k IH]; [reflexivity|].
  rewrite wrep_snoc, fibvl_app, wrep_length. cbn [length fibvl].
  replace (1 + k * 2) with (S (2 * k)) by lia.
  replace (S (2 * S k)) with (S (S (S (2 * k)))) by lia.
  rewrite (fibw_SS (S (2 * k))). cbn [fibvl] in *. lia.
Qed.

Lemma zval_alt1 : forall k, S (S (fibvl 2 (wrep [0;1] k))) = fibw (S (S (2 * k))).
Proof.
  induction k as [|k IH]; [reflexivity|].
  rewrite wrep_snoc, fibvl_app, wrep_length. cbn [length fibvl].
  replace (2 + k * 2) with (S (S (2 * k))) by lia.
  replace (S (S (2 * S k))) with (S (S (S (S (2 * k))))) by lia.
  rewrite (fibw_SS (S (S (2 * k)))). cbn [fibvl] in *. lia.
Qed.

(** the alternating prefix and one more is the next weight *)
Lemma zval_u : forall i k, i < 2 ->
  S (fibvl 1 (zu i ++ wrep [0;1] k)) = fibw (S (length (zu i) + 2 * k)).
Proof.
  intros [|[|i]] k Hi; [| |lia]; cbn [zu Nat.eqb app length].
  - apply zval_alt.
  - cbn [fibvl]. rewrite <- zval_alt1. cbn [fibw]. lia.
Qed.

Lemma zlen_u : forall i, i < 2 -> length (zu0 i) = length (zu i).
Proof. intros [|[|i]] Hi; [reflexivity | reflexivity | lia]. Qed.

Lemma zu0_zeros : forall i, i < 2 -> zu0 i = repeat 0 (length (zu i)).
Proof. intros [|[|i]] Hi; [reflexivity | reflexivity | lia]. Qed.

(** ** 3. The bound: a canonical string of width [w] is below [fibw (w + 1)] *)

Lemma zbound_gen : forall n x j, length x <= n -> zok x = true -> 1 <= j ->
  fibvl j x + fibw (j - 1) <= fibw (j + length x).
Proof.
  induction n as [|n IH]; intros x j Hl Hz Hj.
  - destruct x; [|cbn in Hl; lia]. cbn [fibvl length]. rewrite Nat.add_0_r.
    destruct j as [|j]; [lia|]. replace (S j - 1) with j by lia.
    pose proof (fibw_mono j). lia.
  - destruct x as [|d t].
    + cbn [fibvl length]. rewrite Nat.add_0_r.
      destruct j as [|j]; [lia|]. replace (S j - 1) with j by lia.
      pose proof (fibw_mono j). lia.
    + cbn [zok] in Hz. apply andb_true_iff in Hz as [Hz Hadj].
      apply andb_true_iff in Hz as [Hd Ht]. apply Nat.ltb_lt in Hd.
      cbn [length fibvl].
      destruct d as [|[|d]]; [| |lia].
      * (* a 0: the rest from one weight up *)
        pose proof (IH t (S j) ltac:(cbn in Hl; lia) Ht ltac:(lia)) as H.
        replace (S j - 1) with j in H by lia.
        destruct j as [|j]; [lia|].
        replace (S j - 1) with j by lia. pose proof (fibw_mono j).
        replace (S j + S (length t)) with (S (S j) + length t) by lia. lia.
      * destruct t as [|e t'].
        -- cbn [fibvl length]. destruct j as [|j]; [lia|].
           replace (S j - 1) with j by lia.
           replace (S j + 1) with (S (S j)) by lia.
           rewrite (fibw_SS j). lia.
        -- (* a 1 is followed by a 0 *)
           destruct e as [|e]; [|cbn in Hadj; destruct e; discriminate].
           cbn [zok] in Ht. apply andb_true_iff in Ht as [Ht _].
           apply andb_true_iff in Ht as [_ Ht'].
           pose proof (IH t' (S (S j)) ltac:(cbn in Hl; lia) Ht' ltac:(lia)) as H.
           cbn [fibvl length]. replace (S (S j) - 1) with (S j) in H by lia.
           destruct j as [|j]; [lia|].
           replace (S j - 1) with j by lia.
           replace (S j + S (S (length t'))) with (S (S (S j)) + length t') by lia.
           rewrite (fibw_SS j) in H. lia.
Qed.

Lemma zbound : forall x, zok x = true -> zval x < fibw (S (length x)).
Proof.
  intros x Hz. pose proof (zbound_gen (length x) x 1 (le_n _) Hz (le_n _)) as H.
  unfold zval. change (fibw (1 - 1)) with 1 in H.
  replace (1 + length x) with (S (length x)) in H by lia. lia.
Qed.

(** ** 4. Every canonical string is in one class *)

Definition zrest (s : list nat) : Prop :=
  s = [] \/ s = [0] \/ exists r, s = 0 :: 0 :: r.

Lemma zok_cons0 : forall t, zok (0 :: t) = zok t.
Proof. intros [|e t]; cbn [zok]; [reflexivity|]. rewrite andb_true_r. reflexivity. Qed.

Lemma zok_zeros : forall m t, zok (repeat 0 m ++ t) = zok t.
Proof. induction m as [|m IH]; intros t; [reflexivity|]. cbn [repeat app]. rewrite zok_cons0. apply IH. Qed.

Lemma zok_10 : forall r, zok (1 :: 0 :: r) = zok r.
Proof.
  intros r.
  change (zok (1 :: 0 :: r)) with ((1 <? 2) && zok (0 :: r) && negb ((1 =? 1) && (0 =? 1))).
  rewrite zok_cons0. cbn. destruct (zok r); reflexivity.
Qed.

Lemma zok_suffix : forall a b, zok (a ++ b) = true -> zok b = true.
Proof.
  induction a as [|d a IH]; intros b H; [exact H|].
  cbn [app zok] in H. apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [_ H]. apply IH. exact H.
Qed.

Lemma zok_1 : forall d t, zok (1 :: d :: t) = true -> d = 0.
Proof.
  intros [|[|d]] t H; [reflexivity | |]; exfalso; cbn in H;
    rewrite ?andb_false_r, ?andb_false_l in H; discriminate.
Qed.

Lemma zdecA : forall n x, length x <= n -> zok x = true ->
  (match x with 1 :: _ => False | _ => True end) ->
  exists k s, x = wrep [0;1] k ++ s /\ zrest s.
Proof.
  induction n as [|n IH]; intros x Hl Hz Hx.
  - destruct x; [|cbn in Hl; lia]. exists 0, []. split; [reflexivity | left; reflexivity].
  - destruct x as [|d t].
    + exists 0, []. split; [reflexivity | left; reflexivity].
    + destruct d as [|[|d]]; [| contradiction |].
      2:{ cbn [zok] in Hz. apply andb_true_iff in Hz as [Hz _].
          apply andb_true_iff in Hz as [Hz _]. apply Nat.ltb_lt in Hz. lia. }
      destruct t as [|e t].
      * exists 0, [0]. split; [reflexivity | right; left; reflexivity].
      * destruct e as [|[|e]].
        -- exists 0, (0 :: 0 :: t). split; [reflexivity | right; right; exists t; reflexivity].
        -- rewrite zok_cons0 in Hz.
           destruct t as [|f t'].
           ++ exists 1, []. split; [reflexivity | left; reflexivity].
           ++ pose proof (zok_1 f t' Hz) as Hf. subst f.
              cbn [zok] in Hz. apply andb_true_iff in Hz as [Hz _].
              apply andb_true_iff in Hz as [_ Hz].
              destruct (IH (0 :: t') ltac:(cbn in Hl |- *; lia) Hz I) as (k & s & Hk & Hs).
              exists (S k), s. split; [rewrite wrep_cons01, <- Hk; reflexivity | exact Hs].
        -- rewrite zok_cons0 in Hz. exfalso. cbn in Hz.
           rewrite ?andb_false_r, ?andb_false_l in Hz; discriminate.
Qed.

Lemma zdec : forall x, zok x = true ->
  exists i k s, i < 2 /\ x = zu i ++ wrep [0;1] k ++ s /\ zrest s.
Proof.
  intros x Hz.
  destruct x as [|[|[|d]] t].
  - exists 0, 0, []. split; [lia | split; [reflexivity | left; reflexivity]].
  - destruct (zdecA (length (0 :: t)) (0 :: t) (le_n _) Hz I) as (k & s & Hk & Hs).
    exists 0, k, s. split; [lia | split; [exact Hk | exact Hs]].
  - (* a leading 1 is followed by a 0, or by nothing *)
    cbn [zok] in Hz. apply andb_true_iff in Hz as [Hz Hadj].
    apply andb_true_iff in Hz as [_ Ht].
    assert (H1 : match t with 1 :: _ => False | _ => True end).
    { destruct t as [|[|[|e]] t]; trivial. cbn in Hadj. discriminate. }
    destruct (zdecA (length t) t (le_n _) Ht H1) as (k & s & Hk & Hs).
    exists 1, k, s. split; [lia | split; [cbn [zu Nat.eqb app]; rewrite <- Hk; reflexivity | exact Hs]].
  - cbn [zok] in Hz. apply andb_true_iff in Hz as [Hz _].
    apply andb_true_iff in Hz as [Hz _]. apply Nat.ltb_lt in Hz. lia.
Qed.

(** ** 5. Each class's successor *)

Lemma zok_u : forall i, i < 2 -> zok (zu i) = true.
Proof. intros [|[|i]] Hi; [reflexivity | reflexivity | lia]. Qed.

Lemma zval_cls : forall i k s, i < 2 ->
  zval (zu i ++ wrep [0;1] k ++ s)
    = fibw (S (length (zu i) + 2 * k)) - 1 + fibvl (S (length (zu i) + 2 * k)) s.
Proof.
  intros i k s Hi. unfold zval. rewrite app_assoc, fibvl_app.
  pose proof (zval_u i k Hi) as H. rewrite app_length, wrep_length. cbn [length].
  replace (1 + (length (zu i) + k * 2)) with (S (length (zu i) + 2 * k)) by lia.
  lia.
Qed.

Lemma zval_zcls : forall i k t, i < 2 ->
  zval (zu0 i ++ wrep [0;0] k ++ t) = fibvl (S (length (zu i) + 2 * k)) t.
Proof.
  intros i k t Hi. unfold zval. rewrite zu0_zeros, wrep00, app_assoc, <- repeat_app,
    fibvl_zeros by exact Hi. try (f_equal; lia).
Qed.

Lemma zcls_len : forall i k t t', i < 2 -> length t = length t' ->
  length (zu0 i ++ wrep [0;0] k ++ t) = length (zu i ++ wrep [0;1] k ++ t').
Proof.
  intros i k t t' Hi Ht. rewrite !app_length, !wrep_length, zlen_u, Ht by exact Hi.
  reflexivity.
Qed.

Lemma zok_zcls : forall i k t, i < 2 -> zok (zu0 i ++ wrep [0;0] k ++ t) = zok t.
Proof.
  intros i k t Hi. rewrite zu0_zeros, wrep00, app_assoc, <- repeat_app, zok_zeros
    by exact Hi. reflexivity.
Qed.

(** interior: [u (01)^k 0 0 r -> 0^|u| (00)^k 1 0 r] *)
Lemma zstep_int : forall i k r, i < 2 ->
  zinc (zu i ++ wrep [0;1] k ++ 0 :: 0 :: r) = zu0 i ++ wrep [0;0] k ++ 1 :: 0 :: r
  /\ zval (zu0 i ++ wrep [0;0] k ++ 1 :: 0 :: r) = S (zval (zu i ++ wrep [0;1] k ++ 0 :: 0 :: r)).
Proof.
  intros i k r Hi. split.
  - rewrite zinc_u by (exact Hi || exact I). reflexivity.
  - rewrite zval_zcls, zval_cls by exact Hi. cbn [fibvl].
    pose proof (fibw_pos (S (length (zu i) + 2 * k))). lia.
Qed.

(** end: [u (01)^k 0 -> 0^|u| (00)^k 1] *)
Lemma zstep_end : forall i k, i < 2 ->
  zinc (zu i ++ wrep [0;1] k ++ [0]) = zu0 i ++ wrep [0;0] k ++ [1]
  /\ zval (zu0 i ++ wrep [0;0] k ++ [1]) = S (zval (zu i ++ wrep [0;1] k ++ [0])).
Proof.
  intros i k Hi. split.
  - rewrite zinc_u by (exact Hi || exact I). reflexivity.
  - rewrite zval_zcls, zval_cls by exact Hi. cbn [fibvl].
    pose proof (fibw_pos (S (length (zu i) + 2 * k))). lia.
Qed.

(** top: [u (01)^k -> 0^|u| (00)^k 0], one digit wider *)
Lemma zstep_top : forall i k, i < 2 ->
  zinc (zu i ++ wrep [0;1] k) = zu0 i ++ wrep [0;0] k ++ [0].
Proof.
  intros i k Hi. rewrite <- (app_nil_r (wrep [0;1] k)).
  rewrite zinc_u by (exact Hi || exact I). reflexivity.
Qed.

(** ** 6. Tops recur *)

Fixpoint ziter (x : list nat) (n : nat) : list nat :=
  match n with O => x | S n' => ziter (zinc x) n' end.

Lemma ziter_add : forall n1 n2 x, ziter x (n1 + n2) = ziter (ziter x n1) n2.
Proof. induction n1 as [|n1 IH]; intros n2 x; [reflexivity | apply IH]. Qed.

Definition ZInv (x : list nat) : Prop := zok x = true /\ 0 < length x.

Definition ztop (x : list nat) : Prop :=
  exists i k, i < 2 /\ x = zu i ++ wrep [0;1] k.

Lemma zsucc_inv : forall x, ZInv x -> ZInv (zinc x).
Proof.
  intros x (Hz & Hl).
  destruct (zdec x Hz) as (i & k & s & Hi & -> & [-> | [-> | (r & ->)]]).
  - rewrite app_nil_r, zstep_top by exact Hi. split.
    + rewrite zok_zcls by exact Hi. reflexivity.
    + rewrite !app_length. cbn [length]. lia.
  - rewrite (proj1 (zstep_end i k Hi)). split.
    + rewrite zok_zcls by exact Hi. reflexivity.
    + rewrite !app_length, !wrep_length, zlen_u by exact Hi. cbn [length] in *. lia.
  - rewrite (proj1 (zstep_int i k r Hi)). split.
    + rewrite zok_zcls by exact Hi.
      apply zok_suffix in Hz. apply zok_suffix in Hz.
      rewrite !zok_cons0 in Hz. rewrite zok_10. exact Hz.
    + rewrite !app_length, !wrep_length, zlen_u by exact Hi. cbn [length] in *. lia.
Qed.

Lemma ziter_inv : forall n x, ZInv x -> ZInv (ziter x n).
Proof. induction n as [|n IH]; intros x Hx; [exact Hx | apply IH, zsucc_inv, Hx]. Qed.

Lemma ztop_reached : forall m x, ZInv x -> fibw (S (length x)) - zval x <= m ->
  exists n, ztop (ziter x n).
Proof.
  induction m as [|m IH]; intros x Hx Hm.
  - exfalso. pose proof (zbound x (proj1 Hx)). lia.
  - destruct Hx as (Hz & Hl).
    destruct (zdec x Hz) as (i & k & s & Hi & Hxe & [Hs | [Hs | (r & Hs)]]); subst s.
    + exists 0. exists i, k. split; [exact Hi | rewrite Hxe, app_nil_r; reflexivity].
    + destruct (zstep_end i k Hi) as (He & Hv).
      destruct (IH (zinc x) (zsucc_inv x (conj Hz Hl))) as (n & Hn).
      * rewrite Hxe, He, Hv, (zcls_len i k [1] [0] Hi eq_refl). rewrite Hxe in Hm. lia.
      * exists (S n). exact Hn.
    + destruct (zstep_int i k r Hi) as (He & Hv).
      destruct (IH (zinc x) (zsucc_inv x (conj Hz Hl))) as (n & Hn).
      * rewrite Hxe, He, Hv, (zcls_len i k (1 :: 0 :: r) (0 :: 0 :: r) Hi eq_refl).
        rewrite Hxe in Hm. lia.
      * exists (S n). exact Hn.
Qed.

Theorem ztops_cofinal : forall x N, ZInv x ->
  exists n, N <= n /\ ztop (ziter x n) /\ ZInv (ziter x n).
Proof.
  intros x N Hx.
  pose proof (ziter_inv N x Hx) as HN.
  destruct (ztop_reached (fibw (S (length (ziter x N))) - zval (ziter x N))
              (ziter x N) HN (le_n _)) as (n & Hn).
  exists (N + n). rewrite ziter_add.
  split; [lia | split; [exact Hn | apply ziter_inv, HN]].
Qed.

(** ** 7. The board *)

Section BoardZTr.

Variable tm0   : TM.
Variable pins  : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable F     : Fam.
Variable AI    : nat -> nat -> LRule.   (** interior: kind, index *)
Variable N0i sti : nat.
Variable AE    : nat -> nat -> LRule.   (** end: kind, index *)
Variable N0e ste : nat.
Variable AT    : nat -> nat -> LRule.   (** top: kind, index *)
Variable N0t stt : nat.
Variable rsv   : list LRule.
Variable vsegs : nat -> nat -> Instr -> list nseg.
Variable visI  : nat -> nat -> Instr -> list lstep.
Variable x0    : list nat.

Hypothesis Hz0 : zok x0 = true.
Hypothesis Hl0 : 0 < length x0.

Hypothesis Hsti : 0 < sti.
Hypothesis HAIS : forall i r, i < 2 -> r < N0i + sti ->
  ReachL tm (negb (fm_left F)) (fm_left F) (lr_lhs (AI i r)) (lr_rhs (AI i r)).
Hypothesis HAIL : forall i r, i < 2 -> r < N0i + sti ->
  lr_lhs (AI i r) = cls_conf F (cls_sideW F (zu i) [0;1] r (astride N0i sti r) [0;0]).
Hypothesis HAIR : forall i r, i < 2 -> r < N0i + sti ->
  lr_rhs (AI i r) = cls_conf F (cls_sideW F (zu0 i) [0;0] r (astride N0i sti r) [1;0]).

Hypothesis Hste : 0 < ste.
Hypothesis HAES : forall i r, i < 2 -> r < N0e + ste ->
  ReachL tm true true (lr_lhs (AE i r)) (lr_rhs (AE i r)).
Hypothesis HAEL : forall i r, i < 2 -> r < N0e + ste ->
  lr_lhs (AE i r) = cls_conf F (run_sideW F [0;1] r (astride N0e ste r) 0 0 (zu i) [0]).
Hypothesis HAER : forall i r, i < 2 -> r < N0e + ste ->
  lr_rhs (AE i r) = cls_conf F (run_sideW F [0;0] r (astride N0e ste r) 0 0 (zu0 i) [1]).

Hypothesis Hstt : 0 < stt.
Hypothesis HN0t : 0 < N0t.
Hypothesis HATS : forall i r, i < 2 -> r < N0t + stt -> (i = 0 -> 0 < r) ->
  ReachL tm true true (lr_lhs (AT i r)) (lr_rhs (AT i r)).
Hypothesis HATL : forall i r, i < 2 -> r < N0t + stt -> (i = 0 -> 0 < r) ->
  lr_lhs (AT i r) = cls_conf F (run_sideW F [0;1] r (astride N0t stt r) 0 0 (zu i) []).
Hypothesis HATR : forall i r, i < 2 -> r < N0t + stt -> (i = 0 -> 0 < r) ->
  lr_rhs (AT i r) = cls_conf F (run_sideW F [0;0] r (astride N0t stt r) 0 0 (zu0 i) [0]).

Hypothesis Hrsv : Forall (RuleSound tm false false) rsv.
Hypothesis Hfire : forall i r t, ~ In t pins -> i < 2 -> r < N0t + stt ->
  (i = 0 -> 0 < r) ->
  nfire tm true true rsv (vsegs i r t) (visI i r t) (lr_lhs (AT i r)) = Some t.

Local Notation Cf := (fun n => fam_cfg F (ziter x0 n, 0, 0)).

Lemma cells_runZ : forall tw w1 w2 r st m,
  fam_cells F (w1 ++ wrep tw (r + st * m) ++ w2) 0
    = sden [] m (run_sideW F tw r st 0 0 w1 w2).
Proof.
  intros tw w1 w2 r st m. rewrite <- fam_cells_runW. rewrite Nat.add_0_r. reflexivity.
Qed.

(** the top arm serving a top string, and its configuration *)
Lemma top_armZ : forall i k, i < 2 -> 0 < length (zu i ++ wrep [0;1] k) ->
  let r := aoff N0t stt k in
  r < N0t + stt /\ (i = 0 -> 0 < r)
  /\ fam_cfg F (zu i ++ wrep [0;1] k, 0, 0)
     = cden [] [] (acnt N0t stt k) (lr_lhs (AT i r)).
Proof.
  intros i k Hi Hl r.
  assert (Hrlt : r < N0t + stt) by (apply arm_index_lt; exact Hstt).
  assert (Hr0 : i = 0 -> 0 < r).
  { intros ->. apply arm_index_pos; [exact HN0t|].
    cbn [zu Nat.eqb app] in Hl. rewrite wrep_length in Hl. cbn in Hl. lia. }
  assert (Hk : r + astride N0t stt r * acnt N0t stt k = k)
    by (apply arm_index; exact Hstt).
  split; [exact Hrlt | split; [exact Hr0|]].
  rewrite (HATL i r Hi Hrlt Hr0).
  rewrite <- (cden_cls_conf F (run_sideW F [0;1] r (astride N0t stt r) 0 0 (zu i) [])
                [] (acnt N0t stt k) (zu i ++ wrep [0;1] k) 0 0).
  - unfold tailL, tailR; destruct (fm_left F); reflexivity.
  - rewrite <- Hk at 1. rewrite <- (app_nil_r (wrep [0;1] _)).
    apply cells_runZ.
Qed.

Lemma board_armZ : forall x, ZInv x ->
  exists A el er X n,
    ReachL tm el er (lr_lhs A) (lr_rhs A)
    /\ (el = true -> tailL F X = []) /\ (er = true -> tailR F X = [])
    /\ fam_cfg F (x, 0, 0) = cden (tailL F X) (tailR F X) n (lr_lhs A)
    /\ fam_cfg F (zinc x, 0, 0) = cden (tailL F X) (tailR F X) n (lr_rhs A).
Proof.
  intros x (Hz & Hl).
  destruct (zdec x Hz) as (i & k & s & Hi & Hxe & [Hs | [Hs | (r0 & Hs)]]); subst s.
  - (* the top *)
    rewrite app_nil_r in Hxe. subst x.
    destruct (top_armZ i k Hi Hl) as (Hrlt & Hr0 & Hden).
    set (r := aoff N0t stt k) in *.
    assert (Hk : r + astride N0t stt r * acnt N0t stt k = k)
      by (apply arm_index; exact Hstt).
    exists (AT i r), true, true, [], (acnt N0t stt k).
    split; [|split; [|split; [|split]]].
    + exact (HATS i r Hi Hrlt Hr0).
    + intros _; apply tailL_nil.
    + intros _; apply tailR_nil.
    + rewrite tailL_nil, tailR_nil. exact Hden.
    + rewrite zstep_top by exact Hi. rewrite (HATR i r Hi Hrlt Hr0). symmetry.
      apply cden_cls_conf. rewrite <- Hk at 1. apply cells_runZ.
  - (* the end *)
    subst x.
    remember (aoff N0e ste k) as r eqn:Er.
    assert (Hrlt : r < N0e + ste) by (subst r; apply arm_index_lt; exact Hste).
    assert (Hk : r + astride N0e ste r * acnt N0e ste k = k)
      by (subst r; apply arm_index; exact Hste).
    exists (AE i r), true, true, [], (acnt N0e ste k).
    split; [|split; [|split; [|split]]].
    + exact (HAES i r Hi Hrlt).
    + intros _; apply tailL_nil.
    + intros _; apply tailR_nil.
    + rewrite (HAEL i r Hi Hrlt). symmetry. apply cden_cls_conf.
      rewrite <- Hk at 1. apply cells_runZ.
    + rewrite (proj1 (zstep_end i k Hi)), (HAER i r Hi Hrlt). symmetry.
      apply cden_cls_conf. rewrite <- Hk at 1. apply cells_runZ.
  - (* the interior *)
    subst x.
    remember (aoff N0i sti k) as r eqn:Er.
    assert (Hrlt : r < N0i + sti) by (subst r; apply arm_index_lt; exact Hsti).
    assert (Hk : r + astride N0i sti r * acnt N0i sti k = k)
      by (subst r; apply arm_index; exact Hsti).
    exists (AI i r), (negb (fm_left F)), (fm_left F), (cls_tail F r0 0), (acnt N0i sti k).
    split; [|split; [|split; [|split]]].
    + exact (HAIS i r Hi Hrlt).
    + intros He. unfold tailL. destruct (fm_left F); [discriminate|reflexivity].
    + intros He. unfold tailR. rewrite He. reflexivity.
    + rewrite (HAIL i r Hi Hrlt). symmetry. apply cden_cls_conf.
      rewrite <- Hk at 1. exact (fam_cells_classW F (zu i) [0;1] r _ _ [0;0] r0 0).
    + rewrite (proj1 (zstep_int i k r0 Hi)), (HAIR i r Hi Hrlt). symmetry.
      apply cden_cls_conf.
      rewrite <- Hk at 1. exact (fam_cells_classW F (zu0 i) [0;0] r _ _ [1;0] r0 0).
Qed.

Lemma zinv0 : ZInv x0.
Proof. split; assumption. Qed.

Lemma lapZ : forall n, exists m c',
  0 < m /\ csteps tm m (Cf n) = Some c' /\ lift c' = lift (Cf (S n)).
Proof.
  intros n.
  destruct (board_armZ _ (ziter_inv n x0 zinv0))
    as (A & el & er & X & k & HA & HL & HR & Hl & Hr).
  destruct (HA _ _ k HL HR) as (m & c' & Hm & Hc' & Hlc).
  exists m, c'. split; [exact Hm|]. split.
  - cbn beta. rewrite Hl. exact Hc'.
  - rewrite Hlc, <- Hr. cbn beta.
    replace (S n) with (n + 1) by lia. rewrite ziter_add. reflexivity.
Qed.

Lemma fireZ : forall t N, ~ In t pins ->
  exists n k c', N <= n /\ csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t N Hnp.
  destruct (ztops_cofinal x0 N zinv0) as (n & HN & (i & k & Hi & Hx) & (_ & Hl)).
  exists n. cbn beta. rewrite Hx. rewrite Hx in Hl.
  destruct (top_armZ i k Hi Hl) as (Hrlt & Hr0 & Hden).
  set (r := aoff N0t stt k) in *.
  destruct (nfire_sound tm true true rsv (vsegs i r t) (visI i r t)
              (lr_lhs (AT i r)) t Hrsv (Hfire i r t Hnp Hi Hrlt Hr0)
              [] [] (acnt N0t stt k)
              (fun _ => eq_refl) (fun _ => eq_refl)) as (k' & c' & Hc' & Ht).
  exists k', c'. rewrite Hden. split; [exact HN | split; [exact Hc' | exact Ht]].
Qed.

Theorem boardZ_neverqhtr : forall t0,
  stepn tm t0 InitES = Some (lift (fam_cfg F (x0, 0, 0))) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros t0 Hboot.
  apply (glue_neverqhtrN tm0 pins Cf).
  - exists t0. exact Hboot.
  - intros n. destruct (lapZ n) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [exact Hl | exact Hm]].
  - intros t Hnp N. exact (fireZ t N Hnp).
Qed.

Lemma reachZ : forall d n,
  exists Tm, stepn tm Tm (lift (Cf n)) = Some (lift (Cf (n + d))).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (Tm & HT).
    destruct (lapZ (n + d)) as (m & c' & _ & Hm & Hl).
    exists (Tm + m). rewrite stepn_add, HT.
    replace (n + S d) with (S (n + d)) by lia.
    rewrite <- Hl. apply csteps_lift. exact Hm.
Qed.

Lemma fire_everyZ : forall t, ~ In t pins -> forall n,
  exists k c', csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t Hnp n.
  destruct (fireZ t n Hnp) as (m & k & c' & Hm & Hk & Hc').
  destruct (reachZ (m - n) n) as (Tm & HT).
  replace (n + (m - n)) with m in HT by lia.
  assert (Hs : stepn tm (Tm + k) (lift (Cf n)) = Some (lift c')).
  { rewrite stepn_add, HT. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (Tm + k) (Cf n) (lift c') Hs) as (c'' & Hc'' & Hl').
  exists (Tm + k), c''. split; [exact Hc''|].
  rewrite <- cinstr_lift, Hl', cinstr_lift. exact Hc'.
Qed.

Theorem boardZ_qhtr : forall t0 B,
  stepn tm0 t0 InitES = Some (lift (fam_cfg F (x0, 0, 0))) ->
  existsb (fun tg => cfires tm0 CTape.c0 t0 tg) pins = true ->
  (t0 <=? B) = true ->
  NonHalt tm0 /\ QHBoundTr B tm0 /\ QuasiHaltsTr tm0.
Proof.
  intros t0 B Hboot Hwit Hle.
  apply (lap_qh_stage tm0 pins (fun p => Cf (Nat.pred (Pos.to_nat p)))
           1%positive t0 B).
  - exact Hboot.
  - intros p _.
    destruct (lapZ (Nat.pred (Pos.to_nat p))) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (fire_everyZ t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End BoardZTr.
