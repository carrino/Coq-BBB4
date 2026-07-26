(** * LapDecider: an EXACT lap decider — one soundness theorem, per-machine
    cost a [vm_compute].

    Wave-12 established (docs/WHY_NO_HAMMER.md) that no lossy abstraction can
    finish this residue: the n-gram closure always closes, but the q-avoiding
    subgraph the liveness certificate needs stays cyclic at every precision
    setting, because a counter's carry after ~2^k steps is invisible to any
    finite window.  Exactness is required for the LIVENESS half — which is
    also mxdys' stated condition: *"my inductive decider can only decide a TM
    when it can model the forward behavior exactly"*.

    What was wrong was not the exactness, it was the EXPONENT: waves 8-12
    spent one hand-authored theorem per machine (five emitters, ~500 boards
    against a 1,385 residue).  This file is the fix — the same symbolic lap
    those emitters compute, but run by a CHECKER with the soundness argument
    discharged once.

    THE MODEL.  Every lap chain those emitters derived has the same shape:
    each tape side is a fixed prefix, one repeated block whose count is affine
    in the carry index [j], and a fixed suffix — followed by an OPAQUE TAIL
    that the lap never reaches (for a counter that tail is [Ip q0 ++ ...], the
    high bits above the carry).  So a symbolic side

      sside := (pre, u, (a, b), post)   denoting   pre ++ rep u (a*j+b) ++ post ++ X

    with [X] universally quantified is expressive enough for the whole family.

    THE STEP LANGUAGE is a faithful forward simulator, not a pattern matcher:

      - [SWin n]      run [n] real steps inside the two concrete prefixes.
                      The window is the prefixes THEMSELVES, so the entry is
                      concrete and [wsteps true true] returns [None] exactly
                      when the run would leave what we know.  Nothing to
                      guess: the certificate carries only the step count.
      - [SCycL n m]   consume the left repeated block leftward ([WTape.cycL]),
                      depositing under the first [m] cells of the right prefix.
      - [SCycR n]     consume the right repeated block rightward ([cycR]).
      - [SRotL/R m], [SUnrotL/R m]  rotate a block boundary
                      ([rep (v++w) k ++ v = v ++ rep (w++v) k]) — the
                      re-association the hand proofs did with [rep_dbl] /
                      [rep_slide], now a checked step.

    Each step is DERIVED, not asserted: [sstep] runs [wsteps] itself and reads
    the result off, so a certificate is a list of small numbers.  [srun_sound]
    turns a successful symbolic run into a concrete [csteps] for EVERY [j] and
    EVERY tail at once, and [lap_of_run] hands that to [LapGlue.glue_neverqh].

    UNTRUSTED input, trusted checker: a certificate is just data.  A wrong one
    fails to typecheck or makes [srun] return [None]; it cannot mis-prove. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape.
Import ListNotations.

(** ** List plumbing *)

Fixpoint syms_eqb (a b : list Sym) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => sym_eqb x y && syms_eqb a' b'
  | _, _ => false
  end.

Lemma syms_eqb_eq : forall a b, syms_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate.
  - reflexivity.
  - apply andb_true_iff in H as [H1 H2].
    apply sym_eqb_spec in H1; subst. now rewrite (IH b H2).
Qed.

(** [strip p l = Some r] iff [l = p ++ r]. *)
Fixpoint strip (p l : list Sym) : option (list Sym) :=
  match p with
  | [] => Some l
  | x :: p' => match l with
               | [] => None
               | y :: l' => if sym_eqb x y then strip p' l' else None
               end
  end.

Lemma strip_sound : forall p l r, strip p l = Some r -> l = p ++ r.
Proof.
  induction p as [|x p IH]; intros l r H; cbn in H.
  - now injection H as <-.
  - destruct l as [|y l]; [discriminate|].
    destruct (sym_eqb x y) eqn:E; [|discriminate].
    apply sym_eqb_spec in E; subst y.
    cbn. now rewrite <- (IH l r H).
Qed.

(** [strip_suf v l = Some r] iff [l = r ++ v]. *)
Definition strip_suf (v l : list Sym) : option (list Sym) :=
  if syms_eqb (skipn (length l - length v) l) v
  then Some (firstn (length l - length v) l)
  else None.

Lemma strip_suf_sound : forall v l r, strip_suf v l = Some r -> l = r ++ v.
Proof.
  intros v l r H; unfold strip_suf in H.
  remember (length l - length v) as k eqn:Ek; clear Ek.
  destruct (syms_eqb (skipn k l) v) eqn:E; [|discriminate].
  injection H as <-. apply syms_eqb_eq in E.
  rewrite <- E. symmetry. apply firstn_skipn.
Qed.

Lemma rep_nil : forall k, rep ([] : list Sym) k = [].
Proof. induction k; cbn; [reflexivity | exact IHk]. Qed.

(** The block-boundary rotation, the one algebraic law the chain needs. *)
Lemma rep_rot_gen : forall (v w : list Sym) k Y,
  rep (v ++ w) k ++ v ++ Y = v ++ rep (w ++ v) k ++ Y.
Proof.
  induction k; intros Y; cbn [rep].
  - reflexivity.
  - rewrite <- !app_assoc. f_equal. f_equal. apply IHk.
Qed.

(** ** Symbolic tape sides *)

(** [pre ++ rep u (a*j+b) ++ post ++ X] — [X] is the opaque tail the lap
    never reaches, quantified in every soundness statement. *)
Record sside := mkS {
  s_pre  : list Sym;
  s_u    : list Sym;
  s_a    : nat;
  s_b    : nat;
  s_post : list Sym
}.

Definition sden (X : list Sym) (j : nat) (s : sside) : list Sym :=
  s_pre s ++ rep (s_u s) (s_a s * j + s_b s) ++ s_post s ++ X.

(** A side with no repeated block: everything concrete, in [s_pre]. *)
Definition sflat (w : list Sym) : sside := mkS w [] 0 0 [].

Lemma sden_flat : forall X j w, sden X j (sflat w) = w ++ X.
Proof.
  intros. unfold sden, sflat; cbn. try rewrite rep_nil. reflexivity.
Qed.

Definition setpre (s : sside) (w : list Sym) : sside :=
  mkS w (s_u s) (s_a s) (s_b s) (s_post s).

(** ** Symbolic configurations *)

Record sconf := mkC {
  c_st : St;
  c_l  : sside;
  c_h  : Sym;
  c_r  : sside
}.

Definition cden (XL XR : list Sym) (j : nat) (c : sconf) : cconf :=
  (c_st c, (sden XL j (c_l c), c_h c, sden XR j (c_r c))).

(** ** Chain steps

    [el]/[er] record that the opaque tail on that side is KNOWN EMPTY (the
    anchor's written region ends there).  Only the open-window steps need it,
    and it is constant along a run, so it is a parameter rather than part of
    the configuration. *)

Inductive lstep :=
| SWin    (n : nat)          (** walled both sides *)
| SWinL   (n : nat)          (** open LEFT: the left side must be fully concrete *)
| SWinR   (n : nat)          (** open RIGHT: the right side must be fully concrete *)
| SCycL   (n : nat) (m : nat)
| SCycR   (n : nat)
| SRotL   (m : nat)
| SRotR   (m : nat)
| SUnrotL (m : nat)
| SUnrotR (m : nat)
| SFoldL  (m : nat)
| SFoldR  (m : nat).

(** *** Rotation, as a side transformer

    [SRot m]: [v := firstn m u] must also open [post];
      [(pre, v++w, post = v++post')  ->  (pre++v, w++v, post')].
    [SUnrot m]: [v := ] the last [m] cells of [u] must also close [pre];
      [(pre = pre'++v, w++v, post)  ->  (pre', v++w, v++post)]. *)

Definition srot (m : nat) (s : sside) : option sside :=
  let v := firstn m (s_u s) in
  let w := skipn m (s_u s) in
  match strip v (s_post s) with
  | None => None
  | Some post' => Some (mkS (s_pre s ++ v) (w ++ v) (s_a s) (s_b s) post')
  end.

Definition sunrot (m : nat) (s : sside) : option sside :=
  let k := length (s_u s) - m in
  let v := skipn k (s_u s) in
  let w := firstn k (s_u s) in
  match strip_suf v (s_pre s) with
  | None => None
  | Some pre' => Some (mkS pre' (v ++ w) (s_a s) (s_b s) (v ++ s_post s))
  end.

(** [SFold m]: absorb [m] copies of the unit sitting at the END of the prefix
    into the count itself, [(pre'++rep u m, u, (a,b), post) -> (pre', u,
    (a,b+m), post)].  The rotations move a block BOUNDARY; this moves the
    block's CONSTANT OFFSET, which no rotation can do -- an overflow anchor
    is naturally reached as [uD ++ rep uD j ++ ...] but stated by [cview] as
    [rep uD (S j) ++ ...], and this is the step that reconciles them. *)

Definition sfold (m : nat) (s : sside) : option sside :=
  match strip_suf (rep (s_u s) m) (s_pre s) with
  | None => None
  | Some pre' => Some (mkS pre' (s_u s) (s_a s) (s_b s + m) (s_post s))
  end.

Lemma sfold_den : forall m s s', sfold m s = Some s' ->
  forall X j, sden X j s = sden X j s'.
Proof.
  unfold sfold; intros m s s' H X j.
  destruct (strip_suf (rep (s_u s) m) (s_pre s)) as [pre'|] eqn:E;
    [|discriminate].
  injection H as <-. apply strip_suf_sound in E.
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  rewrite E, <- (app_assoc pre'). f_equal.
  replace (s_a s * j + (s_b s + m)) with (m + (s_a s * j + s_b s)) by lia.
  rewrite (rep_add (s_u s) m (s_a s * j + s_b s)),
          <- (app_assoc (rep (s_u s) m)).
  reflexivity.
Qed.

(** The rotation, once, on the raw denotations. *)
Lemma rot_side : forall pre v w c post X,
  pre ++ rep (v ++ w) c ++ (v ++ post) ++ X
  = (pre ++ v) ++ rep (w ++ v) c ++ post ++ X.
Proof.
  intros. rewrite <- (app_assoc pre v).
  f_equal. rewrite <- (app_assoc v post X).
  apply rep_rot_gen.
Qed.

(** ... and lifted to [sside]s, stated by their decomposition so no
    occurrence-counting is needed at the call sites. *)
Lemma sden_rot : forall X j s s' v w,
  s_u s = v ++ w ->
  s_post s = v ++ s_post s' ->
  s_pre s' = s_pre s ++ v ->
  s_u s' = w ++ v ->
  s_a s' = s_a s -> s_b s' = s_b s ->
  sden X j s = sden X j s'.
Proof.
  intros X j s s' v w Hu Hpost Hpre Hu' Ha Hb.
  unfold sden. rewrite Hu, Hpost, Hpre, Hu', Ha, Hb.
  apply rot_side.
Qed.

Lemma srot_den : forall m s s', srot m s = Some s' ->
  forall X j, sden X j s = sden X j s'.
Proof.
  unfold srot; intros m s s' H X j.
  destruct (strip (firstn m (s_u s)) (s_post s)) as [post'|] eqn:E;
    [|discriminate].
  injection H as <-.
  apply strip_sound in E.
  apply (sden_rot X j s _ (firstn m (s_u s)) (skipn m (s_u s)));
    cbn; try reflexivity.
  - symmetry; apply firstn_skipn.
  - exact E.
Qed.

Lemma sunrot_den : forall m s s', sunrot m s = Some s' ->
  forall X j, sden X j s = sden X j s'.
Proof.
  unfold sunrot; intros m s s' H X j.
  destruct (strip_suf (skipn (length (s_u s) - m) (s_u s)) (s_pre s))
    as [pre'|] eqn:E; [|discriminate].
  injection H as <-.
  apply strip_suf_sound in E.
  symmetry.
  apply (sden_rot X j _ s (skipn (length (s_u s) - m) (s_u s))
                          (firstn (length (s_u s) - m) (s_u s)));
    cbn; try reflexivity.
  - exact E.
  - symmetry; apply firstn_skipn.
Qed.

(** ** The symbolic step

    Returns the next symbolic configuration and the step count as an affine
    function [ca * j + cb] of the carry index. *)

Definition sstep (tm : TM) (el er : bool) (st : lstep) (c : sconf)
  : option (sconf * nat * nat) :=
  match st with
  | SWin n =>
      match wsteps true true tm n
              (c_st c, (s_pre (c_l c), c_h c, s_pre (c_r c))) with
      | Some (q', (xl, xh, xr)) =>
          Some (mkC q' (setpre (c_l c) xl) xh (setpre (c_r c) xr), 0, n)
      | None => None
      end
  | SWinL n =>
      if el then
        match s_u (c_l c), s_post (c_l c) with
        | [], [] =>
            match wsteps false true tm n
                    (c_st c, (s_pre (c_l c), c_h c, s_pre (c_r c))) with
            | Some (q', (xl, xh, xr)) =>
                Some (mkC q' (sflat xl) xh (setpre (c_r c) xr), 0, n)
            | None => None
            end
        | _, _ => None
        end
      else None
  | SWinR n =>
      if er then
        match s_u (c_r c), s_post (c_r c) with
        | [], [] =>
            match wsteps true false tm n
                    (c_st c, (s_pre (c_l c), c_h c, s_pre (c_r c))) with
            | Some (q', (xl, xh, xr)) =>
                Some (mkC q' (setpre (c_l c) xl) xh (sflat xr), 0, n)
            | None => None
            end
        | _, _ => None
        end
      else None
  | SCycL n m =>
      match s_pre (c_l c), s_u (c_r c) with
      | [], [] =>
          let rw := firstn m (s_pre (c_r c)) in
          let rest := skipn m (s_pre (c_r c)) in
          match wsteps true true tm n (c_st c, (s_u (c_l c), c_h c, rw)) with
          | Some (q2, ([], h2, r2)) =>
              if st_eqb (c_st c) q2 && sym_eqb (c_h c) h2 then
                match strip rw r2 with
                | Some w =>
                    Some (mkC (c_st c)
                              (sflat (s_post (c_l c)))
                              (c_h c)
                              (mkS rw w (s_a (c_l c)) (s_b (c_l c))
                                   (rest ++ s_post (c_r c))),
                          n * s_a (c_l c), n * s_b (c_l c))
                | None => None
                end
              else None
          | _ => None
          end
      | _, _ => None
      end
  | SCycR n =>
      match s_pre (c_r c), s_u (c_l c) with
      | [], [] =>
          match wsteps true true tm n (c_st c, ([], c_h c, s_u (c_r c))) with
          | Some (q2, (w, h2, [])) =>
              if st_eqb (c_st c) q2 && sym_eqb (c_h c) h2 then
                Some (mkC (c_st c)
                          (mkS [] w (s_a (c_r c)) (s_b (c_r c))
                               (s_pre (c_l c) ++ s_post (c_l c)))
                          (c_h c)
                          (sflat (s_post (c_r c))),
                      n * s_a (c_r c), n * s_b (c_r c))
              else None
          | _ => None
          end
      | _, _ => None
      end
  | SRotL m =>
      match srot m (c_l c) with
      | Some l' => Some (mkC (c_st c) l' (c_h c) (c_r c), 0, 0)
      | None => None
      end
  | SRotR m =>
      match srot m (c_r c) with
      | Some r' => Some (mkC (c_st c) (c_l c) (c_h c) r', 0, 0)
      | None => None
      end
  | SUnrotL m =>
      match sunrot m (c_l c) with
      | Some l' => Some (mkC (c_st c) l' (c_h c) (c_r c), 0, 0)
      | None => None
      end
  | SUnrotR m =>
      match sunrot m (c_r c) with
      | Some r' => Some (mkC (c_st c) (c_l c) (c_h c) r', 0, 0)
      | None => None
      end
  | SFoldL m =>
      match sfold m (c_l c) with
      | Some l' => Some (mkC (c_st c) l' (c_h c) (c_r c), 0, 0)
      | None => None
      end
  | SFoldR m =>
      match sfold m (c_r c) with
      | Some r' => Some (mkC (c_st c) (c_l c) (c_h c) r', 0, 0)
      | None => None
      end
  end.

(** *** SWin soundness

    The window IS the pair of concrete prefixes, so the entry is concrete and
    [wsteps_frame] applies with the rest of each side (repeated block, fixed
    suffix, opaque tail) as the frame.  [sden] is already right-associated
    around exactly that split, so the frame instance is definitional. *)
Lemma swin_sound : forall tm n c q' xl xh xr,
  wsteps true true tm n (c_st c, (s_pre (c_l c), c_h c, s_pre (c_r c)))
    = Some (q', (xl, xh, xr)) ->
  forall XL XR j,
  csteps tm n (cden XL XR j c)
    = Some (cden XL XR j (mkC q' (setpre (c_l c) xl) xh (setpre (c_r c) xr))).
Proof.
  intros tm n c q' xl xh xr H XL XR j.
  destruct c as [q l h r]; cbn in *.
  unfold cden, sden, setpre; cbn.
  exact (wsteps_frame tm n q (s_pre l) h (s_pre r) q' xl xh xr
           (rep (s_u l) (s_a l * j + s_b l) ++ s_post l ++ XL)
           (rep (s_u r) (s_a r * j + s_b r) ++ s_post r ++ XR) H).
Qed.

(** *** Open-window soundness

    At a tape edge the window has no wall: the run may step onto fresh blank.
    [wsteps_frame_l]/[_r] pay for that by demanding that the OPEN side carry
    no frame at all — so that side's block, suffix and opaque tail must all be
    empty.  That is exactly the situation at an overflow lap, where the
    anchor's written region ends at the frontier. *)
Lemma swinl_sound : forall tm n q pl al bl h pr ur ar br sr q' xl xh xr XR j,
  wsteps false true tm n (q, (pl, h, pr)) = Some (q', (xl, xh, xr)) ->
  csteps tm n
    (cden [] XR j (mkC q (mkS pl [] al bl []) h (mkS pr ur ar br sr)))
  = Some (cden [] XR j (mkC q' (sflat xl) xh (mkS xr ur ar br sr))).
Proof.
  intros tm n q pl al bl h pr ur ar br sr q' xl xh xr XR j H.
  unfold cden; cbn [c_st c_l c_h c_r].
  rewrite (sden_flat [] j xl).
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  rewrite rep_nil, !app_nil_l, !app_nil_r.
  exact (wsteps_frame_l tm n q pl h pr q' xl xh xr
           (rep ur (ar * j + br) ++ sr ++ XR) H).
Qed.

Lemma swinr_sound : forall tm n q pl ul al bl sl h pr ar br q' xl xh xr XL j,
  wsteps true false tm n (q, (pl, h, pr)) = Some (q', (xl, xh, xr)) ->
  csteps tm n
    (cden XL [] j (mkC q (mkS pl ul al bl sl) h (mkS pr [] ar br [])))
  = Some (cden XL [] j (mkC q' (mkS xl ul al bl sl) xh (sflat xr))).
Proof.
  intros tm n q pl ul al bl sl h pr ar br q' xl xh xr XL j H.
  unfold cden; cbn [c_st c_l c_h c_r].
  rewrite (sden_flat [] j xr).
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  rewrite rep_nil, !app_nil_l, !app_nil_r.
  exact (wsteps_frame_r tm n q pl h pr q' xl xh xr
           (rep ul (al * j + bl) ++ sl ++ XL) H).
Qed.

(** *** Cycle soundness

    [WTape.cycL]/[cycR] at the affine count [a*j+b], with the surrounding
    symbolic sides.  Stated on fully-decomposed configurations so the call
    sites need no occurrence-counted rewriting.

    [SCycL] consumes the left repeated block; the deposit lands under the
    first [m] cells of the right prefix ([rw]), which is why the right side
    must carry no block of its own yet ([s_u = []]). *)
Lemma scycl_step : forall tm n q h u rw rest pr w a b sl ar br sr XL XR j,
  pr = rw ++ rest ->
  wsteps true true tm n (q, (u, h, rw)) = Some (q, ([], h, rw ++ w)) ->
  csteps tm (n * (a * j + b))
    (cden XL XR j (mkC q (mkS [] u a b sl) h (mkS pr [] ar br sr)))
  = Some (cden XL XR j
            (mkC q (sflat sl) h (mkS rw w a b (rest ++ sr)))).
Proof.
  intros tm n q h u rw rest pr w a b sl ar br sr XL XR j Hpr Hu; subst pr.
  unfold cden; cbn [c_st c_l c_h c_r].
  rewrite (sden_flat XL j sl).
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  rewrite rep_nil, !app_nil_l, <- !app_assoc.
  exact (cycL tm n q h u rw w Hu (a * j + b) (sl ++ XL) (rest ++ sr ++ XR)).
Qed.

(** [SCycR] consumes the right repeated block; the deposit lands at the very
    front of the left side, so the left must carry no block of its own. *)
Lemma scycr_step : forall tm n q h u w a b pl al bl sl sr XL XR j,
  wsteps true true tm n (q, ([], h, u)) = Some (q, (w, h, [])) ->
  csteps tm (n * (a * j + b))
    (cden XL XR j (mkC q (mkS pl [] al bl sl) h (mkS [] u a b sr)))
  = Some (cden XL XR j
            (mkC q (mkS [] w a b (pl ++ sl)) h (sflat sr))).
Proof.
  intros tm n q h u w a b pl al bl sl sr XL XR j Hu.
  unfold cden; cbn [c_st c_l c_h c_r].
  rewrite (sden_flat XR j sr).
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  rewrite rep_nil, !app_nil_l, <- !app_assoc.
  exact (cycR tm n q h u w Hu (a * j + b) (pl ++ sl ++ XL) (sr ++ XR)).
Qed.

(** *** The generic step soundness *)

Theorem sstep_sound : forall tm el er st c c' ca cb,
  sstep tm el er st c = Some (c', ca, cb) ->
  forall XL XR j,
  (el = true -> XL = []) -> (er = true -> XR = []) ->
  csteps tm (ca * j + cb) (cden XL XR j c) = Some (cden XL XR j c').
Proof.
  intros tm el er st c c' ca cb H XL XR j HL HR.
  destruct c as [q [pl ul al bl sl] h [pr ur ar br sr]].
  destruct st as [n | n | n | n m | n | m | m | m | m | m | m];
    cbn [sstep c_st c_l c_h c_r s_pre s_u s_a s_b s_post] in H.

  - (* SWin *)
    destruct (wsteps true true tm n (q, (pl, h, pr)))
      as [[q' [[xl xh] xr]]|] eqn:E; [|discriminate].
    injection H as <- <- <-.
    replace (0 * j + n) with n by lia.
    exact (swin_sound tm n (mkC q (mkS pl ul al bl sl) h (mkS pr ur ar br sr))
             q' xl xh xr E XL XR j).

  - (* SWinL: open left *)
    destruct el; [|discriminate].
    rewrite (HL eq_refl).
    destruct ul as [|? ?]; [|discriminate].
    destruct sl as [|? ?]; [|discriminate].
    destruct (wsteps false true tm n (q, (pl, h, pr)))
      as [[q' [[xl xh] xr]]|] eqn:E; [|discriminate].
    injection H as <- <- <-.
    replace (0 * j + n) with n by lia.
    exact (swinl_sound tm n q pl al bl h pr ur ar br sr q' xl xh xr XR j E).

  - (* SWinR: open right *)
    destruct er; [|discriminate].
    rewrite (HR eq_refl).
    destruct ur as [|? ?]; [|discriminate].
    destruct sr as [|? ?]; [|discriminate].
    destruct (wsteps true false tm n (q, (pl, h, pr)))
      as [[q' [[xl xh] xr]]|] eqn:E; [|discriminate].
    injection H as <- <- <-.
    replace (0 * j + n) with n by lia.
    exact (swinr_sound tm n q pl ul al bl sl h pr ar br q' xl xh xr XL j E).

  - (* SCycL *)
    destruct pl as [|? ?]; [|discriminate].
    destruct ur as [|? ?]; [|discriminate].
    destruct (wsteps true true tm n (q, (ul, h, firstn m pr)))
      as [[q2 [[l2 h2] r2]]|] eqn:E; [|discriminate].
    destruct l2 as [|? ?]; [|discriminate].
    destruct (st_eqb q q2 && sym_eqb h h2) eqn:Eq; [|discriminate].
    apply andb_true_iff in Eq as [Eq1 Eq2].
    apply st_eqb_spec in Eq1; apply sym_eqb_spec in Eq2; subst q2 h2.
    destruct (strip (firstn m pr) r2) as [w|] eqn:Ew; [|discriminate].
    injection H as <- <- <-.
    apply strip_sound in Ew; subst r2.
    replace (n * al * j + n * bl) with (n * (al * j + bl)) by lia.
    apply (scycl_step tm n q h ul (firstn m pr) (skipn m pr) pr w al bl sl
             ar br sr XL XR j).
    + symmetry; apply firstn_skipn.
    + exact E.

  - (* SCycR *)
    destruct pr as [|? ?]; [|discriminate].
    destruct ul as [|? ?]; [|discriminate].
    destruct (wsteps true true tm n (q, ([], h, ur)))
      as [[q2 [[w h2] r2]]|] eqn:E; [|discriminate].
    destruct r2 as [|? ?]; [|discriminate].
    destruct (st_eqb q q2 && sym_eqb h h2) eqn:Eq; [|discriminate].
    apply andb_true_iff in Eq as [Eq1 Eq2].
    apply st_eqb_spec in Eq1; apply sym_eqb_spec in Eq2; subst q2 h2.
    injection H as <- <- <-.
    replace (n * ar * j + n * br) with (n * (ar * j + br)) by lia.
    exact (scycr_step tm n q h ur w ar br pl al bl sl sr XL XR j E).

  - (* SRotL *)
    destruct (srot m (mkS pl ul al bl sl)) as [l'|] eqn:E; [|discriminate].
    injection H as <- <- <-.
    replace (0 * j + 0) with 0 by lia.
    unfold cden; cbn [c_st c_l c_h c_r].
    now rewrite <- (srot_den m _ _ E XL j).
  - (* SRotR *)
    destruct (srot m (mkS pr ur ar br sr)) as [r'|] eqn:E; [|discriminate].
    injection H as <- <- <-.
    replace (0 * j + 0) with 0 by lia.
    unfold cden; cbn [c_st c_l c_h c_r].
    now rewrite <- (srot_den m _ _ E XR j).
  - (* SUnrotL *)
    destruct (sunrot m (mkS pl ul al bl sl)) as [l'|] eqn:E; [|discriminate].
    injection H as <- <- <-.
    replace (0 * j + 0) with 0 by lia.
    unfold cden; cbn [c_st c_l c_h c_r].
    now rewrite <- (sunrot_den m _ _ E XL j).
  - (* SUnrotR *)
    destruct (sunrot m (mkS pr ur ar br sr)) as [r'|] eqn:E; [|discriminate].
    injection H as <- <- <-.
    replace (0 * j + 0) with 0 by lia.
    unfold cden; cbn [c_st c_l c_h c_r].
    now rewrite <- (sunrot_den m _ _ E XR j).
  - (* SFoldL *)
    destruct (sfold m (mkS pl ul al bl sl)) as [l'|] eqn:E; [|discriminate].
    injection H as <- <- <-.
    replace (0 * j + 0) with 0 by lia.
    unfold cden; cbn [c_st c_l c_h c_r].
    now rewrite <- (sfold_den m _ _ E XL j).
  - (* SFoldR *)
    destruct (sfold m (mkS pr ur ar br sr)) as [r'|] eqn:E; [|discriminate].
    injection H as <- <- <-.
    replace (0 * j + 0) with 0 by lia.
    unfold cden; cbn [c_st c_l c_h c_r].
    now rewrite <- (sfold_den m _ _ E XR j).
Qed.

(** ** Running a chain *)

Fixpoint srun (tm : TM) (el er : bool) (l : list lstep) (c : sconf)
  : option (sconf * nat * nat) :=
  match l with
  | [] => Some (c, 0, 0)
  | st :: l' =>
      match sstep tm el er st c with
      | None => None
      | Some (c1, a1, b1) =>
          match srun tm el er l' c1 with
          | None => None
          | Some (c2, a2, b2) => Some (c2, a1 + a2, b1 + b2)
          end
      end
  end.

Theorem srun_sound : forall tm el er l c c' ca cb,
  srun tm el er l c = Some (c', ca, cb) ->
  forall XL XR j,
  (el = true -> XL = []) -> (er = true -> XR = []) ->
  csteps tm (ca * j + cb) (cden XL XR j c) = Some (cden XL XR j c').
Proof.
  intros tm el er l; induction l as [|st l IH];
    intros c c' ca cb H XL XR j HL HR; cbn in H.
  - injection H as <- <- <-. reflexivity.
  - destruct (sstep tm el er st c) as [[[c1 a1] b1]|] eqn:E1; [|discriminate].
    destruct (srun tm el er l c1) as [[[c2 a2] b2]|] eqn:E2; [|discriminate].
    injection H as <- <- <-.
    replace ((a1 + a2) * j + (b1 + b2)) with ((a1 * j + b1) + (a2 * j + b2))
      by lia.
    rewrite csteps_add,
      (sstep_sound tm el er st c c1 a1 b1 E1 XL XR j HL HR).
    exact (IH c1 c2 a2 b2 E2 XL XR j HL HR).
Qed.

(** ** The lap obligation, stated once

    A certificate proves this for an anchor family [Cf].  [glue_neverqh]
    (Counters/LapGlue.v) consumes exactly this plus boot and visits, so a
    decided certificate plugs straight into the existing closer. *)

Definition LapStep (tm : TM) (Cf : positive -> cconf) : Prop :=
  forall p, exists n c', csteps tm n (Cf p) = Some c'
                    /\ lift c' = lift (Cf (Pos.succ p))
                    /\ 0 < n.

(** One branch of a lap: the symbolic run [l] carries the anchor at [p] to
    (the [lift] of) the anchor at [p+1].  The two equalities are the ANCHOR
    GLUE — for a counter family they are exactly [cview_some_X]/[cview_none_X]
    followed by [reflexivity]. *)
Theorem lap_of_run : forall tm (Cf : positive -> cconf) el er l c0 c1 ca cb
                            p j XL XR,
  srun tm el er l c0 = Some (c1, ca, cb) ->
  (el = true -> XL = []) -> (er = true -> XR = []) ->
  Cf p = cden XL XR j c0 ->
  lift (cden XL XR j c1) = lift (Cf (Pos.succ p)) ->
  0 < cb ->
  exists n c', csteps tm n (Cf p) = Some c'
          /\ lift c' = lift (Cf (Pos.succ p)) /\ 0 < n.
Proof.
  intros tm Cf el er l c0 c1 ca cb p j XL XR Hrun HL HR H0 H1 Hcb.
  exists (ca * j + cb), (cden XL XR j c1).
  split; [| split].
  - rewrite H0. exact (srun_sound tm el er l c0 c1 ca cb Hrun XL XR j HL HR).
  - exact H1.
  - lia.
Qed.

(** A visit witness from a PREFIX of a lap chain: the same run, stopped early,
    lands in a config whose state is the one we need.  This is how the [Hvis]
    premise of [glue_neverqh] is discharged for the states that only fire
    mid-lap.  Only the STATE reached matters, so [srun_st] drops the rest and
    the per-machine obligation is a [vm_compute] against a state literal. *)

Definition srun_st (tm : TM) (el er : bool) (l : list lstep) (c : sconf)
  : option St :=
  match srun tm el er l c with
  | Some (c1, _, _) => Some (c_st c1)
  | None => None
  end.

Theorem vis_of_run : forall tm (Cf : positive -> cconf) el er l c0 p j XL XR q,
  srun_st tm el er l c0 = Some q ->
  (el = true -> XL = []) -> (er = true -> XR = []) ->
  Cf p = cden XL XR j c0 ->
  exists k c, csteps tm k (Cf p) = Some c /\ fst c = q.
Proof.
  intros tm Cf el er l c0 p j XL XR q Hst HL HR H0.
  unfold srun_st in Hst.
  destruct (srun tm el er l c0) as [[[c1 ca] cb]|] eqn:E; [|discriminate].
  injection Hst as <-.
  exists (ca * j + cb), (cden XL XR j c1). split.
  - rewrite H0. exact (srun_sound tm el er l c0 c1 ca cb E XL XR j HL HR).
  - reflexivity.
Qed.
