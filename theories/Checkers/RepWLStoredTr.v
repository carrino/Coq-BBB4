(** * Compact, supplied RepWL closure and ranking certificates.

    The decoders below only construct untrusted data. Soundness does not
    assume that they invert an encoder: the pool checker verifies the seed,
    every successor, and the lexicographic certificate on the decoded data.
    Stored data are ordinary Coq source, evaluated again in every build. *)
From Coq Require Import Arith Bool List ZArith Hexadecimal FSets.FMapPositive.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape Closure.
From BBB4.Checkers Require Import RepWL ClosureIdx ClosurePoolTr HexFuelData.
From BBB4.Census Require Import RepWLSearch.
From BBB4.CensusTr Require Import RepWLTr.
Import ListNotations.

(** Sorted key/rank dictionaries use differences, avoiding repeated large
    numerals. Adding natural differences also shares the unary rank tails. *)
Fixpoint rws_keys_from (ds : list Number.uint) (previous : N)
    (acc : list positive) : N * list positive :=
  match ds with
  | [] => (previous, acc)
  | d :: rest =>
      let k := (previous + N.of_num_uint d)%N in
      let p := match k with N0 => 1%positive | Npos p => p end in
      rws_keys_from rest k (p :: acc)
  end.
Definition rws_keys (chunks : list (list Number.uint)) : list positive :=
  List.rev (snd (fold_left (fun '(p, acc) ds => rws_keys_from ds p acc)
                       chunks (0%N, []))).

Fixpoint rws_ranks_from (ds : list Number.uint) (previous : nat)
    (acc : list nat) : nat * list nat :=
  match ds with
  | [] => (previous, acc)
  | d :: rest =>
      let v := N.to_nat (N.of_num_uint d) + previous in
      rws_ranks_from rest v (v :: acc)
  end.
Definition rws_ranks (chunks : list (list Number.uint)) : list nat :=
  List.rev (snd (fold_left (fun '(p, acc) ds => rws_ranks_from ds p acc)
                       chunks (0, []))).

(** As in HexFuelData, chunks hold at most 128 entries. Rank references
    use four hexadecimal digits to accommodate more than 255 values. *)
Fixpoint rws_pairs (keys : PositiveMap.tree positive)
    (ranks : PositiveMap.tree nat) (fuel : nat) (previous : N)
    (u : Hexadecimal.uint) : list (positive * nat) :=
  match fuel with
  | 0 => []
  | S f =>
      match hfd_var 6 1%N 0%N u with
      | Some (delta, tail) =>
          match hfd_take 4 0%N tail with
          | Some (v, rest) =>
              let k := (previous + delta)%N in
              (hfd_get keys 1%positive k, hfd_get ranks 0 v) ::
                rws_pairs keys ranks f k rest
          | None => []
          end
      | None => []
      end
  end.
Definition rws_phi keys ranks (chunks : list Number.uint) :=
  concat (map (fun u => rws_pairs keys ranks 128 0%N (hfd_hex u)) chunks).

Inductive rwscomp : Type :=
| RwsRank (phi : list Number.uint)
| RwsMeas (m : rwmeas) (K : nat) (phi gate : list Number.uint).

Definition rws_comp keys ranks (c : rwscomp) : rwcomp :=
  match c with
  | RwsRank phi => RwRankE (rws_phi keys ranks phi)
  | RwsMeas m K phi gate =>
      RwMeasE m K (rws_phi keys ranks phi) (hfd_dgate keys gate)
  end.

(** Decode the self-delimiting [rconf_enc] bit stream. These routines may
    reject data; their results still pass the full closure check. *)
Definition rws_bit (p : positive) : option (bool * positive) :=
  match p with xH => None | xO q => Some (false,q) | xI q => Some (true,q) end.
Fixpoint rws_syms (fuel : nat) (p : positive) : option (list Sym * positive) :=
  match fuel, p with
  | S _, xO q => Some ([], q)
  | S f, xI q =>
      match rws_bit q with
      | Some (b,r) =>
          match rws_syms f r with
          | Some (xs,t) => Some ((if b then S1 else S0)::xs,t)
          | None => None end
      | None => None end
  | _, _ => None
  end.
Fixpoint rws_nat (fuel : nat) (p : positive) : option (nat * positive) :=
  match fuel, p with
  | S _, xO q => Some (0,q)
  | S f, xI q =>
      match rws_nat f q with Some (n,r) => Some (S n,r) | None => None end
  | _, _ => None end.
Definition rws_item fuel p : option (ritem * positive) :=
  match rws_syms fuel p with
  | Some (w,q) =>
      match rws_nat fuel q with
      | Some (n,r) =>
          match rws_bit r with
          | Some (cap,t) => Some (mkItem w n cap,t) | None => None end
      | None => None end
  | None => None end.
Fixpoint rws_items (fuel : nat) (p : positive) : option (list ritem * positive) :=
  match fuel, p with
  | S _, xO q => Some ([],q)
  | S f, xI q =>
      match rws_item f q with
      | Some (it,r) =>
          match rws_items f r with
          | Some (xs,t) => Some (it::xs,t) | None => None end
      | None => None end
  | _, _ => None end.

Definition rws_conf (p : positive) : option rconf :=
  let fuel := Pos.size_nat p in
  match rws_bit p with
  | Some (b0,p1) => match rws_bit p1 with
    | Some (b1,p2) => match rws_bit p2 with
      | Some (h,p3) => match rws_syms fuel p3 with
        | Some (lb,p4) => match rws_syms fuel p4 with
          | Some (rb,p5) => match rws_items fuel p5 with
            | Some (li,p6) => match rws_items fuel p6 with
              | Some (ri,xH) =>
                  let q := if b1 then (if b0 then StD else StC)
                           else (if b0 then StB else StA) in
                  Some (q,(li,lb,(if h then S1 else S0),rb,ri))
              | _ => None end
            | None => None end
          | None => None end
        | None => None end
      | None => None end
    | None => None end
  | None => None end.

Definition rw_check_stored_tr (tm : TM) (L T t M : nat)
    (keys : list positive) (ranks : list nat)
    (cert : Instr -> list rwscomp) : bool :=
  (1 <=? L) && (2 <=? T) &&
  match csteps tm t c0, map_opt rws_conf keys with
  | Some cc, Some pool =>
      let km := hfd_pool keys in
      let rm := hfd_pool ranks in
      closure_pool_check_tr tm rconf rconf_enc rw_instr (rw_succs_cut M tm L T)
        t (rw_seed L T cc) pool
        (fun tg => map (rw_comp_denote tm) (map (rws_comp km rm) (cert tg)))
  | _, _ => false
  end.

Theorem rw_check_stored_tr_sound : forall tm L T t M keys ranks cert,
  rw_check_stored_tr tm L T t M keys ranks cert = true ->
  NeverQuasiHaltsTr tm.
Proof.
  intros tm L T t M keys ranks cert H.
  unfold rw_check_stored_tr in H.
  apply andb_prop in H as [Hg H].
  apply andb_prop in Hg as [HL HT].
  apply Nat.leb_le in HL. apply Nat.leb_le in HT.
  destruct (csteps tm t c0) as [cc|] eqn:Et; [|discriminate].
  destruct (map_opt rws_conf keys) as [pool|] eqn:Ep; [|discriminate].
  eapply (closure_pool_check_tr_sound tm rconf rconf_enc rw_instr
            (rw_succs_cut M tm L T) rw_covers') in H;
    [exact H | | | | exact Et | |].
  - exact rconf_enc_inj.
  - exact rw_covers'_instr.
  - intros a c Hc. apply rw_succs_cut_sound'; assumption.
  - split; [apply rw_seed_covers | apply rw_seed_wf]; assumption.
  - intros tg. apply Forall_forall. intros comp Hin.
    apply in_map_iff in Hin. destruct Hin as (c & <- & _).
    destruct c as [phi | m K phi gate]; simpl.
    + exact I.
    + intros a cc0 a' cc0' sl Hca Hca' Hstep Es HInl.
      exact (rw_meas_exact tm m a cc0 cc0' Hca Hstep).
Qed.
