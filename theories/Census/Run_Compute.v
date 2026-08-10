(** * Census/Run_Compute: the census decider and queue, COMPUTATIONALLY.

    Split out of Census/Run.v (2026-08-09).  Everything here is what a
    walk unit's [native_compute] actually runs -- the parameters, the
    three lookup maps, [decider], the root and [q_suc] -- and NOTHING
    here needs a boarded-machine theorem.  The lookup tiers take their
    machines from the DATA-only Proven_List.v / ProvenQH_List.v
    (tools/gen_census_lists.py) instead of from Proven_Data.v /
    ProvenQH_Data.v, whose [Require] drags in every board behind
    [proven_all].

    Why the split exists, measured (docs/CENSUS_RUNTIME.md):
    a walk unit that requires Run.v pays 5.32 GB and 25 s natively
    BEFORE deciding one machine -- 79% of its 6.76 GB peak, times 154
    files.  Requiring this file instead costs 0.27 GB.

    The certificates are NOT weakened and NOT re-proved: Census/Run.v
    requires both this file and the board files and states
    [Forall NeverQuasiHaltsSt proven_list_data := proven_all], which
    type-checks only if the data list is convertible to the board list.
    That type-check is the whole gate between the two, and it is the
    kernel's.  [reroot_qh_list] stays on its real module: its machines
    are built by [row_to_tm], which is not convertible to a literal
    transition table, and it costs ~0.08 GB anyway. *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement Mirror.
From BBB4.Census Require Import TNF_QH Decide Deferred_Defs Deferred_Data
  Proven_List ProvenQH_List RerootQH_Data.
Import ListNotations.

Set Default Goal Selector "!".

(** ** Parameters *)

Definition B_census : nat := 2000.

Definition ng_rungs_census : list (nat * nat) :=
  [(2, 100); (3, 200); (4, 400); (6, 800)].

(** the rank-rules tier's ladder (mirrored by
    tools/sweep_rank_residue.py, which generates the deferred list) *)
Definition rank_rungs_census : list (nat * nat) :=
  [(3, 0); (3, 64); (3, 256); (3, 1024)].

(** the wrapped-QHBound tiers' ladder (mirrored by
    tools/sweep_qhbound_residue.py and tools/sweep_qhbound_lex.py, and,
    for the larger-prefix extension, by measure_B/run_sweep.py).

    The first nine rungs (n <= 4, t <= 1024) were the original vocabulary.
    Lever B extends the prefix depth: an all-survivor sweep of the 9,775
    wrap-QH machines found 2,533 more caught by the SAME rank + count-lex
    gates at larger prefixes -- t in {1280, 1536, 1999} for n in {2, 3, 4}
    (per-rung yield 1545/156/4, 188/13/3, 607/16 -- (4,1999) caught none),
    plus a single machine at (6, 1999).  Every added rung keeps
    S t <= B_census = 2000, so t = 1999 is the deepest legal prefix; the
    n=5,6 and t=4096 probes the sweep also ran caught nothing usable under
    that bound and are omitted.  Rungs are a Section variable of the
    pipeline, so extending the list needs no soundness re-proof: try_qhb's
    per-rung [S t <=? B] gate rejects any illegal prefix. *)
(** PROVEN-ONLY (D_census 16,115): reverted to the original 19,735 rungs.
    Lever B's extended prefix rungs (t=1280/1536/1999) were tried on every
    machine reaching the qhb tier IN-WALK and made the census walk far
    heavier (GG_1LC units ~9min -> >1h) -- unsustainable under container
    preemption.  The lever-B machines stay DEFERRED (in the 16,115 list),
    caught by deferred_lookup before the rungs, so the walk is the light
    19,735 walk.  (Re-add the extended rungs only with a stable long-lived
    compute env; see NEXT_SESSION post-mortem.) *)
Definition qhb_rungs_census : list (nat * nat) :=
  [(2, 64); (2, 256); (2, 1024);
   (3, 64); (3, 256); (3, 1024);
   (4, 64); (4, 256); (4, 1024)].

(** the RepWL tier's (L, T, t) ladder (mirrored by
    tools/sweep_repwl_residue.py for the first four rungs and by
    tools/sweep_repwl2.py for the block-width extension): t = 0 only --
    the 16-rung grid measured zero catches at t > 0 -- in measured
    yield order, so late-rung machines pay as few diverging-closure
    fuel burns as possible.  The fuel is the walk's per-rung cost
    bound; it covers every kept catch's closure (pops <= 2 * nodes + 1).

    Lever C extends the block width: an all-survivor sweep of the 6,247
    never-QH residue machines (tools/repwl2_caught.tsv) found 592 more
    caught by the SAME rules (a)/(b) over the five built-in measures at
    wider blocks -- rungs (5, 2, 0), (6, 2, 0), (7, 2, 0), per-rung
    yield 223 / 273 / 96, disjoint.  (6, 2, 0) is placed LAST because it
    is the only expensive-diverging new rung; a machine caught at
    (5, 2, 0) or (7, 2, 0) never pays the diverging (6, 2, 0) closure.
    Measured zero marginal yield at T >= 3 / T = 4 and at 2x/4x fuel, so
    neither the threshold nor the fuel is raised; no new measure kind is
    needed (the 5 built-ins discharge all 592: 400 plain-rank rule (a),
    192 measure-lex rule (b)).  Rungs are a Section variable, so
    extending the list needs no soundness re-proof.

    The fuel is TIGHT: the largest kept catch closes in 7947 nodes /
    8145 pops (fuel need 8146); rw_fuel_census = 8192 leaves 46 pops of
    headroom, so any catch needing more stays deferred rather than
    silently raising the bound. *)
(** PROVEN-ONLY: reverted to the original 19,735 four rungs (lever C's
    wider blocks (5/6/7,2,0) also load the walk; its machines stay
    deferred). *)
(** rung order, MEASURED (docs/CENSUS_RUNTIME.md, ProbeRwWin): the
    expensive (3,2,0) rung second looks wrong until you see the catch
    sets -- (2,2,0) catches 30 of the 32 rw-catchable sample machines
    and its only misses are exactly the machines ONLY (3,2,0)
    catches, so any machine reaching the second rung either wins
    there or fails everything.  Demoting (3,2,0) was tried and
    reverted: it only adds failing (4,2,0)+(2,3,0) attempts in front
    of those wins.  Order changes no verdict: every rung's catch is
    independently verified R_NeverQH. *)
Definition rw_rungs_census : list (nat * nat * nat) :=
  [(2, 2, 0); (3, 2, 0); (4, 2, 0); (2, 3, 0)].

(** MEASURED + GATED (2026-08-07), lowered 8192 -> 5120.

    The "7947 nodes / 8145 pops" the comment above uses to call this
    fuel TIGHT is a lever-C rung (6,2,0) catch -- and lever C is
    DEFERRED, so the walk never runs that rung.  Over all 25,511 kept
    catches at the four rungs the walk DOES run
    (tools/repwl_residue_caught.tsv), the largest closure is 3,963
    nodes; not one exceeds 4,096.  The old fuel was sized for rungs
    that are not in [rw_rungs_census], and ~half the machines reaching
    (3,2,0) burned all 8,192 units to no verdict.

    This changes WHICH machines are caught, so it is gated on a
    catch-diff -- and the diff here is EXHAUSTIVE rather than sampled.
    Lowering fuel is monotone: less fuel can only turn [close]'s [Some]
    into [None], so a catch can be lost but never gained.  By the
    [pops <= 2 * nodes + 1] bound above, only a catch whose closure
    exceeds 2303 nodes could be lost at 4608 -- and the census-wide
    table has exactly 28 such machines, ALL of which
    tools/probes/ProbeRwFuelDiff.v re-checks at 4608: zero lost,
    largest pops actually used 4,132.  5120 is then safe a fortiori
    (more fuel never loses a catch that less fuel kept), and leaves
    ~24% headroom over the largest closure the census actually walks.

    No proof impact: fuel is a Section variable and [rw_tier_sound]
    quantifies over it. *)
Definition rw_fuel_census : nat := 5120.

(** the proven-machines map, built once from the DATA copy of
    [proven_list] (mirrors how [dmap_of D_census] is applied inside
    [decider]); a hit is decided R_NeverQH by [proven_all]'s
    [Forall NeverQuasiHaltsSt] certificate, which Census/Run.v attaches
    to this list. *)
Definition pmap : DeferredMap := dmap_of proven_list_data.

(** the proven-QH map, built once from [provenqh_list] EXTENDED with the
    re-root QH tier ([reroot_qh_list], Census/RerootQH_Data.v): list-B 0RB
    residue machines boarded R_QH by [qh_reroot] through a tiny never-QH core.
    Both lists carry the same [NonHalt /\ QHBound B_census /\ QuasiHaltsSt]
    certificate ([provenqh_all], [reroot_qh_all]), composed by [Forall_app]
    in [reroot_provenqh_all]; a hit in either is decided R_QH. *)
Definition qhmap : DeferredMap :=
  dmap_of (provenqh_list_data ++ reroot_qh_list).

(** the winning-rung hint map (Decide.v [HintMap]): ADVISORY, empty
    by default -- tools/gen_hints.py can generate a table from a
    tools/census_ladder.c CSV, but the measured walk win was ~10%
    (the winning rung's own cost dominates), not worth the per-unit
    table weight; the mechanism stays for targeted use. *)
Definition hmap_census : HintMap := hmap_of [].

Definition decider : QHDecider :=
  decide_easy B_census 130 512 200000 512 ng_rungs_census
              rank_rungs_census qhb_rungs_census rw_rungs_census
              rw_fuel_census pmap qhmap (dmap_of D_census) hmap_census.

(** ** The root and its symmetrized first level *)

Definition TM0 : TM := fun _ _ => None.

Definition root : TNF_Node := mkNode TM0 (Some StB).


(** the four first-move-right children of the root *)
Definition child (w : Sym) (d : Dir) (nx : St) : TNF_Node :=
  mkNode (TM_upd' TM0 StA S0 (Some (mkTrans w d nx)))
         (ptr_after (Some StB) nx).

Definition q_0 : SearchQueue :=
  ([child S0 DR StA; child S1 DR StA; child S0 DR StB; child S1 DR StB],
   []).

(** ** The walk *)

Definition q_suc (q : SearchQueue) : SearchQueue :=
  SearchQueue_upds q decider 13.
