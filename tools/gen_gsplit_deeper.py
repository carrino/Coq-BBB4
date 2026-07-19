#!/usr/bin/env python3
"""Split a heavy great-grandchild census walk ONE MORE level deeper.

The verified-tier shrink (D_census 19,735 -> 12,974) made several
great-grandchild walks (Compute/GGH_<tag>_<ft>.v and Compute/GG_1LC_*.v)
exceed the container's preemption window.  This tool applies the SAME
node_expand_spec argument (Run_Split.child_from_grandchildren /
Run_Split2.gchild_from_ggchildren generalized) to such a unit: it
expands the unit's machine at its NEXT undefined transition into the
12/16 admissible fills, so the one heavy walk becomes 12-16 sub-walks.

Per heavy unit U (whose machine M has node-pointer P and whose Coq
node/WF live in an already-imported module) it emits, into OUTDIR:
  Run_Split_<U>.v      -- gggchild_<U> node, q_gggsub, its WF, the
                          decided lemma, and the cover lemma
                          <parent>_from_children_<U>
  GGGH_<U>_<ft2>.v     -- one native queue walk per deeper fill
  <U>.v  (REPLACEMENT)  -- proves the SAME <declemma> the monolithic
                          unit did, now via the cover + per-fill facts.

Nothing here is trusted: every walk is a native_compute Qed, and the
cover lemmas ride node_expand_spec, exactly like the shallower splits.

Design mirrors tools/gen_gsplit_heavy.py; read that first.  It is
RECURSIVELY applicable: a still-heavy GGGH unit can be fed back in
(its spec has 4 defined transitions instead of 3).

Usage: gen_gsplit_deeper.py OUTDIR UNIT [UNIT ...]   [--niter N]
  UNIT is a Compute-unit basename, e.g. GGH_0RB_1LC_0LD or GG_1LC_0LB.
"""
import os
import sys

SYM = {0: 'S0', 1: 'S1'}
SYMN = {'S0': 0, 'S1': 1}
DIRC = {'L': 'DL', 'R': 'DR'}
STC = {0: 'StA', 1: 'StB', 2: 'StC', 3: 'StD'}
STN = {'StA': 0, 'StB': 1, 'StC': 2, 'StD': 3}

# the 7 heavy grandchildren from gen_gsplit_heavy.HEAVY:
#   (A0-tag,B0-tag) -> (w, w2, d2, nx2); A0=<w>RB, B0=<w2><d2><nx2>
HEAVY = {
    ('1RB', '0LC'): (1, 0, 'L', 2), ('1RB', '0RC'): (1, 0, 'R', 2),
    ('1RB', '1LA'): (1, 1, 'L', 0), ('1RB', '1LB'): (1, 1, 'L', 1),
    ('1RB', '1RC'): (1, 1, 'R', 2), ('0RB', '1LC'): (0, 1, 'L', 2),
    ('0RB', '1RC'): (0, 1, 'R', 2),
}


def st_suc(p):
    return {0: 1, 1: 2, 2: 3, 3: None}[p]


def ptr_after(p, nx):
    # p, nx as int state codes; p may be None
    if p is None:
        return None
    return st_suc(p) if nx == p else p


def simulate(trans, maxk=4000):
    """trans: dict (st,sym)->(w,dir,nx).  Run from blank tape; return
    (k, qu, su, steps) at the first undefined (st,sym).  steps is a list
    of (w, dir_char) actually taken."""
    tape = {}
    pos = 0
    st = 0
    steps = []
    for k in range(maxk):
        h = tape.get(pos, 0)
        tr = trans.get((st, h))
        if tr is None:
            return k, st, h, steps
        w, d, nx = tr
        tape[pos] = w
        pos += 1 if d == 'R' else -1
        steps.append((w, d))
        st = nx
    raise RuntimeError("no hole within maxk steps")


def tape_expr(steps):
    e = "(mkTape blank_side S0 blank_side)"
    for (w, d) in steps:
        e = f"(tape_move {DIRC[d]} {SYM[w]} {e})"
    return e


def fills_for(p):
    """node_expand order over all_trans, filtered by trans_ok p.
    p None -> all 16; Some code -> targets 0..code."""
    hi = 3 if p is None else p
    out = []
    for w in (0, 1):
        for d in ('L', 'R'):
            for nx in range(4):
                if nx <= hi:
                    out.append((SYM[w], DIRC[d], STC[nx]))
    return out


def ft_of(w3s, d3c, nx3s):
    return f"{w3s[1]}{d3c[1]}{nx3s[2]}"   # e.g. S0,DL,StD -> 0LD


# ---- per-unit spec construction ----------------------------------------
def spec_for(unit):
    """Return a dict describing UNIT's machine + Coq context:
      trans   : dict (st,sym)->(w,dircode,nx) of DEFINED transitions
      parent  : Coq expr of the TNF_Node being split
      parentWF: Coq term proving Node_WF parent
      pptr    : node-pointer int|None of parent
      imp     : module to Require Import for parent defs
      declemma: the lemma name the monolithic unit proves
    """
    parts = unit.split('_')
    if unit.startswith('GGH_'):
        # GGH_<A0>_<B0>_<ft>
        a0, b0, ft = parts[1], parts[2], parts[3]
        w, w2, d2, nx2 = HEAVY[(a0, b0)]
        tag = f"{a0}_{b0}"
        # tm_g transitions (A0, B0)
        base = {(0, 0): (w, 'R', 1), (1, 0): (w2, d2, nx2)}
        _, qu, su, _ = simulate(base)           # tm_g's hole
        gptr = 3 if nx2 == 2 else 2             # Some StD / StC
        # ft -> (w3,d3,nx3)
        w3 = SYMN['S' + ft[0]]
        d3 = 'L' if ft[1] == 'L' else 'R'
        nx3 = {'A': 0, 'B': 1, 'C': 2, 'D': 3}[ft[2]]
        trans = dict(base)
        trans[(qu, su)] = (w3, d3, nx3)
        pptr = ptr_after(gptr, nx3)
        parent = f"ggchild_{tag} {SYM[w3]} {DIRC[d3]} {STC[nx3]}"
        parentWF = f"ggchild_{tag}_WF {SYM[w3]} {DIRC[d3]} {STC[nx3]} eq_refl"
        imp = f"Run_Split_{tag}"
        decl = f"ggh_{tag}_{ft}_decided"
        return dict(trans=trans, parent=parent, parentWF=parentWF,
                    pptr=pptr, imp=imp, declemma=decl)
    if unit.startswith('GG_1LC_'):
        # Run_Split2 family: A0=1RB, B0=1LC, ggchild fills StC/S1
        ft = parts[2]
        base = {(0, 0): (1, 'R', 1), (1, 0): (1, 'L', 2)}   # 1RB,1LC
        _, qu, su, _ = simulate(base)          # StC/S1 at step 2
        w3 = SYMN['S' + ft[0]]
        d3 = 'L' if ft[1] == 'L' else 'R'
        nx3 = {'A': 0, 'B': 1, 'C': 2, 'D': 3}[ft[2]]
        trans = dict(base)
        trans[(qu, su)] = (w3, d3, nx3)
        pptr = ptr_after(3, nx3)               # ggchild ptr = ptr_after(StD,nx3)
        parent = f"ggchild {SYM[w3]} {DIRC[d3]} {STC[nx3]}"
        parentWF = f"ggchild_WF {SYM[w3]} {DIRC[d3]} {STC[nx3]} eq_refl"
        imp = "Run_Split2"
        decl = f"gg_{ft}_decided"                # matches Compute/GG_1LC_<ft>.v
        return dict(trans=trans, parent=parent, parentWF=parentWF,
                    pptr=pptr, imp=imp, declemma=decl)
    raise RuntimeError(f"unknown unit family: {unit}")


def used_witness(trans, qu2):
    """Find a DEFINED transition (st,sym)->(w,d,nx) with nx==qu2, to
    prove ~UnusedState M qu2.  Returns (st,sym,w,d,nx) or None."""
    for (st, sym), (w, d, nx) in trans.items():
        if nx == qu2:
            return (st, sym, w, d, nx)
    return None


def gen_one(outdir, unit, niter):
    sp = spec_for(unit)
    trans = sp['trans']
    k2, qu2, su2, steps = simulate(trans)
    pptr = sp['pptr']
    fl = fills_for(pptr)
    nfill = len(fl)
    uw = used_witness(trans, qu2)
    if uw is None:
        raise RuntimeError(
            f"{unit}: hole state {STC[qu2]} not targeted by any defined "
            f"transition (start-state hole) -- needs manual handling")
    us, usym, uw_w, uw_d, uw_nx = uw
    tape = tape_expr(steps)
    quC, suC = STC[qu2], SYM[su2]
    pptrC = "None" if pptr is None else f"(Some {STC[pptr]})"

    # destruct nesting for nfill cases
    ncases = '[<-|' * nfill + '[]' + ']' * nfill
    coverbr = '\n      '.join(
        f"{'[' if i == 0 else '|'} exact (Hg {a} {b} {c} eq_refl)"
        for i, (a, b, c) in enumerate(fl)) + " ]"

    # ---- Run_Split_<unit>.v ----
    mod = f"""(** GENERATED by tools/gen_gsplit_deeper.py -- do not edit.
    Deeper split of heavy unit {unit}: its machine reaches hole {quC}
    reading {suC} at step {k2}; parent pointer {pptrC}, {nfill} fills. *)
From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import TNF_QH Decide Deferred_Data Run Run_Split.
From BBB4.Census Require Import {sp['imp']}.
Import ListNotations.

Set Default Goal Selector "!".

Definition ggm_{unit} : TM := node_tm ({sp['parent']}).

Definition gggchild_{unit} (w4 : Sym) (d4 : Dir) (nx4 : St) : TNF_Node :=
  mkNode (TM_upd' ggm_{unit} {quC} {suC} (Some (mkTrans w4 d4 nx4)))
         (ptr_after {pptrC} nx4).

Definition q_gggsub_{unit} (w4 : Sym) (d4 : Dir) (nx4 : St) : SearchQueue :=
  ([gggchild_{unit} w4 d4 nx4], []).

Lemma ggm_{unit}_used : ~ UnusedState ggm_{unit} {quC}.
Proof.
  intros (Hin & _ & _).
  refine (Hin {STC[us]} {SYM[usym]} (mkTrans {SYM[uw_w]} {DIRC[uw_d]} {STC[uw_nx]}) _ eq_refl).
  reflexivity.
Qed.

Lemma gggchild_{unit}_WF : forall w4 d4 nx4,
  trans_ok {pptrC} (mkTrans w4 d4 nx4) = true ->
  Node_WF (gggchild_{unit} w4 d4 nx4).
Proof.
  intros w4 d4 nx4 Hok.
  unfold Node_WF, gggchild_{unit}; simpl.
  rewrite TM_upd'_spec.
  apply (UnusedState_ptr_upd ggm_{unit} {quC} {suC} (mkTrans w4 d4 nx4) {pptrC}).
  - reflexivity.
  - exact ggm_{unit}_used.
  - exact ({sp['parentWF']}).
  - exact Hok.
Qed.

Lemma gggsub_decided_{unit} : forall w4 d4 nx4 n,
  trans_ok {pptrC} (mkTrans w4 d4 nx4) = true ->
  Nat.iter n q_suc (q_gggsub_{unit} w4 d4 nx4) = ([], []) ->
  NodeDecided B_census D_census (node_tm (gggchild_{unit} w4 d4 nx4)).
Proof.
  intros w4 d4 nx4 n Hok Hempty.
  assert (HWF : SearchQueue_WF B_census D_census
                  (Nat.iter n q_suc (q_gggsub_{unit} w4 d4 nx4))
                  (gggchild_{unit} w4 d4 nx4)).
  {{ clear Hempty. induction n.
    - apply SearchQueue_init_spec. apply gggchild_{unit}_WF. exact Hok.
    - simpl. apply SearchQueue_upds_spec; [exact IHn | exact decider_WF]. }}
  rewrite Hempty in HWF.
  exact (SearchQueue_empty_decided B_census D_census _ HWF).
Qed.

Lemma cover_{unit} :
  (forall w4 d4 nx4,
     trans_ok {pptrC} (mkTrans w4 d4 nx4) = true ->
     NodeDecided B_census D_census (node_tm (gggchild_{unit} w4 d4 nx4))) ->
  NodeDecided B_census D_census (node_tm ({sp['parent']})).
Proof.
  intros Hg.
  assert (Hstep : stepn ggm_{unit} {k2} InitES = Some ({quC}, {tape})).
  {{ reflexivity. }}
  assert (Hhole : ggm_{unit} {quC} (t_head {tape}) = None) by reflexivity.
  assert (HB : {k2 + 1} <= B_census) by (unfold B_census; lia).
  pose proof (node_expand_spec B_census D_census ggm_{unit} {pptrC} {k2}
                {quC} {tape}
                Hstep Hhole HB ({sp['parentWF']})) as [_ Hexp].
  change (NodeDecided B_census D_census ggm_{unit}).
  apply Hexp.
  intros x' Hin.
  cbn [node_expand node_tm node_ptr filter trans_ok all_trans map
       t_next t_head tape_move St_to_nat Nat.leb In] in Hin.
  destruct Hin as {ncases};
    cbn [node_tm];
    first
      {coverbr}.
Qed.
"""
    open(os.path.join(outdir, f"Run_Split_{unit}.v"), 'w').write(mod)

    # ---- per-fill deep walks ----
    for (w4, d4, nx4) in fl:
        ft2 = ft_of(w4, d4, nx4)
        wf = f"""(** GENERATED by tools/gen_gsplit_deeper.py -- do not edit.
    Deep sub-walk of {unit}: {quC}{suC[1]} = {ft2}. *)
From Coq Require Import Arith List.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import TNF_QH Decide Deferred_Data Run Run_Split.
From BBB4.Census Require Import {sp['imp']} Run_Split_{unit}.
Import ListNotations.

Lemma gggh_{unit}_{ft2}_empty :
  Nat.iter {niter} q_suc (q_gggsub_{unit} {w4} {d4} {nx4}) = ([], []).
Proof.
  native_cast_no_check (eq_refl (@nil TNF_Node, @nil TNF_Node)).
Qed.

Lemma gggh_{unit}_{ft2}_decided :
  NodeDecided B_census D_census (node_tm (gggchild_{unit} {w4} {d4} {nx4})).
Proof.
  exact (gggsub_decided_{unit} {w4} {d4} {nx4} {niter} eq_refl
           gggh_{unit}_{ft2}_empty).
Qed.
"""
        open(os.path.join(outdir, f"GGGH_{unit}_{ft2}.v"), 'w').write(wf)

    # ---- REPLACEMENT of the heavy unit file ----
    imports = '\n'.join(
        f"From BBB4.Census.Compute Require Import GGGH_{unit}_{ft_of(*f)}."
        for f in fl)
    # destruct produces all 16 (w4,d4,nx4) branches; the admissible ones
    # match a per-fill decided lemma, the inadmissible ones (target beyond
    # the pointer) are closed by [discriminate Hok] (trans_ok = false).
    # [first] finds the matching exact regardless of branch order.
    exacts = '\n      '.join(
        f"{'[' if i == 0 else '|'} exact gggh_{unit}_{ft_of(*f)}_decided"
        for i, f in enumerate(fl)) + "\n      | discriminate Hok ]"
    repl = f"""(** GENERATED by tools/gen_gsplit_deeper.py -- REPLACES the
    monolithic {unit} walk (too heavy for the preemption window) with an
    assembly of {nfill} deeper sub-walks, proving the SAME lemma
    {sp['declemma']}. *)
From Coq Require Import Arith List.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import TNF_QH Decide Deferred_Data Run Run_Split.
From BBB4.Census Require Import {sp['imp']} Run_Split_{unit}.
{imports}
Import ListNotations.

Lemma {sp['declemma']} :
  NodeDecided B_census D_census (node_tm ({sp['parent']})).
Proof.
  apply cover_{unit}.
  intros w4 d4 nx4 Hok.
  destruct w4, d4, nx4;
    first
      {exacts}.
Qed.
"""
    open(os.path.join(outdir, f"{unit}.v"), 'w').write(repl)
    return unit, k2, quC, suC, nfill, pptrC


def main():
    args = sys.argv[1:]
    niter = 700
    if '--niter' in args:
        i = args.index('--niter')
        niter = int(args[i + 1])
        del args[i:i + 2]
    outdir = args[0]
    units = args[1:]
    os.makedirs(outdir, exist_ok=True)
    for u in units:
        u = os.path.basename(u).replace('.v', '')
        tag, k2, quC, suC, nfill, pptrC = gen_one(outdir, u, niter)
        print(f"{tag}: hole {quC}/{suC} step {k2}, ptr {pptrC}, {nfill} fills")


if __name__ == "__main__":
    main()
