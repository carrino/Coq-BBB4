#!/usr/bin/env python3
"""Emit the census lookup tiers as DATA-ONLY Coq: Proven_List.v,
ProvenQH_List.v, RerootQH_List.v.

Why.  Every walk unit `Require`s Census/Run.v, which drags in
Census/Proven_Data.v -- and with it the boarded-machine THEOREMS behind
[proven_all], across Machines/Bulk, Machines/ListCStage and the rest.
Measured (docs/CENSUS_RUNTIME.md, 2026-08-09): 5.32 GB and 25 s per
unit, natively, BEFORE the first machine is decided -- 79% of a walk
unit's 6.76 GB peak.  The expensive half of a unit needs those machines
only as DATA, for [dmap_of]; [proven_all] feeds [decider_WF], which only
the millisecond half uses.  The same lists as data cost ~4 MB.

So the lists are emitted here as literal [TM] definitions with no
theorems attached, Census/Run_Compute.v builds the decider from them,
and Census/Run.v re-attaches the certificates by

    Lemma proven_list_nqh : Forall NeverQuasiHaltsSt proven_list
      := Proven_Data.proven_all.

which type-checks ONLY if the two lists are convertible.  That is the
gate, and it is the kernel's, not a sample's: a machine dropped,
duplicated, re-encoded or reordered by this script fails to compile.
Nothing here carries proof weight.

Input is the [tm_enc] positives of the three lists IN LIST ORDER, which
Coq prints for you:

    cat > /tmp/Extract.v <<'EOF'
    From Coq Require Import List PArith.
    From BBB4 Require Import BBB4_Statement.
    From BBB4.Census Require Import TNF_QH Decide Proven_Data
                                    ProvenQH_Data RerootQH_Data.
    Set Printing Depth 1000000.
    Set Printing Width 200.
    Definition encs (l : list TM) : list positive := map tm_enc l.
    Eval vm_compute in (encs proven_list).
    Eval vm_compute in (encs provenqh_list).
    Eval vm_compute in (encs reroot_qh_list).
    EOF
    coqc -Q theories BBB4 /tmp/Extract.v > /tmp/encs.log
    python3 tools/gen_census_lists.py /tmp/encs.log

The three `Eval`s must appear in that order.  Decoding mirrors
tools/dec_tm_enc.py; emission mirrors the shape Machines/Bulk already
uses, so a re-emitted machine is syntactically identical to the one its
theorem is about.

Re-run this whenever a board is added to any of the three tiers -- the
same run that regenerates Proven_Data.v / ProvenQH_Data.v /
RerootQH_Data.v.  If you forget, Run.v stops compiling; it cannot go
wrong quietly.
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DIRS = {'L': 'DL', 'R': 'DR'}

# (data list name, file, what it is, where its certificate lives, the
#  certificate's name).  The data lists are named apart from the board
#  lists deliberately: both are in scope in Run.v, and the whole point is
#  that the kernel compares them rather than a notation hiding one.
OUT = [
    ('proven_list_data', 'Proven_List.v', 'the R_NeverQH lookup tier',
     'Census/Proven_Data.v', 'proven_all'),
    ('provenqh_list_data', 'ProvenQH_List.v',
     'the R_QH proven-quasihalting tier',
     'Census/ProvenQH_Data.v', 'provenqh_all'),
    ('reroot_qh_list_data', 'RerootQH_List.v', 'the R_QH re-root tier',
     'Census/RerootQH_Data.v', 'reroot_qh_all'),
]


def dec_slot(c):
    if c == 0:
        return '---'
    c -= 1
    w, d, st = c & 1, (c >> 1) & 1, c >> 2
    return f"{w}{'R' if d else 'L'}{chr(65 + st)}"


def dec(v):
    """tm_enc positive -> machine text (tools/dec_tm_enc.py, verbatim)."""
    v -= 1                                    # N.succ_pos
    slots = []
    for _ in range(8):
        slots.append(v % 17)
        v //= 17
    slots.reverse()
    return '_'.join(dec_slot(slots[2 * i]) + dec_slot(slots[2 * i + 1])
                    for i in range(4))


def tm_def(name, m):
    """Machine text -> the TM definition, in Machines/Bulk's exact shape."""
    lines = [f"Definition {name} : TM := fun q s =>", "  match q, s with"]
    for qi, part in enumerate(m.split('_')):
        for si in range(2):
            e = part[3 * si:3 * si + 3]
            pat = f"St{chr(65 + qi)}, S{si}"
            if e == '---':
                lines.append(f"  | {pat} => None")
            else:
                w, d, n = e[0], e[1], e[2]
                lines.append(
                    f"  | {pat} => Some (mkTrans S{w} {DIRS[d]} St{n})")
    lines.append("  end.")
    return "\n".join(lines)


def parse(log_path):
    """The three printed [list positive] bodies, in order."""
    txt = open(log_path).read()
    bodies = re.findall(r'=\s*\[([^\]]*)\]\s*:\s*list positive', txt,
                        re.S)
    if len(bodies) != 3:
        sys.exit(f"{log_path}: found {len(bodies)} `list positive' results, "
                 f"expected 3 (proven, provenqh, reroot -- in that order)")
    out = []
    for b in bodies:
        vals = [int(x) for x in re.findall(r'(\d+)%positive', b)]
        if not vals:
            sys.exit(f"{log_path}: a result list parsed as empty")
        out.append(vals)
    return out


def emit(list_name, fname, what, data_src, cert, encs, outdir):
    seen, dups = set(), 0
    for v in encs:
        if v in seen:
            dups += 1
        seen.add(v)
    body = [f'''(** GENERATED by tools/gen_census_lists.py -- do not edit.

    {what}, as DATA: the machines of [{list_name}] with no theorems
    attached, so the census walk units can build their lookup maps
    without loading the boards.  {data_src} keeps the certificate
    ([{cert}]) and Census/Run.v re-attaches it to THIS list -- a
    type-check that fails if the two ever differ, which is the only
    thing keeping the two in step.  Order is [{list_name}]'s own.

    {len(encs)} machines.  Untrusted generated data; the kernel checks it. *)
From Coq Require Import List.
From BBB4 Require Import BBB4_Statement.
Import ListNotations.
''']
    names = []
    stem = list_name.replace('_list_data', '')
    for i, v in enumerate(encs):
        nm = f"tm_{stem}_{i:05d}"
        m = dec(v)
        body.append(f"(* {m} *)")
        body.append(tm_def(nm, m))
        names.append(nm)
    # CHUNKED, not one flat literal.  A single [a; b; ...] of 5,270
    # elements is a 5,270-deep cons chain and `coqnative' recurses over
    # the term, so it dies with "Fatal error: exception Stack overflow"
    # (seen 2026-08-10 on the census opam switch).  Plain `coqc' takes
    # it happily, which is exactly why this is invisible on a build
    # without a native compiler -- do not "simplify" it back.
    #
    # 250 is chosen against a demonstrated-safe depth, not a guess: the
    # boards this list mirrors already reach [proven_list] through
    # 500-element literals (Census/Proven_00..07, CHUNK = 500 in
    # gen_proven.py), and those compile natively today.
    #
    # The list VALUE is unchanged: [++] applied to literals reduces to
    # the same cons chain, so Run.v's convertibility gate still sees one
    # list.  Verified, not assumed -- Run.v compiles (22.9 s, 3.16 GB).
    CH = 250
    chunks = [names[i:i + CH] for i in range(0, len(names), CH)]
    for k, ch in enumerate(chunks):
        body.append(f"Definition {list_name}_{k:03d} : list TM :=")
        body.append("  [" + ";\n   ".join(ch) + "].")
        body.append("")
    body.append(f"Definition {list_name} : list TM :=")
    body.append("  " + " ++\n  ".join(f"{list_name}_{k:03d}"
                                      for k in range(len(chunks))) + ".")
    path = os.path.join(outdir, fname)
    with open(path, 'w') as f:
        f.write("\n".join(body) + "\n")
    note = f"  ({dups} repeated encodings -- kept, the list is order-exact)" \
        if dups else ""
    print(f"wrote {path}: {len(encs)} machines{note}", file=sys.stderr)


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    log = sys.argv[1]
    outdir = sys.argv[2] if len(sys.argv) > 2 \
        else os.path.join(ROOT, 'theories', 'Census')
    lists = parse(log)
    for (list_name, fname, what, src, cert), encs in zip(OUT, lists):
        emit(list_name, fname, what, src, cert, encs, outdir)
    return 0


if __name__ == '__main__':
    sys.exit(main())
