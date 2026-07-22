#!/usr/bin/env python3
"""Emit the census PROVEN-QH tier: the R_QH sibling of the proven tier.

For each input machine, find a census-grade QHBound certificate and emit
a per-machine theorem

  qhb_G : NonHalt tm
          /\ (forall q' s', QuietAfter tm q' s' -> S s' <= S t)   (* QHBound (S t) *)
          /\ QuasiHaltsSt tm

closed by vm_compute.  Two gates are tried, PLAIN first:

  - PLAIN acyclicity liveness (sweep_qhbound_residue.find_qhbound ->
    ngram_check_qhbound_sound, theories/Checkers/Wrap.v);
  - LEX measure liveness (gen_qhbound_lex.find_lex ->
    ngram_check_qhbound_lex_sound, with a per-state ngcomp certificate).

Both conclude the SAME shape, so the assembly is gate-agnostic.  Machines
that fall to neither gate are reported UNCAUGHT and skipped.

Output, in lockstep 1:1 chunks (default 100 machines/chunk):

  theories/Machines/QHBoard/QHB_XX.v      -- the machine theorems
  theories/Census/ProvenQH_XX.v           -- [provenqh_XX] + its Forall cert
  theories/Census/ProvenQH_Data.v         -- [provenqh_list] + [provenqh_all]
  tools/provenqh_map.tsv                   -- machine -> theorem/file/gate

Everything under tools/ is UNTRUSTED: the generated Coq is re-checked by
the kernel; soundness rests only on the [ngram_check_qhbound(_lex)_sound]
vm_compute type-checks and the [Forall ...] statements, never on this
script.

Usage: gen_provenqh.py PARAMS_TXT [PER_FILE] [LIMIT] [JOBS]
  PARAMS_TXT: one machine string per line ('#' comments skipped).
"""
import itertools
import os
import sys
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import bulk_prover as bp            # noqa: E402
import gen_bulk_certs as gb         # noqa: E402
import sweep_qhbound_residue as sq  # noqa: E402

B_PQ = 2000  # census score bound (B_census); every emitted t stays < B_PQ

# richer lex search than gen_qhbound_lex (count-of-1s only): the full
# pattern-measure vocabulary, count-of-1s FIRST so easy machines keep small
# certs and only the hard ones reach for patterns.
_CAND_CACHE = {}


def rich_cands(n):
    if n in _CAND_CACHE:
        return _CAND_CACHE[n]
    cands = [c for c in bp.DEFAULT_MEASURES if bp.meas_ok(c[0], c[1], n)]
    seen = set(cands)
    for reg in ('A', 'L', 'R'):
        maxlen = n + 1 if reg == 'A' else n
        for L in range(1, maxlen + 1):
            for bits in itertools.product((0, 1), repeat=L):
                if 1 not in bits:
                    continue
                key = (bits, reg)
                if key in seen or not bp.meas_ok(bits, reg, n):
                    continue
                seen.add(key)
                cands.append(key)
    _CAND_CACHE[n] = cands
    return cands


def grown_closure(tbl, qq, n, t, cap=200000):
    """The wrapped n-gram closure with the sets GROWN to a fixpoint --
    mirrors the Coq checker's [ng_grow] (theories/Checkers/Wrap.v).  This
    is what gen_residue_wrap.closure_sizes computes; sweep_qhbound_residue's
    non-growing variant under-approximates and fails on machines that need
    growth (e.g. most of listB).  Returns (seen, lset, rset, tw) or None."""
    tape = {}
    pos = 0
    q = 0
    for _ in range(t):
        tr = tbl[(q, tape.get(pos, 0))]
        if tr is None:
            return None
        w, d, nq = tr
        tape[pos] = w
        pos += 1 if d == "R" else -1
        q = nq
    if q == qq:
        return None
    tw = dict(tbl)
    tw[(qq, 0)] = None
    tw[(qq, 1)] = None
    minp = min([pos] + list(tape))
    maxp = max([pos] + list(tape))
    Lf = lambda i: tape.get(pos - 1 - i, 0)
    Rf = lambda i: tape.get(pos + 1 + i, 0)
    win = lambda f, d: tuple(f(d + i) for i in range(n))
    depth = max(pos - minp, maxp - pos) + n + 2
    lset = {win(Lf, d) for d in range(1, depth)}
    rset = {win(Rf, d) for d in range(1, depth)}
    a0 = (q, tape.get(pos, 0), win(Lf, 0), win(Rf, 0))
    for _ in range(400):
        seen = set()
        todo = [a0]
        while todo:
            a = todo.pop()
            if a in seen:
                continue
            seen.add(a)
            if len(seen) > cap:
                return None
            q1, s1, lw, rw = a
            tr = tw[(q1, s1)]
            if tr is None:
                continue
            w, d, q2 = tr
            if d == "R":
                for x in (0, 1):
                    rw2 = rw[1:] + (x,)
                    if rw2 in rset:
                        todo.append((q2, rw[0], (w,) + lw[:-1], rw2))
            else:
                for x in (0, 1):
                    lw2 = lw[1:] + (x,)
                    if lw2 in lset:
                        todo.append((q2, lw[0], lw2, (w,) + rw[:-1]))
        newl = {a[2] for a in seen if tw[(a[0], a[1])] and tw[(a[0], a[1])][1] == "R"}
        newr = {a[3] for a in seen if tw[(a[0], a[1])] and tw[(a[0], a[1])][1] == "L"}
        if newl <= lset and newr <= rset:
            # qq must not recur (else the wrapped machine halts inside the
            # closure -- not a bounded quiet state)
            if any(a[0] == qq for a in seen):
                return None
            return seen, lset, rset, tw
        lset |= newl
        rset |= newr
    return None


def find_lex_rich(m, cand_n=(2, 3, 4), cand_t=(64, 256, 1024)):
    """gen_qhbound_lex.find_lex, but growing-closure + full pattern vocab."""
    tbl = bp.parse(m)
    tape = {}
    pos = 0
    q = 0
    vis = set()
    for _ in range(1024):
        vis.add(q)
        tr = tbl[(q, tape.get(pos, 0))]
        if tr is None:
            break
        w, d, nq = tr
        tape[pos] = w
        pos += 1 if d == 'R' else -1
        q = nq
    for qq in sorted(vis, key=lambda x: (x == 0, x)):
        for n in cand_n:
            cands = rich_cands(n)
            for t in cand_t:
                r = grown_closure(tbl, qq, n, t)
                if r is None:
                    continue
                seen, lset, rset, tw = r
                comps_by_state = {}
                ok = True
                for qq2 in set(a[0] for a in seen):
                    comps = bp.procedure(tw, n, seen, lset, rset, qq2, cands)
                    if comps is None:
                        ok = False
                        break
                    good, _ = bp.lex_check(tw, n, seen, lset, rset, qq2, comps)
                    if not good:
                        ok = False
                        break
                    comps_by_state[qq2] = comps
                if not ok:
                    continue
                tp = {}
                p = 0
                qc = 0
                s = None
                for i in range(t):
                    if qc == qq:
                        s = i
                    w, d, nq = tbl[(qc, tp.get(p, 0))]
                    tp[p] = w
                    p += 1 if d == 'R' else -1
                    qc = nq
                if s is None or s >= t:
                    continue
                return qq, s, n, t, seen, lset, rset, comps_by_state
    return None

MACH_HEADER = """(** GENERATED by tools/gen_provenqh.py -- DO NOT EDIT.

    Census-grade quasihalting theorems (NonHalt /\\ QHBound (S t) /\\
    QuasiHaltsSt, the middle conjunct stated unfolded so this stays in the
    Machines layer) for the proven-QH census tier.  Each is closed by
    ngram_check_qhbound_sound (PLAIN gate) or ngram_check_qhbound_lex_sound
    (LEX gate) from theories/Checkers/Wrap.v. *)

From Coq Require Import List ZArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import NGram Wrap.
Import ListNotations.
"""


def _last_visit(tbl, qq, t):
    """last-visit index of state qq strictly before step t, or None."""
    tp = {}
    p = 0
    qc = 0
    s = None
    for i in range(t):
        if qc == qq:
            s = i
        w, d, nq = tbl[(qc, tp.get(p, 0))]
        tp[p] = w
        p += 1 if d == 'R' else -1
        qc = nq
    return s if (s is not None and s < t) else None


def find_plain(m, cand_n=(2, 3, 4), cand_t=(64, 256, 1024)):
    """PLAIN acyclicity gate over the GROWING closure."""
    tbl = bp.parse(m)
    tape = {}
    pos = 0
    q = 0
    vis = set()
    for _ in range(1024):
        vis.add(q)
        tr = tbl[(q, tape.get(pos, 0))]
        if tr is None:
            break
        w, d, nq = tr
        tape[pos] = w
        pos += 1 if d == 'R' else -1
        q = nq
    for qq in sorted(vis, key=lambda x: (x == 0, x)):
        for n in cand_n:
            for t in cand_t:
                r = grown_closure(tbl, qq, n, t)
                if r is None:
                    continue
                if not sq.live_ok(*r):
                    continue
                s = _last_visit(tbl, qq, t)
                if s is None:
                    continue
                seen, lset, rset, tw = r
                return qq, s, n, t, seen, lset, rset
    return None


def find_cert(m):
    """Return a dict describing a QHBound cert for machine m, or None.

    PLAIN: {gate:'plain', m, qq, s, n, t, fuel, rounds}
    LEX:   {gate:'lex',   m, qq, s, n, t, fuel, rounds, comps_by_state}
    """
    # PLAIN gate (growing closure)
    r = find_plain(m)
    if r is not None:
        qq, s, n, t, seen, lset, rset = r
        return dict(gate='plain', m=m, qq=qq, s=s, n=n, t=t,
                    fuel=8 * len(seen) + 64, rounds=len(lset) + len(rset) + 4)
    # LEX gate (full pattern vocabulary)
    lr = find_lex_rich(m)
    if lr is not None:
        qq, s, n, t, seen, lset, rset, comps_by_state = lr
        return dict(gate='lex', m=m, qq=qq, s=s, n=n, t=t,
                    fuel=8 * len(seen) + 64, rounds=len(lset) + len(rset) + 4,
                    comps_by_state=comps_by_state)
    return None


def _work(m):
    try:
        return find_cert(m)
    except Exception as e:  # noqa
        return None


def emit_theorem(gi, c):
    """Return the Coq source for one machine's TM + theorem."""
    m, qq, s, n, t = c['m'], c['qq'], c['s'], c['n'], c['t']
    fuel, rounds = c['fuel'], c['rounds']
    qs = chr(65 + qq)
    name = "tm_qhb_%05d" % gi
    thm = "qhb_%05d" % gi
    if c['gate'] == 'plain':
        return """(** %s: quiet %s s=%d; PLAIN QHBound %d (n=%d t=%d) *)

%s

Theorem %s :
  NonHalt %s
  /\\ (forall q' s', QuietAfter %s q' s' -> S s' <= S %d)
  /\\ QuasiHaltsSt %s.
Proof.
  apply (ngram_check_qhbound_sound _ St%s %d %d %d %d %d).
  vm_compute. reflexivity.
Qed.""" % (m, qs, s, t, n, t, gb.emit_tm(name, m), thm, name, name, t, name,
           qs, s, n, t, fuel, rounds)
    else:
        cname = "cert_qhb_%05d" % gi
        comps = c['comps_by_state']
        per_state = []
        for qi in range(4):
            cs = comps.get(qi, [])
            body = ("[" + ";\n   ".join(gb.emit_comp(x) for x in cs) + "]") \
                if cs else "[]"
            per_state.append("  | St%s =>\n  %s" % (chr(65 + qi), body))
        return """(** %s: quiet %s s=%d; LEX QHBound %d (n=%d t=%d) *)

%s

Definition %s (q : St) : list ngcomp :=
  match q with
%s
  end.

Theorem %s :
  NonHalt %s
  /\\ (forall q' s', QuietAfter %s q' s' -> S s' <= S %d)
  /\\ QuasiHaltsSt %s.
Proof.
  apply (ngram_check_qhbound_lex_sound _ St%s %d %d %d %d %d %s).
  vm_compute. reflexivity.
Qed.""" % (m, qs, s, t, n, t, gb.emit_tm(name, m), cname,
           "\n".join(per_state), thm, name, name, t, name,
           qs, s, n, t, fuel, rounds, cname)


PRED = "(fun tm => NonHalt tm /\\ QHBound %d tm /\\ QuasiHaltsSt tm)" % B_PQ

PRED_FILE = """(** GENERATED by tools/gen_provenqh.py -- do not edit.

    The proven-QH tier predicate, kept as a NAMED constant so the per-chunk
    [Forall census_qh] proofs stay folded (elaborating the unfolded triple
    at every list node is ~5x slower).  It is definitionally the R_QH
    contract at the census bound; [provenqh_all] converts it to the
    unfolded form once, so Run.v's decider sees the exact shape. *)
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import TNF_QH.

Definition census_qh (tm : TM) : Prop :=
  NonHalt tm /\\ QHBound %d tm /\\ QuasiHaltsSt tm.
""" % B_PQ


def emit_data_chunk(fidx, rows):
    tag = "%02d" % fidx
    L = ["(** GENERATED by tools/gen_provenqh.py -- do not edit.",
         "",
         "    Proven census-grade quasihalters, chunk %s (%d machines)." % (tag, len(rows)),
         "    Each row's [S s' <= S t] theorem is lifted to [census_qh]",
         "    (= [QHBound %d] triple; sound: every t < %d, so S t <= %d)," % (B_PQ, B_PQ, B_PQ),
         "    then the list's [Forall] is one nested [Forall_cons] term",
         "    (O(n), not the O(n^2) apply-loop). *)",
         "From Coq Require Import List Lia.",
         "From BBB4 Require Import BBB4_Statement.",
         "From BBB4.Census Require Import TNF_QH ProvenQH_Pred.",
         "Require Import BBB4.Machines.QHBoard.QHB_%s." % tag,
         "Import ListNotations.",
         ""]
    # per-machine lift lemma: [S s' <= S t]  ->  [census_qh]
    for gi, _c in rows:
        L += ["Lemma cqh_%05d : census_qh tm_qhb_%05d." % (gi, gi),
              "Proof.",
              "  destruct qhb_%05d as (Hnh & Hqb & Hqh);" % gi,
              "  split; [exact Hnh | split;",
              "    [ intros q' s' HQ; specialize (Hqb q' s' HQ); lia",
              "    | exact Hqh ] ].",
              "Qed."]
    L += ["",
          "Definition provenqh_%s : list TM :=" % tag,
          "  [" + ";\n   ".join("tm_qhb_%05d" % gi for gi, _ in rows) + "].",
          ""]
    # the Forall as one nested term (fast: census_qh stays folded)
    term = "(Forall_nil census_qh)"
    for gi, _ in reversed(rows):
        term = "(Forall_cons _ cqh_%05d\n     %s)" % (gi, term)
    L += ["Lemma provenqh_%s_qh : Forall census_qh provenqh_%s." % (tag, tag),
          "Proof.",
          "  unfold provenqh_%s." % tag,
          "  exact",
          "    " + term + ".",
          "Qed.", ""]
    return "\n".join(L)


def emit_data(n_chunks):
    tags = ["%02d" % i for i in range(n_chunks)]
    L = ["(** GENERATED by tools/gen_provenqh.py -- do not edit.",
         "",
         "    The census proven-QH tier: machines with a committed in-Coq",
         "    census-grade quasihalting theorem (NonHalt /\\ QHBound /\\",
         "    QuasiHaltsSt), assembled into one list with its [Forall]",
         "    certificate.  Wired into Census/Run.v's decider as the R_QH",
         "    lookup tier (ahead of the deferred fallthrough). *)",
         "From Coq Require Import List.",
         "From BBB4 Require Import BBB4_Statement.",
         "From BBB4.Census Require Import TNF_QH ProvenQH_Pred.",
         "From BBB4.Census Require Import %s." % " ".join("ProvenQH_" + t for t in tags),
         "Import ListNotations.",
         "",
         "Definition provenqh_list : list TM :=",
         "  " + " ++ ".join("provenqh_" + t for t in tags) + ".",
         "",
         "(* folded [census_qh] form -- proved fast per chunk *)",
         "Lemma provenqh_all_cqh : Forall census_qh provenqh_list.",
         "Proof.",
         "  unfold provenqh_list."]
    for t in tags[:-1]:
        L.append("  apply Forall_app; split; [exact provenqh_%s_qh|]." % t)
    L += ["  exact provenqh_%s_qh." % tags[-1], "Qed.", "",
          "(* unfolded form Run.v's decider expects: one conversion of the",
          "   named predicate to the QHBound triple over the whole list *)",
          "Lemma provenqh_all :",
          "  Forall (fun tm => NonHalt tm /\\ QHBound %d tm /\\ QuasiHaltsSt tm)" % B_PQ,
          "         provenqh_list.",
          "Proof. exact provenqh_all_cqh. Qed.", ""]
    return "\n".join(L)


def main():
    txt = sys.argv[1]
    per_file = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    limit = int(sys.argv[3]) if len(sys.argv) > 3 else None
    jobs = int(sys.argv[4]) if len(sys.argv) > 4 else 2

    machines = []
    with open(txt) as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith("#"):
                machines.append(line)
    if limit:
        machines = machines[:limit]

    with Pool(jobs) as p:
        results = p.map(_work, machines)

    caught = [c for c in results if c is not None]
    uncaught = [m for m, c in zip(machines, results) if c is None]
    for c in caught:
        assert c['t'] < B_PQ, ("t >= B_PQ", c['m'], c['t'])
    # stamp global indices
    sized = [(i + 1, c) for i, c in enumerate(caught)]

    mach_dir = os.path.join(ROOT, "theories/Machines/QHBoard")
    cen_dir = os.path.join(ROOT, "theories/Census")
    os.makedirs(mach_dir, exist_ok=True)

    open(os.path.join(cen_dir, "ProvenQH_Pred.v"), "w").write(PRED_FILE)

    n_chunks = (len(sized) + per_file - 1) // per_file
    manifest = []
    for i in range(n_chunks):
        chunk = sized[i * per_file:(i + 1) * per_file]
        tag = "%02d" % i
        src = MACH_HEADER + "\n\n" + "\n\n".join(
            emit_theorem(gi, c) for gi, c in chunk) + "\n"
        open(os.path.join(mach_dir, "QHB_%s.v" % tag), "w").write(src)
        open(os.path.join(cen_dir, "ProvenQH_%s.v" % tag), "w").write(
            emit_data_chunk(i, chunk))
        for gi, c in chunk:
            manifest.append((c['m'], "qhb_%05d" % gi, "QHB_%s.v" % tag,
                             c['gate'], chr(65 + c['qq']), c['s'], c['n'], c['t']))
        print("wrote QHB_%s.v + ProvenQH_%s.v: %d machines" % (tag, tag, len(chunk)))

    if n_chunks:
        open(os.path.join(cen_dir, "ProvenQH_Data.v"), "w").write(emit_data(n_chunks))
        print("wrote ProvenQH_Data.v: %d chunks, %d machines" % (n_chunks, len(sized)))

    with open(os.path.join(HERE, "provenqh_map.tsv"), "w") as f:
        f.write("machine\ttheorem\tfile\tgate\tquiet_state\ts\tn\tt\n")
        for row in manifest:
            f.write("\t".join(str(x) for x in row) + "\n")
    with open(os.path.join(HERE, "provenqh_uncaught.txt"), "w") as f:
        f.write("\n".join(uncaught) + ("\n" if uncaught else ""))
    print("caught %d / %d  (uncaught %d -> tools/provenqh_uncaught.txt)"
          % (len(caught), len(machines), len(uncaught)))


if __name__ == "__main__":
    main()
