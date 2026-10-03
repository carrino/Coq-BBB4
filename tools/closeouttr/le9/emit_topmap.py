#!/usr/bin/env python3
"""UNTRUSTED emitter (SCOPING_INSTR 7.4.LE9): a binary counter whose top
transitions are a map G on (phase, width, run) -> a Coq board closed by
[TopMapTr].

Each row is a record in ROWS below: the anchor, the digit words, the arm
forms (LE8's arm search, [emit_nest.Gen]) and the row's own Coq for the
tails, the map G, the invariant, the top transitions (by the arm lemmas)
and the macro recurrence (a hand proof: which phase the macro dynamics
revisit).  The fires are read off one arm family, at the tops of one phase.

    python3 emit_topmap.py SPEC -o OUT.v [--qh]
"""
import argparse
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'le8'))
sys.path.insert(0, os.path.join(HERE, '..', 'le3'))
import emit_nest as N  # noqa: E402
from emit_nest import E, NoClosure, F, Gen, nvisits_f, ST, SYM  # noqa: E402
from emit_step import inner_coq, coq_chain_l, coq_seg, clist  # noqa: E402
from csim import parse as csim_parse  # noqa: E402

# ---------------------------------------------------------------- the rows
#
# 1RB0RD_1LB1LC_1RC0RA_0LB1RD: at D0 with the counter on the left, a binary
# COUNTDOWN over 11 / 00 (read as an up-counter, 0 = 11, 1 = 00), three
# phases: W (tail (01)^m, m odd: the top widens x two digits into the run,
# m - 2; at m = 1 one digit and the tail becomes 1), X (tail 1: the top
# narrows x to the tail 1001), N (tail 1001 (01)^m: the top narrows x and
# the run grows; an empty x restarts W at x = [1;0], m + 1).
CD3 = dict(
    q='D', side='L', fix=(), Z=(1, 1), O=(0, 0),
    fires=[('X', 'fun k m p => p = 1',
            'intros k m p -> Hi. destruct Hi as [a ->]. replace (2 * a + 1) with (S (2 * a)) by lia. '
            'exact (%(fire)s (2 * a) []).', 'trecX'),
           ('N0', 'fun k m p => p = 2 /\\ k = 0',
            'intros k m p [-> ->] _. exact (%(fire)s m []).', 'trecN0')],
    arms=[
        ('carry', [('c', (0,)), ('r', (0, 0), 0), ('c', (1, 1)), ('X',)],
                  [('c', (0,)), ('r', (1, 1), 0), ('c', (0, 0)), ('X',)]),
        ('W3', [('c', (0,)), ('r', (0, 0), 0), ('c', (0, 1, 0, 1)), ('X',)],
               [('c', (0,)), ('r', (1, 1), 0), ('c', (0, 0, 1, 1)), ('X',)]),
        ('W1', [('c', (0,)), ('r', (0, 0), 0), ('c', (0, 1))],
               [('c', (0,)), ('r', (1, 1), 0), ('c', (0, 0, 1))]),
        ('X', [('c', (0,)), ('r', (0, 0), 1), ('c', (1,))],
              [('c', (0,)), ('r', (1, 1), 0), ('c', (1, 0, 0, 1))]),
        ('N1', [('c', (0,)), ('r', (0, 0), 1), ('c', (1, 0, 0, 1)), ('X',)],
               [('c', (0,)), ('r', (1, 1), 0), ('c', (1, 0, 0, 1, 0, 1)), ('X',)]),
        ('N0', [('c', (0, 1, 0, 0, 1)), ('r', (0, 1), 0)],
               [('c', (0, 0, 0, 1, 1, 0, 1)), ('r', (0, 1), 0)]),
    ],
    coq=r"""
Definition tbase_%(mid)s (l : list Sym) : cconf := cfgL StD (S0 :: l) [].
Definition ttail_%(mid)s (p m : nat) : list Sym :=
  match p with
  | 0 => rep [S0;S1] m
  | 1 => [S1]
  | _ => [S1;S0;S0;S1] ++ rep [S0;S1] m
  end.
Definition tG_%(mid)s (p k m : nat) : list bool * nat * nat :=
  match p with
  | 0 => match m with
         | 0 => ([], 0, 0)
         | 1 => (repeat false k ++ [true], 0, 1)
         | S (S m') => (repeat false k ++ [true; false], m', 0)
         end
  | 1 => (repeat false (pred k), 0, 2)
  | _ => match k with
         | 0 => ([true; false], S m, 0)
         | S k' => (repeat false k', S m, 2)
         end
  end.
Definition tInv_%(mid)s (k m p : nat) : Prop :=
  match p with
  | 0 => (exists a, k = 2 * a) /\ (exists b, m = 2 * b + 1)
  | 1 => exists a, k = 2 * a + 1
  | 2 => exists a, k + m = 2 * a
  | _ => False
  end.

Local Notation BASE := tbase_%(mid)s.
Local Notation TAIL := ttail_%(mid)s.
Local Notation GG := tG_%(mid)s.
Local Notation INV := tInv_%(mid)s.

Lemma tcarry_%(mid)s : forall k X,
  Reach1 tm (BASE (rep [S0;S0] k ++ [S1;S1] ++ X)) (BASE (rep [S1;S1] k ++ [S0;S0] ++ X)).
Proof. intros k X. exact (%(carry)s k X). Qed.

Lemma ttop_%(mid)s : forall p k m, INV k m p ->
  Reach1 tm (BASE (rep [S0;S0] k ++ TAIL p m)) (tcfg BASE [S1;S1] [S0;S0] TAIL (GG p k m)).
Proof.
  intros p k m Hi. destruct p as [|[|[|p]]]; cbn [tInv_%(mid)s] in Hi; [| | |contradiction].
  - destruct Hi as [_ [b Hb]]. destruct m as [|[|m']]; [lia| |].
    + cbn [tG_%(mid)s ttail_%(mid)s tcfg]. rewrite bcells_app, bcells_rep_false, <- !app_assoc.
      exact (%(W1)s k []).
    + cbn [tG_%(mid)s ttail_%(mid)s tcfg]. rewrite bcells_app, bcells_rep_false, <- !app_assoc.
      exact (%(W3)s k (rep [S0;S1] m')).
  - destruct Hi as [a ->]. replace (2 * a + 1) with (S (2 * a)) by lia.
    cbn [tG_%(mid)s ttail_%(mid)s tcfg pred]. rewrite bcells_rep_false.
    exact (%(X)s (2 * a) []).
  - destruct k as [|k'].
    + cbn [tG_%(mid)s ttail_%(mid)s tcfg]. exact (%(N0)s m []).
    + cbn [tG_%(mid)s ttail_%(mid)s tcfg]. rewrite bcells_rep_false.
      exact (%(N1)s k' (rep [S0;S1] m)).
Qed.

Lemma tGinv_%(mid)s : forall p k m, INV k m p -> TInv INV (GG p k m).
Proof.
  intros p k m Hi. destruct p as [|[|[|p]]]; cbn [tInv_%(mid)s] in Hi; [| | |contradiction].
  - destruct Hi as [[a Ha] [b Hb]]. destruct m as [|[|m']]; [lia| |].
    + cbn [tG_%(mid)s TInv tInv_%(mid)s]. rewrite app_length, repeat_length. exists a. cbn. lia.
    + cbn [tG_%(mid)s TInv tInv_%(mid)s]. rewrite app_length, repeat_length.
      split; [exists (S a); cbn; lia | exists (b - 1); lia].
  - destruct Hi as [a Ha]. cbn [tG_%(mid)s TInv tInv_%(mid)s]. rewrite repeat_length.
    exists a. lia.
  - destruct Hi as [a Ha]. destruct k as [|k'].
    + cbn [tG_%(mid)s TInv tInv_%(mid)s length]. split; [exists 1; reflexivity | exists a; lia].
    + cbn [tG_%(mid)s TInv tInv_%(mid)s]. rewrite repeat_length. exists a. lia.
Qed.

Local Notation MI := (miter GG).

Lemma tmacro_W_%(mid)s : forall b k, (exists a, k = 2 * a) ->
  exists n, snd (MI (k, 2 * b + 1, 0) n) = 1.
Proof.
  induction b as [|b IH]; intros k [a Ha].
  - exists 1. reflexivity.
  - assert (Hk2 : exists a', k + 2 = 2 * a') by (exists (S a); lia).
    destruct (IH (k + 2) Hk2) as (n & Hn).
    exists (S n). cbn [miter macro tG_%(mid)s].
    replace (2 * S b + 1) with (S (S (2 * b + 1))) by lia. cbn [tG_%(mid)s].
    rewrite app_length, repeat_length. cbn [length]. exact Hn.
Qed.

Lemma tmacro_N_%(mid)s : forall k m, (exists a, k + m = 2 * a) ->
  exists n, snd (MI (k, m, 2) n) = 0 /\ (exists b, m + k + 1 = 2 * b + 1) /\
            MI (k, m, 2) n = (2, m + k + 1, 0).
Proof.
  induction k as [|k IH]; intros m [a Ha].
  - exists 1. split; [reflexivity|]. split; [exists a; lia|]. cbn. f_equal. f_equal. lia.
  - assert (Ha' : exists a', k + S m = 2 * a') by (exists a; lia).
    destruct (IH (S m) Ha') as (n & H1 & H2 & H3).
    exists (S n). cbn [miter macro tG_%(mid)s]. rewrite repeat_length.
    split; [exact H1|]. replace (m + S k + 1) with (S m + k + 1) by lia. split; [exact H2 | exact H3].
Qed.

Lemma treach_X_%(mid)s : forall k m p, INV k m p -> exists n, snd (MI (k, m, p) n) = 1.
Proof.
  intros k m p Hi. destruct p as [|[|[|p]]]; cbn [tInv_%(mid)s] in Hi; [| | |contradiction].
  - destruct Hi as [Hk [b ->]]. exact (tmacro_W_%(mid)s b k Hk).
  - exists 0. reflexivity.
  - destruct (tmacro_N_%(mid)s k m Hi) as (n1 & _ & [b Hb] & H3).
    assert (H2e : exists a', 2 = 2 * a') by (exists 1; reflexivity).
    destruct (tmacro_W_%(mid)s b 2 H2e) as (n2 & Hn2).
    exists (n1 + n2). rewrite miter_add, H3, Hb. exact Hn2.
Qed.

Lemma tmacro_N0_%(mid)s : forall k m, MI (k, m, 2) k = (0, m + k, 2).
Proof.
  induction k as [|k IH]; intros m.
  - cbn. rewrite Nat.add_0_r. reflexivity.
  - cbn [miter macro tG_%(mid)s]. rewrite repeat_length, IH. f_equal. f_equal. lia.
Qed.

Lemma trecX_%(mid)s : forall k m p, INV k m p ->
  exists n, let '(k', m', p') := MI (k, m, p) n in p' = 1.
Proof.
  intros k m p Hi. destruct (treach_X_%(mid)s k m p Hi) as (n & Hn). exists n.
  destruct (MI (k, m, p) n) as [[k' m'] p']. exact Hn.
Qed.

Lemma trecN0_%(mid)s : forall k m p, INV k m p ->
  exists n, let '(k', m', p') := MI (k, m, p) n in p' = 2 /\ k' = 0.
Proof.
  intros k m p Hi. destruct (treach_X_%(mid)s k m p Hi) as (n & Hn).
  destruct (MI (k, m, p) n) as [[k1 m1] p1] eqn:E1. cbn [snd] in Hn. subst p1.
  exists (n + (1 + pred k1)). rewrite miter_add, E1, miter_add.
  cbn [miter macro tG_%(mid)s]. rewrite repeat_length, tmacro_N0_%(mid)s. split; reflexivity.
Qed.
""",
)

ROWS = {'1RB0RD_1LB1LC_1RC0RA_0LB1RD': CD3}


def find_boot(spec, r, lastf, steps=400000):
    """the first anchor visit past a few thousand steps (the tcfg is matched
    exactly in Coq; the Python side only needs the time and a TInv-state,
    read by the row's own parser)"""
    raise NotImplementedError


FIRE = """Definition %(b)s_vis (r : nat) (t : Instr) : list lstep :=
  match r, t with
  %(vb)s
  | _, _ => []
  end.

Definition %(b)s_vsegs (r : nat) (t : Instr) : list nseg :=
  match r, t with
  %(sb)s
  | _, _ => []
  end.

"""

FIRE1 = """Lemma %(nm)s_vis : forall r, r < %(n0)d + %(st)d ->
  nfire tm %(el)s %(er)s nrules (%(b)s_vsegs r (%(q)s, %(s)s)) (%(b)s_vis r (%(q)s, %(s)s))
    (lr_lhs (%(b)s r)) = Some (%(q)s, %(s)s).
Proof. intros r Hr.
%(br)s  exfalso; lia.
Qed.

Lemma %(nm)s : forall (n : nat) (X : list Sym), Fires tm %(f0)s (%(q)s, %(s)s).
Proof.
  intros n X.
  pose proof (%(lemma)s tm %(el)s %(er)s nrules %(n0)d %(st)d (fun r => %(b)s_vsegs r (%(q)s, %(s)s))
           (fun r => %(b)s_vis r (%(q)s, %(s)s)) (fun r => lr_lhs (%(b)s r)) _ _ _ _ _ _ _
           ltac:(lia) nrules_sound_%(mid)s %(nm)s_vis %(b)s_lhs n %(xa)s %(flag)s) as Hx.
  rewrite ?app_nil_r in Hx. exact Hx.
Qed.

"""


def parse_state(r, cells, side):
    """(x, m, p) of a head-out cell string for the CD3-like rows, or None"""
    Z = ''.join(map(str, r['Z']))
    O = ''.join(map(str, r['O']))
    x = []
    i = 0
    while cells[i:i + 2] in (Z, O) and len(cells[i:i + 2]) == 2:
        x.append(cells[i:i + 2] == O)
        i += 2
        rest = cells[i:]
        for p, pre in ((2, '1001'), (1, '1'), (0, '')):
            t = rest
            if not t.startswith(pre):
                continue
            t = t[len(pre):]
            if p == 1 and t.strip('0') == '':
                return x, 0, 1
            if p != 1:
                m = 0
                while t.startswith('01'):
                    t = t[2:]
                    m += 1
                if t.strip('0') == '':
                    return x, m, p
    return None


def emit_closure_topmap(cert, tab, mid):
    r = cert['row']
    g = Gen(tab, mid, E.TR_PINS)
    vtab = {k: (None if k in E.TR_PINS else v) for k, v in csim_parse(cert['spec']).items()}
    names = {}
    forms = {}
    try:
        for key, a, b in r['arms']:
            fa = F(r['q'], r['side'], r['fix'], a)
            fb = F(r['q'], r['side'], r['fix'], b)
            N.validate(vtab, fa, fb, key)
            names[key] = g.arm(fa, fb, key)
            forms[key] = fa
    except NoClosure as e:
        return E.CLOSURE_NONE % e, None
    out = []
    which = {}
    for key, qd, tac, rec in r['fires']:
        fid = forms[key]
        fd = [x for x in g.firefams if x['form'] == fid][0]
        vis = {rr: nvisits_f(tab, g.want, fd['el'], fd['er'], c0, chp) for rr, c0, c1, chp in fd['arms']}
        mine = [w for w in g.want if w not in which and all(w in vis[rr] for rr in vis)]
        if not mine:
            continue
        b = fd['base']
        out.append(FIRE % dict(
            b=b,
            vb='\n  '.join('| %d, (%s, %s) => %s' % (rr, ST[w[0]], SYM[w[1]], coq_chain_l(vis[rr][w][1]))
                           for rr in sorted(vis) for w in mine),
            sb='\n  '.join('| %d, (%s, %s) => [%s]' % (rr, ST[w[0]], SYM[w[1]],
                                                      '; '.join(coq_seg(sg, 0) for sg in vis[rr][w][0]))
                           for rr in sorted(vis) for w in mine)))
        br = ''.join('  destruct r as [|r].\n  { vm_compute; reflexivity. }\n' for _ in range(fd['n0'] + fd['st']))
        for w in mine:
            nm = 'fire_%s%d_%s' % ('ABCD'[w[0]], w[1], mid)
            which[w] = (qd, tac % dict(fire=nm), rec)
            out.append(FIRE1 % dict(nm=nm, n0=fd['n0'], st=fd['st'], el=str(fd['el']).lower(),
                                    er=str(fd['er']).lower(), b=b, q=ST[w[0]], s=SYM[w[1]], br=br, mid=mid,
                                    f0=N.coq_form(fid),
                                    lemma='fire_of_nfire_r' if r['side'] == 'R' else 'fire_of_nfire_l',
                                    xa='X' if N.hasX(fid) else '[]',
                                    flag=('(fun H => False_ind _ (diff_false_true H))' if N.hasX(fid)
                                          else '(fun _ => eq_refl)')))
    miss = [w for w in g.want if w not in which]
    if miss:
        return E.CLOSURE_NONE % NoClosure('no fire witness for %s' % miss), None
    body = r['coq'] % dict(mid=mid, **names)
    t0, x0, m0, p0 = cert['boot']
    xs = clist(x0, lambda v: 'true' if v else 'false')
    fire_cases = '\n'.join(
        '  - exists (%s). split.\n    + %s\n    + exact %s_%s.' % (which[w][0], which[w][1], which[w][2], mid)
        for w in g.want)
    tmb = ('tm_%s' % mid) if E.TR_QH is not None else 'tm'
    body += """
Lemma tfire_%(mid)s : forall t, ~ In t pins_%(mid)s -> exists Q : nat -> nat -> nat -> Prop,
  (forall k m p, Q k m p -> INV k m p -> Fires tm (BASE (rep [S0;S0] k ++ TAIL p m)) t) /\\
  (forall k m p, INV k m p -> exists n, let '(k', m', p') := MI (k, m, p) n in Q k' m' p').
Proof.
  intros [q s] Hnp. destruct q, s; try (exfalso; apply Hnp; simpl; tauto).
%(fires)s
Qed.

Lemma tinv0_%(mid)s : TInv INV (%(x0)s, %(m0)d, %(p0)d).
Proof. cbn. %(inv0)s Qed.

Lemma bootl_%(mid)s :
  stepn %(tmb)s %(t0)d InitES = Some (lift (tcfg BASE [S1;S1] [S0;S0] TAIL (%(x0)s, %(m0)d, %(p0)d))).
Proof.
  assert (H : match csteps %(tmb)s %(t0)d c0 with
              | Some c => ceqb c (tcfg BASE [S1;S1] [S0;S0] TAIL (%(x0)s, %(m0)d, %(p0)d))
              | None => false end = true) by (vm_compute; reflexivity).
  destruct (csteps %(tmb)s %(t0)d c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** The machine-level theorem, at the INSTRUCTION level, through
    [TopMapTr.topmap_neverqhtr]. *)
Theorem nqhtr_%(mid)s : NeverQuasiHaltsTr tm_%(mid)s.
Proof.
  exact (topmap_neverqhtr tm_%(mid)s pins_%(mid)s BASE [S1;S1] [S0;S0] TAIL GG INV
           tcarry_%(mid)s ttop_%(mid)s tGinv_%(mid)s tfire_%(mid)s %(x0)s %(m0)d %(p0)d tinv0_%(mid)s
           %(t0)d bootl_%(mid)s).
Qed.
""" % dict(mid=mid, fires=fire_cases, x0=xs, m0=m0, p0=p0, t0=t0, tmb=tmb, inv0=cert['inv0'])
    head = """
(** ** The closure: a binary counter whose tops are a map ([TopMapTr]) *)
From BBB4.Checkers Require Import LadderNest LadderCheckNestTr.
From BBB4.Counters Require Import NestCountTr PhBinCountTr TopMapTr.

"""
    txt = inner_coq(mid, g.inner) + ''.join(g.out) + ''.join(out)
    txt = re.sub(r'exact \(((?:armfam|arm1)_[rl]) (.*?)\)\.\nQed\.',
                 lambda mo: 'pose proof (%s %s) as Hx. rewrite ?app_nil_r in Hx. exact Hx.\nQed.'
                 % (mo.group(1), mo.group(2)), txt, flags=re.S)
    return head + txt + body, dict(nest=True)


def boot(spec, r, steps=400000):
    tab = E.parse_tm(spec)
    q0 = 'ABCD'.index(r['q'])
    tape, h, q = {}, 0, 0
    for t in range(steps):
        s = tape.get(h, 0)
        if q == q0 and s == 0 and t > 3000:
            cs = sorted(i for i, v in tape.items() if v)
            if r['side'] == 'L' and (not cs or cs[-1] < h):
                cells = ''.join(str(tape.get(i, 0)) for i in range(h - 1, (cs[0] if cs else h) - 1, -1))
                st = parse_state(r, cells, 'L')
                if st is not None:
                    return (t,) + st
        w, d, nq = tab[(q, s)]
        tape[h] = w
        h += d
        q = nq
    raise NoClosure('no boot')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('spec')
    ap.add_argument('-o', '--out', required=True)
    a = ap.parse_args()
    spec = a.spec
    r = ROWS[spec]
    E.TR_PINS = E.unfired(spec, 10 ** 6)
    t0, x0, m0, p0 = boot(spec, r)
    k = len(x0)
    inv0 = {0: 'split; [exists %d | exists %d]; reflexivity.' % (k // 2, (m0 - 1) // 2),
            1: 'exists %d. reflexivity.' % ((k - 1) // 2),
            2: 'exists %d. reflexivity.' % ((k + m0) // 2)}[p0]
    cert = dict(spec=spec, closed=True, ladder=[], arms=[], row=r, boot=(t0, x0, m0, p0), inv0=inv0,
                family=dict(state=r['q'], head=0, side=r['side'], other_side_cells=[],
                            digits=[list(r['Z']), list(r['O'])], near_head_prefix=[], terminator=[],
                            terminators_by_phase=[[]], n_phases=1, base=2, digit_len=2,
                            code='binary', value_step_per_anchor_visit=1),
                fill=dict(widens_by=1, target_prefix=[], target_fill_digit=0, target_suffix=[],
                          lands_in_phase=0))
    E.emit_closure = emit_closure_topmap
    good, bad, cd = E.emit(cert, a.out)
    print('%s: closure %s' % (a.out, 'BUILT' if cd else 'not built'))
    return 0 if cd else 1


if __name__ == '__main__':
    sys.exit(main())
