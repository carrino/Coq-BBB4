#!/usr/bin/env python3
"""UNTRUSTED emitter (SCOPING_INSTR 7.4.LE9): a bouncer that doubles its
block each round, [R(n, m) = q | 0 1^n 0 1^m ->+ R(2n, m+1)] -> a Coq board
closed by [DoubleBounceTr] (db_neverqhtr / db_qhtr).

The anchor state [q] is read off the run (the state at the left end with the
head on a blank and the tape [1^n 0 1^m]); the two arm families

    eat  : q | 0 1 (00)^n 1 X   ->  q | 0 1 (00)^n 00 X
    turn : q | 0 1 (00)^n 0 X   ->  q | 0 (11)^n 1101 X

are LE8's arm search ([emit_nest.Gen]); the fires are read off whichever
family fires each instruction at every arm index.

    python3 emit_dbounce.py SPEC -o OUT.v [--qh]
"""
import argparse
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'le8'))
sys.path.insert(0, os.path.join(HERE, '..', 'le3'))
import emit_nest as N  # noqa: E402
from emit_nest import E, NoClosure, F, Gen, nvisits_f, ST, SYM  # noqa: E402
from emit_step import inner_coq, coq_chain_l, coq_seg  # noqa: E402
from csim import parse as csim_parse  # noqa: E402


def find_boot(spec, lastf, steps=400000):
    """(t, q, n, m): the first left-end visit past lastf with tape 1^n 0 1^m, n >= 2"""
    tab = E.parse_tm(spec)
    tape, h, q = {}, 0, 0
    for t in range(steps):
        s = tape.get(h, 0)
        if t > lastf and s == 0:
            cs = sorted(i for i, v in tape.items() if v)
            if cs and cs[0] == h + 1:
                st = ''.join(str(tape.get(i, 0)) for i in range(h + 1, cs[-1] + 1))
                parts = st.split('0')
                if len(parts) == 2 and len(parts[0]) >= 2 and parts[1] and set(parts[1]) == {'1'}:
                    return t, q, len(parts[0]), len(parts[1])
        w, d, nq = tab[(q, s)]
        tape[h] = w
        h += d
        q = nq
    raise NoClosure('no doubling-bouncer anchor')


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
  exact (fire_of_nfire_r tm %(el)s %(er)s nrules %(n0)d %(st)d (fun r => %(b)s_vsegs r (%(q)s, %(s)s))
           (fun r => %(b)s_vis r (%(q)s, %(s)s)) (fun r => lr_lhs (%(b)s r)) _ _ _ _ _ _ _
           ltac:(lia) nrules_sound_%(mid)s %(nm)s_vis %(b)s_lhs n X (fun H => False_ind _ (diff_false_true H))).
Qed.

"""


def emit_closure_db(cert, tab, mid):
    q = cert['dbq']
    g = Gen(tab, mid, E.TR_PINS)
    Q = 'ABCD'[q]
    f_eat0 = F(Q, 'R', [], [('c', (0, 1)), ('r', (0, 0), 0), ('c', (1,)), ('X',)])
    f_eat1 = F(Q, 'R', [], [('c', (0, 1)), ('r', (0, 0), 0), ('c', (0, 0)), ('X',)])
    f_trn0 = F(Q, 'R', [], [('c', (0, 1)), ('r', (0, 0), 0), ('c', (0, 1)), ('X',)])
    f_trn1 = F(Q, 'R', [], [('c', (0,)), ('r', (1, 1), 0), ('c', (1, 1, 0, 1, 1)), ('X',)])
    vtab = {k: (None if k in E.TR_PINS else v) for k, v in csim_parse(cert['spec']).items()}
    try:
        N.validate(vtab, f_eat0, f_eat1, 'eat')
        N.validate(vtab, f_trn0, f_trn1, 'turn')
        eat = g.arm(f_eat0, f_eat1, 'eat')
        trn = g.arm(f_trn0, f_trn1, 'turn')
    except NoClosure as e:
        return E.CLOSURE_NONE % e, None
    fams = {}
    for fd in g.firefams:
        fams[tuple(map(tuple, fd['form']['items']))] = fd
    out = []
    which = {}
    for key, fid in (('eat', f_eat0), ('turn', f_trn0)):
        fd = [x for x in g.firefams if x['form'] == fid]
        if not fd:
            continue
        fd = fd[0]
        vis = {r: nvisits_f(tab, g.want, fd['el'], fd['er'], c0, chp) for r, c0, c1, chp in fd['arms']}
        mine = [w for w in g.want if w not in which and all(w in vis[r] for r in vis)]
        if not mine:
            continue
        b = fd['base']
        out.append(FIRE % dict(
            b=b,
            vb='\n  '.join('| %d, (%s, %s) => %s' % (r, ST[w[0]], SYM[w[1]], coq_chain_l(vis[r][w][1]))
                           for r in sorted(vis) for w in mine),
            sb='\n  '.join('| %d, (%s, %s) => [%s]' % (r, ST[w[0]], SYM[w[1]],
                                                     '; '.join(coq_seg(sg, 0) for sg in vis[r][w][0]))
                           for r in sorted(vis) for w in mine)))
        br = ''.join('  destruct r as [|r].\n  { vm_compute; reflexivity. }\n'
                     for _ in range(fd['n0'] + fd['st']))
        for w in mine:
            nm = 'fire_%s%d_%s' % ('ABCD'[w[0]], w[1], mid)
            which[w] = (key, nm)
            out.append(FIRE1 % dict(nm=nm, n0=fd['n0'], st=fd['st'], el=str(fd['el']).lower(),
                                    er=str(fd['er']).lower(), b=b, q=ST[w[0]], s=SYM[w[1]],
                                    br=br, mid=mid, f0=N.coq_form(fid)))
    miss = [w for w in g.want if w not in which]
    if miss:
        return E.CLOSURE_NONE % NoClosure('no fire witness for %s' % miss), None
    t0, n0, m0 = cert['dbboot']
    cases = '\n'.join('  - %s; intros n X; exact (%s n X).' % ('left' if which[w][0] == 'eat' else 'right',
                                                             which[w][1]) for w in g.want)
    qh = E.TR_QH is not None
    tmb = 'tm_%s' % mid if qh else 'tm'
    body = """Lemma eat_%(mid)s : forall n X,
  Reach1 tm (dbmk %(Q)s ([S1] ++ rep [S0; S0] n ++ [S1] ++ X)) (dbmk %(Q)s ([S1] ++ rep [S0; S0] n ++ [S0; S0] ++ X)).
Proof. intros n X. exact (%(eat)s n X). Qed.

Lemma turn_%(mid)s : forall n X,
  Reach1 tm (dbmk %(Q)s ([S1] ++ rep [S0; S0] n ++ [S0; S1] ++ X)) (dbmk %(Q)s (rep [S1; S1] n ++ [S1; S1; S0; S1; S1] ++ X)).
Proof. intros n X. exact (%(trn)s n X). Qed.

Lemma fire_%(mid)s : forall t, ~ In t pins_%(mid)s ->
  (forall n X, Fires tm (dbmk %(Q)s ([S1] ++ rep [S0; S0] n ++ [S1] ++ X)) t) \\/
  (forall n X, Fires tm (dbmk %(Q)s ([S1] ++ rep [S0; S0] n ++ [S0; S1] ++ X)) t).
Proof.
  intros [q s] Hnp. destruct q, s; try (exfalso; apply Hnp; simpl; tauto).
%(cases)s
Qed.

Lemma bootl_%(mid)s :
  stepn %(tmb)s %(t0)d InitES = Some (lift (dbCf %(Q)s %(n0)d %(m0)d 0)).
Proof.
  assert (H : match csteps %(tmb)s %(t0)d c0 with
              | Some c => ceqb c (dbCf %(Q)s %(n0)d %(m0)d 0)
              | None => false end = true) by (vm_compute; reflexivity).
  destruct (csteps %(tmb)s %(t0)d c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

""" % dict(mid=mid, Q=ST[q], eat=eat, trn=trn, cases=cases, t0=t0, n0=n0, m0=m0, tmb=tmb)
    if qh:
        body += """Lemma wit_%(mid)s :
  existsb (fun tg => cfires tm_%(mid)s c0 %(t0)d tg) pins_%(mid)s = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bnd_%(mid)s : (%(t0)d <=? 32779478) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** The machine-level theorem, on the QUASIHALTING side, through
    [DoubleBounceTr.db_qhtr]. *)
Theorem qhtr_%(mid)s :
  NonHalt tm_%(mid)s /\\ QHBoundTr 32779478 tm_%(mid)s /\\ QuasiHaltsTr tm_%(mid)s.
Proof.
  exact (db_qhtr tm_%(mid)s pins_%(mid)s %(Q)s eat_%(mid)s turn_%(mid)s fire_%(mid)s
           %(n0)d %(m0)d ltac:(lia) ltac:(lia) %(t0)d 32779478 bootl_%(mid)s wit_%(mid)s bnd_%(mid)s).
Qed.
""" % dict(mid=mid, Q=ST[q], t0=t0, n0=n0, m0=m0)
    else:
        body += """(** The machine-level theorem, at the INSTRUCTION level, through
    [DoubleBounceTr.db_neverqhtr]. *)
Theorem nqhtr_%(mid)s : NeverQuasiHaltsTr tm_%(mid)s.
Proof.
  exact (db_neverqhtr tm_%(mid)s pins_%(mid)s %(Q)s eat_%(mid)s turn_%(mid)s fire_%(mid)s
           %(n0)d %(m0)d ltac:(lia) ltac:(lia) %(t0)d bootl_%(mid)s).
Qed.
""" % dict(mid=mid, Q=ST[q], t0=t0, n0=n0, m0=m0)
    head = """
(** ** The closure: a bouncer that doubles its block each round ([DoubleBounceTr])

    [R(n, m) = %(Q)s | 0 1^n 0 1^m ->+ R(2n, m+1)]: an eat arm family per
    cell of [1^n] and a turn arm family, both [LadderNest] programs. *)
From BBB4.Checkers Require Import LadderNest LadderCheckNestTr.
From BBB4.Counters Require Import NestCountTr DoubleBounceTr.

""" % dict(Q=ST[q])
    return head + inner_coq(mid, g.inner) + ''.join(g.out) + ''.join(out) + body, dict(nest=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('spec')
    ap.add_argument('-o', '--out', required=True)
    ap.add_argument('--qh', action='store_true')
    ap.add_argument('--scan', default=os.path.join(HERE, '..', '..', '..',
                                                   'censustr_v9_scan_1e8.txt'))
    a = ap.parse_args()
    spec = a.spec
    lastf = -1
    if a.qh:
        row = None
        for l in open(a.scan):
            if l.startswith(spec + ' '):
                row = l.split()[1:]
                break
        E.TR_PINS, lastf = E.quiet_pins(spec, row)
    else:
        E.TR_PINS = E.unfired(spec, 10 ** 6)
    t0, q, n0, m0 = find_boot(spec, lastf)
    if a.qh:
        E.TR_QH = t0
    cert = dict(spec=spec, closed=True, ladder=[], arms=[], dbq=q, dbboot=(t0, n0, m0),
                family=dict(state='ABCD'[q], head=0, side='R', other_side_cells=[],
                            digits=[[0], [1]], near_head_prefix=[], terminator=[],
                            terminators_by_phase=[[]], n_phases=1, base=2, digit_len=1,
                            code='binary', value_step_per_anchor_visit=1),
                fill=dict(widens_by=1, target_prefix=[], target_fill_digit=0, target_suffix=[],
                          lands_in_phase=0))
    E.emit_closure = emit_closure_db
    good, bad, cd = E.emit(cert, a.out)
    print('%s: closure %s' % (a.out, 'BUILT' if cd else 'not built'))
    return 0 if cd else 1


if __name__ == '__main__':
    sys.exit(main())
