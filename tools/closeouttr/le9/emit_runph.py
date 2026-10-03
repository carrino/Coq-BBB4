#!/usr/bin/env python3
"""UNTRUSTED emitter (SCOPING_INSTR 7.4.LE9): a binary counter beside a marker
run that grows as the counter narrows, with phases between refills -> a Coq
board closed by [RunPhCountTr].

A model (one JSON record per row, `le9/runph_models.jsonl`):

    {"spec": ..., "q": "A", "side": "R"|"L", "fix": "", "Z": "11", "O": "10",
     "M": "0", "R": "01", "phases": [{"suf": "", "ca": 0, "zt": [1]}, ...]}

The configuration is the head reading a blank in state q, the counter side
[x (Z/O digits, LSB at the head) ++ M ++ R^m ++ suf_p], the far side [fix];
an empty x refills to [0^(ca_p + m) ++ zt_p] in phase p + 1 (mod the count).
The arms (a carry, a narrowing, a refill per phase) are LE8's arm search; the
fires are read off one phase's refill family.

    python3 emit_runph.py SPEC MODELS.jsonl -o OUT.v [--qh]
"""
import argparse
import json
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


def cells(s):
    return tuple(int(c) for c in s)


def syms(c):
    return '[' + ';'.join('S%d' % x for x in c) + ']'


def read(m, L, R):
    """(x, mm, p) of an anchor visit, or None"""
    Z, O, Mk, Rw = m['Z'], m['O'], m['M'], m['R']
    if L.rstrip('0') != m['fix'].rstrip('0'):
        return None
    l = len(Z)
    for p, ph in enumerate(m['phases']):
        for pad in range(len(Rw) + len(ph['suf']) + l + 2):
            b = R + '0' * pad
            x = []
            i = 0
            while b[i:i + l] in (Z, O) and len(b[i:i + l]) == l:
                rest = b[i:]
                if rest.startswith(Mk):
                    tail = rest[len(Mk):]
                    mm = 0
                    while tail.startswith(Rw) and tail != ph['suf']:
                        tail = tail[len(Rw):]
                        mm += 1
                    if tail == ph['suf']:
                        return x, mm, p
                x.append(b[i:i + l] == O)
                i += l
            rest = b[i:]
            if rest.startswith(Mk):
                tail = rest[len(Mk):]
                mm = 0
                while tail.startswith(Rw) and tail != ph['suf']:
                    tail = tail[len(Rw):]
                    mm += 1
                if tail == ph['suf']:
                    return x, mm, p
    return None


def find_boot(spec, m, lastf, steps=600000):
    tab = E.parse_tm(spec)
    q0 = 'ABCD'.index(m['q'])
    tape, h, q = {}, 0, 0
    for t in range(steps):
        s = tape.get(h, 0)
        if t > lastf and q == q0 and s == 0 and t > 2000:
            cs = sorted(i for i, v in tape.items() if v)
            if m['side'] == 'R':
                L = ''.join(str(tape.get(i, 0)) for i in range(h - 1, (cs[0] if cs else h) - 1, -1))
                R = ''.join(str(tape.get(i, 0)) for i in range(h + 1, (cs[-1] if cs else h) + 1))
            else:
                L = ''.join(str(tape.get(i, 0)) for i in range(h + 1, (cs[-1] if cs else h) + 1))
                R = ''.join(str(tape.get(i, 0)) for i in range(h - 1, (cs[0] if cs else h) - 1, -1))
            r = read(m, L, R)
            if r is not None:
                return (t,) + tuple(r)
        w, d, nq = tab[(q, s)]
        tape[h] = w
        h += d
        q = nq
    raise NoClosure('no run-counter boot')


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
  exact (%(lemma)s tm %(el)s %(er)s nrules %(n0)d %(st)d (fun r => %(b)s_vsegs r (%(q)s, %(s)s))
           (fun r => %(b)s_vis r (%(q)s, %(s)s)) (fun r => lr_lhs (%(b)s r)) _ _ _ _ _ _ _
           ltac:(lia) nrules_sound_%(mid)s %(nm)s_vis %(b)s_lhs n %(xa)s %(flag)s).
Qed.

"""


def emit_closure_runph(cert, tab, mid):
    m = cert['model']
    g = Gen(tab, mid, E.TR_PINS)
    vtab = {k: (None if k in E.TR_PINS else v) for k, v in csim_parse(cert['spec']).items()}
    q, side = m['q'], m['side']
    fix = cells(m['fix'])
    Z, O, Mk, Rw = cells(m['Z']), cells(m['O']), cells(m['M']), cells(m['R'])
    phs = m['phases']
    P = len(phs)
    refills, rfams = [], []
    try:
        a = F(q, side, fix, [('c', (0,)), ('r', O, 0), ('c', Z), ('X',)])
        b = F(q, side, fix, [('c', (0,)), ('r', Z, 0), ('c', O), ('X',)])
        N.validate(vtab, a, b, 'carry')
        carry = g.arm(a, b, 'carry')
        a = F(q, side, fix, [('c', (0,)), ('r', O, 0), ('c', O + Mk), ('X',)])
        b = F(q, side, fix, [('c', (0,)), ('r', Z, 0), ('c', Mk + Rw), ('X',)])
        N.validate(vtab, a, b, 'narrow')
        narrow = g.arm(a, b, 'narrow')
        for i, ph in enumerate(phs):
            nx = phs[(i + 1) % P]
            zc = tuple(c for d in ph['zt'] for c in (O if d else Z))
            a = F(q, side, fix, [('c', (0,) + Mk), ('r', Rw, 0), ('c', cells(ph['suf']))])
            b = F(q, side, fix, [('c', (0,)), ('r', Z, ph['ca']), ('c', zc + Mk + cells(nx['suf']))])
            N.validate(vtab, a, b, 'refill %d' % i)
            refills.append(g.arm(a, b, 'refill %d' % i))
            rfams.append(a)
    except NoClosure as e:
        return E.CLOSURE_NONE % e, None
    out = []
    which = {}
    for i, fid in enumerate(rfams):
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
            which[w] = (i, nm)
            out.append(FIRE1 % dict(nm=nm, n0=fd['n0'], st=fd['st'], el=str(fd['el']).lower(),
                                    er=str(fd['er']).lower(), b=b, q=ST[w[0]], s=SYM[w[1]],
                                    br=br, mid=mid, f0=N.coq_form(fid),
                                    lemma='fire_of_nfire_r' if side == 'R' else 'fire_of_nfire_l',
                                    xa='[]', flag='(fun _ => eq_refl)'))
    miss = [w for w in g.want if w not in which]
    if miss:
        return E.CLOSURE_NONE % NoClosure('no fire witness for %s' % miss), None
    t0, x0, m0, p0 = cert['boot']
    Qs = ST['ABCD'.index(q)]

    def pmatch(f):
        return ' '.join('| %s => %s' % ('_' if i == P - 1 else str(i), f(i)) for i in range(P))

    if side == 'R':
        mkd = 'cfgR %s %s (S0 :: l)' % (Qs, syms(fix))
    else:
        mkd = 'cfgL %s (S0 :: l) %s' % (Qs, syms(fix))
    red = ('unfold rmk_%(mid)s; cbn [suf_%(mid)s ca_%(mid)s zt_%(mid)s nxtB bcells flat_map Nat.eqb Nat.add app]; '
           'rewrite ?app_nil_r; rewrite ?app_nil_r in Hx; exact Hx' % dict(mid=mid))
    refill_cases = ''.join('  destruct p as [|p]; [pose proof (%s m []) as Hx; %s|].\n' % (refills[i], red)
                           for i in range(P))
    fire_cases = '\n'.join('  - exists %d. split; [lia|]. intros m. pose proof (%s m []) as Hx. %s.'
                            % (which[w][0], which[w][1], red) for w in g.want)
    xs = clist(x0, lambda b: 'true' if b else 'false')
    body = """Definition rmk_%(mid)s (l : list Sym) : cconf := %(mkd)s.
Definition suf_%(mid)s (p : nat) : list Sym := match p with %(sb)s end.
Definition ca_%(mid)s (p : nat) : nat := match p with %(cb)s end.
Definition zt_%(mid)s (p : nat) : list bool := match p with %(zb)s end.

Lemma refill_%(mid)s : forall p m, p < %(P)d ->
  Reach1 tm (rmk_%(mid)s (%(M)s ++ rep %(R)s m ++ suf_%(mid)s p))
            (rmk_%(mid)s (rep %(Z)s (ca_%(mid)s p + m) ++ bcells %(Z)s %(O)s (zt_%(mid)s p) ++ %(M)s
                          ++ suf_%(mid)s (nxtB %(P)d p))).
Proof.
  intros p m Hp.
%(refill)s  exfalso; lia.
Qed.

Lemma fire_%(mid)s : forall t, ~ In t pins_%(mid)s -> exists p, p < %(P)d /\\
  forall m, Fires tm (rmk_%(mid)s (%(M)s ++ rep %(R)s m ++ suf_%(mid)s p)) t.
Proof.
  intros [q s] Hnp. destruct q, s; try (exfalso; apply Hnp; simpl; tauto).
%(fires)s
Qed.

Lemma bootl_%(mid)s :
  stepn %(tmb)s %(t0)d InitES = Some (lift (rcfg rmk_%(mid)s %(Z)s %(O)s %(M)s %(R)s suf_%(mid)s %(x0)s %(m0)d %(p0)d)).
Proof.
  assert (H : match csteps %(tmb)s %(t0)d c0 with
              | Some c => ceqb c (rcfg rmk_%(mid)s %(Z)s %(O)s %(M)s %(R)s suf_%(mid)s %(x0)s %(m0)d %(p0)d)
              | None => false end = true) by (vm_compute; reflexivity).
  destruct (csteps %(tmb)s %(t0)d c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

""" % dict(mid=mid, mkd=mkd, P=P, Z=syms(Z), O=syms(O), M=syms(Mk), R=syms(Rw),
           sb=pmatch(lambda i: syms(cells(phs[i]['suf']))),
           cb=pmatch(lambda i: str(phs[i]['ca'])),
           zb=pmatch(lambda i: clist([bool(d) for d in phs[i]['zt']], lambda b: 'true' if b else 'false')),
           refill=refill_cases, fires=fire_cases, x0=xs, m0=m0, p0=p0, t0=t0,
           tmb=('tm_%s' % mid) if E.TR_QH is not None else 'tm')
    call = ('%%s tm_%(mid)s pins_%(mid)s %(P)d rmk_%(mid)s %(Z)s %(O)s %(M)s %(R)s suf_%(mid)s ca_%(mid)s '
            'zt_%(mid)s ltac:(lia) %(carry)s %(narrow)s refill_%(mid)s fire_%(mid)s %(x0)s %(m0)d %(p0)d '
            'ltac:(lia) %(t0)d'
            % dict(mid=mid, P=P, Z=syms(Z), O=syms(O), M=syms(Mk), R=syms(Rw), carry=carry,
                   narrow=narrow, x0=xs, m0=m0, p0=p0, t0=t0))
    if E.TR_QH is not None:
        body += """Lemma wit_%(mid)s :
  existsb (fun tg => cfires tm_%(mid)s c0 %(t0)d tg) pins_%(mid)s = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bnd_%(mid)s : (%(t0)d <=? 32779478) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem qhtr_%(mid)s :
  NonHalt tm_%(mid)s /\\ QHBoundTr 32779478 tm_%(mid)s /\\ QuasiHaltsTr tm_%(mid)s.
Proof. exact (%(call)s 32779478 bootl_%(mid)s wit_%(mid)s bnd_%(mid)s). Qed.
""" % dict(mid=mid, t0=t0, call=call % 'runph_qhtr')
    else:
        body += """(** The machine-level theorem, at the INSTRUCTION level, through
    [RunPhCountTr.runph_neverqhtr]. *)
Theorem nqhtr_%(mid)s : NeverQuasiHaltsTr tm_%(mid)s.
Proof. exact (%(call)s bootl_%(mid)s). Qed.
""" % dict(mid=mid, call=call % 'runph_neverqhtr')
    head = """
(** ** The closure: a binary counter beside a growing marker run, with phases ([RunPhCountTr])

    Digits %(Z)s / %(O)s, LSB at the head, marker %(M)s, run word %(R)s, %(P)d
    phases.  A carry, a narrowing and a refill family per phase, all
    [LadderNest] programs. *)
From BBB4.Checkers Require Import LadderNest LadderCheckNestTr.
From BBB4.Counters Require Import NestCountTr PhBinCountTr RunPhCountTr.

""" % dict(Z=m['Z'], O=m['O'], M=m['M'], R=m['R'], P=P)
    txt = inner_coq(mid, g.inner) + ''.join(g.out) + ''.join(out)
    # a form ending in a block with no tail: [armfam_*] / [fire_of_nfire_*] state
    # it as [... ++ rep w n ++ [] ++ []]
    txt = re.sub(r'exact \(((?:armfam|arm1|fire_of_nfire)_[rl]) (.*?)\)\.\nQed\.',
                 lambda mo: 'pose proof (%s %s) as Hx. rewrite ?app_nil_r in Hx. exact Hx.\nQed.'
                 % (mo.group(1), mo.group(2)), txt, flags=re.S)
    return head + txt + body, dict(nest=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('spec')
    ap.add_argument('models')
    ap.add_argument('-o', '--out', required=True)
    ap.add_argument('--qh', action='store_true')
    ap.add_argument('--scan', default=os.path.join(HERE, '..', '..', '..',
                                                   'censustr_v9_scan_1e8.txt'))
    a = ap.parse_args()
    spec = a.spec
    m = None
    for l in open(a.models):
        r = json.loads(l)
        if r['spec'] == spec:
            m = r
    if m is None:
        raise SystemExit('%s: no model' % spec)
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
    t0, x0, m0, p0 = find_boot(spec, m, lastf)
    if a.qh:
        E.TR_QH = t0
    cert = dict(spec=spec, closed=True, ladder=[], arms=[], model=m, boot=(t0, x0, m0, p0),
                family=dict(state=m['q'], head=0, side=m['side'], other_side_cells=[],
                            digits=[[int(c) for c in m['Z']], [int(c) for c in m['O']]],
                            near_head_prefix=[], terminator=[], terminators_by_phase=[[]],
                            n_phases=1, base=2, digit_len=len(m['Z']), code='binary',
                            value_step_per_anchor_visit=1),
                fill=dict(widens_by=1, target_prefix=[], target_fill_digit=0, target_suffix=[],
                          lands_in_phase=0))
    E.emit_closure = emit_closure_runph
    good, bad, cd = E.emit(cert, a.out)
    print('%s: closure %s' % (a.out, 'BUILT' if cd else 'not built'))
    return 0 if cd else 1


if __name__ == '__main__':
    sys.exit(main())
