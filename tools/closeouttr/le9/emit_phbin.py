#!/usr/bin/env python3
"""UNTRUSTED emitter (SCOPING_INSTR 7.4.LE9): a binary counter with phases,
each its own anchor -> a Coq board closed by [PhBinCountTr].

A model (one JSON record per row, `le9/phbin_models.jsonl`):

    {"spec": ..., "q": "A", "side": "R"|"L", "Z": "101", "O": "111",
     "phases": [{"fix": "", "T": "11", "zpre": [1], "zcut": 0}, ...]}

Phase p's configuration is the head reading a blank in state q, the counter
side [Z/O digits (LSB at the head) ++ T_p], the far side [fix_p]; its top
fills to phase p + 1 (mod the count) at the digits [zpre_p ++ 0^(k - zcut_p)].
Every arm is LE8's arm search ([emit_nest.Gen]): a carry family per phase and
a fill family per phase; the fires are read off one phase's fill family.

    python3 emit_phbin.py SPEC MODELS.jsonl -o OUT.v [--qh]
"""
import argparse
import json
import os
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
    """(x, p) of an anchor visit (L, R: the far / counter side, nearest first)"""
    Z, O = m['Z'], m['O']
    l = len(Z)
    for p, ph in enumerate(m['phases']):
        if L.rstrip('0') != ph['fix'].rstrip('0') or len(L.rstrip('0')) > len(ph['fix']):
            continue
        for pad in range(l + len(ph['T']) + 1):
            b = R + '0' * pad
            if not b.endswith(ph['T']):
                continue
            b = b[:len(b) - len(ph['T'])]
            if len(b) % l:
                continue
            ws = [b[i:i + l] for i in range(0, len(b), l)]
            if all(w in (Z, O) for w in ws):
                return [w == O for w in ws], p
    return None


def find_boot(spec, m, lastf, kmin, steps=600000):
    tab = E.parse_tm(spec)
    q0 = 'ABCD'.index(m['q'])
    tape, h, q = {}, 0, 0
    for t in range(steps):
        s = tape.get(h, 0)
        if t > lastf and q == q0 and s == 0:
            cs = sorted(i for i, v in tape.items() if v)
            if m['side'] == 'R':
                L = ''.join(str(tape.get(i, 0)) for i in range(h - 1, (cs[0] if cs else h) - 1, -1))
                R = ''.join(str(tape.get(i, 0)) for i in range(h + 1, (cs[-1] if cs else h) + 1))
            else:
                L = ''.join(str(tape.get(i, 0)) for i in range(h + 1, (cs[-1] if cs else h) + 1))
                R = ''.join(str(tape.get(i, 0)) for i in range(h - 1, (cs[0] if cs else h) - 1, -1))
            r = read(m, L, R)
            if r is not None and len(r[0]) >= kmin and len(r[0]) % m.get('W', 1) == 0:
                return (t,) + tuple(r)
        w, d, nq = tab[(q, s)]
        tape[h] = w
        h += d
        q = nq
    raise NoClosure('no phased-counter boot')


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


def emit_closure_phbin(cert, tab, mid):
    m = cert['model']
    g = Gen(tab, mid, E.TR_PINS)
    vtab = {k: (None if k in E.TR_PINS else v) for k, v in csim_parse(cert['spec']).items()}
    q, side = m['q'], m['side']
    Z, O = cells(m['Z']), cells(m['O'])
    phs = m['phases']
    P = len(phs)
    kmin = cert['kmin']
    W = m.get('W', 1)
    carries, fills, ffams = [], [], []
    try:
        for i, ph in enumerate(phs):
            fix = cells(ph['fix'])
            a = F(q, side, fix, [('c', (0,)), ('r', O, 0), ('c', Z), ('X',)])
            b = F(q, side, fix, [('c', (0,)), ('r', Z, 0), ('c', O), ('X',)])
            N.validate(vtab, a, b, 'carry %d' % i)
            carries.append(g.arm(a, b, 'carry %d' % i))
        for i, ph in enumerate(phs):
            nx = phs[(i + 1) % P]
            bb = ph['zcut']
            assert bb % W == 0, 'zcut must be a multiple of W'
            zc = tuple(c for d in ph['zpre'] for c in (O if d else Z))
            a = F(q, side, cells(ph['fix']), [('c', (0,)), ('r', O * W, bb // W), ('c', cells(ph['T']))])
            b = F(q, side, cells(nx['fix']), [('c', (0,) + zc), ('r', Z * W, 0), ('c', cells(nx['T']))])
            N.validate(vtab, a, b, 'fill %d' % i)
            fills.append(g.arm(a, b, 'fill %d' % i))
            ffams.append(a)
    except NoClosure as e:
        return E.CLOSURE_NONE % e, None
    out = []
    which = {}
    for i, fid in enumerate(ffams):
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
    t0, x0, p0 = cert['boot']
    Qs = ST['ABCD'.index(q)]

    def pmatch(f):
        return ' '.join('| %s => %s' % ('_' if i == P - 1 else str(i), f(i)) for i in range(P))

    if side == 'R':
        mkb = pmatch(lambda i: 'cfgR %s %s (S0 :: l)' % (Qs, syms(cells(phs[i]['fix']))))
    else:
        mkb = pmatch(lambda i: 'cfgL %s (S0 :: l) %s' % (Qs, syms(cells(phs[i]['fix']))))
    carry_cases = ''.join('  destruct p as [|p]; [exact (%s k X)|].\n' % carries[i] for i in range(P))
    dec = ('pose proof (kdecomp %(W)d %(b)d k ltac:(lia) ltac:(lia) eq_refl Hm) as Ek; '
           'change (%(b)d / %(W)d) with %(bw)d in Ek; set (n := (k - %(b)d) / %(W)d) in Ek; clearbody n; subst k')
    fill_cases = ''.join(
        ('  destruct p as [|p].\n  { ' + dec + '.\n'
         '    replace (%(W)d * (%(bw)d + n) - zcut_%(mid)s %(i)d) with (%(W)d * n) by (cbn [zcut_%(mid)s]; lia).\n'
         '    rewrite <- !rep_pow. exact (%(lem)s n []). }\n')
        % dict(b=phs[i]['zcut'], bw=phs[i]['zcut'] // W, W=W, mid=mid, i=i, lem=fills[i])
        for i in range(P))
    fire_cases = '\n'.join(
        ('  - exists %(i)d. split; [lia|]. intros k Hk Hm. ' + dec + '.\n'
         '    rewrite <- !rep_pow. exact (%(nm)s n []).')
        % dict(i=which[w][0], b=phs[which[w][0]]['zcut'], bw=phs[which[w][0]]['zcut'] // W, W=W,
               nm=which[w][1])
        for w in g.want)
    body = """Definition pmk_%(mid)s (p : nat) (l : list Sym) : cconf := match p with %(mkb)s end.
Definition T_%(mid)s (p : nat) : list Sym := match p with %(Tb)s end.
Definition zpre_%(mid)s (p : nat) : list bool := match p with %(zb)s end.
Definition zcut_%(mid)s (p : nat) : nat := match p with %(cb)s end.

Lemma carry_%(mid)s : forall p k X, p < %(P)d ->
  Reach1 tm (pmk_%(mid)s p (rep %(O)s k ++ %(Z)s ++ X)) (pmk_%(mid)s p (rep %(Z)s k ++ %(O)s ++ X)).
Proof.
  intros p k X Hp.
%(carry)s  exfalso; lia.
Qed.

Lemma fill_%(mid)s : forall p k, p < %(P)d -> %(kmin)d <= k -> k mod %(W)d = 0 ->
  Reach1 tm (pmk_%(mid)s p (rep %(O)s k ++ T_%(mid)s p))
            (pmk_%(mid)s (nxtB %(P)d p) (bcells %(Z)s %(O)s (zpre_%(mid)s p) ++ rep %(Z)s (k - zcut_%(mid)s p)
                 ++ T_%(mid)s (nxtB %(P)d p))).
Proof.
  intros p k Hp Hk Hm.
%(fill)s  exfalso; lia.
Qed.

Lemma zcut_ok_%(mid)s : forall p, p < %(P)d -> zcut_%(mid)s p <= length (zpre_%(mid)s p).
Proof. intros p Hp. do %(P)d (destruct p as [|p]; [cbn; lia|]). exfalso; lia. Qed.

Lemma zmod_ok_%(mid)s : forall p, p < %(P)d -> (length (zpre_%(mid)s p) - zcut_%(mid)s p) mod %(W)d = 0.
Proof. intros p Hp. do %(P)d (destruct p as [|p]; [reflexivity|]). exfalso; lia. Qed.

Lemma kz_ok_%(mid)s : forall p, p < %(P)d -> zcut_%(mid)s p <= %(kmin)d.
Proof. intros p Hp. do %(P)d (destruct p as [|p]; [cbn; lia|]). exfalso; lia. Qed.

Lemma fire_%(mid)s : forall t, ~ In t pins_%(mid)s -> exists p, p < %(P)d /\\
  forall k, %(kmin)d <= k -> k mod %(W)d = 0 -> Fires tm (pmk_%(mid)s p (rep %(O)s k ++ T_%(mid)s p)) t.
Proof.
  intros [q s] Hnp. destruct q, s; try (exfalso; apply Hnp; simpl; tauto).
%(fires)s
Qed.

Lemma inv0_%(mid)s : BInv %(P)d %(kmin)d %(W)d (%(x0)s, %(p0)d).
Proof. split; [|split]; cbn; [lia | reflexivity | lia]. Qed.

Lemma bootl_%(mid)s :
  stepn %(tmb)s %(t0)d InitES = Some (lift (pbcfg pmk_%(mid)s %(Z)s %(O)s T_%(mid)s %(p0)d %(x0)s)).
Proof.
  assert (H : match csteps %(tmb)s %(t0)d c0 with
              | Some c => ceqb c (pbcfg pmk_%(mid)s %(Z)s %(O)s T_%(mid)s %(p0)d %(x0)s)
              | None => false end = true) by (vm_compute; reflexivity).
  destruct (csteps %(tmb)s %(t0)d c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

""" % dict(mid=mid, mkb=mkb, P=P, kmin=kmin, Z=syms(Z), O=syms(O),
           Tb=pmatch(lambda i: syms(cells(phs[i]['T']))),
           zb=pmatch(lambda i: clist([bool(d) for d in phs[i]['zpre']], lambda b: 'true' if b else 'false')),
           cb=pmatch(lambda i: str(phs[i]['zcut'])),
           carry=carry_cases, fill=fill_cases, fires=fire_cases,
           x0=clist(x0, lambda b: 'true' if b else 'false'), p0=p0, t0=t0, W=W,
           tmb=('tm_%s' % mid) if E.TR_QH is not None else 'tm')
    call = ('%%s tm_%(mid)s pins_%(mid)s %(P)d pmk_%(mid)s %(Z)s %(O)s T_%(mid)s zpre_%(mid)s zcut_%(mid)s %(kmin)d %(W)d '
            'ltac:(lia) ltac:(lia) carry_%(mid)s fill_%(mid)s zcut_ok_%(mid)s zmod_ok_%(mid)s kz_ok_%(mid)s '
            'fire_%(mid)s %(x0)s %(p0)d inv0_%(mid)s %(t0)d'
            % dict(mid=mid, P=P, Z=syms(Z), O=syms(O), kmin=kmin, W=W,
                   x0=clist(x0, lambda b: 'true' if b else 'false'), p0=p0, t0=t0))
    if E.TR_QH is not None:
        body += """Lemma wit_%(mid)s :
  existsb (fun tg => cfires tm_%(mid)s c0 %(t0)d tg) pins_%(mid)s = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bnd_%(mid)s : (%(t0)d <=? 32779478) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem qhtr_%(mid)s :
  NonHalt tm_%(mid)s /\\ QHBoundTr 32779478 tm_%(mid)s /\\ QuasiHaltsTr tm_%(mid)s.
Proof. exact (%(call)s 32779478 bootl_%(mid)s wit_%(mid)s bnd_%(mid)s). Qed.
""" % dict(mid=mid, t0=t0, call=call % 'phbin_qhtr')
    else:
        body += """(** The machine-level theorem, at the INSTRUCTION level, through
    [PhBinCountTr.phbin_neverqhtr]. *)
Theorem nqhtr_%(mid)s : NeverQuasiHaltsTr tm_%(mid)s.
Proof. exact (%(call)s bootl_%(mid)s). Qed.
""" % dict(mid=mid, call=call % 'phbin_neverqhtr')
    head = """
(** ** The closure: a binary counter with phases, each its own anchor ([PhBinCountTr])

    Digits %(Z)s / %(O)s, LSB at the head; %(P)d phases.  A carry family per
    phase and a fill family per phase, all [LadderNest] programs. *)
From BBB4.Checkers Require Import LadderNest LadderCheckNestTr.
From BBB4.Counters Require Import NestCountTr PhBinCountTr.

""" % dict(Z=m['Z'], O=m['O'], P=P)
    return head + inner_coq(mid, g.inner) + ''.join(g.out) + ''.join(out) + body, dict(nest=True)


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
    W = m.get('W', 1)
    kmin = max(1, max(ph['zcut'] for ph in m['phases']))
    kmin = -(-kmin // W) * W
    t0, x0, p0 = find_boot(spec, m, lastf, kmin)
    if a.qh:
        E.TR_QH = t0
    cert = dict(spec=spec, closed=True, ladder=[], arms=[], model=m, kmin=kmin, boot=(t0, x0, p0),
                family=dict(state=m['q'], head=0, side=m['side'], other_side_cells=[],
                            digits=[[int(c) for c in m['Z']], [int(c) for c in m['O']]],
                            near_head_prefix=[], terminator=[], terminators_by_phase=[[]],
                            n_phases=1, base=2, digit_len=len(m['Z']), code='binary',
                            value_step_per_anchor_visit=1),
                fill=dict(widens_by=1, target_prefix=[], target_fill_digit=0, target_suffix=[],
                          lands_in_phase=0))
    E.emit_closure = emit_closure_phbin
    good, bad, cd = E.emit(cert, a.out)
    print('%s: closure %s' % (a.out, 'BUILT' if cd else 'not built'))
    return 0 if cd else 1


if __name__ == '__main__':
    sys.exit(main())
