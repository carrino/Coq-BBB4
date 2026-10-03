#!/usr/bin/env python3
"""UNTRUSTED emitter (SCOPING_INSTR 7.4.LE9): LE7's "base3-side" rows, a
TERNARY counter left of a pivot cell and a binary one right of it, stepped
in turn -> a Coq board closed by [AbsStepTr].

At the pivot (state qB reading hB) the tape is

    [PLc ++ tcells x | hB | bcells z]

x a list of ternary digits (LSB at the pivot) spelled by the words W0 W1 W2
(W0 blank), z binary over ZR / OR (ZR blank).  A round: the right counter
steps (qB hB -> qD hD, the cell beside the pivot turning PLc -> PLd), then
the left (qD hD -> qB hB).  Both tops are the carry into the blank end, so
the round is plainly (x, z) |-> (x + 1, z + 1).

    python3 emit_ab3.py SPEC -o OUT.v
"""
import argparse
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'le8'))
import gen2 as G2  # noqa: E402
from gen2 import NoClosure, ST, SYM, syms  # noqa: E402
from emit_step import inner_coq  # noqa: E402
from csim import parse as csim_parse  # noqa: E402

E = G2.S.E
A, B, C, D = 0, 1, 2, 3

ROWS = {
    # pivot D1 / B0; left words 0000 / 0110 / 0010 beyond the cell 0 (D1) / 1 (B0);
    # right 00 / 01
    '1RB0LA_1LC1RD_1LA1LB_1LA0RD': dict(qB=D, hB=1, qD=B, hD=0, PLc=(0,), PLd=(1,),
                                        W=((0, 0, 0, 0), (0, 1, 1, 0), (0, 0, 1, 0)),
                                        ZR=(0, 0), OR=(0, 1)),
    '1RB0LA_1LC1RD_1LD1LB_1LA0RD': dict(qB=D, hB=1, qD=B, hD=0, PLc=(0,), PLd=(1,),
                                        W=((0, 0, 0, 0, 0), (0, 0, 1, 1, 0), (0, 0, 0, 1, 0)),
                                        ZR=(0, 0), OR=(0, 1)),
}


def arms_of(r):
    qB, hB, qD, hD = r['qB'], r['hB'], r['qD'], r['hD']
    PLc, PLd, (W0, W1, W2), ZR, OR = r['PLc'], r['PLd'], r['W'], r['ZR'], r['OR']
    X = ('X',)
    out = []
    for b, sfx in ((0, ''), (1, '1')):
        out += [
            ('rc' + sfx, (qB, hB, [('c', PLc), X], [('r', OR, b), ('c', ZR), X]),
                         (qD, hD, [('c', PLd), X], [('r', ZR, b), ('c', OR), X])),
            ('rt' + sfx, (qB, hB, [('c', PLc), X], [('r', OR, b)]),
                         (qD, hD, [('c', PLd), X], [('r', ZR, b), ('c', OR)]))]
    out += [
        ('lc0', (qD, hD, [('c', PLd), ('r', W2, 0), ('c', W0), X], [X]),
                (qB, hB, [('c', PLc), ('r', W0, 0), ('c', W1), X], [X])),
        ('lc1', (qD, hD, [('c', PLd), ('r', W2, 0), ('c', W1), X], [X]),
                (qB, hB, [('c', PLc), ('r', W0, 0), ('c', W2), X], [X])),
        ('lt', (qD, hD, [('c', PLd), ('r', W2, 0)], [X]),
               (qB, hB, [('c', PLc), ('r', W0, 0), ('c', W1)], [X])),
    ]
    return out


def boot(spec, r, steps=400000):
    """(t, x, z): the first pivot visit past 2000 steps whose tape reads as
    the two counters"""
    tab = E.parse_tm(spec)
    s2 = lambda w: ''.join(map(str, w))  # noqa: E731
    W = [s2(w) for w in r['W']]
    ZR, OR, PLc = s2(r['ZR']), s2(r['OR']), s2(r['PLc'])
    n = len(W[0])
    tape, h, q = {}, 0, 0
    for t in range(steps):
        s = tape.get(h, 0)
        if q == r['qB'] and s == r['hB'] and t > 2000:
            cs = sorted(i for i, v in tape.items() if v)
            L = ''.join(str(tape.get(i, 0)) for i in range(h - 1, cs[0] - 1, -1)).rstrip('0')
            R = ''.join(str(tape.get(i, 0)) for i in range(h + 1, cs[-1] + 1)).rstrip('0')
            ok = L.startswith(PLc)
            x, z = [], []
            if ok:
                rest = L[len(PLc):]
                rest += '0' * (-len(rest) % n)
                for i in range(0, len(rest), n):
                    if rest[i:i + n] not in W:
                        ok = False
                        break
                    x.append(W.index(rest[i:i + n]))
                R += '0' * (len(R) % 2)
                for i in range(0, len(R), 2):
                    if R[i:i + 2] not in (ZR, OR):
                        ok = False
                        break
                    z.append(R[i:i + 2] == OR)
            if ok and x and z:
                return t, x, z
        w, d, nq = tab[(q, s)]
        tape[h] = w
        h += d
        q = nq
    raise NoClosure('no boot')


COQ = r"""
(** *** The ternary counter *)
Fixpoint tinc_%(mid)s (x : list nat) : list nat :=
  match x with
  | [] => [1]
  | d :: r => match d with 0 => 1 :: r | 1 => 2 :: r | _ => 0 :: tinc_%(mid)s r end
  end.
Definition tW_%(mid)s (d : nat) : list Sym := match d with 0 => %(W0)s | 1 => %(W1)s | _ => %(W2)s end.
Definition tcells_%(mid)s (x : list nat) : list Sym := flat_map tW_%(mid)s x.

Lemma tcells_app_%(mid)s : forall a b, tcells_%(mid)s (a ++ b) = tcells_%(mid)s a ++ tcells_%(mid)s b.
Proof. intros a b. unfold tcells_%(mid)s. apply flat_map_app. Qed.

Lemma tcells_rep_%(mid)s : forall d k, tcells_%(mid)s (repeat d k) = rep (tW_%(mid)s d) k.
Proof.
  intros d. induction k as [|k IH]; [reflexivity|].
  cbn [repeat]. change (tcells_%(mid)s (d :: repeat d k)) with (tW_%(mid)s d ++ tcells_%(mid)s (repeat d k)).
  rewrite IH. reflexivity.
Qed.

Lemma tinc_c0_%(mid)s : forall k r, tinc_%(mid)s (repeat 2 k ++ 0 :: r) = repeat 0 k ++ 1 :: r.
Proof. induction k as [|k IH]; intros r; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
Lemma tinc_c1_%(mid)s : forall k r, tinc_%(mid)s (repeat 2 k ++ 1 :: r) = repeat 0 k ++ 2 :: r.
Proof. induction k as [|k IH]; intros r; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
Lemma tinc_t_%(mid)s : forall k, tinc_%(mid)s (repeat 2 k) = repeat 0 k ++ [1].
Proof. induction k as [|k IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma tdecomp_%(mid)s : forall x, Forall (fun d => d <= 2) x ->
  (exists k r, x = repeat 2 k ++ 0 :: r) \/ (exists k r, x = repeat 2 k ++ 1 :: r) \/
  (exists k, x = repeat 2 k).
Proof.
  induction x as [|d x IH]; intros Hx.
  - right; right. exists 0. reflexivity.
  - inversion Hx as [|? ? Hd Hx']; subst.
    destruct d as [|[|[|d]]]; [left; exists 0, x; reflexivity | right; left; exists 0, x; reflexivity | | lia].
    destruct (IH Hx') as [(k & r & ->) | [(k & r & ->) | (k & ->)]].
    + left. exists (S k), r. reflexivity.
    + right; left. exists (S k), r. reflexivity.
    + right; right. exists (S k). reflexivity.
Qed.

Lemma tinc_forall_%(mid)s : forall x, Forall (fun d => d <= 2) x -> Forall (fun d => d <= 2) (tinc_%(mid)s x).
Proof.
  induction x as [|d x IH]; intros Hx; [repeat constructor|].
  inversion Hx as [|? ? Hd Hx']; subst.
  destruct d as [|[|d]]; cbn; constructor; try lia; auto.
Qed.

Lemma tinc_len_%(mid)s : forall x, 1 <= length (tinc_%(mid)s x).
Proof. intros [|[|[|d]] x]; cbn; lia. Qed.

Lemma binc_t_%(mid)s : forall j, binc (repeat true j) = repeat false j ++ [true].
Proof. induction j as [|j IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma binc_len_%(mid)s : forall z, 1 <= length (binc z).
Proof. intros [|[|] z]; cbn; lia. Qed.

(** *** The two counters at the pivot *)
Definition aC_%(mid)s (s : list nat * list bool * nat) : cconf :=
  let '(x, z, p) := s in (%(qB)s, (%(PLc)s ++ tcells_%(mid)s x, %(hB)s, bcells %(ZR)s %(OR)s z)).
Definition aD_%(mid)s (x : list nat) (z : list bool) (p : nat) : cconf :=
  (%(qD)s, (%(PLd)s ++ tcells_%(mid)s x, %(hD)s, bcells %(ZR)s %(OR)s z)).
Definition aF_%(mid)s (s : list nat * list bool * nat) : list nat * list bool * nat :=
  let '(x, z, p) := s in (tinc_%(mid)s x, binc z, p).
Definition aI_%(mid)s (s : list nat * list bool * nat) : Prop :=
  let '(x, z, p) := s in Forall (fun d => d <= 2) x /\ 1 <= length x /\ 1 <= length z.

(** *** The right half: the binary counter steps *)
Lemma ahRc_%(mid)s : forall x j s p,
  Reach1 tm (aC_%(mid)s (x, repeat true j ++ false :: s, p)) (aD_%(mid)s x (repeat false j ++ true :: s) p).
Proof.
  intros x j s p. unfold aC_%(mid)s, aD_%(mid)s. rewrite bcells_tt, bcells_ff.
  change (bcells %(ZR)s %(OR)s (false :: s)) with (%(ZR)s ++ bcells %(ZR)s %(OR)s s).
  change (bcells %(ZR)s %(OR)s (true :: s)) with (%(OR)s ++ bcells %(ZR)s %(OR)s s).
  exact (%(rc)s j (tcells_%(mid)s x) (bcells %(ZR)s %(OR)s s)).
Qed.

Lemma ahRt_%(mid)s : forall x j p,
  Reach1 tm (aC_%(mid)s (x, repeat true j, p)) (aD_%(mid)s x (repeat false j ++ [true]) p).
Proof.
  intros x j p. unfold aC_%(mid)s, aD_%(mid)s. rewrite bcells_rep_true, bcells_ff.
  change (bcells %(ZR)s %(OR)s [true]) with (%(OR)s ++ []).
  pose proof (%(rt)s j (tcells_%(mid)s x) []) as H. rewrite ?app_nil_r in H. rewrite ?app_nil_r. exact H.
Qed.

Lemma ahR_%(mid)s : forall x z p, Reach1 tm (aC_%(mid)s (x, z, p)) (aD_%(mid)s x (binc z) p).
Proof.
  intros x z p. destruct (ttdecomp z) as [(j & s & ->) | (j & ->)].
  - rewrite binc_int. apply ahRc_%(mid)s.
  - rewrite binc_t_%(mid)s. apply ahRt_%(mid)s.
Qed.

(** *** The left half: the ternary counter steps *)
Lemma ahL0_%(mid)s : forall k r z p,
  Reach1 tm (aD_%(mid)s (repeat 2 k ++ 0 :: r) z p) (aC_%(mid)s (repeat 0 k ++ 1 :: r, z, p)).
Proof.
  intros k r z p. unfold aC_%(mid)s, aD_%(mid)s. rewrite !tcells_app_%(mid)s, !tcells_rep_%(mid)s.
  change (tcells_%(mid)s (0 :: r)) with (%(W0)s ++ tcells_%(mid)s r).
  change (tcells_%(mid)s (1 :: r)) with (%(W1)s ++ tcells_%(mid)s r).
  exact (%(lc0)s k (tcells_%(mid)s r) (bcells %(ZR)s %(OR)s z)).
Qed.

Lemma ahL1_%(mid)s : forall k r z p,
  Reach1 tm (aD_%(mid)s (repeat 2 k ++ 1 :: r) z p) (aC_%(mid)s (repeat 0 k ++ 2 :: r, z, p)).
Proof.
  intros k r z p. unfold aC_%(mid)s, aD_%(mid)s. rewrite !tcells_app_%(mid)s, !tcells_rep_%(mid)s.
  change (tcells_%(mid)s (1 :: r)) with (%(W1)s ++ tcells_%(mid)s r).
  change (tcells_%(mid)s (2 :: r)) with (%(W2)s ++ tcells_%(mid)s r).
  exact (%(lc1)s k (tcells_%(mid)s r) (bcells %(ZR)s %(OR)s z)).
Qed.

Lemma ahLt_%(mid)s : forall k z p,
  Reach1 tm (aD_%(mid)s (repeat 2 k) z p) (aC_%(mid)s (repeat 0 k ++ [1], z, p)).
Proof.
  intros k z p. unfold aC_%(mid)s, aD_%(mid)s. rewrite !tcells_app_%(mid)s, !tcells_rep_%(mid)s.
  change (tcells_%(mid)s [1]) with (%(W1)s ++ []).
  pose proof (%(lt)s k [] (bcells %(ZR)s %(OR)s z)) as H. rewrite ?app_nil_r in H. rewrite ?app_nil_r. exact H.
Qed.

Lemma ahL_%(mid)s : forall x z p, Forall (fun d => d <= 2) x ->
  Reach1 tm (aD_%(mid)s x z p) (aC_%(mid)s (tinc_%(mid)s x, z, p)).
Proof.
  intros x z p Hx. destruct (tdecomp_%(mid)s x Hx) as [(k & r & ->) | [(k & r & ->) | (k & ->)]].
  - rewrite tinc_c0_%(mid)s. apply ahL0_%(mid)s.
  - rewrite tinc_c1_%(mid)s. apply ahL1_%(mid)s.
  - rewrite tinc_t_%(mid)s. apply ahLt_%(mid)s.
Qed.

Lemma aHI_%(mid)s : forall s, aI_%(mid)s s -> aI_%(mid)s (aF_%(mid)s s).
Proof.
  intros [[x z] p] (Hx & Hl & Hz). cbn [aF_%(mid)s aI_%(mid)s].
  split; [apply tinc_forall_%(mid)s, Hx|]. split; [apply tinc_len_%(mid)s | apply binc_len_%(mid)s].
Qed.

Lemma aHstep_%(mid)s : forall s, aI_%(mid)s s -> Reach1 tm (aC_%(mid)s s) (aC_%(mid)s (aF_%(mid)s s)).
Proof.
  intros [[x z] p] (Hx & _ & _). cbn [aF_%(mid)s].
  apply (reach10 tm _ (aD_%(mid)s x (binc z) p)); [apply ahR_%(mid)s|].
  apply reach1_0, ahL_%(mid)s, Hx.
Qed.

(** *** Where each instruction fires *)
Lemma afR_%(mid)s : forall t,
  (forall x j s p, Fires tm (aC_%(mid)s (x, repeat true j ++ false :: s, p)) t) ->
  (forall x j p, Fires tm (aC_%(mid)s (x, repeat true j, p)) t) ->
  forall s, aI_%(mid)s s -> Fires tm (aC_%(mid)s s) t.
Proof.
  intros t Hc Ht [[x z] p] _.
  destruct (ttdecomp z) as [(j & s & ->) | (j & ->)]; [apply Hc | apply Ht].
Qed.

Lemma afL_%(mid)s : forall t,
  (forall k r z p, Fires tm (aD_%(mid)s (repeat 2 k ++ 0 :: r) z p) t) ->
  (forall k r z p, Fires tm (aD_%(mid)s (repeat 2 k ++ 1 :: r) z p) t) ->
  (forall k z p, Fires tm (aD_%(mid)s (repeat 2 k) z p) t) ->
  forall s, aI_%(mid)s s -> Fires tm (aC_%(mid)s s) t.
Proof.
  intros t H0 H1 Ht [[x z] p] (Hx & _ & _).
  apply (fire_back tm _ (aD_%(mid)s x (binc z) p)); [apply reach1_0, ahR_%(mid)s|].
  destruct (tdecomp_%(mid)s x Hx) as [(k & r & ->) | [(k & r & ->) | (k & ->)]];
    [apply H0 | apply H1 | apply Ht].
Qed.

(** fired by the left half when the ternary counter's low digit is 0: so
    within two rounds *)
Lemma afZ_%(mid)s : forall t,
  (forall r z p, Fires tm (aD_%(mid)s (0 :: r) z p) t) ->
  forall s, aI_%(mid)s s -> exists n, Fires tm (aC_%(mid)s (fiter _ aF_%(mid)s n s)) t.
Proof.
  intros t H0 [[x z] p] (Hx & Hl & _).
  assert (Hz : forall r z p, Fires tm (aC_%(mid)s (0 :: r, z, p)) t).
  { intros r z' p'. apply (fire_back tm _ (aD_%(mid)s (0 :: r) (binc z') p')); [apply reach1_0, ahR_%(mid)s|].
    apply H0. }
  destruct x as [|d r]; [cbn in Hl; lia|].
  destruct d as [|[|[|d]]].
  - exists 0. apply Hz.
  - exists 2. apply Hz.
  - exists 1. apply Hz.
  - inversion Hx; lia.
Qed.

Lemma aHfire_%(mid)s : forall t, ~ In t pins_%(mid)s -> forall s, aI_%(mid)s s ->
  exists n, Fires tm (aC_%(mid)s (fiter _ aF_%(mid)s n s)) t.
Proof.
  intros t Hnp st Hs.
  destruct t as [q h]; destruct q, h; try (exfalso; apply Hnp; simpl; tauto).
%(firecases)s
Qed.
"""

FIRE_RC = """      intros x j s p. unfold aC_%(mid)s. rewrite bcells_tt.
      change (bcells %(ZR)s %(OR)s (false :: s)) with (%(ZR)s ++ bcells %(ZR)s %(OR)s s).
      exact (%(frc)s j (tcells_%(mid)s x) (bcells %(ZR)s %(OR)s s))."""
FIRE_RT = """      intros x j p. unfold aC_%(mid)s. rewrite bcells_rep_true.
      pose proof (%(frt)s j (tcells_%(mid)s x) []) as H. rewrite ?app_nil_r in H. rewrite ?app_nil_r. exact H."""
FIRE_L0 = """      intros k r z p. unfold aD_%(mid)s. rewrite tcells_app_%(mid)s, tcells_rep_%(mid)s.
      change (tcells_%(mid)s (0 :: r)) with (%(W0)s ++ tcells_%(mid)s r).
      exact (%(flc0)s k (tcells_%(mid)s r) (bcells %(ZR)s %(OR)s z))."""
FIRE_L1 = """      intros k r z p. unfold aD_%(mid)s. rewrite tcells_app_%(mid)s, tcells_rep_%(mid)s.
      change (tcells_%(mid)s (1 :: r)) with (%(W1)s ++ tcells_%(mid)s r).
      exact (%(flc1)s k (tcells_%(mid)s r) (bcells %(ZR)s %(OR)s z))."""
FIRE_LT = """      intros k z p. unfold aD_%(mid)s. rewrite tcells_rep_%(mid)s.
      pose proof (%(flt)s k [] (bcells %(ZR)s %(OR)s z)) as H. rewrite ?app_nil_r in H. rewrite ?app_nil_r. exact H."""

FIRE_R = ("  - exists 0. apply afR_%(mid)s; [| |exact Hs].\n    +" + FIRE_RC[5:] + "\n    +" + FIRE_RT[5:])
FIRE_L = ("  - exists 0. apply afL_%(mid)s; [| | |exact Hs].\n    +" + FIRE_L0[5:] + "\n    +" + FIRE_L1[5:]
          + "\n    +" + FIRE_LT[5:])
FIRE_Z = """  - apply afZ_%(mid)s; [|exact Hs].
    intros r z p. unfold aD_%(mid)s. change (tcells_%(mid)s (0 :: r)) with (%(W0)s ++ tcells_%(mid)s r).
    exact (%(flc0)s 0 (tcells_%(mid)s r) (bcells %(ZR)s %(OR)s z))."""


def emit_closure_ab3(cert, tab, mid):
    r = cert['row']
    ctab = {k: (None if k in E.TR_PINS else v) for k, v in csim_parse(cert['spec']).items()}
    g = G2.Gen2(tab, mid, E.TR_PINS, ctab)
    names, fires = {}, {}
    try:
        for key, a, b in arms_of(r):
            names[key] = g.arm(a, b, key)
    except NoClosure as e:
        return E.CLOSURE_NONE % e, None
    for key in names:
        fires[key] = g.fires(names[key])
    W0, W1, W2 = r['W']
    P = dict(mid=mid, qB=ST[r['qB']], hB=SYM[r['hB']], qD=ST[r['qD']], hD=SYM[r['hD']],
             PLc=syms(r['PLc']), PLd=syms(r['PLd']), W0=syms(W0), W1=syms(W1), W2=syms(W2),
             ZR=syms(r['ZR']), OR=syms(r['OR']), **names)
    cases = []
    for w in g.want:
        inn = lambda *ks: all(w in fires[k] for k in ks)  # noqa: E731
        f = lambda k: fires[k][w]  # noqa: E731
        if inn('rc', 'rt'):
            cases.append(FIRE_R % dict(P, frc=f('rc'), frt=f('rt')))
        elif inn('lc0', 'lc1', 'lt'):
            cases.append(FIRE_L % dict(P, flc0=f('lc0'), flc1=f('lc1'), flt=f('lt')))
        elif inn('lc0'):
            cases.append(FIRE_Z % dict(P, flc0=f('lc0')))
        else:
            return E.CLOSURE_NONE % NoClosure('no fire strategy for %s%d' % ('ABCD'[w[0]], w[1])), None
    body = COQ % dict(P, firecases='\n'.join(cases))
    t0, x0, z0 = cert['boot']
    xs = '[' + ';'.join(str(d) for d in x0) + ']'
    zs = '[' + ';'.join('true' if b else 'false' for b in z0) + ']'
    body += """
Lemma aboot_%(mid)s :
  stepn tm %(t0)d InitES = Some (lift (aC_%(mid)s (%(x0)s, %(z0)s, 0))).
Proof.
  assert (H : match csteps tm %(t0)d c0 with
              | Some c => ceqb c (aC_%(mid)s (%(x0)s, %(z0)s, 0))
              | None => false end = true) by (vm_compute; reflexivity).
  destruct (csteps tm %(t0)d c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** The machine-level theorem, at the INSTRUCTION level, through
    [AbsStepTr.absstep_neverqhtr]. *)
Theorem nqhtr_%(mid)s : NeverQuasiHaltsTr tm_%(mid)s.
Proof.
  exact (absstep_neverqhtr tm_%(mid)s pins_%(mid)s _ aC_%(mid)s aF_%(mid)s aI_%(mid)s
           aHI_%(mid)s aHstep_%(mid)s aHfire_%(mid)s (%(x0)s, %(z0)s, 0)
           ltac:(cbn; repeat split; repeat constructor; lia) %(t0)d aboot_%(mid)s).
Qed.
""" % dict(mid=mid, t0=t0, x0=xs, z0=zs)
    head = """
(** ** The closure: a ternary and a binary counter at a pivot, stepped in turn
    ([AbsStepTr], [TwoSideArmTr]) *)
From BBB4.Checkers Require Import LadderNest LadderCheckNestTr.
From BBB4.Counters Require Import NestCountTr PhBinCountTr TwoSideArmTr AbsStepTr.

"""
    return head + inner_coq(mid, g.inner) + ''.join(g.out) + body, dict(nest=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('spec')
    ap.add_argument('-o', '--out', required=True)
    a = ap.parse_args()
    spec = a.spec
    r = ROWS[spec]
    E.TR_PINS = E.unfired(spec, 10 ** 6)
    t0, x0, z0 = boot(spec, r)
    cert = dict(spec=spec, closed=True, ladder=[], arms=[], row=r, boot=(t0, x0, z0),
                family=dict(state='ABCD'[r['qB']], head=r['hB'], side='R', other_side_cells=[],
                            digits=[list(r['ZR']), list(r['OR'])], near_head_prefix=[], terminator=[],
                            terminators_by_phase=[[]], n_phases=1, base=2, digit_len=2,
                            code='binary', value_step_per_anchor_visit=1),
                fill=dict(widens_by=1, target_prefix=[], target_fill_digit=0, target_suffix=[],
                          lands_in_phase=0))
    E.emit_closure = emit_closure_ab3
    good, bad, cd = E.emit(cert, a.out)
    print('%s: closure %s' % (a.out, 'BUILT' if cd else 'not built'))
    return 0 if cd else 1


if __name__ == '__main__':
    sys.exit(main())
