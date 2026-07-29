#!/usr/bin/env python3
"""Generate the route-A closeout stage files from tools/closeout/frozen_map.tsv.

Emits theories/Closeout/CB_XX.v (one [Lemma cov_*] : [covers (row_to_tm r)]
per proven frozen row, discharged from the board theorem via
[covers_nqh_at]/[covers_iqh_at] -- the pointwise premise is an 8-way case
split the kernel re-checks) plus theories/Closeout/Closeout.v (the app-chain,
the remaining-rows table, the reflective split check, [closeout_partial], and
[census_boarded] chaining [census_decided]).

Board modules are Require'd WITHOUT Import and referenced fully qualified, so
per-board name clashes (Cc, U_RIP, ...) cannot occur.

Everything here is UNTRUSTED; every generated line is re-checked by the
kernel.  Usage: gen_stages.py [CHUNK]  (default 100 rows per stage).
"""
import csv
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if not os.path.isdir(os.path.join(ROOT, 'theories')):
    ROOT = '/home/user/Coq-BBB4'
OUT = os.path.join(ROOT, 'theories/Closeout')
CHUNK = int(sys.argv[1]) if len(sys.argv) > 1 else 100

SLOT_ORDER = [0, 1, 2, 3, 4, 5, 6, 7]


def spec_rows(spec):
    """'0RB---_..._1RA1LC' -> ['t0RB', 'tN', ...] (8 Deferred_Defs shorthands)."""
    toks = []
    for grp in spec.split('_'):
        assert len(grp) == 6, spec
        toks += [grp[0:3], grp[3:6]]
    assert len(toks) == 8, spec
    out = []
    for t in toks:
        if t == '---':
            out.append('tN')
        else:
            assert t[0] in '01' and t[1] in 'RL' and t[2] in 'ABCD', spec
            out.append('t' + t)
    return out


def module_of(vfile):
    assert vfile.startswith('theories/') and vfile.endswith('.v'), vfile
    return 'BBB4.' + vfile[len('theories/'):-len('.v')].replace('/', '.')


def ops_term(base, ops):
    """The Coq term ops(base), constructors applied in emission order."""
    t = base
    for op in ops:
        if op[0] == 'mirror':
            t = '(mirror_tm %s)' % t
        else:
            t = '(TM_swap St%s St%s %s)' % (op[1], op[2], t)
    return t


def write_if_changed(path, text):
    """Leave the file (and its mtime) alone when the content is identical, so
    an unchanged stage does not force a needless recompile."""
    if os.path.exists(path) and open(path).read() == text:
        return False
    open(path, 'w').write(text)
    return True


# ---------------------------------------------------------------------------
# _CoqProject board closure
#
# The stage files [Require] one module per proven frozen row.  If a board .v
# (or one of ITS deps) is not listed in _CoqProject, coq_makefile emits no rule
# for its .vo and `make closeout` dies with "No rule to make target".  Wave-12
# lost a day to exactly this: 533 boards -- all of waves 10/11 -- were
# unlisted.  So the generator now computes the dependency closure of every
# board it references and adds whatever is missing.
#
# theories/Census/ is deliberately EXCLUDED: its Compute/ .vo are committed
# (OCaml-toolchain-specific) and must never be rebuilt from source.
# ---------------------------------------------------------------------------

def strip_comments(text):
    """Remove Coq (* ... *) comments (nesting-aware) so Require-scanning does
    not trip over prose."""
    out, depth, i, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith('(*', i):
            depth += 1
            i += 2
        elif depth and text.startswith('*)', i):
            depth -= 1
            i += 2
        else:
            if not depth:
                out.append(text[i])
            i += 1
    return ''.join(out)


REQ_RE = None


def _req_re():
    global REQ_RE
    if REQ_RE is None:
        import re
        REQ_RE = re.compile(
            r'(?:From\s+([\w.]+)\s+)?Require\s+(?:Import\s+|Export\s+)?'
            r'((?:[\w.]+\s+)*[\w.]+)\s*\.')
    return REQ_RE


def module_index():
    """logical module name -> repo-relative .v path, for every file under
    theories/ (Census included, so deps RESOLVE; the caller filters)."""
    idx = {}
    for dirpath, _dirs, files in os.walk(os.path.join(ROOT, 'theories')):
        for f in files:
            if not f.endswith('.v'):
                continue
            full = os.path.join(dirpath, f)
            rel = os.path.relpath(full, ROOT)
            idx[module_of(rel)] = rel
    return idx


def deps_of(vpath, idx):
    """In-tree modules Require'd by ROOT/vpath, resolved against idx."""
    try:
        text = strip_comments(open(os.path.join(ROOT, vpath)).read())
    except OSError:
        return []
    # suffix lookup: 'WTape' under 'From BBB4.Counters' -> BBB4.Counters.WTape
    out = []
    for prefix, names in _req_re().findall(text):
        for name in names.split():
            cands = []
            if prefix:
                cands.append(prefix + '.' + name)
            cands.append(name)
            if not name.startswith('BBB4.'):
                cands.append('BBB4.' + name)
            hit = next((c for c in cands if c in idx), None)
            if hit is None:
                # last resort: unique suffix match ('Require BBB4.X.Y' forms)
                tail = '.' + name.split('.')[-1]
                sfx = [m for m in idx if m.endswith(tail)]
                if len(sfx) == 1:
                    hit = sfx[0]
            if hit is not None:
                out.append(idx[hit])
    return out


def board_closure(vfiles):
    """Transitive in-tree dependency closure of vfiles, minus theories/Census/
    and theories/Closeout/.

    Closeout is excluded because THIS generator owns that section of
    _CoqProject: it strips every `theories/Closeout/' line and re-appends the
    canonical list.  Without the exclusion a board that reaches into the kit
    (RerootStage/RRPartner_02.v imports CloseoutKit) drags the whole Closeout
    closure into the "missing board files" set -- which is computed against a
    `listed' set the strip has already emptied of Closeout -- so all 53 files
    get added a second time.  make then warns "target ... given more than once
    in the same rule" for every one of them on the doc targets."""
    idx = module_index()
    seen, stack = set(), list(vfiles)
    while stack:
        v = stack.pop()
        if (v in seen or v.startswith('theories/Census/')
                or v.startswith('theories/Closeout/')):
            continue
        seen.add(v)
        stack.extend(deps_of(v, idx))
    return seen


def main():
    rows = list(csv.reader(open(os.path.join(ROOT, 'tools/closeout/frozen_map.tsv')),
                           delimiter='\t'))[1:]
    rows.sort(key=lambda r: (r[2], r[3]))
    remaining = [l.strip() for l in
                 open(os.path.join(ROOT, 'tools/closeout/frozen_unproven.txt'))
                 if l.strip()]

    # ---- shadow classification (Closeout/ShadowKit.v's skipped disjunct) ----
    sys.path.insert(0, os.path.join(ROOT, 'tools/closeout'))
    import shadowlib
    core_specs, shadows = shadowlib.classify(remaining)
    with open(os.path.join(ROOT, 'tools/closeout/core_rows.txt'), 'w') as f:
        f.write('\n'.join(core_specs) + '\n')
    with open(os.path.join(ROOT, 'tools/closeout/shadow_rows.tsv'), 'w') as f:
        f.write('machine\tqstar\tprefix\tpartner\tops\n')
        for sh in shadows:
            f.write('%s\t%s\t%d\t%s\t%s\n' % (
                sh['spec'], sh['qs'], sh['t'], sh['partner'],
                ','.join(':'.join(o) for o in sh['ops'])))

    nwrote = 0
    stages = [rows[i:i + CHUNK] for i in range(0, len(rows), CHUNK)]
    stage_names = []
    for si, chunk in enumerate(stages):
        name = 'CB_%02d' % si
        stage_names.append(name)
        mods = sorted(set(module_of(r[2]) for r in chunk))
        L = []
        L.append('(** GENERATED by tools/closeout/gen_stages.py -- do not edit.')
        L.append('    Closeout stage %s: covers-proofs for %d frozen rows. *)' % (name, len(chunk)))
        L.append('From Coq Require Import List.')
        L.append('From BBB4 Require Import BBB4_Statement.')
        L.append('From BBB4.Census Require Import Deferred_Defs.')
        L.append('From BBB4.Closeout Require Import CloseoutKit.')
        for m in mods:
            L.append('Require %s.' % m)
        L.append('Import ListNotations.')
        L.append('')
        covs = []
        for i, (spec, kind, vfile, thm, const) in enumerate(chunk):
            mod = module_of(vfile)
            row = '[' + ';'.join(spec_rows(spec)) + ']'
            cov = 'cov_%02d_%04d' % (si, i)
            covs.append(cov)
            L.append('(* %s *)' % spec)
            L.append('Lemma %s : covers (row_to_tm %s).' % (cov, row))
            if kind == 'nqh':
                L.append('Proof.')
                L.append('  apply (covers_nqh_at %s.%s);' % (mod, const))
                L.append('    [exact %s.%s | intros q s; destruct q, s; reflexivity].' % (mod, thm))
                L.append('Qed.')
            elif kind.startswith('iqhle:'):
                bound = kind.split(':', 1)[1]
                L.append('Proof.')
                L.append('  apply (covers_iqh_le_at %s %s.%s);' % (bound, mod, const))
                L.append('    [exact %s.%s | vm_compute; reflexivity' % (mod, thm))
                L.append('     | intros q s; destruct q, s; reflexivity].')
                L.append('Qed.')
            else:
                L.append('Proof.')
                L.append('  apply (covers_iqh_at %s.%s);' % (mod, const))
                L.append('    [exact %s.%s | intros q s; destruct q, s; reflexivity].' % (mod, thm))
                L.append('Qed.')
            L.append('')
        L.append('Definition cbrows_%02d : list (list (option Trans)) := [' % si)
        for i, (spec, kind, vfile, thm, const) in enumerate(chunk):
            sep = ';' if i + 1 < len(chunk) else ''
            L.append('  [' + ';'.join(spec_rows(spec)) + ']' + sep)
        L.append('].')
        L.append('')
        L.append('Lemma cb_%02d_covers : Forall covers (map row_to_tm cbrows_%02d).' % (si, si))
        L.append('Proof.')
        L.append('  unfold cbrows_%02d; cbn [map].' % si)
        chain = 'Forall_nil covers'
        for cov in reversed(covs):
            chain = 'Forall_cons _ %s (%s)' % (cov, chain)
        L.append('  exact (%s).' % chain)
        L.append('Qed.')
        nwrote += write_if_changed(os.path.join(OUT, name + '.v'), '\n'.join(L) + '\n')

    # ---- Closeout.v ----
    L = []
    L.append('(** GENERATED by tools/closeout/gen_stages.py -- do not edit.')
    L.append('')
    L.append('    The route-A partial closeout.  [proven_rows] concatenates the stage')
    L.append('    tables (%d rows, each with a kernel-checked [covers] proof);' % len(rows))
    L.append('    [remaining_rows] (CoreRows.v) lists the %d distinct undecided'
             % len(core_specs))
    L.append('    machines; [shadow_rows] (SH_00.v) the %d 0RB re-root shadows'
             % len(shadows))
    L.append('    discharged into [skipped]\'s re-root disjunct (ShadowKit.v).  The')
    L.append('    reflective check [census_rows_split] states every frozen row is in')
    L.append('    one of the three tables; [deferred_split_sh] then gives')
    L.append('')
    L.append('      [closeout_partial : Deferred D_census tm ->')
    L.append('                          boarded tm \\/ skipped D_remaining tm].')
    L.append('')
    L.append('    No census walk is involved, and no census .vo is loaded: this file')
    L.append('    only consumes the frozen row tables (Deferred_Data) and the')
    L.append('    per-board theorems.  The corollary chaining [census_decided] lives')
    L.append('    in CloseoutFinal.v, which loads the committed census .vo and')
    L.append('    therefore compiles only under the census opam switch (the committed')
    L.append('    .vo are OCaml-toolchain-specific). *)')
    L.append('From Coq Require Import Bool List.')
    L.append('From BBB4 Require Import BBB4_Statement.')
    L.append('From BBB4.Census Require Import TNF_QH Deferred_Defs Deferred_Data.')
    L.append('From BBB4.Closeout Require Import CloseoutKit ShadowKit CoreRows SH_00 %s.'
             % ' '.join(stage_names))
    L.append('Import ListNotations.')
    L.append('')
    L.append('Definition proven_rows : list (list (option Trans)) :=')
    L.append('  ' + ' ++ '.join('cbrows_%02d' % i for i in range(len(stages))) + '.')
    L.append('')
    L.append('Lemma proven_rows_covers : Forall covers (map row_to_tm proven_rows).')
    L.append('Proof.')
    L.append('  unfold proven_rows.')
    L.append('  repeat rewrite map_app.')
    L.append('  repeat (apply Forall_app; split);')
    L.append('    first [ %s ].' % '\n          | '.join(
        'exact cb_%02d_covers' % i for i in range(len(stages))))
    L.append('Qed.')
    L.append('')
    L.append('Definition shadow_rows : list (list (option Trans)) := shrows_00.')
    L.append('')
    L.append('Lemma census_rows_split :')
    L.append('  forallb (fun r => row_inb r proven_rows || row_inb r remaining_rows')
    L.append('                    || row_inb r shadow_rows)')
    L.append('          deferred_rows = true.')
    L.append('Proof. vm_compute. reflexivity. Qed.')
    L.append('')
    L.append('Theorem closeout_partial : forall tm,')
    L.append('  Deferred D_census tm -> boarded tm \\/ skipped D_remaining tm.')
    L.append('Proof.')
    L.append('  exact (deferred_split_sh deferred_rows proven_rows remaining_rows')
    L.append('           shadow_rows census_rows_split proven_rows_covers')
    L.append('           sh_00_skipped).')
    L.append('Qed.')
    nwrote += write_if_changed(os.path.join(OUT, 'Closeout.v'), '\n'.join(L) + '\n')

    # ---- CoreRows.v (the distinct undecided machines) ----
    L = []
    L.append('(** GENERATED by tools/closeout/gen_stages.py -- do not edit.')
    L.append('')
    L.append('    The CORE remaining rows: the %d distinct undecided machines.'
             % len(core_specs))
    L.append('    The %d SHADOW rows (0RB machines whose re-roots land in the'
             % len(shadows))
    L.append('    orbit of a core row -- the bbchallenge community\'s 0RB')
    L.append('    observation) are NOT listed here: SH_00.v proves each one')
    L.append('    satisfies [skipped]\'s re-root disjunct against this table, so')
    L.append('    they resolve automatically as core machines are boarded. *)')
    L.append('From Coq Require Import List.')
    L.append('From BBB4 Require Import BBB4_Statement.')
    L.append('From BBB4.Census Require Import TNF_QH Deferred_Defs.')
    L.append('Import ListNotations.')
    L.append('')
    L.append('Definition remaining_rows : list (list (option Trans)) := [')
    for i, spec in enumerate(core_specs):
        sep = ';' if i + 1 < len(core_specs) else ''
        L.append('  (* %s *)' % spec)
        L.append('  [' + ';'.join(spec_rows(spec)) + ']' + sep)
    L.append('].')
    L.append('')
    L.append('Definition D_remaining : list TM := map row_to_tm remaining_rows.')
    nwrote += write_if_changed(os.path.join(OUT, 'CoreRows.v'), '\n'.join(L) + '\n')

    # ---- SH_00.v (the shadow discharges) ----
    L = []
    L.append('(** GENERATED by tools/closeout/gen_stages.py -- do not edit.')
    L.append('')
    L.append('    The %d SHADOW rows: each is a 0RB machine that runs an'
             % len(shadows))
    L.append('    all-blank prefix and then IS its re-root started fresh, and the')
    L.append('    re-root lies in the census orbit of a CORE row (CoreRows.v).')
    L.append('    Each lemma proves the row\'s every completion satisfies the')
    L.append('    re-root disjunct of [skipped] (ShadowKit.v): the prefix is one')
    L.append('    [vm_compute], the orbit path is [Deferred] constructors, and the')
    L.append('    row-level [TM_le] fact is checked reflectively.  A wrong partner,')
    L.append('    path or prefix fails to compile. *)')
    L.append('From Coq Require Import Bool List.')
    L.append('From BBB4 Require Import BBB4_Statement Mirror.')
    L.append('From BBB4.Census Require Import TNF_QH Deferred_Defs Reroot.')
    L.append('From BBB4.Closeout Require Import CloseoutKit ShadowKit CoreRows.')
    L.append('Import ListNotations.')
    L.append('')
    shnames = []
    for i, sh in enumerate(shadows):
        rowlit = '[' + ';'.join(spec_rows(sh['spec'])) + ']'
        plit = '[' + ';'.join(spec_rows(sh['partner'])) + ']'
        base = '(TM_swap StA St%s (row_to_tm %s))' % (sh['qs'], rowlit)
        mid = ops_term(base, sh['ops'])
        nm = 'sh_00_%04d' % i
        shnames.append(nm)
        L.append('(* %s  ~>  %s  (q*=%s, t=%d) *)'
                 % (sh['spec'], sh['partner'], sh['qs'], sh['t']))
        L.append('Lemma %s : forall tm\', TM_le (row_to_tm %s) tm\' ->'
                 % (nm, rowlit))
        L.append('  skipped D_remaining tm\'.')
        L.append('Proof.')
        L.append('  assert (Hpre : prefix_ok (row_to_tm %s) St%s %d = true)'
                 % (rowlit, sh['qs'], sh['t']))
        L.append('    by (vm_compute; reflexivity).')
        L.append('  assert (Hdef : forall tm2, TM_le (row_to_tm %s) tm2 ->'
                 % rowlit)
        L.append('    Deferred D_remaining (TM_swap StA St%s tm2)).' % sh['qs'])
        L.append('  { intros tm2 Hle2.')
        for op in sh['ops']:
            if op[0] == 'mirror':
                L.append('    apply Deferred_mirror.')
            else:
                L.append('    apply (Deferred_swap _ St%s St%s _);' % (op[1], op[2]))
                L.append('      [congruence | congruence | congruence |].')
        L.append('    apply (Deferred_base _ (row_to_tm %s) _).' % plit)
        L.append('    - apply in_map. apply row_inb_In. vm_compute. reflexivity.')
        L.append('    - apply (TM_le_trans _ %s _).' % mid)
        L.append('      + apply tm_le_b_sound. vm_compute. reflexivity.')
        monos = []
        for op in reversed(sh['ops']):
            monos.append('apply TM_le_mirror_mono.' if op[0] == 'mirror'
                         else 'apply TM_le_swap_mono.')
        monos.append('apply TM_le_swap_mono. exact Hle2. }')
        L.append('      + ' + ' '.join(monos))
        L.append('  exact (shadow_at _ St%s %d _ Hpre Hdef).' % (sh['qs'], sh['t']))
        L.append('Qed.')
        L.append('')
    L.append('Definition shrows_00 : list (list (option Trans)) := [')
    for i, sh in enumerate(shadows):
        sep = ';' if i + 1 < len(shadows) else ''
        L.append('  [' + ';'.join(spec_rows(sh['spec'])) + ']' + sep)
    L.append('].')
    L.append('')
    L.append('Lemma sh_00_skipped :')
    L.append('  Forall (fun h => forall tm, TM_le h tm -> skipped D_remaining tm)')
    L.append('         (map row_to_tm shrows_00).')
    L.append('Proof.')
    L.append('  unfold shrows_00; cbn [map].')
    chain = 'Forall_nil _'
    for nm in reversed(shnames):
        chain = 'Forall_cons _ %s (%s)' % (nm, chain)
    L.append('  exact (%s).' % chain)
    L.append('Qed.')
    nwrote += write_if_changed(os.path.join(OUT, 'SH_00.v'), '\n'.join(L) + '\n')

    # ---- CloseoutFinal.v (census opam switch only) ----
    L = []
    L.append('(** GENERATED by tools/closeout/gen_stages.py -- do not edit.')
    L.append('')
    L.append('    The certified partial census statement: chain [census_decided]')
    L.append('    (Census/Compute/Census_Theorem.v, committed .vo) with')
    L.append('    [closeout_partial] (Closeout.v).')
    L.append('')
    L.append('      [census_boarded : forall tm, QHBound B_census tm \\/ boarded tm')
    L.append('                                   \\/ skipped D_remaining tm]')
    L.append('')
    L.append('    -- every (4,2) machine is a bounded quasihalter, or has its')
    L.append('    quasihalting behaviour settled by a board, or is skipped: one of')
    L.append('    the %d core [remaining_rows] machines, or a 0RB re-root shadow'
             % len(core_specs))
    L.append('    of one (%d at generation time; ShadowKit.v).' % len(shadows))
    L.append('')
    L.append('    This file LOADS the committed census .vo, which are')
    L.append('    OCaml-toolchain-specific: compile it on the census box under the')
    L.append('    census opam switch (see tools/census_cache.py), not in a fresh')
    L.append('    container.  It involves NO census re-walk. *)')
    L.append('From Coq Require Import List.')
    L.append('From BBB4 Require Import BBB4_Statement.')
    L.append('From BBB4.Census Require Import TNF_QH Deferred_Defs Deferred_Data Run.')
    L.append('From BBB4.Census.Compute Require Import Census_Theorem.')
    L.append('From BBB4.Closeout Require Import CloseoutKit ShadowKit CoreRows Closeout.')
    L.append('Import ListNotations.')
    L.append('')
    L.append('Theorem census_boarded : forall tm,')
    L.append('  QHBound B_census tm \\/ boarded tm \\/ skipped D_remaining tm.')
    L.append('Proof.')
    L.append('  intro tm.')
    L.append('  destruct (census_decided tm) as [H | H]; [left; exact H | right].')
    L.append('  exact (closeout_partial tm H).')
    L.append('Qed.')
    nwrote += write_if_changed(os.path.join(OUT, 'CloseoutFinal.v'), '\n'.join(L) + '\n')

    # ---- BBB4_Theorem.v (the `make proof` target; census opam switch only) ----
    CHAMPION = '1RB1LD_1RC1RB_1LC1LA_0RC0RD'
    CHAMPION_SCORE = 32779478
    PREV_CHAMPION_SCORE = 66349
    L = []
    L.append('(** GENERATED by tools/closeout/gen_stages.py -- do not edit.')
    L.append('')
    L.append('    The top-level BBB(4) target, modulo the residue:')
    L.append('')
    L.append('      [bbb4_target : forall tm,')
    L.append('         QHBound champion_score tm \\/ NeverQuasiHaltsSt tm')
    L.append('         \\/ skipped D_remaining tm]')
    L.append('')
    L.append('    -- every (4,2) machine either quasihalts with every quiet state')
    L.append('    quiet before index %s (the champion\'s score), or never'
             % '{:,}'.format(CHAMPION_SCORE))
    L.append('    quasihalts, or is SKIPPED: one of the %d distinct undecided'
             % len(core_specs))
    L.append('    core machines (tools/closeout/core_rows.txt), or one of their')
    L.append('    %d 0RB re-root shadows (shadow_rows.tsv), which resolve'
             % len(shadows))
    L.append('    automatically as core machines are boarded.')
    if CHAMPION in core_specs:
        L.append('')
        L.append('    The champion [%s] is itself one of the' % CHAMPION)
        L.append('    skipped machines (its 32.8M-step prefix has no board yet),')
        L.append('    so this is NOT a proof that BBB(4) = %s --'
                 % '{:,}'.format(CHAMPION_SCORE))
        L.append('    see docs/CLAIMS.md.')
    else:
        L.append('')
        L.append('    NOTE: the champion [%s] is no longer on the' % CHAMPION)
        L.append('    residue list -- revisit docs/CLAIMS.md and this statement.')
    L.append('')
    L.append('    Like CloseoutFinal.v this file loads the committed census .vo:')
    L.append('    compile under the census opam switch (see tools/census_cache.py).')
    L.append('    It involves NO census re-walk. *)')
    L.append('From Coq Require Import Arith List Lia.')
    L.append('From BBB4 Require Import BBB4_Statement.')
    L.append('From BBB4.Census Require Import TNF_QH Deferred_Defs Deferred_Data Run.')
    L.append('From BBB4.Closeout Require Import CloseoutKit ShadowKit CoreRows Closeout CloseoutFinal.')
    L.append('Import ListNotations.')
    L.append('')
    # Horner digit form: a bare 32779478 nat literal is abstracted to
    # [Nat.of_num_uint] (the large-number guard), which [lia] cannot see
    # through, so the qhbound_mono side goals below would fail.
    horner = str(CHAMPION_SCORE)[0]
    for d in str(CHAMPION_SCORE)[1:]:
        horner = '(%s)*10 + %s' % (horner, d)
    L.append('(** The conjectured BBB(4) value: the champion\'s score,')
    L.append('    %s.  Written digit by digit (Horner form)'
             % '{:,}'.format(CHAMPION_SCORE))
    L.append('    because a bare literal this large is abstracted to')
    L.append('    [Nat.of_num_uint], which [lia] cannot see through. *)')
    L.append('Definition champion_score : nat :=')
    L.append('  %s.' % horner)
    L.append('')
    L.append('Theorem bbb4_target : forall tm,')
    L.append('  QHBound champion_score tm \\/ NeverQuasiHaltsSt tm')
    L.append('  \\/ skipped D_remaining tm.')
    L.append('Proof.')
    L.append('  intro tm.')
    L.append('  destruct (census_boarded tm) as [H | [[H | (Hnh & Hb & Hq)] | H]].')
    L.append('  - left. apply (qhbound_mono B_census);')
    L.append('      [unfold B_census, champion_score; lia | exact H].')
    L.append('  - right; left; exact H.')
    L.append('  - left. apply (qhbound_mono B_board);')
    L.append('      [unfold B_board, champion_score; lia | exact Hb].')
    L.append('  - right; right; exact H.')
    L.append('Qed.')
    L.append('')
    L.append('(** The reading `make proof` reports: skipping the residue, every')
    L.append('    machine quasihalts by the champion\'s score or never quasihalts. *)')
    L.append('Corollary bbb4_target_skipping_residue : forall tm,')
    L.append('  ~ skipped D_remaining tm ->')
    L.append('  QHBound champion_score tm \\/ NeverQuasiHaltsSt tm.')
    L.append('Proof.')
    L.append('  intros tm Hres.')
    L.append('  destruct (bbb4_target tm) as [H | [H | H]];')
    L.append('    [left; exact H | right; exact H | destruct (Hres H)].')
    L.append('Qed.')
    L.append('')
    L.append('(** The PREVIOUS champion\'s score: [CloseoutKit.B_board] =')
    L.append('    %s (1RB0LD_1LC0LA_1LA0LC_1RD1RC, theories/Machines/'
             % '{:,}'.format(PREV_CHAMPION_SCORE))
    L.append('    Counters/BlankTail_66349.v) -- the bound [boarded] carries. *)')
    L.append('Definition prev_champion_score : nat := B_board.')
    L.append('')
    L.append('(** The community-facing reading: every machine the theorem')
    L.append('    decides quasihalts by the PREVIOUS champion\'s score or never')
    L.append('    quasihalts -- the four previous champions are among the')
    L.append('    decided -- so among all known (4,2) machines, only the')
    L.append('    (skipped, undecided) champion exceeds the previous record. *)')
    L.append('Corollary bbb4_decided_le_prev_champion : forall tm,')
    L.append('  ~ skipped D_remaining tm ->')
    L.append('  QHBound prev_champion_score tm \\/ NeverQuasiHaltsSt tm.')
    L.append('Proof.')
    L.append('  intros tm Hres.')
    L.append('  destruct (census_boarded tm) as [H | [[H | (Hnh & Hb & Hq)] | H]].')
    L.append('  - left. apply (qhbound_mono B_census);')
    L.append('      [unfold B_census, prev_champion_score, B_board; lia | exact H].')
    L.append('  - right; exact H.')
    L.append('  - left; exact Hb.')
    L.append('  - destruct (Hres H).')
    L.append('Qed.')
    L.append('')
    L.append('Print Assumptions bbb4_target.')
    L.append('Print Assumptions bbb4_decided_le_prev_champion.')
    nwrote += write_if_changed(os.path.join(OUT, 'BBB4_Theorem.v'), '\n'.join(L) + '\n')

    # ---- keep the _CoqProject Closeout section in sync ----
    cp = os.path.join(ROOT, '_CoqProject')
    lines = [l for l in open(cp).read().splitlines()
             if not l.startswith('theories/Closeout/')]

    # ---- and make sure every board the stages Require has a build rule ----
    listed = set(l.strip() for l in lines if l.strip().endswith('.v'))
    need = board_closure(sorted(set(r[2] for r in rows)))
    missing = sorted(need - listed)
    if missing:
        while lines and not lines[-1].strip():
            lines.pop()
        lines.append('')
        lines.append('# board files (+ their deps) added automatically by '
                     'tools/closeout/gen_stages.py')
        lines.extend(missing)
    print('board closure: %d files, %d added to _CoqProject' %
          (len(need), len(missing)))
    for m in missing[:10]:
        print('  + %s' % m)
    if len(missing) > 10:
        print('  + ... %d more' % (len(missing) - 10))

    while lines and not lines[-1].strip():
        lines.pop()
    lines.append('')
    lines.append('theories/Closeout/CloseoutKit.v')
    lines.append('theories/Closeout/ShadowKit.v')
    lines.append('theories/Closeout/CoreRows.v')
    lines.append('theories/Closeout/SH_00.v')
    for name in stage_names:
        lines.append('theories/Closeout/%s.v' % name)
    lines.append('theories/Closeout/Closeout.v')
    # CloseoutFinal.v and BBB4_Theorem.v are deliberately NOT in _CoqProject:
    # they load the committed census .vo (toolchain-specific), so the default
    # `make' must not depend on them.  `make proof' compiles them explicitly.

    # Defensive: a .v listed twice makes coq_makefile emit duplicate doc-target
    # rules, and `make' warns "given more than once in the same rule" for each.
    # Keep first occurrences; blanks and comments pass through untouched.
    seen_v, deduped = set(), []
    for l in lines:
        s = l.strip()
        if s.endswith('.v'):
            if s in seen_v:
                continue
            seen_v.add(s)
        deduped.append(l)
    if len(deduped) != len(lines):
        print('_CoqProject: dropped %d duplicate .v line(s)'
              % (len(lines) - len(deduped)))
    lines = deduped
    nwrote += write_if_changed(cp, '\n'.join(lines) + '\n')
    print('stages: %d (%d rows) + Closeout.v (%d remaining)'
          ' + CloseoutFinal.v + BBB4_Theorem.v'
          % (len(stages), len(rows), len(remaining)))
    print('files rewritten: %d (unchanged files keep their mtime)' % nwrote)


if __name__ == '__main__':
    main()
