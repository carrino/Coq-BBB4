#!/usr/bin/env python3
"""LE12 (UNTRUSTED generator): write a FuelWideTr instruction-target
certificate as several small Coq files, so that no single file has to
elaborate the whole multi-megabyte term (SCOPING_INSTR 7.4.LE12).

FuelWideTr's n = 6 certificates for the two heavy sweepers check in ~12 s
and ~0.7 GB once the certificate is a compiled constant; elaborating the
6 MB term in the same file is what took ~11 GB.  Here every list inside the
certificate is its own typed constant ([list (positive * nat)] or [list
positive]; typing a big list literal in place, as an argument of
[NgRankE], is what is slow), cut into pieces of at most CHUNK bytes and
spread over part files; the last file rebuilds the same certificate with
[++] (the checker's [vm_compute] evaluates the concatenation).  The checked statement is unchanged.

    python3 tools/closeouttr/le12/fuel_split.py JSONL SPEC [--chunk BYTES]

writes theories/Machines/FuelSplitTr/FS_<SPEC>_<k>.v (chunks) and
FS_<SPEC>.v (the certificate [cert_<SPEC>] and [check_<SPEC>]), and lists
them in _CoqProject.
"""
import json
import os
import re
import sys

REPO = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))
OUT = os.path.join(REPO, 'theories', 'Machines', 'FuelSplitTr')
HDR = ('From Coq Require Import List ZArith.\n'
       'From BBB4 Require Import BBB4_Statement BBBT4_Statement.\n'
       'From BBB4.Checkers Require Import NGram.\n'
       'Import ListNotations.\n\n')


def top_split(s, sep=';'):
    """split s at top-level (bracket depth 0) separators"""
    out, depth, cur = [], 0, []
    for ch in s:
        if ch in '([':
            depth += 1
        elif ch in ')]':
            depth -= 1
        if ch == sep and depth == 0:
            out.append(''.join(cur).strip())
            cur = []
        else:
            cur.append(ch)
    if ''.join(cur).strip():
        out.append(''.join(cur).strip())
    return out


def parse_cert(cert):
    body = cert[cert.index('match target with') + len('match target with'):]
    body = body[:body.rindex('end')]
    cases = re.split(r'\n\s*\| \((St[ABCD]), (S[01])\) => ', '\n' + body)
    assert cases[0].strip() == '', cases[0][:100]
    res = []
    for i in range(1, len(cases), 3):
        q, s, rhs = cases[i], cases[i + 1], cases[i + 2].strip()
        assert rhs[0] == '(' and rhs[-1] == ')'
        parts = top_split(rhs[1:-1], ',')
        assert len(parts) == 2, len(parts)
        comps, poss = parts
        assert comps[0] == '[' and comps[-1] == ']'
        res.append(((q, s), top_split(comps[1:-1]), poss))
    assert len(res) == 8
    return res


def ws_split(s):
    """split s at top-level whitespace"""
    out, depth, cur = [], 0, []
    for ch in s:
        if ch in '([':
            depth += 1
        elif ch in ')]':
            depth -= 1
        if ch.isspace() and depth == 0:
            if cur:
                out.append(''.join(cur))
            cur = []
        else:
            cur.append(ch)
    if cur:
        out.append(''.join(cur))
    return out


def list_items(txt):
    txt = txt.strip()
    assert txt[0] == '[' and txt[-1] == ']', txt[:50]
    return top_split(txt[1:-1]) if txt[1:-1].strip() else []


def main():
    args = sys.argv[1:]
    chunk = 250000
    if '--chunk' in args:
        i = args.index('--chunk')
        chunk = int(args[i + 1])
        del args[i:i + 2]
    jsonl, spec = args
    d = None
    for line in open(jsonl):
        e = json.loads(line)
        if e.get('spec') == spec and e.get('status') == 'found':
            d = e
            break
    assert d, 'no certificate for %s' % spec
    cases = parse_cert(d['cert'])
    os.makedirs(OUT, exist_ok=True)
    raws = []          # (name, type, items)
    counter = [0]

    def raw(ty, items):
        """one or more raw list constants (each <= chunk bytes), glued by ++"""
        names, part, sz = [], [], 0
        for it in items:
            if part and sz + len(it) > chunk:
                nm = 'fs_%s_r%d' % (spec, counter[0])
                counter[0] += 1
                raws.append((nm, ty, part))
                names.append(nm)
                part, sz = [], 0
            part.append(it)
            sz += len(it) + 2
        nm = 'fs_%s_r%d' % (spec, counter[0])
        counter[0] += 1
        raws.append((nm, ty, part))
        names.append(nm)
        return '(' + ' ++ '.join(names) + ')'

    tabs = {}
    for (q, s), comps, poss in cases:
        out = []
        for c in comps:
            f = ws_split(c)
            if f[0] == 'NgRankE':
                assert len(f) == 2
                out.append('NgRankE ' + raw('list (positive * nat)', list_items(f[1])))
            elif f[0] == 'NgPattE':
                assert len(f) == 6, f[:5]
                out.append('NgPattE %s %s %s %s %s' % (f[1], f[2], f[3],
                           raw('list (positive * nat)', list_items(f[4])),
                           raw('list positive', list_items(f[5]))))
            else:
                raise SystemExit('unexpected component ' + f[0])
        tabs[(q, s)] = (out, raw('list positive', list_items(poss)))
    files, cur, cursz = [], [], 0
    for r in raws:
        sz = sum(len(x) for x in r[2])
        if cur and cursz + sz > chunk:
            files.append(cur)
            cur, cursz = [], 0
        cur.append(r)
        cursz += sz
    if cur:
        files.append(cur)
    base = 'FS_%s' % spec
    mods = []
    for k, fl in enumerate(files):
        mod = '%s_%d' % (base, k)
        mods.append(mod)
        with open(os.path.join(OUT, mod + '.v'), 'w') as f:
            f.write('(** GENERATED by tools/closeouttr/le12/fuel_split.py: part %d of the\n'
                    '    FuelWideTr certificate for %s (SCOPING_INSTR 7.4.LE12). *)\n' % (k, spec))
            f.write(HDR)
            for nm, ty, items in fl:
                f.write('Definition %s : %s :=\n  [%s].\n\n' % (nm, ty, ';\n   '.join(items)))
    with open(os.path.join(OUT, base + '.v'), 'w') as f:
        f.write('(** GENERATED by tools/closeouttr/le12/fuel_split.py: the FuelWideTr\n'
                '    certificate for %s (n = %d, t = %d, fuel = %d, rounds = %d%s), its\n'
                '    lists glued from the part files, and the check.\n'
                '    (SCOPING_INSTR 7.4.LE12) *)\n'
                % (spec, d['n'], d['t'], d['fuel'], d['rounds'], ', mirrored' if d['mirrored'] else ''))
        f.write('From Coq Require Import List ZArith.\n'
                'From BBB4 Require Import BBB4_Statement BBBT4_Statement Mirror.\n'
                'From BBB4.Census Require Import Deferred_Defs.\n'
                'From BBB4.Checkers Require Import NGram FuelWideTr.\n'
                'From BBB4.Machines.FuelSplitTr Require Import %s.\n'
                'Import ListNotations.\n\n' % ' '.join(mods))
        f.write('Definition cert_%s : Instr -> list ngcomp * list positive :=\n'
                'fun target : Instr => match target with\n' % spec)
        for (q, s), _, _ in cases:
            out, poss = tabs[(q, s)]
            f.write('  | (%s, %s) => ([%s], %s)\n' % (q, s, ';\n      '.join(out), poss))
        f.write('  end.\n\n')
        sp = spec.replace('_', '')
        row = '[' + ';'.join('t' + sp[i:i + 3] for i in range(0, 24, 3)) + ']'
        tm = '(row_to_tm %s)' % row
        if d['mirrored']:
            tm = '(mirror_tm %s)' % tm
        f.write('Lemma check_%s : ngram_check_neverqh_fuelwtr %s %d %d %d %d cert_%s = true.\n'
                'Proof. vm_compute. reflexivity. Qed.\n' % (spec, tm, d['n'], d['t'], d['fuel'], d['rounds'], spec))
    cp = os.path.join(REPO, '_CoqProject')
    lines = open(cp).read().split('\n')
    for mod in mods + [base]:
        ent = 'theories/Machines/FuelSplitTr/%s.v' % mod
        if ent not in lines:
            i = lines.index('theories/Checkers/FuelWideTr.v')
            lines.insert(i + 1, ent)
    open(cp, 'w').write('\n'.join(lines))
    print('%d part files, %d raw lists' % (len(mods), len(raws)))


if __name__ == '__main__':
    main()
