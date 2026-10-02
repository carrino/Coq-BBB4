#!/usr/bin/env python3
"""Reproduce two paired-word recurrence and partial Fuel certificates.

    python3 tools/closeouttr/paired_carry_batch.py find certificates.jsonl
    python3 tools/closeouttr/paired_carry_batch.py batch certificates.jsonl --number 59
"""
import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fuelmixtr_batch as fm
from cbt import write_batch

ROWS = {
    "1RB1LD_1LC0RA_0LD0LB_1RD0RB": (0, False, ("StA", "StB", "StC", "StD"), 20, 1),
    "1RB0LD_0RC0RA_1LC0LA_1LA1RC": (3, True, ("StD", "StA", "StB", "StC"), 17, 0),
}
STATES = ("StA", "StB", "StC", "StD")


def find(spec, n, target_state=None):
    if target_state is None:
        target_state = ROWS[spec][0]
    ft = fm.ft
    table = ft.bp.parse(ft.gf.mirror_mtext(spec))
    _, left, right, initial, _ = ft.bp.build_closure(table, n, 0)
    seen = ft.gf.build_fw_closure(table, left, right, (initial, 0, 0))
    adjacent = ft.gf.fw_adj(table, left, right, seen)
    candidates = ft.pattern_candidates(n, n + 1)
    delta = ft.make_pattern_delta(table, n)
    record = dict(spec=spec, n=n, contexts=len(seen), mirrored=True, targets={},
                  fuel=8 * len(seen) + 64, rounds=len(left) + len(right) + 4, t=0)
    certificates = {}
    for state in range(4):
        for symbol in range(2):
            instruction = state, symbol
            if instruction == (target_state, 1):
                record["targets"][str(instruction)] = False
                continue
            cert = ft.instruction_procedure(table, n, adjacent, seen, instruction,
                                            candidates, delta)
            ok = cert is not None and ft.instruction_check(
                table, n, adjacent, seen, instruction, *cert)
            record["targets"][str(instruction)] = ok
            if not ok:
                raise RuntimeError("Fuel did not certify %s at %s" % (spec, instruction))
            certificates[instruction] = cert
    record["cert"] = fm.emit_cert(certificates)
    return record


def batch(records, number, overwrite):
    preamble, entries = [], []
    for i, record in enumerate(records):
        spec = record["spec"]
        state, manual_mirrored, states, boot, ones = ROWS[spec]
        if not record["mirrored"]:
            raise ValueError("expected mirrored Fuel certificate")
        for q in range(4):
            for symbol in range(2):
                if (q, symbol) != (state, 1) and not record["targets"][str((q, symbol))]:
                    raise ValueError("missing instruction certificate")
        suffix = "AST_%02d_%04d" % (number, i)
        row, cert, skip = "r_" + suffix, "cert_" + suffix, "skip_" + suffix
        preamble.append("Definition %s(q:Instr):bool:=\n  match q with (%s,S1)=>true|_=>false end."
                        % (skip, STATES[state]))
        preamble.append("Definition %s:Instr->list fmxcomp*list positive:=\n%s."
                        % (cert, record["cert"].rstrip().rstrip(".")))
        machine = "(row_to_tm %s)" % row
        if manual_mirrored:
            machine = "(mirror_tm %s)" % machine
        proof = """assert(Hmanual:forall N,exists j e,N<=j /\\
    stepn %(machine)s j InitES=Some e /\\instr_of e=(%(target)s,S1)).
  { eapply paired_carry_A1_recurrent with (qa:=%(qa)s)(qb:=%(qb)s)(qc:=%(qc)s)(qd:=%(qd)s);try reflexivity.
    exists %(boot)d,[],%(ones)d,0. rewrite <-lift_c0. apply csteps_lift. vm_compute. reflexivity. }
  apply coversTr_nqh,neverqhtr_mirror.
  apply(ngram_check_neverqh_fuelmixtr_except_sound _ %(n)d %(t)d %(fuel)d %(rounds)d %(skip)s %(cert)s).
  - intros [[] []]H N;try discriminate.
    destruct(Hmanual N)as(j&e&Hj&He&Hi). exists j. split;[exact Hj|].
    %(transport)s exists e. auto.
  - vm_compute. reflexivity.""" % dict(machine=machine, target=STATES[state], boot=boot, ones=ones,
            qa=states[0], qb=states[1], qc=states[2], qd=states[3], skip=skip, cert=cert,
            transport="" if manual_mirrored else "apply mirror_fires.",
            **{k: record[k] for k in ("n", "t", "fuel", "rounds")})
        entries.append((spec, proof))
    write_batch("AST", number,
                ["From BBB4 Require Import CTape Mirror.",
                 "From BBB4.Checkers Require Import NGram FuelMixTr FuelMixPartialTr.",
                 "From BBB4.Counters Require Import PairedCarryTr.",
                 "From BBB4.CensusTr Require Import TNF_QHTr."],
                entries, "paired-word recurrence and partial Fuel certificates",
                overwrite=overwrite, preamble="\n\n".join(preamble))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    finder = sub.add_parser("find")
    finder.add_argument("output", type=Path)
    finder.add_argument("--window", type=int, default=3)
    emitter = sub.add_parser("batch")
    emitter.add_argument("certificates", type=Path)
    emitter.add_argument("--number", type=int, default=59)
    emitter.add_argument("--overwrite", action="store_true")
    args = parser.parse_args()
    if args.command == "find":
        records = [find(spec, args.window) for spec in ROWS]
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text("".join(json.dumps(record, sort_keys=True) + "\n"
                                       for record in records))
    else:
        records = [json.loads(line) for line in args.certificates.read_text().splitlines()
                   if line.strip()]
        batch(records, args.number, args.overwrite)


if __name__ == "__main__":
    main()
