#!/usr/bin/env python3
"""Reproduce the dyadic pair's partial Fuel certificates and AST batch.

The manual A1 recurrence is proved by DyadicWindowTr. The untrusted finder
checks each other instruction independently with the existing Fuel engine.
FuelMixPartialTr joins those checks with the manual recurrence theorem.

    python3 tools/closeouttr/dyadic_batch.py find certificates.jsonl
    python3 tools/closeouttr/dyadic_batch.py batch certificates.jsonl --number 57
"""
import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fuelmixtr_batch as fm
from cbt import write_batch

ROWS = {
    "1RB0LA_0RC0RB_0LD1LA_1LD0LA": 1,
    "1RB1RC_0RC0RB_0LD1LA_1LD0LA": 3,
}


def find(spec, n):
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
            if instruction == (0, 1):
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
    preamble = ["Definition skipA1 (q : Instr) : bool :=\n"
                "  match q with (StA,S1) => true | _ => false end."]
    entries = []
    for i, record in enumerate(records):
        spec = record["spec"]
        if spec not in ROWS or not record["mirrored"]:
            raise ValueError("unsupported manual recurrence: " + spec)
        for state in range(4):
            for symbol in range(2):
                if (state, symbol) != (0, 1) and not record["targets"][str((state, symbol))]:
                    raise ValueError("missing instruction certificate")
        suffix = "AST_%02d_%04d" % (number, i)
        cert_name = "cert_" + suffix
        row_name = "r_" + suffix
        preamble.append("Definition %s : Instr -> list fmxcomp * list positive :=\n%s."
                        % (cert_name, record["cert"].rstrip().rstrip(".")))
        proof = """assert (Hmanual : forall N, exists j e, N<=j /\\
    stepn (row_to_tm %(row)s) j InitES=Some e /\\ instr_of e=(StA,S1)).
  { eapply dw_blank_A1_recurrent with (ka:=%(ka)d);try reflexivity.
    repeat constructor. }
  apply coversTr_nqh,neverqhtr_mirror.
  apply (ngram_check_neverqh_fuelmixtr_except_sound _ %(n)d %(t)d %(fuel)d %(rounds)d skipA1 %(cert)s).
  - intros [[] []] H N;try discriminate.
    destruct (Hmanual N) as (j&e&Hj&He&Hi).
    exists j. split;[exact Hj|]. apply mirror_fires. exists e. auto.
  - vm_compute. reflexivity.""" % dict(row=row_name, ka=ROWS[spec], cert=cert_name,
                                      **{k: record[k] for k in ("n", "t", "fuel", "rounds")})
        entries.append((spec, proof))
    write_batch("AST", number,
                ["From BBB4 Require Import CTape Mirror.",
                 "From BBB4.Checkers Require Import NGram FuelMixTr FuelMixPartialTr.",
                 "From BBB4.Counters Require Import DyadicWindowTr.",
                 "From BBB4.CensusTr Require Import TNF_QHTr."],
                entries, "binary-window A1 recurrence and partial Fuel certificates",
                overwrite=overwrite, preamble="\n\n".join(preamble))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    finder = sub.add_parser("find")
    finder.add_argument("output", type=Path)
    finder.add_argument("--window", type=int, default=2)
    emitter = sub.add_parser("batch")
    emitter.add_argument("certificates", type=Path)
    emitter.add_argument("--number", type=int, default=57)
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
