#!/usr/bin/env python3
"""Reproduce the B0-return row's partial Fuel certificate and AST batch.

FuelB0ReturnTr proves unbounded B0 recurrence from every finite B0 tape.
The remaining seven instructions are checked independently by the existing
Fuel graph engine, then joined by FuelMixPartialTr.

    python3 tools/closeouttr/b0_return_batch.py find certificates.jsonl
    python3 tools/closeouttr/b0_return_batch.py batch certificates.jsonl --number 38
"""
import argparse
import json
from pathlib import Path
import fuelmixtr_batch as fm
from cbt import write_batch

SPEC = "1RB1RC_0LC0RA_1RA1LD_1LA0LC"


def find(window):
    ft = fm.ft
    table = ft.bp.parse(ft.gf.mirror_mtext(SPEC))
    _, left, right, initial, _ = ft.bp.build_closure(table, window, 0)
    seen = ft.gf.build_fw_closure(table, left, right, (initial, 0, 0))
    adjacent = ft.gf.fw_adj(table, left, right, seen)
    candidates = ft.pattern_candidates(window, window + 1)
    delta = ft.make_pattern_delta(table, window)
    record = dict(spec=SPEC, n=window, t=0, contexts=len(seen), mirrored=True,
                  targets={}, fuel=8 * len(seen) + 64,
                  rounds=len(left) + len(right) + 4)
    certificates = {}
    for state in range(4):
        for symbol in range(2):
            instruction = state, symbol
            if instruction == (1, 0):
                record["targets"][str(instruction)] = False
                continue
            cert = ft.instruction_procedure(table, window, adjacent, seen,
                                            instruction, candidates, delta)
            ok = cert is not None and ft.instruction_check(
                table, window, adjacent, seen, instruction, *cert)
            record["targets"][str(instruction)] = ok
            if not ok:
                raise RuntimeError("Fuel did not certify %s" % (instruction,))
            certificates[instruction] = cert
    record["cert"] = fm.emit_cert(certificates)
    return record


def batch(record, number, overwrite=False):
    if record["spec"] != SPEC or not record["mirrored"]:
        raise ValueError("unsupported manual recurrence")
    for state in range(4):
        for symbol in range(2):
            if ((state, symbol) != (1, 0)
                    and not record["targets"][str((state, symbol))]):
                raise ValueError("missing instruction certificate")
    suffix = "AST_%02d_0000" % number
    cert_name, row_name = "cert_" + suffix, "r_" + suffix
    preamble = """Definition skipB0 (q : Instr) : bool :=
  match q with (StB,S0) => true | _ => false end.
Definition %s : Instr -> list fmxcomp * list positive :=
%s.""" % (cert_name, record["cert"].rstrip().rstrip("."))
    proof = """assert (Hmanual : forall N, exists j, N<=j /\\
    FiresAt (row_to_tm %(row)s) (StB,S0) j).
  { apply bf_B0_recurrent; reflexivity. }
  apply coversTr_nqh,neverqhtr_mirror.
  apply (ngram_check_neverqh_fuelmixtr_except_sound _ %(n)d %(t)d %(fuel)d %(rounds)d skipB0 %(cert)s).
  - intros [[] []] H N;try discriminate.
    destruct (Hmanual N) as (j&Hj&Hfire).
    exists j. split;[exact Hj|]. apply mirror_fires. exact Hfire.
  - vm_compute. reflexivity.""" % dict(row=row_name, cert=cert_name,
        **{k: record[k] for k in ("n", "t", "fuel", "rounds")})
    write_batch("AST", number,
        ["From BBB4 Require Import CTape Mirror.",
         "From BBB4.Checkers Require Import NGram FuelMixTr FuelMixPartialTr.",
         "From BBB4.Counters Require Import FuelB0ReturnTr.",
         "From BBB4.CensusTr Require Import TNF_QHTr."], [(SPEC, proof)],
        "finite-tape B0 recurrence and partial Fuel certificates",
        overwrite=overwrite, preamble=preamble)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    finder = commands.add_parser("find")
    finder.add_argument("output", type=Path)
    finder.add_argument("--window", type=int, default=3)
    emitter = commands.add_parser("batch")
    emitter.add_argument("certificates", type=Path)
    emitter.add_argument("--number", type=int, default=38)
    emitter.add_argument("--overwrite", action="store_true")
    args = parser.parse_args()
    if args.command == "find":
        record = find(args.window)
        args.output.write_text(json.dumps(record, sort_keys=True) + "\n")
    else:
        batch(json.loads(args.certificates.read_text()), args.number, args.overwrite)


if __name__ == "__main__":
    main()
