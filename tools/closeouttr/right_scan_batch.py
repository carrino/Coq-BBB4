#!/usr/bin/env python3
"""Reproduce the normalized right scan recurrence and its partial Fuel certificate.

    python3 tools/closeouttr/right_scan_batch.py find certificates.jsonl
    python3 tools/closeouttr/right_scan_batch.py batch certificates.jsonl --number 93
"""
import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cbt import write_batch
from paired_carry_batch import find as find_partial

SPEC = "1RB0LA_0LC1RD_1LC1LA_0RB0RD"


def batch(record, number, overwrite):
    if record["spec"] != SPEC or not record["mirrored"]:
        raise ValueError("unsupported right scan recurrence")
    for state in range(4):
        for symbol in range(2):
            if (state, symbol) != (0, 1) and not record["targets"][str((state, symbol))]:
                raise ValueError("missing instruction certificate")
    suffix = "AST_%02d_0000" % number
    row, cert, skip = "r_" + suffix, "cert_" + suffix, "skip_" + suffix
    preamble = "Definition %s(q:Instr):bool:=\n  match q with(StA,S1)=>true|_=>false end.\n\n" % skip
    preamble += "Definition %s:Instr->list fmxcomp*list positive:=\n%s." % (
        cert, record["cert"].rstrip().rstrip("."))
    proof = """assert(Hmanual:forall N,exists j e,N<=j /\\
    stepn(row_to_tm %(row)s)j InitES=Some e /\\instr_of e=(StA,S1)).
  { apply right_scan_A1_recurrent;reflexivity. }
  apply coversTr_nqh,neverqhtr_mirror.
  apply(ngram_check_neverqh_fuelmixtr_except_sound _ %(n)d %(t)d %(fuel)d %(rounds)d %(skip)s %(cert)s).
  - intros [[] []]H N;try discriminate.
    destruct(Hmanual N)as(j&e&Hj&He&Hi). exists j. split;[exact Hj|].
    apply mirror_fires. exists e. auto.
  - vm_compute. reflexivity.""" % dict(row=row, skip=skip, cert=cert,
        **{k: record[k] for k in ("n", "t", "fuel", "rounds")})
    write_batch("AST", number,
                ["From BBB4 Require Import CTape Mirror.",
                 "From BBB4.Checkers Require Import NGram FuelMixTr FuelMixPartialTr.",
                 "From BBB4.Counters Require Import RightScanReturnTr.",
                 "From BBB4.CensusTr Require Import TNF_QHTr."],
                [(SPEC, proof)], "normalized right scan recurrence and partial Fuel certificates",
                overwrite=overwrite, preamble=preamble)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    finder = sub.add_parser("find")
    finder.add_argument("output", type=Path)
    finder.add_argument("--window", type=int, default=3)
    emitter = sub.add_parser("batch")
    emitter.add_argument("certificates", type=Path)
    emitter.add_argument("--number", type=int, default=93)
    emitter.add_argument("--overwrite", action="store_true")
    args = parser.parse_args()
    if args.command == "find":
        record = find_partial(SPEC, args.window, target_state=0)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(record, sort_keys=True) + "\n")
    else:
        batch(json.loads(args.certificates.read_text()), args.number, args.overwrite)


if __name__ == "__main__":
    main()
