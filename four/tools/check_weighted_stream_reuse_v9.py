"""Replay suffix boards with the proved-equal trie-based finite-wall checker.

Candidate selection remains the unchanged untrusted native selector. The Coq
proof rewrites by FastWall's equality theorem before computation, so the
conclusion and every previously proved soundness theorem stay unchanged.
"""
from pathlib import Path

import check_weighted_stream_reuse_v8 as previous
from kernel_audit_cache import digest
import weighted_tail_data
from weighted_transform_v2 import transform

ROOT=Path(__file__).resolve().parents[1]
native=previous.native
original_template=native.coq.template
COMMON=native.coq.COMMON+'From BBB24 Require Import FastWall.\n'


def sources(registry):
    rows,ids,inputs=previous.sources(registry)
    for path in (Path(previous.__file__),ROOT/'theories/FastWall.v'):
        inputs[str(path.resolve().relative_to(ROOT))]=digest(path)
    return rows,ids,inputs


def template(raw,rows,name,proof):
    text,width=original_template(raw,rows,name,proof)
    if proof:
        old='Proof. vm_compute. reflexivity. Qed.\nDefinition board'
        new='Proof. rewrite <-fast_wt_hybrid_check_eq. vm_compute. reflexivity. Qed.\nDefinition board'
        if text.count(old)!=1:raise ValueError('Tail proof producer changed')
        text=text.replace(old,new)
    return text,width


def main():
    native.coq.transform=transform
    weighted_tail_data.transform=transform
    pipeline=native.pipeline
    pipeline.sources=sources;pipeline.select=native.select;pipeline.probe=native.probe
    pipeline.template=template;pipeline.generate=native.coq.generate
    pipeline.COMMON=COMMON;pipeline.__file__=__file__
    pipeline.main()


if __name__=='__main__':main()
