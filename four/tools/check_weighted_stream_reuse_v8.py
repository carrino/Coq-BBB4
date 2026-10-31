"""Use fresh coefficient vectors when renaming compact shared certificates.

V8 fixes a candidate-producer false-negative: compact-v2 decoding can alias a
coefficient list across distinct target certificates. The frozen older rename
mutated that shared list repeatedly. This version installs a nonmutating
rename for both native selection and Coq source generation. Every retained
machine still receives the unchanged kernel-checked tail proof.
"""
from pathlib import Path

import check_weighted_stream_reuse_v7 as native
from kernel_audit_cache import digest
import weighted_tail_data
from weighted_transform_v2 import transform

ROOT=Path(__file__).resolve().parents[1]


def sources(registry):
    rows,ids,inputs=native.sources(registry)
    for path in (Path(native.__file__),ROOT/'tools/weighted_transform_v2.py'):
        inputs[str(path.resolve().relative_to(ROOT))]=digest(path)
    return rows,ids,inputs


def main():
    native.coq.transform=transform
    weighted_tail_data.transform=transform
    pipeline=native.pipeline
    pipeline.sources=sources;pipeline.select=native.select;pipeline.probe=native.probe
    pipeline.template=native.coq.template;pipeline.generate=native.coq.generate
    pipeline.COMMON=native.coq.COMMON;pipeline.__file__=__file__
    pipeline.main()


if __name__=='__main__':main()
