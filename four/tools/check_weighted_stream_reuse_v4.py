"""Use dense gate tables for new stream batches; preserve older producers.

V4 retains the exhaustive-target syntax fix and changes only certificate
rendering. Every generated closure, ranking and target boot is still replayed
by the same WeightedSuffix checker and independently kernel audited.
"""
from pathlib import Path

import check_weighted_stream_reuse as pipeline
from kernel_audit_cache import digest
from weighted_render_v4 import HEADER,render

ROOT=Path(__file__).resolve().parents[1]
_sources=pipeline.sources
_pipeline_source=Path(pipeline.__file__).resolve()


def sources(registry):
    rows,ids,inputs=_sources(registry)
    for path in (_pipeline_source,ROOT/'tools/weighted_render_v3.py',ROOT/'tools/weighted_render_v4.py'):
        inputs[str(path.relative_to(ROOT))]=digest(path)
    return rows,ids,inputs


def main():
    if HEADER!=pipeline.CERT_HEADER:raise ValueError('Renderer header interface changed')
    pipeline.sources=sources
    pipeline.render=render
    pipeline.__file__=__file__
    pipeline.main()


if __name__=='__main__':main()
