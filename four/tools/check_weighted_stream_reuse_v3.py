"""Use the syntax-corrected V3 renderer without changing frozen V2 producers.

The shared stream pipeline and both renderer sources are pinned in each
report, alongside this wrapper. All checker logic and audit requirements are
unchanged; V3 omits a redundant wildcard after eight exhaustive branches.
"""
from pathlib import Path

import check_weighted_stream_reuse as pipeline
from kernel_audit_cache import digest
from weighted_render_v3 import HEADER,render

ROOT=Path(__file__).resolve().parents[1]
_sources=pipeline.sources
_pipeline_source=Path(pipeline.__file__).resolve()


def sources(registry):
    rows,ids,inputs=_sources(registry)
    for path in (_pipeline_source,ROOT/'tools/weighted_render_v3.py'):
        inputs[str(path.relative_to(ROOT))]=digest(path)
    return rows,ids,inputs


def main():
    if HEADER!=pipeline.CERT_HEADER:raise ValueError('Renderer header interface changed')
    pipeline.sources=sources
    pipeline.render=render
    # The shared entrypoint pins __file__; retain its own source separately
    # above and identify this actual producer as the command being replayed.
    pipeline.__file__=__file__
    pipeline.main()


if __name__=='__main__':main()
