"""Replay compiled prefix interfaces while preserving historical build receipts.

The prefix inventory, Coq source hashes, bounds and theorem names must reproduce.
Compiled-object hashes and the local transitive snapshot describe one particular
build and may differ on a clean checkout. A replay saves fresh local evidence;
only the later campaign kernel audit can promote this interface to checked.
"""
import json
from pathlib import Path

import compile_weighted_prefix as prior
from kernel_audit_cache import digest

_original_frozen=prior.frozen
_source=Path(prior.__file__).resolve()


def portable(data):
    data=dict(data);data.pop('compiled_snapshot_sha256',None)
    data['source_artifacts_sha256']={p:h for p,h in data['source_artifacts_sha256'].items()if p.endswith('.v')}
    return data


def frozen(path,text):
    if path.name=='compiled-snapshot.json':
        # Local evidence is regenerated for the current object set. No audit
        # receipt or portable proof report treats this as a cached audit.
        path.write_text(text);return
    if path.name.endswith('-compiled.json'):
        data=json.loads(text);data['driver_source_sha256']=digest(_source)
        text=json.dumps(data,indent=2)+'\n'
        if path.exists():
            if portable(json.loads(path.read_text()))!=portable(data):
                raise ValueError('Portable prefix proof inputs changed')
            local=prior.ROOT/data['compiled_snapshot']
            local.with_name('latest-compiled-replay.json').write_text(text)
            return
    _original_frozen(path,text)


def main():
    prior.frozen=frozen;prior.__file__=__file__;prior.main()


if __name__=='__main__':main()
