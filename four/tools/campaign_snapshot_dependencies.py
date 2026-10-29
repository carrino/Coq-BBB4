"""Project kernel snapshots onto explicitly mapped local compile dependencies.

The kernel snapshot includes Coq's implicit Prelude and standard library. A
compilation receipt made by the historical coqdep invocation contains only the
local libraries supplied with -Q. The Coq installation may itself live inside
the checkout, so repository containment cannot distinguish these closures.
"""
import os
from pathlib import Path


def snapshot_dependencies(compiled, module, loadpaths, root):
    """Return the local source closure without changing the kernel snapshot.

    A node is local only when both its physical source and logical module match
    an explicit -Q mapping. Traverse local edges only, just as coqdep without
    -boot leaves the runtime libraries to Coq. An explicitly mapped library can
    use any namespace, including Coq; no logical prefix is excluded globally.
    """
    root = Path(root).resolve()
    mappings = [(Path(path).resolve(), prefix) for path, prefix in loadpaths]
    for path, _ in mappings:
        path.relative_to(root.parent)
    graph = compiled['graph']

    def local(name):
        source = Path(graph[name]['source']).resolve()
        return any(source.is_relative_to(path)
                   and name == prefix + '.' + '.'.join(
                       source.relative_to(path).with_suffix('').parts)
                   for path, prefix in mappings)

    if not local(module):
        raise ValueError('Compilation root lacks an explicit local logical loadpath')
    seen = set()
    pending = [module]
    while pending:
        name = pending.pop()
        if name in seen or not local(name):
            continue
        seen.add(name)
        pending.extend(graph[name]['dependencies'])
    return {os.path.relpath(graph[name]['source'], root): graph[name]['source_sha256']
            for name in seen}
