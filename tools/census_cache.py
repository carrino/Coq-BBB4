#!/usr/bin/env python3
"""census_cache.py -- the state census's INPUT hash (BUILD HYGIENE ONLY).

History: the census walk's .vo used to be committed, and this script guarded
them (--check / --touch / --update against a committed CENSUS_VO_HASH).
Since 2026-10-07 nothing is committed: the census is walked from source by
`make proof' / `make proof-all' on the verifier's machine, so the proof is
one from-source build with no binaries in the repository.

What remains is the input hash: it hashes the census's .v INPUTS (the
transitive dependency closure of the census target), and the Makefile's
walk-stamp (census_probes/walk-stamp) records it, so census .vo on disk are
reused only when they were walked from THIS tree, and quarantined otherwise.

  --print-hash  print the current census input hash (no side effects)
  --check       kept for old callers (CI's audit step, research scripts):
                prints that nothing is committed and the current hash, exit 0
  --touch, --update  retired (there is no committed cache); exit 2

TRUST BOUNDARY.  Nothing here carries proof weight.  The Coq kernel is what
certifies the census (`census_decided`, Print Assumptions =
functional_extensionality_dep only).  Everything under tools/ is UNTRUSTED.

Coq's coqdep computes the dependency closure.
"""

import hashlib
import os
import shutil
import subprocess
import sys

# --- repo layout -----------------------------------------------------------

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
THEORIES = os.path.join(REPO_ROOT, "theories")

# The census target's .v inputs whose transitive closure we hash: the assembled
# theorem, all Run_Split* base-split units, and every Compute/*.v walk unit.
CENSUS_TARGET_GLOBS = [
    ("theories/Census", "Run_Split*.v"),
    ("theories/Census/Compute", "*.v"),  # includes Census_Theorem.v + all walk units
]



# --- coqdep discovery / invocation -----------------------------------------

def find_coqdep():
    """Locate coqdep: PATH first, then the census opam switch."""
    exe = shutil.which("coqdep")
    if exe:
        return exe
    for cand in (
        "/root/.opam/census/bin/coqdep",
        os.path.join(os.environ.get("OPAMROOT", "/root/.opam"), "census", "bin", "coqdep"),
    ):
        if os.path.isfile(cand) and os.access(cand, os.X_OK):
            return cand
    return None


def all_theory_v_files():
    """Every .v under theories/, repo-relative with forward slashes, sorted."""
    out = []
    for dirpath, _dirs, files in os.walk(THEORIES):
        for f in files:
            if f.endswith(".v"):
                rel = os.path.relpath(os.path.join(dirpath, f), REPO_ROOT)
                out.append(rel.replace(os.sep, "/"))
    return sorted(out)


def run_coqdep():
    """Run `coqdep -Q theories BBB4 <all theories .v>`; return stdout text.

    Relies on the ambient environment (an active `census` opam switch) to
    resolve Coq's stdlib.  Raises RuntimeError with coqdep's stderr on failure.
    """
    coqdep = find_coqdep()
    if not coqdep:
        raise RuntimeError(
            "coqdep not found; activate the census switch:\n"
            "  export OPAMROOT=/root/.opam; eval $(opam env --switch=census)"
        )
    vfiles = all_theory_v_files()
    cmd = [coqdep, "-Q", "theories", "BBB4"] + vfiles
    proc = subprocess.run(
        cmd, cwd=REPO_ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        text=True,
    )
    if not proc.stdout.strip():
        raise RuntimeError(
            "coqdep produced no dependency output (Coq stdlib not resolvable?).\n"
            "Ensure the census switch is active:\n"
            "  export OPAMROOT=/root/.opam; eval $(opam env --switch=census)\n"
            "coqdep stderr:\n" + proc.stderr
        )
    return proc.stdout


# --- dependency closure ----------------------------------------------------

def _stem(token):
    """Strip a coq artifact extension to its module stem, or None if not a .vo."""
    # We build the module graph from *.vo targets/deps only.  coqdep also emits
    # .glob/.vio/.v.beautified/.required_vo/.v tokens; only true '.vo' count.
    if token.endswith(".vo"):
        return os.path.normpath(token)[:-3].replace(os.sep, "/")
    return None


def parse_coqdep(text):
    """Parse coqdep make-rules into {module_stem: set(dep_module_stem)}."""
    deps = {}
    for line in text.splitlines():
        if ":" not in line:
            continue
        lhs, rhs = line.split(":", 1)
        # The rule's module = the .vo target on the LHS (ignore .glob/.vio/etc).
        tgt = None
        for tok in lhs.split():
            s = _stem(tok)
            if s is not None:
                tgt = s
                break
        if tgt is None:
            continue  # e.g. the separate .vio rule line -- skip
        dep_set = deps.setdefault(tgt, set())
        for tok in rhs.split():
            s = _stem(tok)
            if s is not None and s != tgt:
                dep_set.add(s)
    return deps


def census_target_stems():
    """Module stems of the census target .v inputs."""
    import glob
    stems = set()
    for subdir, pat in CENSUS_TARGET_GLOBS:
        for p in glob.glob(os.path.join(REPO_ROOT, subdir, pat)):
            rel = os.path.relpath(p, REPO_ROOT).replace(os.sep, "/")
            stems.add(rel[:-2])  # drop trailing '.v'
    return stems


def closure_v_files():
    """Return the sorted list of repo-relative .v files in the census input
    closure (transitive over coqdep's dependency graph)."""
    deps = parse_coqdep(run_coqdep())
    frontier = census_target_stems()
    seen = set()
    while frontier:
        stem = frontier.pop()
        if stem in seen:
            continue
        seen.add(stem)
        for d in deps.get(stem, ()):  # stdlib deps are not emitted, so we stay in-tree
            if d not in seen:
                frontier.add(d)
    vfiles = []
    for stem in seen:
        vpath = stem + ".v"
        if os.path.isfile(os.path.join(REPO_ROOT, vpath)):
            vfiles.append(vpath)
    return sorted(vfiles)


def compute_hash():
    """Stable sha256 over the sorted (path, content) list of the closure."""
    vfiles = closure_v_files()
    h = hashlib.sha256()
    for path in vfiles:  # already sorted, repo-relative, forward-slash
        with open(os.path.join(REPO_ROOT, path), "rb") as fh:
            data = fh.read()
        pb = path.encode("utf-8")
        # length-prefixed framing => injective, order-stable
        h.update(len(pb).to_bytes(8, "big"))
        h.update(pb)
        h.update(len(data).to_bytes(8, "big"))
        h.update(data)
    return h.hexdigest(), vfiles



# --- modes -----------------------------------------------------------------

def mode_check():
    try:
        current, vfiles = compute_hash()
    except RuntimeError as e:
        sys.stderr.write(str(e) + "\n")
        return 1
    print("CENSUS: nothing committed -- the census is walked from source by")
    print("  `make proof' / `make proof-all' (no .vo in the repository).")
    print("  closure: %d .v input files; input hash: %s" % (len(vfiles), current))
    return 0


def mode_retired():
    sys.stderr.write("census_cache.py: --touch / --update are retired -- no census .vo\n"
                     "are committed any more; `make proof' walks the census from source.\n")
    return 2


def mode_print_hash():
    """Print the CURRENT census input hash (no comparison, no side effects).
    Used by the Makefile's walk-stamp to decide whether census .vo on disk
    were produced by walking THIS tree (resume) or must be quarantined
    (.vo walked from an older tree / differently-wired leftovers)."""
    try:
        digest, _ = compute_hash()
    except RuntimeError as e:
        sys.stderr.write(str(e) + "\n")
        return 1
    print(digest)
    return 0


def main(argv):
    modes = {"--check": mode_check, "--touch": mode_retired,
             "--update": mode_retired, "--print-hash": mode_print_hash}
    if len(argv) != 1 or argv[0] not in modes:
        sys.stderr.write(
            "usage: census_cache.py (--print-hash | --check)\n"
            "  --print-hash  the current census input hash\n"
            "  --check       note that nothing is committed, and the hash\n"
        )
        return 2
    return modes[argv[0]]()


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
