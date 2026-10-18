#!/usr/bin/env python3
"""Print a portable identity for Coq and its generated-native-code toolchain.

This is build invalidation metadata, not proof evidence.  Probe failures are
fatal: an incomplete identity must never approve existing compiled artifacts.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys


# These fields locate an installation; they do not describe its native ABI.
COQ_LOCATION_FIELDS = {"COQLIB", "COQCORELIB", "DOCDIR", "OCAMLFIND"}
OCAML_LOCATION_FIELDS = {"standard_library", "standard_library_default"}


def output(argv):
    return subprocess.run(argv, check=True, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, text=True).stdout.strip()


def fields(text, separator):
    result = {}
    for line in text.splitlines():
        if separator not in line:
            raise ValueError(f"malformed configuration line: {line!r}")
        key, value = line.split(separator, 1)
        key, value = key.strip(), value.strip()
        if not key or key in result:
            raise ValueError(f"empty or duplicate configuration field: {key!r}")
        result[key] = value
    return result


def require(config, keys):
    for key in keys:
        if not config.get(key):
            raise ValueError(f"missing toolchain configuration field: {key}")


def content_sha256(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def stamp():
    coqc = shutil.which("coqc")
    if coqc is None:
        raise ValueError("coqc is not on PATH")
    version = output([coqc, "--version"])
    if not version:
        raise ValueError("empty coqc version output")
    coq = fields(output([coqc, "-config"]), "=")
    require(coq, ("OCAMLFIND", "COQ_NATIVE_COMPILER_DEFAULT"))

    # Coq's native backend calls this configured command with `opt`, rather
    # than necessarily using the ocamlopt first on the caller's PATH.
    ocaml = fields(output([coq["OCAMLFIND"], "opt", "-config"]), ":")
    require(ocaml, ("version", "flambda", "architecture", "word_size",
                    "standard_library"))
    if ocaml["flambda"] not in {"true", "false"}:
        raise ValueError("unrecognized OCaml flambda configuration")
    # Native magic numbers are retained whenever this compiler reports them.
    # Retain all other configuration fields too; do not guess a smaller ABI.
    internal = Path(ocaml["standard_library"]) / "ocaml_compiler_internal_params"
    internal_digest = content_sha256(internal) if internal.exists() else None
    return {
        "format": "bbb4-toolchain-v2",
        "coq": {
            "version": version,
            "executable_sha256": content_sha256(coqc),
            "config": {k: v for k, v in coq.items()
                       if k not in COQ_LOCATION_FIELDS},
        },
        "ocaml_native_config": {k: v for k, v in ocaml.items()
                                if k not in OCAML_LOCATION_FIELDS},
        "generated_native_parameters": {
            # Raw spelling is intentionally conservative.  Never shell-eval
            # it, or simulate OCaml's ordering of flags and file-pattern rules.
            "OCAMLPARAM": os.environ.get("OCAMLPARAM"),
            "compiler_internal_params_sha256": internal_digest,
        },
    }


# Compiled output extensions used by OCaml/Coq.  Source (.v/.ml/.native),
# diagnostics, and every other extension are deliberately left alone.
NATIVE_COMPILED_EXTENSIONS = {
    ".cmi", ".cmo", ".cmx", ".cma", ".cmxa", ".cmxs", ".o", ".a", ".cmt", ".cmti",
}


def native_cache_files(root=Path(".")):
    """Find compiled native artifacts without decoding old .vo headers.

    The Coq-generated clean target discovers these through old .vo summaries.
    On an ABI/version mismatch that discovery can silently omit entire caches.
    Do not follow directory symlinks or delete any source.  A cache itself must
    be a real flat directory; unexpected cache structures fail closed.
    """
    def walk_error(error):
        raise error

    pending = []
    for directory, directories, files in os.walk(root, followlinks=False,
                                                onerror=walk_error):
        if ".coq-native" not in directories and ".coq-native" not in files:
            continue
        cache = Path(directory) / ".coq-native"
        if not stat.S_ISDIR(cache.lstat().st_mode):
            raise ValueError(f"native cache is not a real directory: {cache}")
        directories.remove(".coq-native")
        for item in cache.iterdir():
            mode = item.lstat().st_mode
            if stat.S_ISDIR(mode):
                raise ValueError(f"unexpected directory inside native cache: {item}")
            if item.suffix in NATIVE_COMPILED_EXTENSIONS:
                if not (stat.S_ISREG(mode) or stat.S_ISLNK(mode)):
                    raise ValueError(f"unexpected compiled cache entry: {item}")
                # Unlink a cache-file symlink itself, never its target.
                pending.append(item)
            elif stat.S_ISLNK(mode) and item.is_dir():
                raise ValueError(f"directory symlink inside native cache: {item}")
    return pending


def main():
    try:
        if sys.argv[1:] in (["--check-native-cache"], ["--clean-native-cache"]):
            pending = native_cache_files()
            if sys.argv[1] == "--clean-native-cache":
                for item in pending:
                    item.unlink()
                print(f">>> removed {len(pending)} remaining compiled native-cache files")
            return 0
        if sys.argv[1:]:
            raise ValueError("usage: proof_toolchain_stamp.py [--check-native-cache | --clean-native-cache]")
        value = stamp()
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"toolchain stamp: {error}", file=sys.stderr)
        if isinstance(error, subprocess.CalledProcessError) and error.stderr:
            print(error.stderr.rstrip(), file=sys.stderr)
        return 1
    print(json.dumps(value, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    sys.exit(main())
