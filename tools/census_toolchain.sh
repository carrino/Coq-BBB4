#!/bin/sh
# Ensure a Coq that can do native_compute, and print the environment
# that provides it (for `eval').  Diagnostics go to stderr so stdout
# stays evaluable.
#
# The census walk is native_compute.  On a Coq built without the native
# compiler, `native_cast_no_check' silently falls back to VM conversion
# -- a warning, not an error -- and `coqnative' never runs, so such a
# walk proves nothing about a native one and native-only failures stay
# invisible.  `opam env' lives in the shell and survives neither a new
# terminal nor a reboot, which is exactly how a verifier ends up there
# without noticing.
#
# So this does the whole toolchain job, and only leaves the one step
# that needs a package manager (installing opam itself) to the reader.
#
#   1. coqc on PATH already native-capable  -> print nothing, exit 0
#   2. the switch exists                    -> print its opam env
#   3. opam exists, switch does not         -> CREATE it, then print
#   4. no opam                              -> explain, exit 1
#
# Untrusted build tooling: carries no proof weight.
#
# Usage:  eval "$(tools/census_toolchain.sh)"
# Knobs:  CENSUS_SWITCH (default census), CENSUS_OCAML, CENSUS_COQ,
#         CENSUS_BOOTSTRAP=0 to refuse to create anything.

set -e

SWITCH="${CENSUS_SWITCH:-census}"
OCAML="${CENSUS_OCAML:-4.14.2}"
COQPKG="${CENSUS_COQ:-coq.8.18.0}"
BOOTSTRAP="${CENSUS_BOOTSTRAP:-1}"

say() { echo ">>> $*" >&2; }

native_of() {
    command -v coqc >/dev/null 2>&1 || { echo none; return; }
    coqc -config 2>/dev/null | sed -n 's/^COQ_NATIVE_COMPILER_DEFAULT=//p' \
        | head -1 | grep . || echo no
}

# 1. already good?
cur=$(native_of)
if [ "$cur" != "no" ] && [ "$cur" != "none" ]; then
    say "coqc: $(command -v coqc) (native compiler present)"
    exit 0
fi

# 4. no opam -- the one manual step
if ! command -v opam >/dev/null 2>&1; then
    cat >&2 <<EOF
############################################################
# No Coq with a native compiler, and no opam to build one.
#   coqc here: $(command -v coqc || echo '(none)')
#
# This is the ONE step that needs your package manager:
#   apt-get install opam     (Debian/Ubuntu)
#   brew install opam        (macOS)
#
# Everything after it is automatic -- re-run and this script
# creates the '$SWITCH' switch and installs Coq + coq-native.
############################################################
EOF
    exit 1
fi

[ -d "${OPAMROOT:-$HOME/.opam}" ] || {
    say "opam has never been initialised here; running 'opam init --bare'."
    opam init --bare -y >&2
}

# 3. create the switch if it is not there
if ! opam env --switch="$SWITCH" >/dev/null 2>&1; then
    if [ "$BOOTSTRAP" = "0" ]; then
        say "no opam switch '$SWITCH' and CENSUS_BOOTSTRAP=0; stopping."
        exit 1
    fi
    cat >&2 <<EOF
############################################################
# No Coq with a native compiler on PATH, and no opam switch
# named '$SWITCH'.  Creating it now -- this is a one-time
# cost of roughly 20-40 minutes (it builds OCaml $OCAML and
# then $COQPKG with coq-native).
#
#   opam switch create $SWITCH $OCAML
#   opam install $COQPKG coq-native
#
# To do it yourself instead: make proof-all CENSUS_BOOTSTRAP=0
# To remove it afterwards:   opam switch remove $SWITCH
############################################################
EOF
    opam switch create "$SWITCH" "$OCAML" >&2
    opam install -y --switch="$SWITCH" "$COQPKG" coq-native >&2
fi

# 2. hand the environment back for eval
eval "$(opam env --switch="$SWITCH")"
got=$(native_of)
if [ "$got" = "no" ] || [ "$got" = "none" ]; then
    say "switch '$SWITCH' still has no native-capable coqc (coq-native"
    say "missing?).  Try: opam install --switch=$SWITCH coq-native"
    exit 1
fi
say "activated opam switch '$SWITCH' for this build."
say "coqc: $(command -v coqc)"
opam env --switch="$SWITCH"
