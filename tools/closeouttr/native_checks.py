"""Use native conversion for expensive closeout searches, retaining their goals.

The three named search checkers and large compacted certificate files use
native conversion. Smaller supplied certificates retain their evaluator:
native compilation overhead can exceed their evaluation savings. This never
changes the machine, parameters, soundness theorem or resulting proposition.
"""
import re

SEARCH = re.compile(r'^\s*apply coversTr_nqh,\s*\('
                    r'(?:rank_tier_tr_sound|rw_tier_tr_sound|mb_tier_tr_sound)\b')
PROOF = re.compile(r'\bProof\.(.*?)\bQed\.', re.S)
COMPACT_NATIVE_MIN_BYTES = 500_000


def proof_evaluator(proof):
    if SEARCH.match(proof):
        return proof.replace('vm_cast_no_check (eq_refl true)',
                             'native_cast_no_check (eq_refl true)')
    return proof


def rewrite(source):
    if ('(* COMPACT CERTIFICATE TABLES v1 *)' in source
            and len(source.encode()) >= COMPACT_NATIVE_MIN_BYTES):
        return PROOF.sub(lambda m: 'Proof.' +
                         re.sub(r'\bvm_compute\b', 'native_compute', m[1]).replace(
                             'vm_cast_no_check', 'native_cast_no_check') + 'Qed.', source)
    return PROOF.sub(lambda m: 'Proof.' + proof_evaluator(m[1]) + 'Qed.', source)
