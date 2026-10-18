"""Use native conversion for expensive closeout searches, retaining their goals.

The named search checkers and large compacted certificate files use
native conversion. Smaller supplied certificates retain their evaluator:
native compilation overhead can exceed their evaluation savings. This never
changes the machine, parameters, soundness theorem or resulting proposition.
"""
import re

SEARCH = re.compile(r'^\s*apply coversTr_nqh,\s*'
                    r'(?:neverqhtr_mirror,\s*)?\('
                    r'(?:rank_tier_tr_sound|rank_tier_ng_closeout_tr_sound|rw_tier_tr_sound|rw_binary_tier_tr_sound|mb_tier_tr_sound)\b')
SEARCH_CAST = re.compile(r'\bvm_cast_no_check(?=\s*\(\s*eq_refl\s+true\s*\))')
PROOF = re.compile(r'\bProof\.(.*?)\bQed\.', re.S)
COMPACT_NATIVE_MIN_BYTES = 500_000


def proof_evaluator(proof):
    if SEARCH.match(proof):
        return SEARCH_CAST.sub('native_cast_no_check', proof)
    return proof


def rewrite(source):
    if ('(* COMPACT CERTIFICATE TABLES v1 *)' in source
            and len(source.encode()) >= COMPACT_NATIVE_MIN_BYTES):
        return PROOF.sub(lambda m: 'Proof.' +
                         re.sub(r'\bvm_compute\b', 'native_compute', m[1]).replace(
                             'vm_cast_no_check', 'native_cast_no_check') + 'Qed.', source)
    return PROOF.sub(lambda m: 'Proof.' + proof_evaluator(m[1]) + 'Qed.', source)
