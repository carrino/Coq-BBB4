"""Use native conversion for expensive closeout searches, retaining their goals.

Only the three named search checkers are selected. Supplied certificates and
small direct checks retain their existing evaluator. This changes the cast,
never the machine, parameters, soundness theorem or resulting proposition.
"""
import re

SEARCH = re.compile(r'^\s*apply coversTr_nqh,\s*\('
                    r'(?:rank_tier_tr_sound|rw_tier_tr_sound|mb_tier_tr_sound)\b')
PROOF = re.compile(r'\bProof\.(.*?)\bQed\.', re.S)


def proof_evaluator(proof):
    if SEARCH.match(proof):
        return proof.replace('vm_cast_no_check (eq_refl true)',
                             'native_cast_no_check (eq_refl true)')
    return proof


def rewrite(source):
    return PROOF.sub(lambda m: 'Proof.' + proof_evaluator(m[1]) + 'Qed.', source)
