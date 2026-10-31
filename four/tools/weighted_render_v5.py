"""Compute the proved-equal trie implementation of the finite-wall checker.

Certificate data and the checked theorem statement are identical to V4.
Only the proof uses FastWall's extensional equality before reduction.
"""
from weighted_render_v4 import HEADER, render as previous_render


def render(row):
    text = previous_render(row)
    if not text.startswith(HEADER):
        raise ValueError('Unexpected weighted renderer header')
    original = 'Proof. vm_compute. reflexivity. Qed.\n'
    if text.count(original) != 1 or text.count('Lemma checked: wc_graph_check ') != 1:
        raise ValueError('Unexpected weighted Boolean proof shape')
    text = text.replace(original,
                        'Proof. rewrite <-fast_wc_graph_check_eq. vm_compute. reflexivity. Qed.\n')
    return HEADER+'From BBB24 Require Import FastWall.\n'+text[len(HEADER):]
