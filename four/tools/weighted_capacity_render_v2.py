"""Use the capacity soundness theorem in both orientation branches.

The original renderer is retained for recorded byte-for-byte reproductions.
Its direct branch inherited the old checker theorem; this adapter supplies
all arguments to the capacity theorem explicitly, without changing data or
the Boolean certificate obligation.
"""
from weighted_capacity_render import HEADER, render as previous


def render(row):
    text = previous(row)
    graph = row['graph']
    if not graph['mirror']:
        old = '  eapply wc_graph_check_sound; exact checked.\n'
        if text.count(old) != 1:
            raise ValueError('Unexpected direct capacity proof template')
        term = ('  exact (wca_graph_check_sound 4096%N 4096%N family '
                f'{graph["n"]}%nat {graph["t"]}%nat nodes certificate capacity checked).\n')
        text = text.replace(old, term)
    return text
