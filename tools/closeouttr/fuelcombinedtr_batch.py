#!/usr/bin/env python3
"""Combine strict and partially decreasing pattern potentials for FuelMixTr.

The ordinary weighted finder is tried first. If it cannot peel a cyclic
component, the nonincreasing-potential finder may remove just its strictly
negative edges. This preserves ordinary certificates that can be lost by
replacing the finder wholesale. Both proposals undergo the landed exact
integer replay, and the emitted Coq data uses the unchanged FuelMixTr checker.
CLI arguments are those of fueltr_batch.py.
"""
from functools import partial
from math import gcd
import fuelmixtr_batch as fm
import fuelpotentialtr_batch as potential


def choose_mix(*args):
    result = fm.choose_mix(*args)
    if result is None:
        result = potential.choose_mix(*args)
    if result is None:
        return None
    terms, values, phi = result
    # A constant shift of all gated potentials cancels on every edge.
    shift = min(phi.values(), default=0)
    phi = {a: v - shift for a, v in phi.items()}
    divisor = 0
    for weight, _, _ in terms:
        divisor = gcd(divisor, weight)
    for value in phi.values():
        divisor = gcd(divisor, value)
    if divisor > 1:
        terms = [(w // divisor, p, r) for w, p, r in terms]
        values = {a: v // divisor for a, v in values.items()}
        phi = {a: v // divisor for a, v in phi.items()}
    return terms, values, phi


ft = fm.ft
ft.instruction_procedure = partial(ft.instruction_procedure.func,
                                   mix_finder=choose_mix)

if __name__ == '__main__':
    ft.main()
