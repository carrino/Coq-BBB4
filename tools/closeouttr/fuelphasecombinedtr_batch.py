#!/usr/bin/env python3
"""Search FuelPhaseTr with both strict and partial weighted potentials.

The combined finder changes only untrusted certificate discovery. The
phase abstraction, certificate format and Coq checker remain unchanged.
"""
import fuelcombinedtr_batch
import fuelphasetr_batch as phase

if __name__ == '__main__':
    phase.ft.main()
