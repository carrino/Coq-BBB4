"""Render exhaustive eight-target certificates without a redundant match arm.

All data validation and proof obligations remain those of the frozen renderer.
This changes only the syntactic fallback when every instruction is supplied.
"""
from weighted_render import HEADER, render as original_render


def render(row):
    text=original_render(row)
    if len(row['certs'])==8 and {int(target) for target in row['certs']}==set(range(8)):
        lines=text.splitlines(keepends=True)
        found=0
        for index,line in enumerate(lines):
            if line.startswith('Definition certificate(t:Instr):'):
                if line.count('|_=>None end.')!=1:raise ValueError('Unexpected certificate match syntax')
                lines[index]=line.replace('|_=>None end.',' end.')
                found+=1
        if found!=1:raise ValueError('Missing certificate definition')
        text=''.join(lines)
    return text
