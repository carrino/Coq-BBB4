"""Use explicit boolean gate tables in the untrusted weighted certificate.

The exact checker and recurrence proofs are unchanged. Every table entry is
still checked through the supplied graph's positivity/decrease obligations.
This avoids rebuilding gates with repeated unary-index membership searches.
"""
from weighted_render import naturals
from weighted_render_v3 import HEADER, render as prior_render


def render(row):
    text=prior_render(row)
    count=len(row['graph']['nodes'])
    replacements={}
    for certificate in row['certs'].values():
        for component in certificate['components']:
            if component['kind']=='rank':continue
            active=set(component['active'])
            old='(wc_gate nodes '+naturals(component['active'])+')'
            flags=';'.join('true' if index in active else 'false' for index in range(count))
            replacements[old]='(wc_table false nodes ['+flags+'])'
    for old,new in replacements.items():text=text.replace(old,new)
    if '(wc_gate nodes ' in text:raise ValueError('A generated gate was not converted')
    return text
