"""Route only generated NG closeout rows through the exact weighted producer.

The original dynamic DecideTr definitions and every row/goal/parameter remain
unchanged. This rewrite is deliberately scoped to the NG closeout family.
"""
import re

OLD_IMPORT = 'From BBB4.CensusTr Require Import DecideTr.'
NEW_IMPORT = 'From BBB4.CensusTr Require Import NGramRankCloseoutTr.'
OLD_THEOREM = 'rank_tier_tr_sound'
NEW_THEOREM = 'rank_tier_ng_closeout_tr_sound'


def rewrite(source, module):
    if not re.fullmatch(r'CBT_NG_[0-9]+', module):
        return source
    old = re.search(r'\b' + OLD_THEOREM + r'\b', source)
    new = re.search(r'\b' + NEW_THEOREM + r'\b', source)
    if not old and not new:
        return source
    if source.count(OLD_IMPORT) + source.count(NEW_IMPORT) != 1:
        raise ValueError('NG rank batch must have exactly one expected import')
    if 'DecideTr.' + OLD_THEOREM in source:
        raise ValueError('Unexpected qualified legacy NG theorem')
    source = source.replace(OLD_IMPORT, NEW_IMPORT)
    return re.sub(r'\b' + OLD_THEOREM + r'\b', NEW_THEOREM, source)
