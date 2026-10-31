"""Frozen scheduling exclusions, separated into checked and merely queued BOTH work.

An assignment can defer work; it is never proof evidence for an omitted family.
Every checker using this module still proves each retained family independently.
"""
import hashlib
import json
from pathlib import Path

from check_campaign import ROOT, load_manifest, read_inventory, sha


def create(path):
    campaign = ROOT/'research/campaign-input.json'
    summary = ROOT/'research/campaign-summary.json'
    _, boards, _, _ = load_manifest(campaign)
    sources = []
    for board in boards:
        if board['scope'] == 'both':
            for spec in board['inventories']:
                sources.append({'id': board['id'], 'status': 'checked', **spec,
                                'sha256': sha(ROOT/spec['path'])})
    for name, fmt in [('wave3-affine-bulk4096b-certs.json', 'affine'),
                      ('wave3-affine-bulk4096c-certs.json', 'affine'),
                      ('wave3-closure-proof-input.json', 'columns'),
                      ('wave3-timeout-proof-input.json', 'columns')]:
        spec = {'path': 'research/'+name, 'format': fmt}
        sources.append({'id': name.removesuffix('.json'), 'status': 'queued', **spec,
                        'sha256': sha(ROOT/spec['path'])})
    data = {'scope': 'Scheduling only. Queued BOTH assignments are not completed proofs.',
            'checked_campaign_input': {'path': str(campaign.relative_to(ROOT)), 'sha256': sha(campaign)},
            'checked_campaign_summary': {'path': str(summary.relative_to(ROOT)), 'sha256': sha(summary)},
            'inventory_parser_sha256': sha(ROOT/'tools/check_campaign.py'), 'sources': sources}
    path.write_text(json.dumps(data, indent=2)+'\n')
    return load(path)


def load(path):
    data = json.loads(path.read_text())
    for field in ('checked_campaign_input', 'checked_campaign_summary'):
        item = data[field]
        if sha(ROOT/item['path']) != item['sha256']:
            raise ValueError('Checked campaign provenance changed')
    if sha(ROOT/'tools/check_campaign.py') != data['inventory_parser_sha256']:
        raise ValueError('Assignment inventory parser changed')
    checked, queued = set(), set()
    for source in data['sources']:
        if sha(ROOT/source['path']) != source['sha256']:
            raise ValueError('Individual BOTH assignment inventory changed')
        rows = read_inventory(source)
        if source['status'] == 'checked':
            checked.update(rows)
        elif source['status'] == 'queued':
            queued.update(rows)
        else:
            raise ValueError('Unknown assignment status')
    return data, checked, queued-checked


def classify(machine, checked, queued):
    return 'checked_both' if machine in checked else 'queued_both' if machine in queued else 'unassigned'
