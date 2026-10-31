"""Supplementary campaign inputs with one explicit exact-champion exception.

The frozen generic loader still rejects the champion. This version admits only
the already proved singleton through a named opt-in, with binary score binding
and symbolic bound terms. All other boards use the historical finite-inventory
and small-bound wrappers unchanged.
"""
import hashlib
import json
from pathlib import Path
import re

from check_campaign import (CHAMPION, HEADER, IDENT, ROOT, inventory_source as ordinary_inventory_source,
                            packed, read_inventory, sha)

SCORE = 205770076433044242247860
BOARD_IDENT = re.compile(r'[A-Za-z_][A-Za-z0-9_]*\Z')
TOOL_SOURCES = ('check_campaign_next.py', 'campaign_next_boards.py',
                'check_campaign.py', 'check_campaign_v2.py',
                'generate_pipeline_examples.py', 'kernel_audit_cache_v3.py')
EXACT_INTERFACE = dict(module='BBB24.ChampionCensusNext', board='champion_census_board',
                       sound='champion_census_board_sound', small_sound='champion_census_board_sound',
                       was_pending='champion_census_board_pending')


def validate_champion(board):
    """Reject all champion occurrences except the explicitly named exact board."""
    opt_in = board.get('exact_champion', False)
    if type(opt_in) is not bool:
        raise ValueError('exact_champion must be a Boolean opt-in')
    if not opt_in:
        if CHAMPION in board['machines']:
            raise ValueError('Small-bound board unexpectedly includes the champion')
        if any(field in board for field in ('state_bound_term', 'instruction_bound_term')):
            raise ValueError('Symbolic bound terms require the exact-champion opt-in')
        return
    if board['machines'] != [CHAMPION] or board['rows'] != 1 or board['scope'] != 'both':
        raise ValueError('Exact champion opt-in requires the canonical singleton BOTH board')
    if any(type(board.get(field)) is not int or board[field] != SCORE
           for field in ('state_bound', 'instruction_bound')):
        raise ValueError('Exact champion bounds must both equal the known binary score')
    if any(board.get(field) != 'scoreN' for field in ('state_bound_term', 'instruction_bound_term')):
        raise ValueError('Exact champion bound terms must both be scoreN')
    if any(board.get(field) != value for field, value in EXACT_INTERFACE.items()):
        raise ValueError('Exact champion opt-in requires the established ChampionCensusNext interface')


def load_manifest(path):
    path = Path(path).resolve()
    manifest = json.loads(path.read_text())
    boards = manifest['boards']
    if not boards or len({board['id'] for board in boards}) != len(boards):
        raise ValueError('Empty or repeated board IDs')
    paths = {'theories': 'BBB24'}
    inputs = {str(path.relative_to(ROOT)): sha(path)}
    inputs.update({'tools/'+name: sha(ROOT/'tools'/name) for name in TOOL_SOURCES})
    if 'cohort' in manifest:
        cohort = manifest['cohort']
        machines = read_inventory(cohort)
        if len(machines) != cohort['rows'] or len(set(machines)) != len(machines):
            raise ValueError('Incomplete or repeated comparison cohort')
        if hashlib.sha256(''.join(machine+'\n' for machine in machines).encode()).hexdigest() != cohort['machine_text_sha256']:
            raise ValueError('Comparison cohort differs from the frozen search remainder')
        if CHAMPION not in machines:
            raise ValueError('Comparison cohort lost its champion control')
        inputs[cohort['path']] = sha(ROOT/cohort['path'])
    for board in boards:
        if not BOARD_IDENT.fullmatch(board['id']) or board['id'] == 'Campaign':
            raise ValueError('Invalid or reserved board ID')
        for field in ('module', 'board', 'sound', 'small_sound', 'was_pending'):
            if not IDENT.fullmatch(board[field]):
                raise ValueError(f'Invalid Coq name: {field}')
        if board['scope'] not in ('both', 'state'):
            raise ValueError('A board must explicitly declare both or state scope')
        for field in ('state_bound', 'instruction_bound'):
            value = board.get(field)
            if field == 'instruction_bound' and board['scope'] == 'state':
                if value is not None:
                    raise ValueError('A state-only board cannot claim an instruction bound')
            elif type(value) is not int or value < 0:
                raise ValueError('Missing or invalid proved bound')
        if type(board['rows']) is not int or board['rows'] <= 0:
            raise ValueError('Missing or invalid board row count')
        for item in board['load_paths']:
            if not IDENT.fullmatch(item['namespace']):
                raise ValueError('Invalid namespace')
            previous = paths.setdefault(item['path'], item['namespace'])
            if previous != item['namespace']:
                raise ValueError('Conflicting logical paths')
        board['machines'] = [machine for spec in board['inventories'] for machine in read_inventory(spec)]
        for spec in board['inventories']:
            inputs[spec['path']] = sha(ROOT/spec['path'])
        if len(board['machines']) != board['rows']:
            raise ValueError(f"Inventory size changed for {board['id']}")
        validate_champion(board)
    if not any(board['scope'] == 'both' for board in boards):
        raise ValueError('Need at least one both-bound board')
    if not any(board['scope'] == 'state' for board in boards):
        raise ValueError('Need at least one state-only board')
    return manifest, boards, paths, inputs


def inventory_source(board):
    validate_champion(board)
    if not board.get('exact_champion', False):
        return ordinary_inventory_source(board)
    module = board['module']
    return HEADER.replace('check_campaign.py', 'check_campaign_next.py') + f'''Require Import {module}.
(** The reported decimal values are checked in binary before any nat view. *)
Definition recorded_state_bound : N := {board['state_bound']}%N.
Definition recorded_instruction_bound : N := {board['instruction_bound']}%N.
Lemma recorded_state_bound_exact : recorded_state_bound = scoreN.
Proof. reflexivity. Qed.
Lemma recorded_instruction_bound_exact : recorded_instruction_bound = scoreN.
Proof. reflexivity. Qed.
Local Opaque scoreN previousN.
Definition rows : list N := [{packed(CHAMPION)}%N].
Definition board := {module}.{board['board']}.
Lemma inventory_checked : manifest_check rows board = true.
Proof. vm_compute. reflexivity. Qed.
Theorem inventory_exact : manifest_board rows = board.
Proof. apply manifest_check_sound. exact inventory_checked. Qed.
Theorem small_sound : BoardSound scoreN scoreN board.
Proof. exact {module}.{board['small_sound']}. Qed.
Theorem recorded_bounds : BoardSound recorded_state_bound recorded_instruction_bound board.
Proof. rewrite recorded_state_bound_exact, recorded_instruction_bound_exact. exact small_sound. Qed.
Theorem sound : BoardSound scoreN scoreN board.
Proof. exact {module}.{board['sound']}. Qed.
Theorem was_pending : forall family, In family board -> bootstrap_pending family.
Proof. exact {module}.{board['was_pending']}. Qed.
'''
