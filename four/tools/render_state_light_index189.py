"""Pure lightweight routed-byte data and individually proved provider adapters."""
import base64,gzip,json

def read_groups(path):
    data=json.loads(gzip.decompress(path.read_bytes()))
    if data['format']!='BBB24 light index189 routed rows v1' or len(data['groups'])!=189:raise ValueError('invalid light routing format')
    rows=0
    for i,group in enumerate(data['groups']):
        if group['provider_index']!=i:raise ValueError('provider order changed')
        raw=base64.b64decode(group['rows_base64'],validate=True)
        if len(raw)!=5*group['count']:raise ValueError('row byte count differs')
        numbers=[int.from_bytes(raw[j:j+5],'little')for j in range(0,len(raw),5)]
        if numbers!=sorted(set(numbers))or any(n>=17**8 for n in numbers):raise ValueError('invalid packed family rows')
        rows+=len(numbers)
        yield {**group,'numbers':numbers}
    if rows!=190809:raise ValueError('wrong total routed rows')

def data_source(group):
    descriptor=group['descriptor'];rows=['row5 '+' '.join(f'x{x:02x}'for x in n.to_bytes(5,'little'))for n in group['numbers']]
    lines=['(** Exact routed target tables for '+descriptor['module']+'.'+descriptor['board']+'. *)',
           'From Coq Require Import List Strings.Byte.',
           'From BBB24LightByte Require Import LightByteRows.',
           'Import ListNotations.']
    if group['provider_index']==129:
        chunks=[rows[j:j+512]for j in range(0,len(rows),512)]
        for j,chunk in enumerate(chunks):
            lines += [f'Definition rows_chunk_{j:03} : list Row5 := [',';\n'.join(chunk),'].']
        lines += ['Definition rows : list Row5 := concat [',';\n'.join(f'rows_chunk_{j:03}'for j in range(len(chunks))),'].']
    else:lines += ['Definition rows : list Row5 := [',';\n'.join(rows),'].']
    lines += ['Definition board := byte_board rows.']
    return '\n'.join(lines)+'\n'


def adapter_source(group):
    i=group['provider_index'];d=group['descriptor'];name=f'Data{i:03}'
    lines=['(** Transfer only this provider to its exact routed lightweight targets. *)',
           'From Coq Require Import NArith.',
           'From BBB24 Require Import Spec StateOnlyCloseout FamilyIndex'+(' DualCloseout'if d['scope']=='both'else'')+'.',
           'From BBB24LightByte Require Import Transfer.',
           f'From BBB24LightIndex189 Require Import {name}.',
           'Require Import '+d['module']+'.',
           'Local Opaque scoreN.',
           f'Lemma actual_transfer_checked : transfer_check (family_index {d["module"]}.{d["board"]}) {name}.board = true.',
           'Proof. Time vm_compute. reflexivity. Qed.',
           'Local Opaque score.',
           'Lemma provider_state_sound : StateBoardSound score '+d['module']+'.'+d['board']+'.']
    lines += ['Proof. apply bounds_board_state. exact '+d['module']+'.'+d['sound']+'. Qed.']if d['scope']=='both'else['Proof. exact '+d['module']+'.'+d['sound']+'. Qed.']
    lines += [f'Theorem sound : StateBoardSound score {name}.board.',f'Proof. exact (transfer_state_sound score {d["module"]}.{d["board"]} {name}.board provider_state_sound actual_transfer_checked). Qed.']
    return '\n'.join(lines)+'\n'

def index_source():
    imports=' '.join(f'Data{i:03}'for i in range(189));boards=';\n'.join(f'Data{i:03}.board'for i in range(189))
    return '\n'.join(['(** LIGHT DATA ONLY: no provider proof or Adapter module is imported. *)',
        'From Coq Require Import List.','From BBB24 Require Import Statement FamilyIndex.',
        'From BBB24LightIndex189 Require Import '+imports+'.','Import ListNotations.',
        'Definition boards : list (list TM) := [',boards,'].','Definition board := concat boards.','Definition index := family_index board.'])+'\n'

def aggregate_source():
    lines=['(** Proof layer only: the global index is never computed in this file. *)',
           'From Coq Require Import List.','From BBB24 Require Import Spec Census StateOnlyCloseout.',
           'From BBB24GlobalLeaves Require Import GlobalLeaves.','From BBB24LightByte Require Import Transfer.',
           'From BBB24LightIndex189 Require Import IndexData '+' '.join(f'Adapter{i:03}'for i in range(189))+'.',
           'Import ListNotations.','Local Opaque scoreN score.',
           'Theorem board_sound : StateBoardSound score IndexData.board.',
           'Proof. unfold IndexData.board. apply state_boards_sound. unfold IndexData.boards.']
    lines += [f'apply Forall_cons; [exact Adapter{i:03}.sound|].'for i in range(189)]
    lines += ['apply Forall_nil. Qed.','Theorem index_sound : IndexSound score IndexData.index.',
              'Proof. unfold IndexData.index. apply board_index_sound. exact board_sound. Qed.']
    return '\n'.join(lines)+'\n'
