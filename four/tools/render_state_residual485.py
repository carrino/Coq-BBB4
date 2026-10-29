"""Pure compact residual emitters; no search, old proof imports or external processes."""
from weighted_codec_v2 import bundle_decode,unpack
from weighted_render import HEADER
from weighted_render_v3 import render as render3
from weighted_render_v4 import render as render4
from weighted_render_v5 import render as render5
from check_weighted_v2 import ordinary

def body(row, version):
 return ordinary(row)if row['kind']=='ordinary'else{3:render3,4:render4,5:render5}[version](unpack(row))[len(HEADER):]

def shard(rows, versions):
 text=HEADER+'From BBB24 Require Import Pipeline NGramCensus Bootstrap Closeout CertifiedBoard StateOnlyCloseout StateBranchJoin.\n'
 for i,row in enumerate(rows):text+=f'Module R{i:04}.\n'+body(row,versions[row['machine']])+f'End R{i:04}.\n'
 entries=';'.join(f'mkCertifiedFamily 4096%N 4096%N R{i:04}.family R{i:04}.family_run'for i in range(len(rows)))
 return text+f'''Definition families : list (CertifiedFamily 4096%N 4096%N) := [{entries}].
Definition board := certified_board 4096%N 4096%N families.
Lemma board_small_sound : BoardSound 4096%N 4096%N board.
Proof. apply certified_board_sound. Qed.
Lemma state_small_sound : StateBoardSound (N.to_nat 4096%N) board.
Proof. intros family Hin complete Hle; exact (proj1 (board_small_sound family Hin complete Hle)). Qed.
Lemma budget : (4096 <= scoreN)%N.
Proof. vm_compute. discriminate. Qed.
Local Opaque scoreN.
Theorem sound : StateBoardSound score board.
Proof. unfold score. exact (state_board_N_weaken 4096%N scoreN board budget state_small_sound). Qed.
Print Assumptions sound.
'''

def packed(machine):
    cells=[]
    for group in machine.split('_'):
        for offset in range(0,len(group),3):
            tr=group[offset:offset+3]
            cells.append(16 if tr=='---'else 4*int(tr[0])+2*(tr[1]=='R')+(tr[2]=='B'))
    if len(cells)!=8:raise ValueError('expected eight transitions')
    return sum(cell*17**i for i,cell in enumerate(cells))

def aggregate(rows,part_count=61):
    names=[f'Part{i:03}'for i in range(part_count)]
    lines=['From Coq Require Import List NArith.',
           'From BBB24 Require Import Statement Spec Census StateOnlyCloseout StateBranchJoin BoardManifest.',
           'From BBB24CompactResidual485 Require Import '+' '.join(names)+'.',
           'Import ListNotations.',
           'Definition boards := ['+';'.join(n+'.board'for n in names)+'].',
           'Definition board := concat boards.',
           'Theorem state_small_sound : StateBoardSound (N.to_nat 4096%N) board.',
           'Proof. apply state_boards_sound. unfold boards.']
    lines += ['apply Forall_cons; [exact '+n+'.state_small_sound|].'for n in names]
    lines += ['apply Forall_nil. Qed.','Local Opaque scoreN score.',
              'Theorem sound : StateBoardSound score board.',
              'Proof. apply state_boards_sound. unfold boards.']
    lines += ['apply Forall_cons; [exact '+n+'.sound|].'for n in names]
    lines += ['apply Forall_nil. Qed.',
              'Definition packed_rows : list N := ['+';'.join(str(packed(r['machine']))+'%N'for r in rows)+'].',
              'Lemma inventory_checked : manifest_check packed_rows board = true.',
              'Proof. vm_compute. reflexivity. Qed.',
              'Theorem inventory_exact : manifest_board packed_rows = board.',
              'Proof. apply manifest_check_sound. exact inventory_checked. Qed.',
              'Print Assumptions sound.']
    return '\n'.join(lines)+'\n'
