"""Pure stdlib source renderer. No Coq, native solver, or project imports.

The ULEB128 decoder produces arbitrary witness data. Every generated theorem
still requires the unchanged actual unit_check=true; no codec premise is added.
"""
from pathlib import Path
import argparse,base64,gzip,hashlib,json

CHUNK=512
STREAM='31c6f1aeb068436172e68d45c2c75dba39141f01be7ad9a8d0aef79003f076aa'
TEMPLATES={'Metadata.v':'46ee9a4650a5b543f21ecbc569b9102f38a9ac7ef799615f06223d768b2b446d','Bounds.v':'45fa156866577d9fc1e2e3342323f8355350b8bcbc7a74d82a4aa737c3daf4f6','Exports.v':'01573e6e99f25bb7e11492c14e747598ccb751f70841c3d872d3164bf67a6402','Final.v':'d8783fb5cd678d81d2d694ea3a67cb98e91a5548b6ef1f1c442f88faa5ebc8ab','WordCodec.v':'0b82fef26f636ce79a88545b0b2eba8de14354dc1c110abb576720cb37b89451'}

def sha_bytes(raw):return hashlib.sha256(raw).hexdigest()
def sha(path):return sha_bytes(Path(path).read_bytes())
def write(path,text):
 if path.exists():raise ValueError('Refusing to overwrite '+str(path))
 path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
def codes(value):
 cells=[]
 for _ in range(8):value,cell=divmod(value,17);cells.append(cell)
 if value:raise ValueError('Family has more than8 cells')
 return cells

def decode(raw):
 partial=0;place=1;words=[]
 for value in raw:
  next_value=partial+(value%128)*place
  if value<128:words.append(next_value);partial=0;place=1
  else:partial=next_value;place*=128
 if place!=1:raise ValueError('Unterminated original archived word')
 return words

def encode(words):
 raw=bytearray()
 for word in words:
  while word>=128:raw.append((word%128)+128);word//=128
  raw.append(word)
 return bytes(raw)

def metadata_source(rows):
 lines=['(** Small original family/parent/root/depth metadata. No words. *)','From Coq Require Import List PArith.','From BBB24 Require Import Statement Census Pipeline.','Import ListNotations.']
 for row in rows:
  uid=row['id'];cells='['+';'.join(map(str,row['family_codes']))+']'
  lines += [f'Definition family_{uid:03} := machine_of_codes {cells}.',f'Definition parents_{uid:03} : list TM := ['+';'.join(f'family_{p:03}'for p in row['parents'])+'].',f'Definition root_{uid:03} : positive := {row["root_positive"]}%positive.',f'Definition depth_{uid:03} : nat := {row["depth"]}.']
 return '\n'.join(lines)+'\n'

def batch_source(rows):
 lines=['(** Opaque checked certificates with inline ordinary byte witnesses.','    Source candidate until actual VM checks and fresh kernel audits pass. *)','From Coq Require Import List NArith Strings.Byte.','From BBB24 Require Import Spec.','From BBB24LightByte Require Import Transfer.','From BBB24OpaqueCensus448 Require Import Metadata.','From BBB24LightIndex189 Require Import IndexData.','From BBB24OpaqueByteWords Require Import WordCodec.','Import ListNotations.','Local Open Scope N_scope.','Local Transparent scoreN.']
 for row,raw in rows:
  uid=row['id'];chunks=[raw[i:i+CHUNK]for i in range(0,len(raw),CHUNK)]
  lines += [f'Lemma checked_{uid:03} : CheckedCertificate scoreN IndexData.index',f'  Metadata.family_{uid:03} Metadata.parents_{uid:03}',f'  Metadata.root_{uid:03} Metadata.depth_{uid:03}.','Proof.','  Time exists (decode_words (concat [']
  for i,chunk in enumerate(chunks):lines.append('    ['+';'.join(f'x{b:02x}'for b in chunk)+']'+(';'if i+1<len(chunks)else '])).'))
  lines += ['  Time vm_compute. reflexivity.','Time Qed.']
 goals=[f'CheckedCertificate scoreN IndexData.index Metadata.family_{row["id"]:03} Metadata.parents_{row["id"]:03} Metadata.root_{row["id"]:03} Metadata.depth_{row["id"]:03}'for row,_ in rows]
 lines += ['Lemma batch_contracts :','  '+' /\\\n  '.join(goals)+'.','Proof.']
 for row,_ in rows[:-1]:lines += [f'  split; [exact checked_{row["id"]:03}|].']
 lines += [f'  exact checked_{rows[-1][0]["id"]:03}.','Qed.','Print Assumptions batch_contracts.']
 return '\n'.join(lines)+'\n'

def render(archive,archive_manifest,templates,out):
 if out.exists():raise ValueError('Fresh output directory required')
 meta=json.loads(archive_manifest.read_text());assert sha(archive)==meta['gzip_sha256'];assert meta['node_count']==1495171 and meta['packed_words_sha256']==STREAM
 source_pins={name:sha(templates/name)for name in TEMPLATES}
 for name,wanted in TEMPLATES.items():
  if wanted and source_pins[name]!=wanted:raise ValueError('Changed fixed template '+name)
 template_text={name:(templates/name).read_text()for name in TEMPLATES}
 out.mkdir(parents=True)
 rows=[];batch=[];stats=[];stream=hashlib.sha256();node_count=byte_count=0
 with gzip.open(archive,'rt',encoding='utf-8')as source:
  header=json.loads(next(source));assert header['format']=='BBB24 packed census word data v1'and header['units']==448
  for line in source:
   row=json.loads(line);uid=row['id'];assert uid==len(rows)
   assert row['family_codes']==codes(int(row['family_packed']))
   assert all(type(p)is int and 0<=p<uid for p in row['parents'])
   assert 0<row['root_positive']<=row['nodes']<8192 and row['depth']>=1
   raw=base64.b64decode(row.pop('words_base64'),validate=True);words=decode(raw);assert len(words)==row['nodes']and encode(words)==raw
   for ordinal,word in enumerate(words):stream.update(f'{uid}:{ordinal}:{word}\n'.encode())
   node_count+=len(words);byte_count+=len(raw);rows.append(row);batch.append((row,raw))
   if len(batch)==16:
    bid=uid//16;name=f'CheckBatch{bid:03}.v';text=batch_source(batch);write(out/'proof'/name,text)
    stats.append(dict(name=name,units=[r['id']for r,_ in batch],nodes=sum(r['nodes']for r,_ in batch),raw_bytes=sum(len(b)for _,b in batch),chunks=sum((len(b)+511)//512 for _,b in batch),source_bytes=len(text.encode())))
    batch=[]
 assert not batch and len(rows)==448 and node_count==1495171 and stream.hexdigest()==STREAM
 assert metadata_source(rows)==template_text['Metadata.v'],'Archive metadata differs from preserved template'
 for name in ['Metadata.v','Bounds.v','Exports.v','Final.v']:write(out/'proof'/name,template_text[name])
 write(out/'core/WordCodec.v',template_text['WordCodec.v'])
 outputs={str(p.relative_to(out)):sha(p)for p in sorted(out.rglob('*.v'))};assert len(outputs)==33
 manifest=dict(status='SOURCE_ONLY_FULL28BYTEBATCHES_ALL_EXECUTION_HELD',Coq_invoked=False,solver_invoked=False,credit=0,units=448,unit_words=node_count,uleb128_bytes=byte_count,packed_words_sha256=stream.hexdigest(),chunk_limit=CHUNK,all_large_bytes_only_inside_Qed=True,decoder_requires_no_external_correctness_premise=True,all_theorem_statements_original=True,metadata_roundtrip_byte_exact=True,downstream_template_sources_byte_exact=True,inputs=dict(archive_sha256=sha(archive),archive_manifest_sha256=sha(archive_manifest),template_sha256=source_pins),namespaces=dict(core='BBB24OpaqueByteWords',proof='BBB24OpaqueCensus448'),source_sha256=outputs,source_bytes=sum((out/p).stat().st_size for p in outputs),batches=stats)
 write(out/'manifest.json',json.dumps(manifest,indent=2,sort_keys=True)+'\n')
 print(json.dumps(dict(status=manifest['status'],sources=len(outputs),source_bytes=manifest['source_bytes'],manifest_sha256=sha(out/'manifest.json'),wordstream=stream.hexdigest(),Coq_invoked=False)))

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--archive',required=True,type=Path);p.add_argument('--archive-manifest',required=True,type=Path);p.add_argument('--templates',required=True,type=Path);p.add_argument('--out',required=True,type=Path);a=p.parse_args();render(a.archive,a.archive_manifest,a.templates,a.out)
