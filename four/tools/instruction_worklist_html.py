"""Render a small, self-contained browser for the exact instruction worklist."""
import json

def render(rows, summary, fields, lanes):
    omitted = {'id', 'batch', 'machine', 'righthand_machine'}
    defaults = dict.fromkeys(fields, '')
    defaults.update(proof_status='open', lane='needs_triage', work_status='unclaimed')
    extra = {}
    for row in rows:
        changed = {key: value for key, value in row.items()
                   if key not in omitted and value != defaults[key]}
        if changed:
            extra[row['id'][5:]] = changed
    payload = dict(machines=[int(row['id'][5:]) for row in rows], extra=extra,
                   defaults=defaults, lanes=lanes, summary=summary, fields=fields)
    # Claim notes remain text even if they contain HTML or a closing script tag.
    encoded = json.dumps(payload, separators=(',', ':'), ensure_ascii=True).replace('<', '\\u003c')
    return TEMPLATE.replace('__WORKLIST_DATA__', encoded)


TEMPLATE = '''<!doctype html>
<html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width">
<title>BBB_tr(2,4) instruction worklist</title>
<style>
:root {color-scheme:light dark;font:15px system-ui,sans-serif}
body {max-width:1550px;margin:2rem auto;padding:0 1rem}
h1 {font-size:1.8rem} p {max-width:100ch;line-height:1.5}
.controls {display:flex;gap:.6rem;flex-wrap:wrap;margin:1rem 0}
input,select,button {font:inherit;padding:.5rem;border:1px solid #888;border-radius:4px}
input {min-width:22rem} button {cursor:pointer} button:disabled {cursor:default;opacity:.5}
table {border-collapse:collapse;width:100%;font-size:.9rem}
th,td {text-align:left;vertical-align:top;padding:.65rem;border-bottom:1px solid #9996}
th {position:sticky;top:0;background:Canvas} code {white-space:nowrap}
.tablewrap {overflow-x:auto} .muted {opacity:.75} #stats {font-weight:650}
a {color:LinkText} #position {padding:0 .8rem}
</style>
<h1>Instruction BBB(2,4) worklist</h1>
<p id="stats"></p>
<p>Each row is an exact census family, including every completion of its undefined
transitions. Work claims organize the search; only an accepted proof inventory closes
a row. This is the historical hard cohort, rather than the complete global census.</p>
<div class="controls">
<input id="query" aria-label="Search families" placeholder="ID, program, state case, owner…">
<select id="proof" aria-label="Proof status"><option value="open">Open families</option><option value="all">All families</option><option value="proved">Proved families</option></select>
<select id="lane" aria-label="Work lane"><option value="">All work lanes</option></select>
<select id="batch" aria-label="Work batch"><option value="">All batches</option></select>
<button id="download">Download filtered TSV</button>
</div>
<p class="muted">Diagnostic targets and search outcomes are historical observations.
An empty diagnostic field means no evidence was attached here. Stable batch IDs divide
work; they do not identify additional machine equivalences.</p>
<p><button id="previous">Previous</button><span id="position"></span><button id="next">Next</button></p>
<div class="tablewrap"><table><thead><tr>
<th>Family / batch</th><th>Program (first move right)</th><th>Work lane</th>
<th>Diagnostic target / search</th><th>State proof / evidence</th><th>Claim / note</th>
</tr></thead><tbody id="rows"></tbody></table></div>
<p class="muted">To claim work, edit four/research/instruction-claims.json and regenerate.
This downloaded browser is a read-only snapshot. No network connection is needed to filter it.</p>
<script id="data" type="application/json">__WORKLIST_DATA__</script>
<script>
'use strict';
const data=JSON.parse(document.getElementById('data').textContent);
const el=id=>document.getElementById(id);
function decode(value) {
  const cells=[];
  for(let i=0;i<8;i++) {const c=value%17;value=Math.floor(value/17);
    cells.push(c===16?'---':String(Math.floor(c/4))+((c&2)?'R':'L')+((c&1)?'B':'A'));}
  return cells.slice(0,4).join('')+'_'+cells.slice(4).join('');
}
const all=data.machines.map(n=>{const machine=decode(n);return {...data.defaults,
  ...(data.extra[String(n)]||{}),id:'tr24-'+n,batch:'b'+(n%256).toString(16).padStart(2,'0'),machine,
  righthand_machine:machine[1]==='L'?machine.replace(/[LR]/g,x=>x==='L'?'R':'L'):machine};});
const count=n=>n.toLocaleString('en-US');
el('stats').textContent=count(data.summary.open)+' open · '+count(data.summary.proved)+
  ' recorded proofs · '+Object.keys(data.summary.batches).length+' stable work batches';
for(const [key,label] of Object.entries(data.lanes)) {const o=document.createElement('option');o.value=key;o.textContent=label;el('lane').append(o);}
for(const key of Object.keys(data.summary.batches).sort()) {const o=document.createElement('option');o.value=key;o.textContent=key+' ('+data.summary.batches[key]+' open)';el('batch').append(o);}
let page=0,filtered=[],pageSize=100;
function cell(tr,text) {const td=document.createElement('td');td.textContent=text;tr.append(td);return td;}
function show() {
 const q=el('query').value.toLowerCase().trim(),proof=el('proof').value;
 filtered=all.filter(r=>(proof==='all'||r.proof_status===proof)&&(!el('lane').value||r.lane===el('lane').value)&&
  (!el('batch').value||r.batch===el('batch').value)&&(!q||Object.values(r).join(' ').toLowerCase().includes(q)));
 page=Math.min(page,Math.max(0,Math.ceil(filtered.length/pageSize)-1));el('rows').replaceChildren();
 for(const r of filtered.slice(page*pageSize,(page+1)*pageSize)) {
  const tr=document.createElement('tr');cell(tr,r.id+' / '+r.batch);
  const td=cell(tr,'');const a=document.createElement('a');a.href='https://bbchallenge.org/'+r.righthand_machine;
  const code=document.createElement('code');code.textContent=r.righthand_machine;a.append(code);td.append(a);
  cell(tr,data.lanes[r.lane]+' / '+r.proof_status);
  cell(tr,(r.missing_targets||'unknown')+(r.search_history?' · '+r.search_history:''));
  const evidence=cell(tr,r.state_case?(r.state_case+' · '+r.state_package):'');
  if(r.evidence) {const a=document.createElement('a');a.href='https://github.com/carrino/Coq-BBB4/blob/codex/bbb24-instruction-burn1/four/'+r.evidence;
   a.textContent=' evidence';evidence.append(a);}
  cell(tr,(r.owner?r.owner+' · '+r.work_status:'Unclaimed')+(r.note?' · '+r.note:''));el('rows').append(tr);
 }
 el('position').textContent=filtered.length?count(page*pageSize+1)+'–'+count(Math.min((page+1)*pageSize,filtered.length))+' of '+count(filtered.length):'0 matches';
 el('previous').disabled=page===0;el('next').disabled=(page+1)*pageSize>=filtered.length;
}
for(const id of ['query','proof','lane','batch'])el(id).addEventListener('input',()=>{page=0;show();});
el('previous').onclick=()=>{page--;show();};el('next').onclick=()=>{page++;show();};
el('download').onclick=()=>{
 const quote=v=>/["\\t\\r\\n]/.test(v)?'"'+v.replace(/"/g,'""')+'"':v;
 const text=[data.fields.join('\\t'),...filtered.map(r=>data.fields.map(k=>quote(String(r[k]))).join('\\t'))].join('\\n')+'\\n';
 const url=URL.createObjectURL(new Blob([text],{type:'text/tab-separated-values;charset=utf-8'}));
 const a=document.createElement('a');a.href=url;a.download='instruction-families.tsv';a.click();setTimeout(()=>URL.revokeObjectURL(url),1000);
};
show();
</script></html>
'''
