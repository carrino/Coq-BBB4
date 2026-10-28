"""Find bounded exact source-tail entries, allowing an inert left suffix."""
import hashlib
import json
from pathlib import Path
from screen_burn5_handwritten_templates import cells
ROOT=Path(__file__).resolve().parents[1]
LIMIT=4096
SCREEN=ROOT/'research/burn5-handwritten-template-screen.json'
OUTPUT=ROOT/'research/burn5-tail-template-selection.json'
OVERLAP='1LB2LB2LA1RB_2RA1LA3RB2LA'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def trim(xs):
    while xs and xs[-1]==0:xs.pop()
    return xs

def run(machine,sigma=(0,1,2,3),mirror=False,swapped=False):
    inverse={s:i for i,s in enumerate(sigma)}
    table={}
    for q in range(2):
        for h in range(4):
            c=cells(machine)[4*q+sigma[h]]
            table[q,h]=None if c=='---'else(inverse[int(c[0])],(c[1]=='R')^mirror,ord(c[2])-65)
    q,l,h,r=0,[],0,[]
    for step in range(LIMIT+1):
        yield step,(q^swapped,trim(l[:]),h,trim(r[:]))
        if step==LIMIT:break
        tr=table[q,h]
        if tr is None:break
        w,d,q=tr
        if d:l=[w]+l;h=r[0]if r else 0;r=r[1:]
        else:r=[w]+r;h=l[0]if l else 0;l=l[1:]

def main():
    screen=json.loads(SCREEN.read_text());outputs=[]
    for template in screen['templates']:
        source=template['machine'];first=10 if template['name']=='paired_digit_tail'else 0
        index={}
        for step,(q,l,h,r)in run(source):
            if step>=first:index.setdefault((q,h,tuple(r)),[]).append((step,l))
        for row in template['matches']:
            found=None
            for step,(q,l,h,r)in run(row['machine'],row['symbol_map'],row['mirror'],row['state_exchange']):
                for source_step,source_left in index.get((q,h,tuple(r)),[]):
                    if (l[:len(source_left)]==source_left and
                        (template['name']=='paired_digit_tail'or len(l)==len(source_left))):
                        found={'destination_boot':step,'source_boot':source_step,
                               'source_configuration':[q,source_left,h,r],
                               'dormant_left_suffix':l[len(source_left):]}
                        break
                if found:break
            outputs.append({k:row[k]for k in ['machine','symbol_map','mirror','state_exchange']}|
                           {'template':template['name'],'source':source,'coalesced':found is not None,
                            'excluded_other_agent':row['machine']==OVERLAP}|(found or{}))
    pins=[Path(__file__),SCREEN,ROOT/'tools/screen_burn5_handwritten_templates.py']
    out={'scope':'Untrusted bounded selection; source-invariant transfer and concrete entries require Coq replay.',
         'source_prefix_limit':LIMIT,'target_prefix_limit':LIMIT,
         'sources_sha256':{str(p.relative_to(ROOT)):sha(p)for p in pins},'rows':outputs}
    text=json.dumps(out,indent=2,sort_keys=True)+'\n'
    if OUTPUT.exists()and OUTPUT.read_text()!=text:raise ValueError('Frozen selection differs')
    if not OUTPUT.exists():OUTPUT.write_text(text)
    print(json.dumps({'selected':sum(r['coalesced']and not r['excluded_other_agent']for r in outputs),'rows':outputs}))
if __name__=='__main__':main()
