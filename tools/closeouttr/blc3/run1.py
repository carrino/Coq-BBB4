import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lg3, ex1
import lg_batch as G
G.MAXFAM = int(os.environ.get("MAXFAM", "200"))
t0 = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
nd = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
t = time.time()
try:
    r = lg3.find_dir('0RB1RB_1LC1RA_1RA0LD_1LC1LD', getattr(ex1, os.environ.get("LANG_NAME","lang")), t0, ndata=nd)
except Exception as e:
    import traceback; traceback.print_exc()
    r = {'err': repr(e)}
print(r.get('err', 'OK'), time.time() - t)
if 'err' not in r:
    import json
    json.dump(G.jsonable(dict(r, spec='0RB1RB_1LC1RA_1RA0LD_1LC1LD')), open('ex_cert.json', 'w'))
    print('fams', len(r['fams']), 'leaves', len(r['leaves']))
