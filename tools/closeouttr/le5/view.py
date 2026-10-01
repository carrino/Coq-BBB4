import sys, json
import termrun3_detect as D
spec = sys.argv[1]; N = int(sys.argv[2]) if len(sys.argv) > 2 else 200000
A = D.anchor_strings(spec, N)
ks = sorted(A, key=lambda k: -len(A[k]))[:3]
for k in ks: print(k, len(A[k]))
k = ks[0] if len(sys.argv) <= 3 else eval(sys.argv[3])
s = A[k]
lo = int(sys.argv[4]) if len(sys.argv) > 4 else len(s) - 80
print(' '.join(s[lo:lo + 80]))
