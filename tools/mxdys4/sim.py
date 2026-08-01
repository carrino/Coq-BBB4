import sys
from collections import defaultdict

def parse(code):
    tm = {}
    for si, part in enumerate(code.split('_')):
        st = "ABCD"[si]
        for sym in (0,1):
            f = part[3*sym:3*sym+3]
            if f == '---':
                tm[(st,sym)] = None
            else:
                tm[(st,sym)] = (int(f[0]), f[1], f[2])
    return tm

class Sim:
    def __init__(self, code):
        self.tm = parse(code)
        self.tape = defaultdict(int)
        self.pos = 0
        self.st = 'A'
        self.t = 0
    def step(self):
        tr = self.tm[(self.st, self.tape[self.pos])]
        if tr is None: return False
        w,d,n = tr
        self.tape[self.pos] = w
        self.pos += 1 if d=='R' else -1
        self.st = n
        self.t += 1
        return True
    def tapestr(self, pad=0):
        ks = [k for k,v in self.tape.items() if v] or [0]
        lo = min(min(ks), self.pos)-pad; hi = max(max(ks), self.pos)+pad
        s = ''
        for i in range(lo,hi+1):
            if i == self.pos: s += '[%s%d]' % (self.st, self.tape[i])
            else: s += str(self.tape[i])
        return (lo,hi,s)

if __name__ == '__main__':
    code = sys.argv[1]
    N = int(sys.argv[2]) if len(sys.argv)>2 else 200
    s = Sim(code)
    for i in range(N):
        lo,hi,ts = s.tapestr()
        print("%6d %s" % (s.t, ts))
        if not s.step():
            print("HALT at", s.t); break
