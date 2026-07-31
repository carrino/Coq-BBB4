/* ladder_i.c -- UNTRUSTED measurement tool: the census ladder run at
 * BOTH beep levels, to size the instruction-level variant of BBB(4).
 *
 * Derived from tools/census_ladder.c, which it reproduces verbatim at
 * the state level (same node count, same per-tier tallies, same BB(4)
 * champion).  Added: every tier additionally classifies at the
 * INSTRUCTION level -- the beep is a transition (q,s), not a state --
 * and the run prints the cross-tab of the two verdicts.  See
 * docs/INSTRUCTION_BEEPS.md for what the numbers mean.
 *
 * Enumerates the full (4,2) TNF tree exactly as the Coq census
 * walks it (Coq-BB5 style: root = all-undefined, expand every machine
 * that reaches an undefined transition, first move fixed to R by mirror
 * symmetry, new states in first-use order via the unused-state pointer;
 * UNLIKE the halting census there is NO cnt=1 pruning -- machines with
 * all 8 transitions defined are enumerated and decided too), and runs
 * the quasihalting decider ladder over every node:
 *
 *   tier H  : halt search (undefined transition reached)     -> expand
 *   tier C  : in-place cycle (head-relative config repeats)  -> leaf
 *   tier T  : translated cycle (record-event periodicity)    -> leaf
 *   tier N  : n-gram CPS closure + per-state acyclicity      -> leaf
 *             (mirrors Checkers/NGram.v ngram_check_neverqh:
 *              donation-gated growth to fixpoint, then closed check
 *              + q-avoiding-subgraph acyclicity per visited state)
 *   tier D  : membership in the holdout list (deferred)
 *   residue : everything else (printed)
 *
 * QH classification at cycle tiers: a state visited at least once
 * whose last visit precedes the cycle window is quiet; its last visit
 * + 1 is the score, per the BBB README conventions.  The instruction
 * level reads the same window with (q,s) in place of q -- both cycle
 * tiers therefore decide BOTH levels exactly, from one certificate.
 *
 * At tier N the goal set widens from 4 states to 8 instructions and
 * the goal-avoiding subgraph grows (only nodes whose state AND head
 * symbol match are excluded), so a state-level rank certificate need
 * not survive.  The n-gram context already carries the head symbol,
 * so nothing else about the abstraction changes.
 *
 * The residue file gains two tags on the machines whose state-level
 * n-gram proof does not survive:
 *   NEWQH?  the unproven instruction had stopped firing long before
 *           the gas ran out -- a genuine new quasihalter, needing a
 *           score certificate rather than a liveness one;
 *   SPARSE? it was still firing -- the abstraction is too coarse for
 *           it at this rung, not a new quasihalter.
 *
 * This tool carries no soundness.  gcc -O2 -o ladder_i ladder_i.c
 *
 * Usage: ./ladder_i [--holdouts FILE] [--gas N] [--residue FILE]
 *                   [--csv FILE] [--machines FILE] [--rungs n:t,...]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

/* ----------------------------------------------------------------- */
/* machines: 4 states x 2 symbols; slot = next<<2 | dir<<1 | write,
 * 0xFF = undefined.  dir: 0 = L, 1 = R. */
typedef struct { uint8_t sl[8]; uint8_t ptr; } Node;
#define SLOT(m,q,s) ((m)[(q)*2+(s)])
#define UNDEF 0xFF

static inline int tr_next(uint8_t t){ return t>>2; }
static inline int tr_dir (uint8_t t){ return (t>>1)&1; }
static inline int tr_wr  (uint8_t t){ return t&1; }

static void tm_text(const uint8_t *sl, char *out){
  int q,s; char *p = out;
  for(q=0;q<4;q++){
    if(q) *p++='_';
    for(s=0;s<2;s++){
      uint8_t t = SLOT(sl,q,s);
      if(t==UNDEF){ *p++='-';*p++='-';*p++='-'; }
      else { *p++='0'+tr_wr(t); *p++=tr_dir(t)?'R':'L'; *p++='A'+tr_next(t); }
    }
  }
  *p=0;
}

/* ----------------------------------------------------------------- */
/* simulation with in-place-cycle + record tracking.
 *
 * In-place cycles are detected on the HEAD-RELATIVE configuration
 * (state + written tape relative to head), matching Checkers/Cycle.v's
 * deliberate generalization: pure translations with identical relative
 * tape count as in-place.  Detection uses a rolling polynomial hash
 * H_rel = (sum_{tape[j]=1} r^j) * r^(-head), so each step is O(1). */

#define TAPE_BITS 15
#define TAPE (1<<TAPE_BITS)
#define MAXGAS 8192
#define MOD 2305843009213693951ULL      /* 2^61 - 1 */

static uint64_t powr[2*TAPE];           /* r^k mod MOD */

static inline uint64_t mulmod(uint64_t a, uint64_t b){
  unsigned __int128 z = (unsigned __int128)a*b;
  uint64_t lo = (uint64_t)(z & MOD), hi = (uint64_t)(z>>61);
  uint64_t s = lo + hi;
  if(s >= MOD) s -= MOD;
  return s;
}
static void init_pow(void){
  uint64_t r = 1234577;
  powr[0]=1;
  for(long i=1;i<2*TAPE;i++) powr[i]=mulmod(powr[i-1],r);
}
static inline uint64_t submod(uint64_t a, uint64_t b){ return a>=b? a-b : a+MOD-b; }

/* per-sim outcome */
typedef struct {
  int kind;              /* 0 none, 1 halt, 2 inplace, 3 runner(off-tape) */
  int halt_n, halt_q, halt_s;     /* halt: steps done, state, read sym */
  int n1, p;                      /* inplace: config n1 == config n1+p */
  int last_visit[4];              /* last config index in state q, -1 never */
  long score_hint;                /* max last visit among quiet states (cycle) */
  int last_fire[8];               /* last config index reading (q,s), -1 never
                                     (index q*2+s; instruction fires at +1)  */
  long score_hint_i;              /* max last fire among quiet instrs (cycle) */
  int nrec[2];                    /* record counts per side (0=L,1=R) */
} SimOut;

/* record event log (per side), for the TC tier */
#define MAXREC 4096
static int rec_step[2][MAXREC];
static int8_t rec_state[2][MAXREC];

/* open-addressing table for config-hash -> step */
#define HB 14
#define HSZ (1<<HB)
static uint64_t hkey[HSZ]; static int hval[HSZ];

static int8_t tape_[TAPE];

/* simulate up to gas steps; track everything. */
static void simulate(const uint8_t *sl, int gas, SimOut *o){
  memset(o,0,sizeof *o);
  o->last_visit[0]=o->last_visit[1]=o->last_visit[2]=o->last_visit[3]=-1;
  for(int j=0;j<8;j++) o->last_fire[j]=-1;
  int head = TAPE/2, lo = head, hi = head, q = 0;
  uint64_t habs = 0;
  memset(hkey, 0, sizeof hkey);
  o->nrec[0]=o->nrec[1]=0;
  /* the step-0 configuration is a record on both sides and in state A */
  rec_step[0][0]=0; rec_state[0][0]=0; o->nrec[0]=1;
  rec_step[1][0]=0; rec_state[1][0]=0; o->nrec[1]=1;

  for(int n=0;;n++){
    o->last_visit[q]=n;
    /* config key at index n (before stepping) */
    uint64_t hrel = mulmod(habs, powr[2*TAPE-1-head]);
    uint64_t key = hrel*4 + q + 1;      /* +1: avoid key 0 = empty slot */
    uint32_t b = (uint32_t)(key*0x9E3779B97F4A7C15ULL >> (64-HB));
    for(;;){
      if(hkey[b]==0){ hkey[b]=key; hval[b]=n; break; }
      if(hkey[b]==key){ o->kind=2; o->n1=hval[b]; o->p=n-hval[b];
        /* quiet states: visited, last visit < n1 */
        long sc=-1;
        for(int j=0;j<4;j++)
          if(o->last_visit[j]>=0 && o->last_visit[j]<o->n1 && o->last_visit[j]>sc)
            sc=o->last_visit[j];
        o->score_hint=sc;
        /* quiet instructions: fired, last fire < n1.  Same argument:
           the block [n1,n) repeats forever, so an instruction not fired
           inside it never fires again. */
        long sci=-1;
        for(int j=0;j<8;j++)
          if(o->last_fire[j]>=0 && o->last_fire[j]<o->n1 && o->last_fire[j]>sci)
            sci=o->last_fire[j];
        o->score_hint_i=sci;
        return; }
      b=(b+1)&(HSZ-1);
    }
    if(n>=gas) { o->kind=0; return; }
    int s = tape_[head];
    uint8_t t = SLOT(sl,q,s);
    if(t==UNDEF){ o->kind=1; o->halt_n=n; o->halt_q=q; o->halt_s=s; return; }
    o->last_fire[q*2+s]=n;
    int w = tr_wr(t);
    if(w!=s){ /* update hash: toggle bit at head */
      if(w) habs = habs+powr[head] >= MOD ? habs+powr[head]-MOD : habs+powr[head];
      else  habs = submod(habs, powr[head]);
      tape_[head]=(int8_t)w;
    }
    head += tr_dir(t)? 1 : -1;
    q = tr_next(t);
    if(head<8 || head>TAPE-8){ o->kind=3; return; }
    if(head<lo){ lo=head;
      if(o->nrec[0]<MAXREC){ rec_step[0][o->nrec[0]]=n+1; rec_state[0][o->nrec[0]]=q; o->nrec[0]++; } }
    if(head>hi){ hi=head;
      if(o->nrec[1]<MAXREC){ rec_step[1][o->nrec[1]]=n+1; rec_state[1][o->nrec[1]]=q; o->nrec[1]++; } }
  }
}

/* wipe the touched tape region after each simulate() call */
static void wipe_tape(void){ memset(tape_,0,TAPE); }

/* ----------------------------------------------------------------- */
/* tier T: translated cycles.
 *
 * Candidates come from the record log (same-state record pairs); each
 * candidate (anchor step a, period P) is then VERIFIED by the actual
 * tcycler window argument (the same induction Checkers/TCycler.v
 * checks): re-simulate to step a (a record step, so the tape beyond
 * the head on the record side is virgin blank), snapshot, run P more
 * steps tracking the excursion back from the record side; the run
 * must end in the same state, displaced strictly further out on the
 * record side, with the tape relative to the head equal on the whole
 * excursion window.  Blank-beyond-extent + determinism then repeat
 * the lap forever.  Returns 1 and fills *vis_lap (states visited in
 * [a, a+P)) on success. */

typedef struct { int a, P, side; } TCand;

/* mirrors the Coq pipeline's tc_pairs exactly: for each of the two
 * newest records, its nearest earlier same-state record */
static int tc_candidates(const SimOut *o, int side, TCand *out, int max){
  int n = o->nrec[side], k=0;
  const int *ts = rec_step[side]; const int8_t *st = rec_state[side];
  for(int i=n-1;i>=1 && i>=n-2;i--){
    for(int j=i-1;j>=0;j--){
      if(st[j]!=st[i]) continue;
      if(k<max){ out[k].a=ts[j]; out[k].P=ts[i]-ts[j]; out[k].side=side; k++; }
      break;
    }
  }
  return k;
}

static int8_t tc_tape1[TAPE];

/* verify candidate; returns 1 if proven, and sets vis_lap bitmask + the
 * anchor step (quiet states = visited, last visit < anchor). */
static int tc_verify(const uint8_t *sl, int a, int P, int *vis_lap_out,
                     int *fire_lap_out){
  if(P<=0 || a+P>MAXGAS) return 0;
  /* pass 1: to step a */
  memset(tc_tape1,0,TAPE);
  int head=TAPE/2, q=0;
  for(int i=0;i<a;i++){
    uint8_t t=SLOT(sl,q,tc_tape1[head]);
    if(t==UNDEF) return 0;
    tc_tape1[head]=(int8_t)tr_wr(t); head+=tr_dir(t)?1:-1; q=tr_next(t);
    if(head<8||head>TAPE-8) return 0;
  }
  int head1=head, q1=q;
  /* snapshot is implicit: continue on the same tape, remember bounds */
  int minh=head, maxh=head, vis=1<<q, fired=0;
  /* save the window contents left+right of head1 before continuing:
     we compare against tape AFTER P more steps, but the lap may
     overwrite cells; so save a copy of the whole touched span. */
  static int8_t save[TAPE];
  /* conservative: save [head1-(P+2) .. head1+(P+2)] */
  int slo=head1-P-2, shi=head1+P+2;
  if(slo<0||shi>=TAPE) return 0;
  memcpy(save+slo, tc_tape1+slo, (size_t)(shi-slo+1));
  for(int i=0;i<P;i++){
    int rs=tc_tape1[head];
    uint8_t t=SLOT(sl,q,rs);
    if(t==UNDEF) return 0;
    fired|=1<<(q*2+rs);
    tc_tape1[head]=(int8_t)tr_wr(t); head+=tr_dir(t)?1:-1; q=tr_next(t);
    vis|=1<<q;
    if(head<minh)minh=head;
    if(head>maxh)maxh=head;
    if(head<8||head>TAPE-8) return 0;
  }
  int head2=head, q2=q;
  if(q2!=q1) return 0;
  int d = head2-head1;
  int ok=0;
  if(d>0){
    /* right TC: window = leftward excursion from head1 */
    int W = head1-minh;                 /* lap dug W cells below head1 */
    /* right of head1 at the anchor must be virgin blank (record step) */
    for(int k2=head1+1;k2<=shi;k2++) if(save[k2]) return 0;
    /* after the lap, everything right of the new head must be blank
       again (the lap may have scouted ahead and come back) */
    for(int k2=head2+1;k2<=maxh;k2++) if(tc_tape1[k2]) return 0;
    ok=1;
    for(int k2=-W;k2<=0;k2++)
      if(save[head1+k2]!=tc_tape1[head2+k2]){ ok=0; break; }
  } else if(d<0){
    /* left TC: window = rightward excursion from head1 */
    int W = maxh-head1;
    for(int k2=slo;k2<head1;k2++) if(save[k2]) return 0;
    for(int k2=minh;k2<head2;k2++) if(tc_tape1[k2]) return 0;
    ok=1;
    for(int k2=0;k2<=W;k2++)
      if(save[head1+k2]!=tc_tape1[head2+k2]){ ok=0; break; }
  } else ok=0;                          /* d==0 would be in-place */
  if(ok){ *vis_lap_out = vis; *fire_lap_out = fired; }
  return ok;
}

/* ----------------------------------------------------------------- */
/* tier N: n-gram CPS closure, mirroring Checkers/NGram.v.
 * Context = q(2b) | h(1b) | lw(n bits, bit k = cell k+1 left) | rw(n).
 * Dense arrays over 2^(3+2n) contexts; gram sets = bitmask over 2^n. */

#define NGMAXN 8
static uint8_t ng_seen[1u<<(3+2*NGMAXN)];
static uint32_t ng_stack[1u<<(3+2*NGMAXN)];

/* per-run gram sets */
static uint64_t lset[ (1u<<NGMAXN)/64 + 1 ], rset[ (1u<<NGMAXN)/64 + 1 ];
static inline int gget(uint64_t *s, uint32_t g){ return (s[g>>6]>>(g&63))&1; }
static inline void gput(uint64_t *s, uint32_t g){ s[g>>6] |= 1ULL<<(g&63); }

/* ngram check: 1 = never-quasihalts proven (at level [lvl]: 0 = state,
 * 1 = instruction).  If [failmask] is non-NULL every goal is tried and
 * the bitmask of goals whose liveness went unproven is returned there. */
static int ngram_check(const uint8_t *sl, int n, int t, int lvl, int *failmask){
  if(failmask) *failmask = -1;   /* -1 = closure itself failed */
  /* 1. simulate t steps to seed */
  int head=TAPE/2, q=0;
  int lo=head, hi=head;
  for(int i=0;i<t;i++){
    int s=tape_[head];
    uint8_t tr=SLOT(sl,q,s);
    if(tr==UNDEF){ return 0; }  /* halts: not our business */
    tape_[head]=(int8_t)tr_wr(tr);
    head += tr_dir(tr)?1:-1;
    q = tr_next(tr);
    if(head<lo)lo=head;
    if(head>hi)hi=head;
    if(head<8||head>TAPE-8) return 0;
  }
  uint32_t mask=(1u<<n)-1;
  memset(lset,0,sizeof lset); memset(rset,0,sizeof rset);
  /* seed grams at all depths d>=1 (plus the all-blank window) */
  {
    int llen = head-lo+4, rlen = hi-head+4; /* +slack to include blank windows */
    for(int d=1; d<=llen+1; d++){
      uint32_t g=0;
      for(int k=0;k<n;k++){ int idx=head-(d+k); g |= (uint32_t)(idx>=0?(tape_[idx]&1):0)<<k; }
      gput(lset,g);
    }
    for(int d=1; d<=rlen+1; d++){
      uint32_t g=0;
      for(int k=0;k<n;k++){ int idx=head+(d+k); g |= (uint32_t)(idx<TAPE?(tape_[idx]&1):0)<<k; }
      gput(rset,g);
    }
  }
  uint32_t lw0=0, rw0=0;
  for(int k=0;k<n;k++){
    lw0 |= (uint32_t)(tape_[head-1-k]&1)<<k;
    rw0 |= (uint32_t)(tape_[head+1+k]&1)<<k;
  }
  uint32_t a0 = ((uint32_t)q<<(1+2*n)) | ((uint32_t)(tape_[head]&1)<<(2*n)) | (lw0<<n) | rw0;
  uint32_t nctx = 1u<<(3+2*n);

  /* 2. donation-gated growth to fixpoint (ng_grow) */
  for(int round=0;;round++){
    if(round> (1<<(2*n))+8 ) return 0; /* safety */
    /* explore closure under current sets */
    memset(ng_seen,0,nctx);
    long sp=0; ng_stack[sp++]=a0; ng_seen[a0]=1;
    long ndon=0;
    uint64_t lnew[ (1u<<NGMAXN)/64 + 1 ], rnew[ (1u<<NGMAXN)/64 + 1 ];
    memcpy(lnew,lset,sizeof lset); memcpy(rnew,rset,sizeof rset);
    while(sp){
      uint32_t c = ng_stack[--sp];
      uint32_t rw = c & mask, lw = (c>>n)&mask, h=(c>>(2*n))&1, cq=c>>(1+2*n);
      uint8_t tr = SLOT(sl,cq,h);
      if(tr==UNDEF) return 0;                    /* halt reachable */
      uint32_t q2=tr_next(tr), w=tr_wr(tr);
      if(tr_dir(tr)){ /* R: donate lw; branch on new far-right cell */
        if(!gget(lnew,lw)){ gput(lnew,lw); ndon++; }
        if(gget(lset,lw)){
          uint32_t lw2 = ((lw<<1)|w)&mask;
          for(uint32_t x=0;x<2;x++){
            uint32_t rw2 = (rw>>1)|(x<<(n-1));
            if(!gget(rset,rw2)) continue;
            uint32_t h2 = rw&1;
            uint32_t c2 = (q2<<(1+2*n))|(h2<<(2*n))|(lw2<<n)|rw2;
            if(!ng_seen[c2]){ ng_seen[c2]=1; ng_stack[sp++]=c2; }
          }
        }
      } else { /* L: donate rw */
        if(!gget(rnew,rw)){ gput(rnew,rw); ndon++; }
        if(gget(rset,rw)){
          uint32_t rw2 = ((rw<<1)|w)&mask;
          for(uint32_t x=0;x<2;x++){
            uint32_t lw2 = (lw>>1)|(x<<(n-1));
            if(!gget(lset,lw2)) continue;
            uint32_t h2 = lw&1;
            uint32_t c2 = (q2<<(1+2*n))|(h2<<(2*n))|(lw2<<n)|rw2;
            if(!ng_seen[c2]){ ng_seen[c2]=1; ng_stack[sp++]=c2; }
          }
        }
      }
    }
    if(ndon==0) break;
    memcpy(lset,lnew,sizeof lset); memcpy(rset,rnew,sizeof rset);
  }

  /* 3. closed check: rebuild final closure; every context's moves must
   *    be enabled (window in set) -- blocked contexts fail closedness. */
  memset(ng_seen,0,nctx);
  long sp=0; ng_stack[sp++]=a0; ng_seen[a0]=1;
  long ncl=0;
  static uint32_t cls[1u<<(3+2*NGMAXN)];
  while(sp){
    uint32_t c = ng_stack[--sp];
    cls[ncl++]=c;
    uint32_t rw = c & mask, lw=(c>>n)&mask, h=(c>>(2*n))&1, cq=c>>(1+2*n);
    uint8_t tr = SLOT(sl,cq,h);
    if(tr==UNDEF) return 0;
    uint32_t q2=tr_next(tr), w=tr_wr(tr);
    if(tr_dir(tr)){
      if(!gget(lset,lw)) return 0;               /* blocked: not closed */
      uint32_t lw2=((lw<<1)|w)&mask;
      for(uint32_t x=0;x<2;x++){
        uint32_t rw2=(rw>>1)|(x<<(n-1));
        if(!gget(rset,rw2)) continue;
        uint32_t c2=(q2<<(1+2*n))|((rw&1)<<(2*n))|(lw2<<n)|rw2;
        if(!ng_seen[c2]){ ng_seen[c2]=1; ng_stack[sp++]=c2; }
      }
    } else {
      if(!gget(rset,rw)) return 0;
      uint32_t rw2=((rw<<1)|w)&mask;
      for(uint32_t x=0;x<2;x++){
        uint32_t lw2=(lw>>1)|(x<<(n-1));
        if(!gget(lset,lw2)) continue;
        uint32_t c2=(q2<<(1+2*n))|((lw&1)<<(2*n))|(lw2<<n)|rw2;
        if(!ng_seen[c2]){ ng_seen[c2]=1; ng_stack[sp++]=c2; }
      }
    }
  }

  /* 4. per-GOAL acyclicity of the goal-avoiding subgraph (rank check).
   *
   *    lvl=0 (state level, the shipped BBB(4) contract): goal ga is a
   *    state; a node is a goal node iff its state is ga.
   *    lvl=1 (instruction level): goal ga = (q,s) packed as q*2+s; a
   *    node is a goal node iff its state is q AND its head symbol is s.
   *    The n-gram context carries the head symbol, so this costs nothing
   *    beyond a wider goal loop -- that is the whole point of the
   *    measurement.
   *
   *    Also require liveness for goals fired in the simulated prefix. */
  uint8_t prefvis[4]={0,0,0,0};
  uint8_t preffire[8]={0,0,0,0,0,0,0,0};
  { /* re-simulate the prefix to know visited states / fired instrs */
    int hd=TAPE/2, qq=0;
    static int8_t tp[TAPE]; memset(tp+TAPE/2-t-4, 0, 2*t+8);
    prefvis[0]=1;
    for(int i=0;i<t;i++){
      int rs=tp[hd];
      uint8_t tr=SLOT(sl,qq,rs);
      if(tr==UNDEF) break;
      preffire[qq*2+rs]=1;
      tp[hd]=(int8_t)tr_wr(tr); hd+=tr_dir(tr)?1:-1; qq=tr_next(tr);
      prefvis[qq]=1;
    }
  }
  int ngoal = lvl? 8 : 4;
#define GOALNODE(c) (lvl ? ((((c)>>(1+2*n))*2u + (((c)>>(2*n))&1u)) == (uint32_t)ga) \
                         : (((c)>>(1+2*n)) == (uint32_t)ga))
  int fail=0;
  for(int ga=0;ga<ngoal;ga++){
    int need = lvl? preffire[ga] : prefvis[ga];
    if(!need) for(long i=0;i<ncl;i++) if(GOALNODE(cls[i])){ need=1; break; }
    if(!need) continue;
    /* Kahn peel on the subgraph of non-goal contexts */
    static int32_t indeg[1u<<(3+2*NGMAXN)];
    for(long i=0;i<ncl;i++){ indeg[cls[i]]=0; }
    /* count edges into goal-avoiding successors */
    for(long i=0;i<ncl;i++){
      uint32_t c=cls[i];
      if(GOALNODE(c)) continue;
      uint32_t rw=c&mask, lw=(c>>n)&mask, h=(c>>(2*n))&1, cq=c>>(1+2*n);
      uint8_t tr=SLOT(sl,cq,h);
      uint32_t q2=tr_next(tr), w=tr_wr(tr);
      if(tr_dir(tr)){
        uint32_t lw2=((lw<<1)|w)&mask;
        for(uint32_t x=0;x<2;x++){
          uint32_t rw2=(rw>>1)|(x<<(n-1));
          if(!gget(rset,rw2)) continue;
          uint32_t c2=(q2<<(1+2*n))|((rw&1)<<(2*n))|(lw2<<n)|rw2;
          if(GOALNODE(c2)) continue;
          if(ng_seen[c2]) indeg[c2]++;
        }
      } else {
        uint32_t rw2=((rw<<1)|w)&mask;
        for(uint32_t x=0;x<2;x++){
          uint32_t lw2=(lw>>1)|(x<<(n-1));
          if(!gget(lset,lw2)) continue;
          uint32_t c2=(q2<<(1+2*n))|((lw&1)<<(2*n))|(lw2<<n)|rw2;
          if(GOALNODE(c2)) continue;
          if(ng_seen[c2]) indeg[c2]++;
        }
      }
    }
    /* peel */
    long qsz=0;
    static uint32_t kq[1u<<(3+2*NGMAXN)];
    long alive=0;
    for(long i=0;i<ncl;i++){
      uint32_t c=cls[i];
      if(GOALNODE(c)) continue;
      alive++;
      if(indeg[c]==0) kq[qsz++]=c;
    }
    long peeled=0;
    /* NOTE: Kahn needs predecessor edges; we peel by repeatedly removing
     * indeg-0 nodes and decrementing successors' indegs. */
    for(long i=0;i<qsz;i++){
      uint32_t c=kq[i]; peeled++;
      uint32_t rw=c&mask, lw=(c>>n)&mask, h=(c>>(2*n))&1, cq=c>>(1+2*n);
      uint8_t tr=SLOT(sl,cq,h);
      uint32_t q2=tr_next(tr), w=tr_wr(tr);
      if(tr_dir(tr)){
        uint32_t lw2=((lw<<1)|w)&mask;
        for(uint32_t x=0;x<2;x++){
          uint32_t rw2=(rw>>1)|(x<<(n-1));
          if(!gget(rset,rw2)) continue;
          uint32_t c2=(q2<<(1+2*n))|((rw&1)<<(2*n))|(lw2<<n)|rw2;
          if(GOALNODE(c2)) continue;
          if(ng_seen[c2] && --indeg[c2]==0) kq[qsz++]=c2;
        }
      } else {
        uint32_t rw2=((rw<<1)|w)&mask;
        for(uint32_t x=0;x<2;x++){
          uint32_t lw2=(lw>>1)|(x<<(n-1));
          if(!gget(lset,lw2)) continue;
          uint32_t c2=(q2<<(1+2*n))|((lw&1)<<(2*n))|(lw2<<n)|rw2;
          if(GOALNODE(c2)) continue;
          if(ng_seen[c2] && --indeg[c2]==0) kq[qsz++]=c2;
        }
      }
    }
    if(peeled<alive){            /* cycle avoiding ga: liveness unproven */
      fail |= 1<<ga;
      if(!failmask) return 0;    /* caller wants only the verdict */
    }
  }
#undef GOALNODE
  if(failmask) *failmask = fail;
  return fail==0;
}

/* wrapper: mirror the machine (for left-handed everything is symmetric
 * in this implementation already -- the CPS is two-sided). */

/* ----------------------------------------------------------------- */
/* holdout list */
#define MAXHOLD 8192
static char hold_txt[MAXHOLD][40];
static int nhold=0;
static int hold_sorted_idx[MAXHOLD];

static int cmp_hold(const void *a, const void *b){
  return strcmp(hold_txt[*(const int*)a], hold_txt[*(const int*)b]);
}
static int hold_lookup(const char *txt){
  int lo=0, hi=nhold-1;
  while(lo<=hi){ int mid=(lo+hi)/2;
    int c=strcmp(txt, hold_txt[hold_sorted_idx[mid]]);
    if(c==0) return 1;
    if(c<0) hi=mid-1; else lo=mid+1;
  }
  return 0;
}

/* ----------------------------------------------------------------- */
static int parse_tm(const char *txt, uint8_t *sl){
  int q,s; const char *p=txt;
  for(q=0;q<4;q++){
    if(q){ if(*p!='_') return 0; p++; }
    for(s=0;s<2;s++){
      if(p[0]=='-'){ SLOT(sl,q,s)=UNDEF; }
      else{
        int w=p[0]-'0', d=(p[1]=='R'), nx=p[2]-'A';
        if((w|1)!=1||nx<0||nx>3||(p[1]!='R'&&p[1]!='L')) return 0;
        SLOT(sl,q,s)=(uint8_t)(nx<<2|d<<1|w);
      }
      p+=3;
    }
  }
  return 1;
}

int main(int argc, char **argv){
  const char *hold_file = NULL, *residue_file = NULL, *csv_file = NULL;
  const char *machines_file = NULL;
  int gas = 1030;
  int ng_n[8] = {2,3,4,6,0,0,0,0};
  int ng_t[8] = {100,200,400,800,0,0,0,0};
  int nrungs = 4;
  for(int i=1;i<argc;i++){
    if(!strcmp(argv[i],"--holdouts")) hold_file=argv[++i];
    else if(!strcmp(argv[i],"--gas")) gas=atoi(argv[++i]);
    else if(!strcmp(argv[i],"--residue")) residue_file=argv[++i];
    else if(!strcmp(argv[i],"--csv")) csv_file=argv[++i];
    else if(!strcmp(argv[i],"--machines")) machines_file=argv[++i];
    else if(!strcmp(argv[i],"--rungs")){ /* n:t,n:t,... */
      nrungs=0; char *spec=argv[++i];
      for(char *tok=strtok(spec,","); tok && nrungs<8; tok=strtok(NULL,",")){
        sscanf(tok,"%d:%d",&ng_n[nrungs],&ng_t[nrungs]); nrungs++;
      }
    }
    else { fprintf(stderr,"unknown arg %s\n",argv[i]); return 2; }
  }
  if(gas>MAXGAS){ fprintf(stderr,"gas too big\n"); return 2; }
  init_pow();
  if(hold_file){
    FILE *f=fopen(hold_file,"r");
    if(!f){ perror(hold_file); return 2; }
    while(nhold<MAXHOLD && fscanf(f,"%39s",hold_txt[nhold])==1) nhold++;
    fclose(f);
    for(int i=0;i<nhold;i++) hold_sorted_idx[i]=i;
    qsort(hold_sorted_idx,nhold,sizeof(int),cmp_hold);
    fprintf(stderr,"loaded %d holdouts\n",nhold);
  }
  FILE *rf = residue_file? fopen(residue_file,"w") : NULL;
  FILE *cf = csv_file? fopen(csv_file,"w") : NULL;
  if(cf) fprintf(cf,"machine,status,tier,score\n");

  /* explicit DFS stack */
  static Node stack[1<<22];
  long sp=0;

  /* root expansion, mirroring the Coq root: TM0 halts at step 0 in
   * state A reading 0; children fill A0 with next <= ptr(B), keep
   * dir = R (mirror symmetry). */
  for(int nx=0;nx<2;nx++) for(int w=0;w<2;w++){
    Node nd; memset(nd.sl,UNDEF,8);
    nd.sl[0] = (uint8_t)(nx<<2 | 1<<1 | w);
    nd.ptr = (nx==1)? 2 : 1;
    stack[sp++]=nd;
  }

  long n_nodes=2;         /* count TM0 and its A0-undefined sibling-leaf...
                             actually: count popped nodes below; the root
                             TM0 itself is 1 node (expanded), and the
                             4 Dneg mirror children are not enumerated. */
  n_nodes = 1;            /* the root */
  long c_halt=0,c_inplace_nqh=0,c_inplace_qh=0,c_tc_nqh=0,c_tc_qh=0;
  long c_ng[8]={0,0,0,0,0,0,0,0};   /* per ladder rung */
  long c_hold=0, c_residue=0, c_runner=0;
  long max_qh_score=0, max_halt=0;
  char max_qh_m[40]="", max_halt_m[40]="";
  int list_mode = 0;

  /* ---- instruction-level counters (the delta being measured) ---- */
  /* cycle tiers: cross-tab of the two verdicts (exact at these tiers) */
  long x_c[2][2]={{0,0},{0,0}};      /* [state QH?][instr QH?], tier C */
  long x_t[2][2]={{0,0},{0,0}};      /* same, tier T */
  long max_qh_score_i=0; char max_qh_m_i[40]="";
  /* tier N: cross-tab of "ladder proves never-QH" at the two levels */
  long x_n[2][2]={{0,0},{0,0}};      /* [state proved][instr proved] */
  /* of the state-proved-but-instr-unproven ones, how many look like
     genuine new quasihalters (the failing instruction stopped firing
     long before the simulation ended) vs. merely coarse abstraction */
  long n_lookslive=0, n_looksquiet=0;
  long max_new_gap=0; char max_new_gap_m[40]="";

  if(machines_file){
    FILE *f=fopen(machines_file,"r");
    if(!f){ perror(machines_file); return 2; }
    char buf[64]; sp=0;
    while(fscanf(f,"%63s",buf)==1){
      Node nd; memset(nd.sl,UNDEF,8); nd.ptr=4;
      if(!parse_tm(buf,nd.sl)){ fprintf(stderr,"bad machine %s\n",buf); return 2; }
      stack[sp++]=nd;
    }
    fclose(f);
    list_mode=1; n_nodes=0;
    fprintf(stderr,"list mode: %ld machines\n",sp);
  }

  while(sp){
    Node nd = stack[--sp];
    n_nodes++;
    SimOut o;
    simulate(nd.sl, gas, &o);
    wipe_tape();
    char txt[40];

    if(o.kind==1){
      /* halting: score = halt step (kept for the census stats);
       * expand children (this is the QH tree: even cnt=1 expands). */
      c_halt++;
      int hn = o.halt_n+1;    /* halting step, bbchallenge convention */
      if(hn>max_halt){ max_halt=hn; tm_text(nd.sl,max_halt_m); }
      if(cf){ tm_text(nd.sl,txt); fprintf(cf,"%s,halt,H,%d\n",txt,hn); }
      if(list_mode) continue;
      int maxnext = nd.ptr>3? 3 : nd.ptr;
      for(int nx=0;nx<=maxnext;nx++) for(int d=0;d<2;d++) for(int w=0;w<2;w++){
        Node ch = nd;
        SLOT(ch.sl,o.halt_q,o.halt_s) = (uint8_t)(nx<<2|d<<1|w);
        ch.ptr = (nx==nd.ptr)? nd.ptr+1 : nd.ptr;
        if(sp >= (long)(sizeof stack/sizeof stack[0])){ fprintf(stderr,"stack overflow\n"); return 3; }
        stack[sp++]=ch;
      }
      continue;
    }
    if(o.kind==2){
      /* in-place cycle: BOTH verdicts are exact here */
      if(o.score_hint>=0){
        c_inplace_qh++;
        long sc=o.score_hint+1;
        if(sc>max_qh_score){ max_qh_score=sc; tm_text(nd.sl,max_qh_m); }
        if(cf){ tm_text(nd.sl,txt); fprintf(cf,"%s,qh,C,%ld\n",txt,sc); }
      } else {
        c_inplace_nqh++;
        if(cf){ tm_text(nd.sl,txt); fprintf(cf,"%s,neverqh,C,\n",txt); }
      }
      x_c[o.score_hint>=0][o.score_hint_i>=0]++;
      if(o.score_hint_i>=0){
        long sci=o.score_hint_i+1;
        if(sci>max_qh_score_i){ max_qh_score_i=sci; tm_text(nd.sl,max_qh_m_i); }
      }
      continue;
    }
    if(o.kind==3){ c_runner++; /* fell off tape: treat via TC/ngram below */ }

    /* tier T: translated cycles, both sides, window-verified */
    {
      TCand cand[16];
      int nc = tc_candidates(&o,1,cand,8);
      nc += tc_candidates(&o,0,cand+nc,(int)(16-nc));
      int done=0;
      for(int ci=0;ci<nc && !done;ci++){
        int vis_lap=0, fire_lap=0;
        if(!tc_verify(nd.sl,cand[ci].a,cand[ci].P,&vis_lap,&fire_lap)) continue;
        long sc=-1;
        for(int j=0;j<4;j++)
          if(o.last_visit[j]>=0 && !((vis_lap>>j)&1) && o.last_visit[j]>sc)
            sc=o.last_visit[j];
        long sci=-1;
        for(int j=0;j<8;j++)
          if(o.last_fire[j]>=0 && !((fire_lap>>j)&1) && o.last_fire[j]>sci)
            sci=o.last_fire[j];
        if(sc>=0){
          c_tc_qh++;
          if(sc+1>max_qh_score){ max_qh_score=sc+1; tm_text(nd.sl,max_qh_m); }
          if(cf){ tm_text(nd.sl,txt); fprintf(cf,"%s,qh,T,%ld\n",txt,sc+1); }
        } else {
          c_tc_nqh++;
          if(cf){ tm_text(nd.sl,txt); fprintf(cf,"%s,neverqh,T,\n",txt); }
        }
        x_t[sc>=0][sci>=0]++;
        if(sci>=0 && sci+1>max_qh_score_i){
          max_qh_score_i=sci+1; tm_text(nd.sl,max_qh_m_i); }
        done=1;
      }
      if(done) continue;
    }

    /* tier N: n-gram ladder, run at BOTH levels on the same rungs */
    {
      /* instruction-level success at a rung implies state-level success
         at the same rung (the goal-avoiding subgraph is larger), so one
         pass per rung settles both. */
      int killed=0, killed_i=0, fm=0, fm_keep=0;
      for(int r=0;r<nrungs;r++){
        wipe_tape();
        if(ngram_check(nd.sl, ng_n[r], ng_t[r], 1, &fm)){
          killed=1; killed_i=1; c_ng[r]++;
          if(cf){ tm_text(nd.sl,txt); fprintf(cf,"%s,neverqh,N%d,\n",txt,ng_n[r]); }
          break;
        }
        wipe_tape();
        if(ngram_check(nd.sl, ng_n[r], ng_t[r], 0, NULL)){
          killed=1; fm_keep=fm; c_ng[r]++;
          if(cf){ tm_text(nd.sl,txt); fprintf(cf,"%s,neverqh,N%d,\n",txt,ng_n[r]); }
          break;
        }
      }
      wipe_tape();
      x_n[killed][killed_i]++;
      if(killed && !killed_i){
        /* diagnose: did the unproven instruction actually stop firing? */
        int gap_max=-1;
        for(int j=0;j<8;j++) if((fm_keep>>j)&1){
          if(o.last_fire[j]>=0){
            int gap = gas - o.last_fire[j];
            if(gap>gap_max) gap_max=gap;
          }
        }
        if(gap_max > gas/4){ n_looksquiet++;
          if(gap_max>max_new_gap){ max_new_gap=gap_max; tm_text(nd.sl,max_new_gap_m); }
          if(rf){ tm_text(nd.sl,txt); fprintf(rf,"%s\tNEWQH?\tgap=%d\n",txt,gap_max); }
        }
        else { n_lookslive++;
          if(rf){ tm_text(nd.sl,txt); fprintf(rf,"%s\tSPARSE?\tgap=%d\n",txt,gap_max); } }
      }
      if(killed) continue;
    }

    /* tier D: holdout list */
    tm_text(nd.sl,txt);
    if(nhold && hold_lookup(txt)){ c_hold++;
      if(cf) fprintf(cf,"%s,deferred,D,\n",txt);
      continue; }

    c_residue++;
    if(rf) fprintf(rf,"%s\n",txt);
    if(cf) fprintf(cf,"%s,unknown,-,\n",txt);
  }

  fprintf(stderr,
    "nodes            %ld\n"
    "halt (expanded)  %ld   max halting step %ld  (%s)\n"
    "inplace neverqh  %ld\n"
    "inplace qh       %ld\n"
    "tcycle  neverqh  %ld\n"
    "tcycle  qh       %ld\n"
    "holdout deferred %ld\n"
    "RESIDUE          %ld\n"
    "(runner events   %ld)\n"
    "max easy QH score %ld  (%s)\n",
    n_nodes, c_halt, max_halt, max_halt_m,
    c_inplace_nqh, c_inplace_qh, c_tc_nqh, c_tc_qh,
    c_hold, c_residue, c_runner, max_qh_score, max_qh_m);
  for(int r=0;r<nrungs;r++)
    fprintf(stderr,"ngram n=%d t=%d : %ld\n", ng_n[r], ng_t[r], c_ng[r]);

  fprintf(stderr,
    "\n=== INSTRUCTION-LEVEL DELTA ===\n"
    "tier C (in-place cycle, both verdicts EXACT)\n"
    "  neverQH st / neverQH in  %ld\n"
    "  neverQH st / QH      in  %ld   <- new quasihalters, score free\n"
    "  QH      st / neverQH in  %ld   <- must be 0\n"
    "  QH      st / QH      in  %ld\n"
    "tier T (translated cycle, both verdicts EXACT)\n"
    "  neverQH st / neverQH in  %ld\n"
    "  neverQH st / QH      in  %ld   <- new quasihalters, score free\n"
    "  QH      st / neverQH in  %ld   <- must be 0\n"
    "  QH      st / QH      in  %ld\n"
    "tier N (n-gram ladder, verdict = 'never-QH PROVEN at this rung')\n"
    "  proven st / proven in    %ld\n"
    "  proven st / UNPROVEN in  %ld   <- the new work at this tier\n"
    "     of which the dead instruction stayed dead > gas/4 : %ld"
    " (likely genuine QH -> needs a score certificate)\n"
    "     of which it was still firing late            : %ld"
    " (abstraction too coarse -> needs a finer rung/rank rule)\n"
    "  UNPROVEN st / proven in  %ld   <- must be 0\n"
    "  UNPROVEN st / UNPROVEN   %ld   (already residue at both levels)\n"
    "max easy QH score, instruction level %ld  (%s)\n"
    "widest new quiet gap %ld  (%s)\n",
    x_c[0][0],x_c[0][1],x_c[1][0],x_c[1][1],
    x_t[0][0],x_t[0][1],x_t[1][0],x_t[1][1],
    x_n[1][1],x_n[1][0],n_looksquiet,n_lookslive,x_n[0][1],x_n[0][0],
    max_qh_score_i, max_qh_m_i, max_new_gap, max_new_gap_m);

  if(rf) fclose(rf);
  if(cf) fclose(cf);
  return 0;
}
