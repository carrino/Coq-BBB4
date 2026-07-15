/* census_ladder.c -- UNTRUSTED measurement tool for the Scope B census.
 *
 * Enumerates the full (4,2) TNF tree exactly as the planned Coq census
 * will (Coq-BB5 style: root = all-undefined, expand every machine that
 * reaches an undefined transition, first move fixed to R by mirror
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
 * + 1 is the score, per the BBB README conventions.
 *
 * This tool sizes the Coq sweep (NEXT_SESSION.md "first move"); it
 * carries no soundness.  gcc -O2 -o census_ladder census_ladder.c
 *
 * Usage: ./census_ladder [--holdouts FILE] [--gas N] [--residue FILE]
 *                        [--csv FILE]
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
        return; }
      b=(b+1)&(HSZ-1);
    }
    if(n>=gas) { o->kind=0; return; }
    int s = tape_[head];
    uint8_t t = SLOT(sl,q,s);
    if(t==UNDEF){ o->kind=1; o->halt_n=n; o->halt_q=q; o->halt_s=s; return; }
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
static int tc_verify(const uint8_t *sl, int a, int P, int *vis_lap_out){
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
  int minh=head, maxh=head, vis=1<<q;
  /* save the window contents left+right of head1 before continuing:
     we compare against tape AFTER P more steps, but the lap may
     overwrite cells; so save a copy of the whole touched span. */
  static int8_t save[TAPE];
  /* conservative: save [head1-(P+2) .. head1+(P+2)] */
  int slo=head1-P-2, shi=head1+P+2;
  if(slo<0||shi>=TAPE) return 0;
  memcpy(save+slo, tc_tape1+slo, (size_t)(shi-slo+1));
  for(int i=0;i<P;i++){
    uint8_t t=SLOT(sl,q,tc_tape1[head]);
    if(t==UNDEF) return 0;
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
  if(ok) *vis_lap_out = vis;
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

/* ngram check: 1 = never-quasihalts proven. */
static int ngram_check(const uint8_t *sl, int n, int t){
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

  /* 4. per-state acyclicity of the q-avoiding subgraph (rank check).
   *    Also require it for states visited in the simulated prefix. */
  uint8_t prefvis[4]={0,0,0,0};
  { /* re-simulate the prefix to know visited states (cheap) */
    int hd=TAPE/2, qq=0;
    static int8_t tp[TAPE]; memset(tp+TAPE/2-t-4, 0, 2*t+8);
    prefvis[0]=1;
    for(int i=0;i<t;i++){
      uint8_t tr=SLOT(sl,qq,tp[hd]);
      if(tr==UNDEF) break;
      tp[hd]=(int8_t)tr_wr(tr); hd+=tr_dir(tr)?1:-1; qq=tr_next(tr);
      prefvis[qq]=1;
    }
  }
  for(int qa=0;qa<4;qa++){
    int need = prefvis[qa];
    if(!need) for(long i=0;i<ncl;i++) if((cls[i]>>(1+2*n))==(uint32_t)qa){ need=1; break; }
    if(!need) continue;
    /* Kahn peel on subgraph of contexts with state != qa */
    static int32_t indeg[1u<<(3+2*NGMAXN)];
    long m=0;
    for(long i=0;i<ncl;i++){ indeg[cls[i]]=0; }
    /* count edges into q-avoiding successors */
    for(long i=0;i<ncl;i++){
      uint32_t c=cls[i];
      if((c>>(1+2*n))==(uint32_t)qa) continue;
      uint32_t rw=c&mask, lw=(c>>n)&mask, h=(c>>(2*n))&1, cq=c>>(1+2*n);
      uint8_t tr=SLOT(sl,cq,h);
      uint32_t q2=tr_next(tr), w=tr_wr(tr);
      if(q2==(uint32_t)qa) continue;
      if(tr_dir(tr)){
        uint32_t lw2=((lw<<1)|w)&mask;
        for(uint32_t x=0;x<2;x++){
          uint32_t rw2=(rw>>1)|(x<<(n-1));
          if(!gget(rset,rw2)) continue;
          uint32_t c2=(q2<<(1+2*n))|((rw&1)<<(2*n))|(lw2<<n)|rw2;
          if(ng_seen[c2]) indeg[c2]++;
        }
      } else {
        uint32_t rw2=((rw<<1)|w)&mask;
        for(uint32_t x=0;x<2;x++){
          uint32_t lw2=(lw>>1)|(x<<(n-1));
          if(!gget(lset,lw2)) continue;
          uint32_t c2=(q2<<(1+2*n))|((lw&1)<<(2*n))|(lw2<<n)|rw2;
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
      if((c>>(1+2*n))==(uint32_t)qa) continue;
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
      if(q2==(uint32_t)qa) continue;
      if(tr_dir(tr)){
        uint32_t lw2=((lw<<1)|w)&mask;
        for(uint32_t x=0;x<2;x++){
          uint32_t rw2=(rw>>1)|(x<<(n-1));
          if(!gget(rset,rw2)) continue;
          uint32_t c2=(q2<<(1+2*n))|((rw&1)<<(2*n))|(lw2<<n)|rw2;
          if(ng_seen[c2] && --indeg[c2]==0) kq[qsz++]=c2;
        }
      } else {
        uint32_t rw2=((rw<<1)|w)&mask;
        for(uint32_t x=0;x<2;x++){
          uint32_t lw2=(lw>>1)|(x<<(n-1));
          if(!gget(lset,lw2)) continue;
          uint32_t c2=(q2<<(1+2*n))|((lw&1)<<(2*n))|(lw2<<n)|rw2;
          if(ng_seen[c2] && --indeg[c2]==0) kq[qsz++]=c2;
        }
      }
    }
    if(peeled<alive) return 0;   /* cycle avoiding qa: liveness unproven */
    (void)m;
  }
  return 1;
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
      /* in-place cycle */
      if(o.score_hint>=0){
        c_inplace_qh++;
        long sc=o.score_hint+1;
        if(sc>max_qh_score){ max_qh_score=sc; tm_text(nd.sl,max_qh_m); }
        if(cf){ tm_text(nd.sl,txt); fprintf(cf,"%s,qh,C,%ld\n",txt,sc); }
      } else {
        c_inplace_nqh++;
        if(cf){ tm_text(nd.sl,txt); fprintf(cf,"%s,neverqh,C,\n",txt); }
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
        int vis_lap=0;
        if(!tc_verify(nd.sl,cand[ci].a,cand[ci].P,&vis_lap)) continue;
        long sc=-1;
        for(int j=0;j<4;j++)
          if(o.last_visit[j]>=0 && !((vis_lap>>j)&1) && o.last_visit[j]>sc)
            sc=o.last_visit[j];
        if(sc>=0){
          c_tc_qh++;
          if(sc+1>max_qh_score){ max_qh_score=sc+1; tm_text(nd.sl,max_qh_m); }
          if(cf){ tm_text(nd.sl,txt); fprintf(cf,"%s,qh,T,%ld\n",txt,sc+1); }
        } else {
          c_tc_nqh++;
          if(cf){ tm_text(nd.sl,txt); fprintf(cf,"%s,neverqh,T,\n",txt); }
        }
        done=1;
      }
      if(done) continue;
    }

    /* tier N: n-gram ladder */
    {
      int killed=0;
      for(int r=0;r<nrungs;r++){
        wipe_tape();
        if(ngram_check(nd.sl, ng_n[r], ng_t[r])){ c_ng[r]++; killed=1;
          if(cf){ tm_text(nd.sl,txt); fprintf(cf,"%s,neverqh,N%d,\n",txt,ng_n[r]); }
          break; }
      }
      wipe_tape();
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

  if(rf) fclose(rf);
  if(cf) fclose(cf);
  return 0;
}
