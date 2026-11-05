/* UNTRUSTED tail-only adaptation of tools/census_ladder.c:ngram_check.
 * Keep seed construction, donation growth, closedness and Kahn peeling
 * unchanged. The only behavioral change is skipping prefix-only targets;
 * remove their redundant prefix scan as well. Coq replay is still required.
 * Include AFTER the legacy source, whose helper globals/functions are used.
 * Frozen legacy source SHA256: d22dcea2137b9cd30d3df8049cd5e47d38d012855b4f8472be62d5dbe5836a9f */
#ifndef BBBWAIT42_NGRAM_TAIL_INCLUDED
#define BBBWAIT42_NGRAM_TAIL_INCLUDED

static int tail_ngram_check(const uint8_t *sl, int n, int t){
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

  /* 4. Per-state acyclicity only for states APPEARING in the closed tail.
   * Prefix-only states are absent after the anchor and need no rank.
   * This matches BBBWait42.Ranked.ranked_window_ok / appears, unlike
   * the legacy global NeverQuasiHaltsSt gate. Still UNTRUSTED C. */
  for(int qa=0;qa<4;qa++){
    int need = 0;
    for(long i=0;i<ncl;i++) if((cls[i]>>(1+2*n))==(uint32_t)qa){ need=1; break; }
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

#endif
