/* probe_instr.c -- UNTRUSTED measurement: for each machine on stdin
 * (bbchallenge text, one per line), simulate H steps from the blank
 * tape and report, per STATE and per INSTRUCTION, the last index at
 * which it was visited / fired.
 *
 * Purpose: size the instruction-level ("beep on an instruction, not a
 * state") variant of the BBB(4) development.  A machine whose every
 * VISITED state is visited late but which has a FIRED instruction that
 * stopped firing early is a machine whose board changes character:
 * today it proves NeverQuasiHaltsSt, at instruction level it is a
 * quasihalter and needs a score.
 *
 * Also reports, per instruction, the largest and the last inter-fire
 * gap: that is what separates "the abstraction is too coarse" (bounded
 * gaps) from "this instruction fires once per doubling epoch" (gaps
 * growing without bound), and the second kind is the one no finite
 * acyclicity rank can ever certify.
 *
 * A verdict is only ever a HINT: the horizon is finite, so an
 * instruction reported dead may fire again later.  Measured trap:
 * probed at 5e6 steps, 199 frozen rows looked like their score jumped
 * from 1 to ~2^22; at 5e7 the same instructions fire again at ~2^25.
 * Re-probe anything interesting at a larger horizon before believing
 * it.
 *
 * gcc -O2 -o probe_instr probe_instr.c
 * usage: ./probe_instr [--steps N] < machines.txt
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define SLOT(m,q,s) ((m)[(q)*2+(s)])
#define UNDEF 0xFF
static inline int tr_next(uint8_t t){ return t>>2; }
static inline int tr_dir (uint8_t t){ return (t>>1)&1; }
static inline int tr_wr  (uint8_t t){ return t&1; }

#define TAPE (1<<26)
static int8_t tape_[TAPE];

static int parse_tm(const char *txt, uint8_t *sl){
  const char *p=txt;
  for(int q=0;q<4;q++){
    if(q){ if(*p!='_') return 0; p++; }
    for(int s=0;s<2;s++){
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
  long H = 20000000;
  for(int i=1;i<argc;i++)
    if(!strcmp(argv[i],"--steps")) H=atol(argv[++i]);

  char buf[64];
  long n_all_live=0, n_dying=0, n_halt=0, n_statequiet=0, n_offtape=0;
  printf("machine\tverdict\tstate_last\tinstr_last\tmaxgap\tlastgap\n");
  while(scanf("%63s",buf)==1){
    uint8_t sl[8];
    if(!parse_tm(buf,sl)){ fprintf(stderr,"bad %s\n",buf); continue; }
    long lastv[4]={-1,-1,-1,-1}, lastf[8]={-1,-1,-1,-1,-1,-1,-1,-1};
    long maxgap[8]={0,0,0,0,0,0,0,0}, lastgap[8]={0,0,0,0,0,0,0,0};
    long head=TAPE/2, lo=head, hi=head; int q=0; long n; int halted=0, off=0;
    for(n=0;n<H;n++){
      lastv[q]=n;
      int s=tape_[head];
      uint8_t t=SLOT(sl,q,s);
      if(t==UNDEF){ halted=1; break; }
      { int ii=q*2+s;
        if(lastf[ii]>=0){ long g=n-lastf[ii];
          lastgap[ii]=g; if(g>maxgap[ii]) maxgap[ii]=g; }
        lastf[ii]=n; }
      tape_[head]=(int8_t)tr_wr(t);
      head += tr_dir(t)?1:-1;
      q = tr_next(t);
      if(head<lo)lo=head; if(head>hi)hi=head;
      if(head<4||head>=TAPE-4){ off=1; break; }
    }
    memset(tape_+lo, 0, (size_t)(hi-lo+1));

    /* classify.  "late" = within the last 1% of the run. */
    long cut = n - n/100;
    int state_dies=0, instr_dies=0;
    for(int j=0;j<4;j++) if(lastv[j]>=0 && lastv[j]<cut) state_dies=1;
    for(int j=0;j<8;j++) if(lastf[j]>=0 && lastf[j]<cut) instr_dies=1;

    const char *v;
    if(halted) { v="halt"; n_halt++; }
    else if(off) { v="offtape"; n_offtape++; }
    else if(state_dies) { v="state-quiet"; n_statequiet++; }   /* already a QH machine */
    else if(instr_dies) { v="INSTR-DIES"; n_dying++; }          /* the new work */
    else { v="all-live"; n_all_live++; }

    printf("%s\t%s\t", buf, v);
    for(int j=0;j<4;j++) printf("%s%ld", j?",":"", lastv[j]);
    printf("\t");
    for(int j=0;j<8;j++) printf("%s%ld", j?",":"", lastf[j]);
    printf("\t");
    for(int j=0;j<8;j++) printf("%s%ld", j?",":"", maxgap[j]);
    printf("\t");
    for(int j=0;j<8;j++) printf("%s%ld", j?",":"", lastgap[j]);
    printf("\n");
  }
  fprintf(stderr,
    "horizon %ld\n"
    "all-live      %ld   (every fired instruction still firing late)\n"
    "INSTR-DIES    %ld   (state-level live, instruction-level quasihalter)\n"
    "state-quiet   %ld   (already a quasihalter at state level)\n"
    "halt          %ld\n"
    "offtape       %ld\n",
    H, n_all_live, n_dying, n_statequiet, n_halt, n_offtape);
  return 0;
}
