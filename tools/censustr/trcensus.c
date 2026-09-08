#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
/* stdin: machine text per line.  argv[1]: step budget.
   Output per machine: text, then per-transition cnt:last, then verdict:
   SUSPECT if some fired transition's last fire < budget/10 (trailing
   silence >= 90%), else LIVE.  HALT/EDGE reported. */
static int run(const char*mtxt, uint64_t LIMIT, uint8_t*tape, size_t N){
    uint8_t wr[4][2]; int8_t mv[4][2]; int8_t nx[4][2];
    { int qi=0; const char*p=mtxt;
      while(*p && qi<4){
        for(int s=0;s<2;s++){
          if(p[0]=='-'){ nx[qi][s]=-1; wr[qi][s]=0; mv[qi][s]=1; }
          else { wr[qi][s]=p[0]-'0'; mv[qi][s]=(p[1]=='R')?+1:-1; nx[qi][s]=p[2]-'A'; }
          p+=3;
        }
        if(*p=='_')p++;
        qi++;
      }
    }
    memset(tape,0,N);
    int64_t pos=(int64_t)N/2;
    int st=0; uint64_t step=0;
    uint64_t last[8]={0},cnt[8]={0};
    while(step<LIMIT){
        uint8_t s=tape[pos];
        int t=st*2+s;
        if(nx[st][s]<0){ printf("%s HALT %llu\n",mtxt,(unsigned long long)(step+1)); return 0; }
        cnt[t]++; last[t]=step;
        tape[pos]=wr[st][s]; pos+=mv[st][s]; st=nx[st][s]; step++;
        if(pos<8||pos>=(int64_t)N-8){ printf("%s EDGE %llu\n",mtxt,(unsigned long long)step); return 0; }
    }
    int suspect=0;
    printf("%s",mtxt);
    for(int t=0;t<8;t++){
        printf(" T%c%d:%llu:%llu",'A'+t/2,t%2,
            (unsigned long long)cnt[t],(unsigned long long)last[t]);
        if(cnt[t]>0 && last[t] < LIMIT/10) suspect=1;
    }
    printf(" %s\n", suspect?"SUSPECT":"LIVE");
    return 0;
}
int main(int argc,char**argv){
    uint64_t LIMIT=argc>1?strtoull(argv[1],0,10):100000000ULL;
    size_t N=1u<<26;
    uint8_t*tape=malloc(N);
    char line[256];
    while(fgets(line,sizeof line,stdin)){
        char*nl=strchr(line,'\n'); if(nl)*nl=0;
        if(!line[0]||line[0]=='#')continue;
        run(line,LIMIT,tape,N);
        fflush(stdout);
    }
    return 0;
}
