#include <stdio.h>
#include <stdlib.h>
#include <string.h>
/* fast (4,2) simulator: reports transition-usage counts between successive
   configurations matching a caller-supplied "anchor" predicate.           */
static int W[4][2], D[4][2], N[4][2], defined[4][2];
static unsigned char *tape; static long SZ, lo, hi, pos; static int q;
static long long cnt[8];
int parse(const char*s){int si=0,k=0;for(;;){for(int y=0;y<2;y++){const char*e=s+k+3*y;
 if(e[0]=='-'){defined[si][y]=0;}else{defined[si][y]=1;W[si][y]=e[0]-'0';D[si][y]=(e[1]=='R')?1:-1;N[si][y]=e[2]-'A';}}
 k+=6; if(s[k]==0)break; k++; si++;} return 0;}
int main(int argc,char**argv){
  const char*spec=argv[1]; long long steps=atoll(argv[2]); int mode=atoi(argv[3]);
  parse(spec);
  SZ=200000000L; tape=calloc(SZ,1); long off=SZ/2; pos=off; lo=hi=off; q=0;
  long long t=0; long long prev[8]; memset(prev,0,sizeof prev); long long pt=-1;
  for(t=0;t<steps;t++){
    /* anchor test: state A, head on 0, head at the right frontier */
    if(mode==1 && q==0 && tape[pos]==0 && pos==hi){
      /* left of head: expect 1^m 0 1^w reading leftwards -> print run lengths */
      long i=pos-1; long m=0; while(i>=lo&&tape[i]==1){m++;i--;}
      long z=0; while(i>=lo&&tape[i]==0){z++;i--;}
      long w=0; while(i>=lo&&tape[i]==1){w++;i--;}
      if(z==1&&i<lo){
        printf("t=%lld w=%ld m=%ld dt=%lld",t,w,m,pt<0?-1:t-pt);
        for(int j=0;j<8;j++) printf(" %s%d=%lld","ABCD"[j/2]==0?"":(char[2]){"ABCD"[j/2],0},j%2,cnt[j]-prev[j]);
        printf("\n"); memcpy(prev,cnt,sizeof cnt); pt=t;
      }
    }
    int s=tape[pos]; if(!defined[q][s]){printf("HALT t=%lld\n",t);return 0;}
    cnt[2*q+s]++; tape[pos]=W[q][s]; pos+=D[q][s]; int nq=N[q][s]; q=nq;
    if(pos<lo)lo=pos; if(pos>hi)hi=pos;
    if(pos<=0||pos>=SZ-1){printf("OVERFLOW\n");return 1;}
  }
  return 0;
}
