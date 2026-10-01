/* LE4 probe (untrusted): tape extent at checkpoints 1e5*4^i, and the tape
   (lo..hi) at the last K turns of the head at each tape end.
   usage: ext MACHINE STEPS K */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define SZ (1<<24)
static unsigned char tape[SZ];
int main(int argc,char**argv){
  const char*m=argv[1]; long N=atol(argv[2]); int K=atoi(argv[3]);
  int W[4][2],M[4][2],Q[4][2];
  for(int s=0;s<4;s++)for(int b=0;b<2;b++){const char*t=m+s*7+b*3;
    if(t[0]=='-'){W[s][b]=-1;continue;} W[s][b]=t[0]-'0';M[s][b]=t[1]=='R'?1:-1;Q[s][b]=t[2]-'A';}
  long p=SZ/2,lo=p,hi=p; int q=0; long cp=100000; int lastm=0;
  static char buf[2][64][4096]; int nb[2]={0,0}; long tt[2][64];
  for(long t=0;t<N;t++){
    int b=tape[p]; if(W[q][b]<0){printf("HALT %ld\n",t);return 0;}
    if(t==cp){printf("ext %ld %ld\n",t,hi-lo+1);cp*=4;}
    int mv=M[q][b];
    if(t>N-N/4 && lastm && mv!=lastm && (p<=lo+3||p>=hi-3) && hi-lo<4000){
      int sd=(p<=lo+3)?0:1; int i=nb[sd]%64; tt[sd][i]=t;
      char*o=buf[sd][i]; int k=0;
      for(long x=lo;x<=hi;x++){ if(x==p) o[k++]="ABCD"[q]; o[k++]='0'+tape[x]; }
      o[k]=0; nb[sd]++;
    }
    tape[p]=W[q][b]; p+=mv; q=Q[q][b]; lastm=mv;
    if(p<lo)lo=p; if(p>hi)hi=p;
    if(p<2||p>SZ-3){printf("OUT\n");return 0;}
  }
  printf("ext %ld %ld\n",N,hi-lo+1);
  for(int sd=0;sd<2;sd++){int n=nb[sd]; printf("turns %c %d\n","LR"[sd],n);
    for(int j=(n>K?n-K:0);j<n;j++) printf("%c %ld %s\n","LR"[sd],tt[sd][j%64],buf[sd][j%64]);}
  return 0;
}
