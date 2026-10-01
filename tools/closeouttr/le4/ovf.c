/* LE4 probe (untrusted): the tape at each of the last K extent growths
   (the counter's overflows) in a run of N steps, with the step and the
   side that grew.   usage: ovf MACHINE N K */
#include <stdio.h>
#include <stdlib.h>
#define SZ (1<<22)
static unsigned char tape[SZ];
static char buf[64][8192]; static long bt[64]; static char bs[64];
int main(int argc,char**argv){
  const char*m=argv[1]; long N=atol(argv[2]); int K=atoi(argv[3]);
  int W[4][2],M[4][2],Q[4][2];
  for(int s=0;s<4;s++)for(int b=0;b<2;b++){const char*t=m+s*7+b*3;
    if(t[0]=='-'){W[s][b]=-1;continue;} W[s][b]=t[0]-'0';M[s][b]=t[1]=='R'?1:-1;Q[s][b]=t[2]-'A';}
  long p=SZ/2,lo=p,hi=p; int q=0, n=0;
  for(long t=0;t<N;t++){
    int b=tape[p]; if(W[q][b]<0){printf("HALT %ld\n",t);return 0;}
    tape[p]=W[q][b]; p+=M[q][b]; q=Q[q][b];
    if(p<lo||p>hi){ char sd = p<lo?'L':'R'; if(p<lo)lo=p; else hi=p;
      if(hi-lo<8000){ int i=n%64,k=0; bt[i]=t; bs[i]=sd;
        for(long x=lo;x<=hi;x++){ if(x==p) buf[i][k++]="ABCD"[q]; buf[i][k++]='0'+tape[x]; }
        buf[i][k]=0; n++; } }
    if(p<2||p>SZ-3){printf("OUT\n");return 0;}
  }
  for(int j=(n>K?n-K:0);j<n;j++) printf("%ld %c %s\n",bt[j%64],bs[j%64],buf[j%64]);
  return 0;
}
