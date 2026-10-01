#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
/* farend SPEC T1 W SIDE : at each anchor (head steps beyond the outermost 1 on SIDE), print t and the W cells at the OTHER end (outermost first-from-far) */
int wr[4][2], mv[4][2], nx[4][2];
int main(int argc,char**argv){
  const char*p=argv[1]; uint64_t T1=strtoull(argv[2],0,10); int W=atoi(argv[3]); char side=argv[4][0];
  for(int q=0;q<4;q++){for(int s=0;s<2;s++){wr[q][s]=p[0]-'0';mv[q][s]=p[1]=='R'?1:-1;nx[q][s]=p[2]-'A';p+=3;} if(*p=='_')p++;}
  size_t N=1<<28; uint8_t*t=calloc(N,1); long pos=N/2,lo=pos,hi=pos; int q=0; int in=0;
  char*buf=malloc(W+2);
  for(uint64_t s=0;s<T1;s++){
    int a=t[pos]; t[pos]=wr[q][a]; pos+=mv[q][a]; q=nx[q][a];
    if(pos<lo)lo=pos; if(pos>hi)hi=pos;
    int an = side=='L' ? (pos==lo) : (pos==hi);
    if(an&&!in){
      /* far end: strip blanks */
      long e = side=='L'? hi:lo; int k=0;
      if(side=='L'){ while(e>lo&&!t[e]) e--; for(long j=e;j>e-W&&j>=lo;j--) buf[k++]='0'+t[j]; }
      else { while(e<hi&&!t[e]) e++; for(long j=e;j<e+W&&j<=hi;j++) buf[k++]='0'+t[j]; }
      buf[k]=0; printf("%llu %d %ld %s\n",(unsigned long long)s,q,hi-lo,buf);
    }
    in=an;
  }
}
