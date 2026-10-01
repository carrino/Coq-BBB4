// usage: sim SPEC t1 t2 ... ; prints "t state headpos tape" lines (tape from min to max visited)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<25)
static unsigned char tape[N];
int main(int argc,char**argv){
  const char*s=argv[1]; int wr[8],mv[8],nx[8];
  for(int q=0;q<4;q++)for(int b=0;b<2;b++){const char*p=s+q*7+b*3;int i=q*2+b;
    if(p[2]=='-'){wr[i]=-1;continue;} wr[i]=p[0]-'0'; mv[i]=p[1]=='R'?1:-1; nx[i]=p[2]-'A';}
  long h=N/2,lo=h,hi=h; int q=0; long long t=0;
  for(int a=2;a<argc;a++){ long long T=atoll(argv[a]);
    while(t<T){int i=q*2+tape[h]; if(wr[i]<0){printf("HALT %lld\n",t);return 0;}
      tape[h]=wr[i]; h+=mv[i]; q=nx[i]; t++; if(h<lo)lo=h; if(h>hi)hi=h;
      if(h<=0||h>=N-1){printf("EDGE %lld\n",t);return 0;}}
    printf("%lld %c %ld ",t,'A'+q,h-lo); for(long x=lo;x<=hi;x++)putchar('0'+tape[x]); putchar('\n');}
}
