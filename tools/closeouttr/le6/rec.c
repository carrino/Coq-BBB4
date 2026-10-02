/* LE6 survey probe (untrusted): every time the tape extent grows, print
     R t side lo hi
   and, for the last K records of the run, the tape lo..hi with the head
   marked by its state letter:
     T t side <cells>
   usage: rec MACHINE STEPS K */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define SZ (1<<25)
static unsigned char tape[SZ];
typedef struct { long t; int side; long lo, hi; long p; int q; } rec_t;
#define MAXR 200000
static rec_t R[MAXR];
int main(int argc, char **argv) {
  const char *m = argv[1]; long N = atol(argv[2]); int K = atoi(argv[3]);
  int W[4][2], M[4][2], Q[4][2];
  for (int s = 0; s < 4; s++) for (int b = 0; b < 2; b++) {
    const char *t = m + s * 7 + b * 3;
    if (t[0] == '-') { W[s][b] = -1; continue; }
    W[s][b] = t[0] - '0'; M[s][b] = t[1] == 'R' ? 1 : -1; Q[s][b] = t[2] - 'A';
  }
  long p = SZ / 2, lo = p, hi = p; int q = 0; long nr = 0;
  /* snapshot ring for the last K records */
  char **snap = malloc(sizeof(char *) * K); long *st = malloc(sizeof(long) * K);
  int *ss = malloc(sizeof(int) * K);
  for (int i = 0; i < K; i++) snap[i] = NULL;
  long t;
  for (t = 0; t < N; t++) {
    int b = tape[p];
    if (W[q][b] < 0) { printf("HALT %ld\n", t); break; }
    tape[p] = W[q][b]; p += M[q][b]; q = Q[q][b];
    int side = -1;
    if (p < lo) { lo = p; side = 0; }
    if (p > hi) { hi = p; side = 1; }
    if (side >= 0) {
      if (nr < MAXR) { R[nr].t = t + 1; R[nr].side = side; R[nr].lo = lo; R[nr].hi = hi; }
      if (hi - lo < 20000) {
        int i = nr % K;
        free(snap[i]); snap[i] = malloc(hi - lo + 3);
        int k = 0;
        for (long x = lo; x <= hi; x++) { if (x == p) snap[i][k++] = "ABCD"[q]; snap[i][k++] = '0' + tape[x]; }
        snap[i][k] = 0; st[i] = t + 1; ss[i] = side;
      }
      nr++;
    }
    if (p < 2 || p > SZ - 3) { printf("OUT %ld\n", t); break; }
  }
  printf("N %ld %ld\n", t, nr);
  long from = nr > 3000 ? nr - 3000 : 0;
  for (long i = from; i < nr && i < MAXR; i++) printf("R %ld %d %ld\n", R[i].t, R[i].side, R[i].hi - R[i].lo + 1);
  for (long j = (nr > K ? nr - K : 0); j < nr; j++) { int i = j % K; if (snap[i]) printf("T %ld %d %s\n", st[i], ss[i], snap[i]); }
  return 0;
}
