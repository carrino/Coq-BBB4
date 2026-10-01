/* asnap: far-end-deduplicated anchor snapshots (UNTRUSTED; SCOPING_INSTR.md §7.4.MP).
     cc -O2 -o asnap asnap.c
     asnap SPEC SIDE T0 T1 W
   Runs the machine to T1 steps.  From T0 on, at each SIDE anchor (the head
   steps beyond every 1 on SIDE, L or R), prints the anchor in lsnap's format
     A SIDE t q h pos n RLE
   but only when the W cells at the FAR end (the other end of the marked
   tape) differ from those of the last anchor printed.  The far end of a
   block-list counter changes only when a carry reaches it, so this keeps
   every far-end form of a long run at a few hundred lines. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int wr[4][2], mv[4][2], nx[4][2];
static uint8_t *t; static long lo, hi;
static void dump(char side, uint64_t s, int q, long pos) {
    printf("A %c %llu %d %d %ld %ld", side, (unsigned long long)s, q, t[pos], pos - lo, hi - lo + 1);
    long j = lo;
    while (j <= hi) { long k2 = j; while (k2 <= hi && t[k2] == t[j]) k2++; printf(" %d*%ld", t[j], k2 - j); j = k2; }
    putchar('\n');
}
int main(int argc, char **argv) {
    const char *p = argv[1]; char side = argv[2][0];
    uint64_t T0 = strtoull(argv[3], 0, 10), T1 = strtoull(argv[4], 0, 10); int W = atoi(argv[5]);
    for (int q = 0; q < 4; q++) { for (int s = 0; s < 2; s++) {
        if (p[0] == '-') { nx[q][s] = -1; wr[q][s] = 0; mv[q][s] = 1; }
        else { wr[q][s] = p[0] - '0'; mv[q][s] = p[1] == 'R' ? 1 : -1; nx[q][s] = p[2] - 'A'; }
        p += 3; } if (*p == '_') p++; }
    size_t N = (size_t)1 << 28; t = calloc(N, 1); long pos = N / 2; lo = hi = pos; int q = 0;
    long first1 = -1, last1 = -1; int in = 0;
    char *last = calloc(W + 1, 1), *cur = calloc(W + 1, 1);
    for (uint64_t s = 0; s < T1; s++) {
        if (s >= T0 && first1 >= 0) {
            int an = side == 'L' ? pos < first1 : pos > last1;
            if (an && !in) {
                int k = 0;
                if (side == 'L') for (long j = last1; j > last1 - W && j >= lo; j--) cur[k++] = '0' + t[j];
                else for (long j = first1; j < first1 + W && j <= hi; j++) cur[k++] = '0' + t[j];
                cur[k] = 0;
                if (strcmp(cur, last)) { dump(side, s, q, pos); strcpy(last, cur); }
            }
            in = an;
        }
        int a = t[pos];
        if (nx[q][a] < 0) break;
        if (wr[q][a] && !a) {
            if (first1 < 0 || pos < first1) first1 = pos;
            if (last1 < 0 || pos > last1) last1 = pos;
        } else if (!wr[q][a] && a) {
            t[pos] = 0;
            if (pos == first1) { while (first1 <= last1 && !t[first1]) first1++; if (first1 > last1) first1 = last1 = -1; }
            if (pos == last1 && last1 >= 0) { while (last1 >= first1 && !t[last1]) last1--; }
        }
        t[pos] = wr[q][a]; pos += mv[q][a]; q = nx[q][a];
        if (pos < lo) lo = pos; if (pos > hi) hi = pos;
        if (pos <= 1 || pos >= (long)N - 2) break;
    }
    return 0;
}
