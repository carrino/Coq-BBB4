/* lsnap: tape snapshots for the BLC3 language learner (UNTRUSTED).
     cc -O2 -o lsnap lsnap.c
     lsnap SPEC T0 T1 S [K]
   Runs the machine to T1 steps.  From T0 on it prints
     A L t q h pos  RLE   when the head steps to the left of every 1 (left anchor),
     A R t q h pos  RLE   ... to the right of every 1 (right anchor),
     S - t q h pos  RLE   every S steps, when K runs of 1 lie left of the head
                          (and one right of it),
   where RLE is "lo sym*len sym*len ..." of the visited cells and pos the
   head's cell. One line per anchor episode (its first step). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int wr[4][2], mv[4][2], nx[4][2];
static uint8_t *t; static long lo, hi;
static void dump(char k, char side, uint64_t s, int q, long pos) {
    printf("%c %c %llu %d %d %ld %ld", k, side, (unsigned long long)s, q, t[pos], pos - lo, hi - lo + 1);
    long j = lo;
    while (j <= hi) { long k2 = j; while (k2 <= hi && t[k2] == t[j]) k2++; printf(" %d*%ld", t[j], k2 - j); j = k2; }
    putchar('\n');
}
int main(int argc, char **argv) {
    int K = argc > 5 ? atoi(argv[5]) : 0;
    const char *p = argv[1]; uint64_t T0 = strtoull(argv[2], 0, 10), T1 = strtoull(argv[3], 0, 10), S = strtoull(argv[4], 0, 10);
    for (int q = 0; q < 4; q++) { for (int s = 0; s < 2; s++) {
        if (p[0] == '-') { nx[q][s] = -1; wr[q][s] = 0; mv[q][s] = 1; }
        else { wr[q][s] = p[0] - '0'; mv[q][s] = p[1] == 'R' ? 1 : -1; nx[q][s] = p[2] - 'A'; }
        p += 3; } if (*p == '_') p++; }
    size_t N = 1 << 26; t = calloc(N, 1); long pos = N / 2; lo = hi = pos; int q = 0;
    int inL = 0, inR = 0;
    for (uint64_t s = 0; s < T1; s++) {
        if (s >= T0) {
            int aL = 1; for (long j = pos; j >= lo && j <= hi; j++) { if (j == pos) continue; if (t[j]) break; if (j == hi) { aL = 0; break; } }
            /* aL: every cell from lo to pos is 0 and some 1 lies right of pos */
            aL = 1; for (long j = lo; j <= pos; j++) if (t[j]) { aL = 0; break; }
            if (aL) { int any = 0; for (long j = pos + 1; j <= hi; j++) if (t[j]) { any = 1; break; } aL = any; }
            int aR = 1; for (long j = hi; j >= pos; j--) if (t[j]) { aR = 0; break; }
            if (aR) { int any = 0; for (long j = pos - 1; j >= lo; j--) if (t[j]) { any = 1; break; } aR = any; }
            if (aL && !inL) dump('A', 'L', s, q, pos);
            if (aR && !inR) dump('A', 'R', s, q, pos);
            inL = aL; inR = aR;
            if (S && (s - T0) % S == 0) {
                /* only when at least K runs of 1 lie on each side of the head
                   (left tails are what these samples are for) */
                int nl = 0, nr = 0;
                for (long j = lo; j < pos; j++) if (t[j] && (j == lo || !t[j - 1])) nl++;
                for (long j = pos + 1; j <= hi; j++) if (t[j] && !t[j - 1]) nr++;
                if (nl >= K && nr >= 1) dump('S', '-', s, q, pos);
            }
        }
        int a = t[pos];
        if (nx[q][a] < 0) break;
        t[pos] = wr[q][a]; pos += mv[q][a]; q = nx[q][a];
        if (pos < lo) lo = pos; if (pos > hi) hi = pos;
        if (pos <= 1 || pos >= (long)N - 2) break;
    }
    return 0;
}
