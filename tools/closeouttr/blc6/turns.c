/* turns: per-round turn snapshots for BLC6's left-language learner (UNTRUSTED).
     cc -O2 -o turns turns.c
     turns SPEC T0 T1 [MINX]
   A round is the time between two left-anchor entries (the head steps to the
   left of every 1).  Pass 1 finds, per round, the last step at which the head
   is at the round's rightmost cell; pass 2 prints
     A L t q h pos  RLE   at every left-anchor entry from T0 on,
     S - t q h pos  RLE   at each round's turn step, when the round's
                          excursion is at least MINX cells,
   in learn4's lsnap format, so the turn tapes hold every element the
   round's carry passed, in its left form. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int wr[4][2], mv[4][2], nx[4][2];
static uint8_t *t; static long lo, hi;
static void dump(char k, char side, uint64_t s, int q, long pos) {
    printf("%c %c %llu %d %d %ld %ld", k, side, (unsigned long long)s, q, t[pos], pos - lo, hi - lo + 1);
    long j = lo;
    while (j <= hi) { long k2 = j; while (k2 <= hi && t[k2] == t[j]) k2++; printf(" %d*%ld", t[j], k2 - j); j = k2; }
    putchar('\n');
}
static uint64_t *turn; static size_t nturn, capturn;
static void run(const char *spec, uint64_t T0, uint64_t T1, long minx, int pass) {
    const char *p = spec;
    for (int q = 0; q < 4; q++) { for (int s = 0; s < 2; s++) {
        if (p[0] == '-') { nx[q][s] = -1; wr[q][s] = 0; mv[q][s] = 1; }
        else { wr[q][s] = p[0] - '0'; mv[q][s] = p[1] == 'R' ? 1 : -1; nx[q][s] = p[2] - 'A'; }
        p += 3; } if (*p == '_') p++; }
    size_t N = 1 << 26; memset(t, 0, N); long pos = N / 2; lo = hi = pos; int q = 0;
    int inL = 0; long first1 = -1, last1 = -1;
    long rmax = -1, rstart = 0; uint64_t rstep = 0; size_t ti = 0;
    for (uint64_t s = 0; s < T1; s++) {
        int aL = first1 >= 0 && pos < first1;
        if (aL && !inL) {
            if (pass == 1 && rmax >= 0 && rmax - rstart >= minx) {
                if (nturn == capturn) { capturn = capturn ? 2 * capturn : 4096; turn = realloc(turn, capturn * sizeof *turn); }
                turn[nturn++] = rstep;
            }
            if (pass == 2 && s >= T0) dump('A', 'L', s, q, pos);
            rmax = pos; rstart = pos; rstep = s;
        }
        inL = aL;
        if (pos >= rmax) { rmax = pos; rstep = s; }
        if (pass == 2) {
            while (ti < nturn && turn[ti] < s) ti++;
            if (ti < nturn && turn[ti] == s && s >= T0) dump('S', '-', s, q, pos);
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
        if (pos <= 0 || pos >= (long)N - 1) break;
    }
}
int main(int argc, char **argv) {
    uint64_t T0 = strtoull(argv[2], 0, 10), T1 = strtoull(argv[3], 0, 10);
    long minx = argc > 4 ? atol(argv[4]) : 0;
    t = malloc((size_t)1 << 26);
    run(argv[1], T0, T1, minx, 1);
    run(argv[1], T0, T1, minx, 2);
    return 0;
}
