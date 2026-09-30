/* bl_sim: fire times of the rare instructions, and tape snapshots (UNTRUSTED
   measurement for tools/closeouttr/bl/classify.py, SCOPING_INSTR.md 7.4.BL).

     cc -O2 -o /tmp/bl_sim tools/closeouttr/bl/bl_sim.c
     bl_sim SPEC LIMIT [T1 T2 ...]

   Output: one line per instruction that fires fewer than 64 times,
   "<instr> t1 t2 ...", then per requested step Ti a line "T Ti <tape>"
   (the visited cells, head not marked). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int wr[4][2], mv[4][2], nx[4][2];
int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s SPEC LIMIT [T...]\n", argv[0]); return 2; }
    const char *p = argv[1];
    uint64_t lim = strtoull(argv[2], 0, 10);
    for (int q = 0; q < 4; q++) {
        for (int s = 0; s < 2; s++) {
            if (p[0] == '-') { nx[q][s] = -1; wr[q][s] = 0; mv[q][s] = 1; }
            else { wr[q][s] = p[0] - '0'; mv[q][s] = p[1] == 'R' ? 1 : -1; nx[q][s] = p[2] - 'A'; }
            p += 3;
        }
        if (*p == '_') p++;
    }
    int nt = argc - 3; uint64_t *ts = malloc(sizeof(uint64_t) * (nt + 1));
    for (int i = 0; i < nt; i++) ts[i] = strtoull(argv[3 + i], 0, 10);
    size_t N = 1 << 23; uint8_t *t = calloc(N, 1); long pos = N / 2, lo = pos, hi = pos; int q = 0;
    uint64_t cnt[8] = {0}; static uint64_t ft[8][64];
    for (uint64_t s = 0; s < lim; s++) {
        for (int i = 0; i < nt; i++) if (ts[i] == s) {
            printf("T %llu ", (unsigned long long)s);
            for (long j = lo; j <= hi; j++) putchar('0' + t[j]);
            putchar('\n');
        }
        int a = t[pos], i = q * 2 + a;
        if (nx[q][a] < 0) break;
        if (cnt[i] < 64) ft[i][cnt[i]] = s;
        cnt[i]++;
        t[pos] = wr[q][a]; pos += mv[q][a]; q = nx[q][a];
        if (pos < lo) lo = pos;
        if (pos > hi) hi = pos;
        if (pos <= 0 || pos >= (long)N - 1) break;
    }
    for (int i = 0; i < 8; i++) if (cnt[i] > 0 && cnt[i] < 64) {
        printf("%c%d", 'A' + i / 2, i % 2);
        for (uint64_t k = 0; k < cnt[i]; k++) printf(" %llu", (unsigned long long)ft[i][k]);
        printf("\n");
    }
    return 0;
}
