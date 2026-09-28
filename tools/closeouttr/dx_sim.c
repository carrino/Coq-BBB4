/* dx_sim: the tape-growth profile of one (4,2) machine (UNTRUSTED
   measurement for the class-DN characterisation, SCOPING_INSTR.md 7.4.DX).

     cc -O2 -o dx_sim tools/closeouttr/dx_sim.c
     dx_sim SPEC BUDGET

   Output lines:
     X step lo hi             the visited extent at every power of 10
     R side step              every new leftmost (side L) / rightmost (R)
                              cell, at most the last 4000 of each side
     W n                      full sweeps: head runs from one extent edge to
                              the other (a bouncer makes one per record)
     T tape                   the visited tape at the end, head cell as
                              [<state><sym>], when under 65536 cells
     END budget lo hi         (or HALT step / EDGE step) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define KEEP 4000

int main(int argc, char **argv) {
    if (argc < 3) {
        fprintf(stderr, "usage: %s SPEC BUDGET\n", argv[0]);
        return 2;
    }
    const char *m = argv[1];
    uint64_t lim = strtoull(argv[2], 0, 10);
    uint8_t wr[4][2]; int8_t mv[4][2]; int8_t nx[4][2];
    {
        int qi = 0; const char *p = m;
        while (*p && qi < 4) {
            for (int s = 0; s < 2; s++) {
                if (p[0] == '-') { nx[qi][s] = -1; wr[qi][s] = 0; mv[qi][s] = 1; }
                else { wr[qi][s] = p[0] - '0'; mv[qi][s] = p[1] == 'R' ? 1 : -1; nx[qi][s] = p[2] - 'A'; }
                p += 3;
            }
            if (*p == '_') p++;
            qi++;
        }
    }
    size_t N = 1u << 27;
    uint8_t *tape = calloc(N, 1);
    int64_t c0 = (int64_t)N / 2, pos = c0, lo = pos, hi = pos;
    static uint64_t rl[KEEP], rr[KEEP];
    uint64_t nl = 0, nr = 0, sweeps = 0;
    int lastedge = 0;   /* -1 left edge, +1 right edge */
    int st = 0; uint64_t step = 0, next = 10;
    const char *how = "END";
    while (step < lim) {
        uint8_t s = tape[pos];
        if (nx[st][s] < 0) { how = "HALT"; break; }
        tape[pos] = wr[st][s]; pos += mv[st][s]; st = nx[st][s]; step++;
        if (pos < lo) { lo = pos; rl[nl++ % KEEP] = step; }
        if (pos > hi) { hi = pos; rr[nr++ % KEEP] = step; }
        if (pos == lo && lastedge != -1) { if (lastedge) sweeps++; lastedge = -1; }
        if (pos == hi && lastedge != 1) { if (lastedge) sweeps++; lastedge = 1; }
        if (step == next) {
            printf("X %llu %lld %lld\n", (unsigned long long)step,
                   (long long)(lo - c0), (long long)(hi - c0));
            next *= 10;
        }
        if (pos < 8 || pos >= (int64_t)N - 8) { how = "EDGE"; break; }
    }
    for (uint64_t k = nl > KEEP ? nl - KEEP : 0; k < nl; k++)
        printf("R L %llu\n", (unsigned long long)rl[k % KEEP]);
    for (uint64_t k = nr > KEEP ? nr - KEEP : 0; k < nr; k++)
        printf("R R %llu\n", (unsigned long long)rr[k % KEEP]);
    printf("W %llu\n", (unsigned long long)sweeps);
    if (hi - lo < 65536) {
        printf("T ");
        for (int64_t i = lo; i <= hi; i++) {
            if (i == pos) printf("[%c%d]", 'A' + st, tape[i]);
            else putchar('0' + tape[i]);
        }
        putchar('\n');
    }
    printf("%s %llu %lld %lld\n", how, (unsigned long long)step,
           (long long)(lo - c0), (long long)(hi - c0));
    return 0;
}
