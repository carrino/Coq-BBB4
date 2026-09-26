/* sp_burst: every fire of ONE instruction of a (4,2) machine (UNTRUSTED
   measurement for the class-SP characterisation, SCOPING_INSTR.md 7.4.SP).

     cc -O2 -o sp_burst tools/closeouttr/sp_burst.c
     sp_burst SPEC INSTR BUDGET MAXPRINT

   INSTR is 0..7 (A0, A1, B0, ..., D1).  One line per fire:
     F step head lo hi [tape]
   head/lo/hi are cell indices relative to the start cell (lo/hi: the
   visited extent so far); the tape lo..hi, head cell as [<state><sym>], is
   printed when the extent is under MAXPRINT cells.  Then
     END budget lo hi       (or HALT step / EDGE step) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s SPEC INSTR BUDGET MAXPRINT\n", argv[0]);
        return 2;
    }
    const char *m = argv[1];
    int tg = atoi(argv[2]);
    uint64_t lim = strtoull(argv[3], 0, 10);
    int maxp = atoi(argv[4]);
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
    size_t N = 1u << 26;
    uint8_t *tape = calloc(N, 1);
    int64_t c0 = (int64_t)N / 2, pos = c0, lo = pos, hi = pos;
    int st = 0; uint64_t step = 0;
    while (step < lim) {
        uint8_t s = tape[pos];
        int t = st * 2 + s;
        if (nx[st][s] < 0) { printf("HALT %llu\n", (unsigned long long)step); return 0; }
        if (t == tg) {
            printf("F %llu %lld %lld %lld ", (unsigned long long)step,
                   (long long)(pos - c0), (long long)(lo - c0), (long long)(hi - c0));
            if (hi - lo < maxp)
                for (int64_t i = lo; i <= hi; i++) {
                    if (i == pos) printf("[%c%d]", 'A' + st, tape[i]);
                    else putchar('0' + tape[i]);
                }
            putchar('\n');
        }
        tape[pos] = wr[st][s]; pos += mv[st][s]; st = nx[st][s]; step++;
        if (pos < lo) lo = pos;
        if (pos > hi) hi = pos;
        if (pos < 8 || pos >= (int64_t)N - 8) { printf("EDGE %llu\n", (unsigned long long)step); return 0; }
    }
    printf("END %llu %lld %lld\n", (unsigned long long)step, (long long)(lo - c0), (long long)(hi - c0));
    return 0;
}
