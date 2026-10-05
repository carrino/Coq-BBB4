/* refire: an UNTRUSTED prediction check for BBB_tr(4) = 32,779,478.

   The Coq theorem bbbt4_bound says every eventually-quiet instruction of
   every (4,2) machine fires for the last time before configuration index
   B = 32,779,478.  So any instruction seen firing at an index >= B must
   fire infinitely often -- in particular it must fire again after any
   horizon.  This tool tests that prediction on concrete runs.

   stdin: one machine per line (bbchallenge text, --- = undefined).
   argv: H (the horizon, e.g. 10000000000), CAP (the step cap, > H).

   Per machine it runs to H, recording each instruction's fire count and
   last fire (these re-derive the harness's per-transition columns), then
   keeps running until every instruction whose last fire before H is >= B
   has fired again, or CAP.  Output, one line per machine:

     <machine> H=<H> T<q><a>:<count>:<last>[:<next fire after H>|:-] ... <verdict>

   verdict OK (every such instruction fired again), OPEN (CAP reached
   first; not a contradiction, the run is just too short), HALT or EDGE
   (tape bound; enlarge N). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define B_SCORE 32779478ULL

static int parse(const char *m, uint8_t wr[4][2], int8_t mv[4][2], int8_t nx[4][2]) {
    const char *p = m;
    for (int q = 0; q < 4; q++) {
        for (int s = 0; s < 2; s++) {
            if (!p[0] || !p[1] || !p[2]) return -1;
            if (p[0] == '-') { nx[q][s] = -1; wr[q][s] = 0; mv[q][s] = 1; }
            else { wr[q][s] = p[0] - '0'; mv[q][s] = (p[1] == 'R') ? 1 : -1; nx[q][s] = p[2] - 'A'; }
            p += 3;
        }
        if (*p == '_') p++;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: refire H CAP < machines\n"); return 2; }
    uint64_t H = strtoull(argv[1], 0, 10), CAP = strtoull(argv[2], 0, 10);
    size_t N = (size_t)1 << 28;                 /* 256M cells */
    uint8_t *tape = malloc(N);
    if (!tape) { perror("malloc"); return 2; }
    char line[256];
    while (fgets(line, sizeof line, stdin)) {
        line[strcspn(line, "\r\n")] = 0;
        if (!line[0]) continue;
        uint8_t wr[4][2]; int8_t mv[4][2], nx[4][2];
        if (parse(line, wr, mv, nx)) { printf("%s PARSE\n", line); continue; }
        memset(tape, 0, N);
        int64_t pos = (int64_t)N / 2;
        int st = 0;
        uint64_t step = 0, cnt[8] = {0}, last[8] = {0}, next[8] = {0};
        int need = 0, verdict = 0;               /* 0 ok/open, 1 halt, 2 edge */
        uint8_t want[8] = {0};
        for (;;) {
            if (step == H) {                     /* the horizon: fix the obligations */
                for (int t = 0; t < 8; t++)
                    if (cnt[t] && last[t] >= B_SCORE) { want[t] = 1; need++; }
            }
            if (step >= H && need == 0) break;
            if (step >= CAP) break;
            uint8_t s = tape[pos];
            int t = st * 2 + s;
            if (nx[st][s] < 0) { verdict = 1; break; }
            if (step < H) { cnt[t]++; last[t] = step; }
            else if (want[t] && !next[t]) { next[t] = step; need--; }
            tape[pos] = wr[st][s]; pos += mv[st][s]; st = nx[st][s]; step++;
            if (pos < 8 || pos >= (int64_t)N - 8) { verdict = 2; break; }
        }
        printf("%s H=%llu", line, (unsigned long long)H);
        for (int t = 0; t < 8; t++) {
            printf(" T%c%d:%llu:%llu", 'A' + t / 2, t % 2,
                   (unsigned long long)cnt[t], (unsigned long long)last[t]);
            if (want[t]) {
                if (next[t]) printf(":%llu", (unsigned long long)next[t]);
                else printf(":-");
            }
        }
        if (verdict == 1) printf(" HALT %llu\n", (unsigned long long)step);
        else if (verdict == 2) printf(" EDGE %llu\n", (unsigned long long)step);
        else printf(" %s %llu\n", need ? "OPEN" : "OK", (unsigned long long)step);
        fflush(stdout);
    }
    return 0;
}
