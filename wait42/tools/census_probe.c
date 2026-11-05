/* Bounded UNTRUSTED waiting-census candidate survey. No proof credit.
 * Reuse the frozen four-state TNF simulator and finite n-gram machinery.
 * Build: gcc -O2 -std=c11 wait42/tools/census_probe.c -o wait42/build/census_probe
 * Every candidate needs exact replay through BBBWait42.Periodic / Ranked.
 */
#define _POSIX_C_SOURCE 200809L
#define main legacy_census_ladder_main
#include "../../tools/census_ladder.c"
#undef main
#include "ngram_tail.inc"
#include <errno.h>
#include <inttypes.h>
#include <limits.h>

typedef struct {
  uint64_t visited, expanded, generated, cycle, translated, ngram, unknown;
  uint64_t edge, full, ledger, ng_rung[8];
} ProbeCounts;

static int probe_number(const char *s, uint64_t *value) {
  char *end;
  if (s[0] < '0' || s[0] > '9') return 0;
  errno = 0;
  unsigned long long v = strtoull(s, &end, 10);
  if (errno || *end) return 0;
  *value = (uint64_t)v;
  return 1;
}

static int probe_rungs(const char *spec, int *ns, int *ts, int *count, int gas) {
  *count = 0;
  if (!strcmp(spec, "none")) return 1;
  const char *p = spec;
  while (*p) {
    if (*count == 8) return 0;
    char *end;
    errno = 0;
    long n = strtol(p, &end, 10);
    if (errno || end == p || *end != ':' || n < 1 || n > NGMAXN) return 0;
    p = end + 1;
    errno = 0;
    long t = strtol(p, &end, 10);
    if (errno || end == p || (*end && *end != ',') || t < 0 || t > gas) return 0;
    ns[*count] = (int)n; ts[*count] = (int)t; ++*count;
    if (!*end) return 1;
    p = end + 1;
    if (!*p) return 0;
  }
  return 0;
}

static int probe_full(const Node *nd) {
  for (int i = 0; i < 8; ++i) if (nd->sl[i] == UNDEF) return 0;
  return 1;
}

/* Replay only the short candidate lap to record its actual displacement
   and excursion width. This is metadata, not a periodicity proof. */
static const char *probe_geometry(const Node *nd, int anchor, int period, int *width) {
  wipe_tape();
  int head = TAPE/2, q = 0, start = head, low = head, high = head;
  for (int i = 0; i < anchor+period; ++i) {
    if (i == anchor) start = low = high = head;
    uint8_t tr = SLOT(nd->sl, q, tape_[head]);
    if (tr == UNDEF) { wipe_tape(); *width = -1; return "unknown"; }
    tape_[head] = (int8_t)tr_wr(tr); head += tr_dir(tr) ? 1 : -1; q = tr_next(tr);
    if (head < 8 || head > TAPE-8) { wipe_tape(); *width = -1; return "unknown"; }
    if (i >= anchor) { if (head < low) low = head; if (head > high) high = head; }
  }
  wipe_tape();
  *width = head >= start ? start-low : high-start;
  return head > start ? "right" : head < start ? "left" : "stationary";
}

static FILE *probe_open(const char *prefix, const char *suffix) {
  char path[4096];
  if (snprintf(path, sizeof path, "%s.%s", prefix, suffix) >= (int)sizeof path) {
    fprintf(stderr, "output path too long\n"); return NULL;
  }
  FILE *f = fopen(path, "w");
  if (!f) perror(path);
  return f;
}

static void probe_leaf(FILE *ledger, ProbeCounts *counts, const Node *nd,
    const char *kind, int halt_slot, int anchor, int period, const char *side,
    int n, int t, int contexts, int bound, int edge) {
  char text[40]; tm_text(nd->sl, text);
  int width = -1;
  if (period > 0) side = probe_geometry(nd, anchor, period, &width);
  fprintf(ledger, "%" PRIu64 "\t%s\t%s\t%d\t%d\t%d\t%d\t%s\t%d\t%d\t%d\t%d\t%d\t%d\t%d\tuntrusted\n",
    counts->ledger++, kind, text, nd->ptr, halt_slot, anchor, period, side,
    n, t, contexts, bound, width, edge, probe_full(nd));
}

static void probe_family(FILE *out, const char *kind, const Node *nd) {
  char text[40]; tm_text(nd->sl, text);
  fprintf(out, "%s\t%s\t%d\n", kind, text, nd->ptr);
}

static void probe_summary(FILE *out, const ProbeCounts *c, uint64_t maximum,
    int gas, const char *root, int seeds, int virtual_root, size_t pending,
    const int *ns, const int *ts, int nrungs) {
  fprintf(out,
    "{\n  \"schema_version\": 1,\n  \"trust\": \"untrusted candidate survey\",\n"
    "  \"coverage_proved\": false,\n  \"kernel_credit\": 0,\n"
    "  \"legacy_holdout_lookup_enabled\": false,\n"
    "  \"ngram_tier\": \"tail_ngram\",\n"
    "  \"ngram_checker_source\": \"wait42/tools/ngram_tail.inc\",\n"
    "  \"cycle_hash_candidates_require_exact_replay\": true,\n"
    "  \"root\": \"%s\",\n  \"max_nodes\": %" PRIu64 ",\n  \"gas\": %d,\n"
    "  \"seed_nodes\": %d,\n  \"virtual_root_expanded\": %d,\n"
    "  \"nodes_visited\": %" PRIu64 ",\n  \"expanded_popped_nodes\": %" PRIu64 ",\n"
    "  \"expanded_nodes\": %" PRIu64 ",\n  \"halted_actual_completions\": %" PRIu64 ",\n"
    "  \"generated_children\": %" PRIu64 ",\n  \"cycle_candidates\": %" PRIu64 ",\n"
    "  \"translated_cycle_candidates\": %" PRIu64 ",\n  \"ngram_candidates\": %" PRIu64 ",\n"
    "  \"unknown\": %" PRIu64 ",\n  \"pending\": %zu,\n"
    "  \"edge_events\": %" PRIu64 ",\n  \"full_nodes_visited\": %" PRIu64 ",\n"
    "  \"ledger_rows\": %" PRIu64 ",\n  \"budget_reached\": %s,\n"
    "  \"tree_exhausted_untrusted\": %s,\n"
    "  \"stack_accounting_ok\": %s,\n"
    "  \"halt_family_semantics\": \"reached halt_slot must remain undefined; other undefined slots arbitrary\",\n"
    "  \"halted_completion_count_is_unweighted_family_count\": true,\n"
    "  \"candidate_bound_condition\": \"cutoff B >= anchor; exact Coq replay still required\",\n"
    "  \"family_semantics\": \"unknown and pending rows represent all completions, with TNF ptr retained\",\n"
    "  \"rungs\": [",
    root, maximum, gas, seeds, virtual_root, c->visited, c->expanded,
    c->expanded + virtual_root, c->expanded + virtual_root, c->generated,
    c->cycle, c->translated, c->ngram, c->unknown, pending, c->edge, c->full,
    c->ledger, c->visited == maximum ? "true" : "false", pending ? "false" : "true",
    (uint64_t)seeds + c->generated == c->visited + pending ? "true" : "false");
  for (int i = 0; i < nrungs; ++i)
    fprintf(out, "%s{\"n\":%d,\"t\":%d,\"candidates\":%" PRIu64 "}",
      i ? "," : "", ns[i], ts[i], c->ng_rung[i]);
  fprintf(out, "]\n}\n");
}

int main(int argc, char **argv) {
  uint64_t maximum = 0, gas_number = 0;
  int have_maximum = 0, have_gas = 0;
  const char *root = "all", *prefix = "wait42/build/census-probe", *rungs = "none";
  for (int i = 1; i < argc; ++i) {
    if (!strcmp(argv[i], "--help")) {
      puts("Usage: census_probe --max-nodes N --gas G [--root all|0RA|1RA|0RB|1RB] [--rungs none|n:t,...] [--output PREFIX]");
      return 0;
    }
    if (i+1 >= argc) { fprintf(stderr, "missing option value\n"); return 2; }
    const char *option = argv[i], *value = argv[++i];
    if (!strcmp(option, "--max-nodes")) have_maximum = probe_number(value, &maximum);
    else if (!strcmp(option, "--gas")) have_gas = probe_number(value, &gas_number);
    else if (!strcmp(option, "--root")) root = value;
    else if (!strcmp(option, "--rungs")) rungs = value;
    else if (!strcmp(option, "--output")) prefix = value;
    else { fprintf(stderr, "unknown option: %s\n", option); return 2; }
  }
  if (!have_maximum || !have_gas || gas_number > MAXGAS) {
    fprintf(stderr, "explicit nonnegative --max-nodes and --gas (<=%d) required\n", MAXGAS); return 2;
  }
  int gas = (int)gas_number, ns[8], ts[8], nrungs;
  if (!probe_rungs(rungs, ns, ts, &nrungs, gas)) {
    fprintf(stderr, "invalid rungs (at most 8; 1<=n<=%d; 0<=t<=gas)\n", NGMAXN); return 2;
  }
  const char *roots[] = {"0RA", "1RA", "0RB", "1RB"};
  int choice = -1, virtual_root = !strcmp(root, "all");
  if (!virtual_root) {
    for (int i = 0; i < 4; ++i) if (!strcmp(root, roots[i])) choice = i;
    if (choice < 0) { fprintf(stderr, "invalid root\n"); return 2; }
  }
  FILE *ledger = probe_open(prefix, "ledger.tsv");
  FILE *residual = probe_open(prefix, "residual.tsv");
  FILE *frontier = probe_open(prefix, "frontier.tsv");
  FILE *summary = probe_open(prefix, "summary.json");
  if (!ledger || !residual || !frontier || !summary) return 2;
  fprintf(ledger, "index\tkind\tmachine\tptr\thalt_slot\tanchor\tperiod\tside\tngram_n\tngram_t\tcontexts\tcandidate_wait_upper\texcursion_width\tedge_event\tfull\ttrust\n");
  fprintf(residual, "kind\tmachine\tptr\n");
  fprintf(frontier, "kind\tmachine\tptr\n");

  /* DFS depth <=8 and branching <=16; a small fixed stack suffices.
     Guard overflow anyway; never silently discard nodes. */
  Node stack[256]; size_t sp = 0;
  ProbeCounts counts = {0};
  if (virtual_root) {
    Node empty; memset(empty.sl, UNDEF, 8); empty.ptr = 1;
    probe_leaf(ledger, &counts, &empty, "halt_completion", 0, 1, -1, "none", -1, -1, -1, 0, 0);
  }
  /* Push in reverse so pop order is the Coq q_0 order. */
  for (int i = 3; i >= 0; --i) if (virtual_root || choice == i) {
    Node nd; memset(nd.sl, UNDEF, 8);
    int next = i / 2, write = i % 2;
    nd.sl[0] = (uint8_t)(next<<2 | 2 | write);
    nd.ptr = next == 1 ? 2 : 1;
    stack[sp++] = nd;
  }
  int seeds = (int)sp;
  init_pow(); wipe_tape();
  while (sp && counts.visited < maximum) {
    Node nd = stack[--sp]; ++counts.visited;
    counts.full += probe_full(&nd);
    SimOut o; simulate(nd.sl, gas, &o); wipe_tape();
    int edge = o.kind == 3; counts.edge += edge;
    if (o.kind == 1) {
      ++counts.expanded;
      probe_leaf(ledger, &counts, &nd, "halt_completion", 2*o.halt_q+o.halt_s,
        o.halt_n+1, -1, "none", -1, -1, -1, 0, edge);
      int maxnext = nd.ptr > 3 ? 3 : nd.ptr;
      for (int next = maxnext; next >= 0; --next)
        for (int dir = 1; dir >= 0; --dir) for (int write = 1; write >= 0; --write) {
          Node child = nd;
          SLOT(child.sl, o.halt_q, o.halt_s) = (uint8_t)(next<<2 | dir<<1 | write);
          child.ptr = next == nd.ptr ? nd.ptr+1 : nd.ptr;
          if (sp == sizeof stack / sizeof stack[0]) {
            fprintf(stderr, "frontier overflow; run incomplete\n"); return 3;
          }
          stack[sp++] = child; ++counts.generated;
        }
      continue;
    }
    if (o.kind == 2) {
      ++counts.cycle;
      probe_leaf(ledger, &counts, &nd, "cycle_hash_candidate", -1, o.n1, o.p,
        "unknown", -1, -1, -1, o.p, edge);
      continue;
    }
    TCand candidates[16];
    int nc = tc_candidates(&o, 1, candidates, 8);
    nc += tc_candidates(&o, 0, candidates+nc, 16-nc);
    int stopped = 0;
    for (int i = 0; i < nc; ++i) {
      int visited_lap;
      if (!tc_verify(nd.sl, candidates[i].a, candidates[i].P, &visited_lap)) continue;
      ++counts.translated;
      probe_leaf(ledger, &counts, &nd, "translated_cycle_candidate", -1,
        candidates[i].a, candidates[i].P, candidates[i].side ? "right" : "left",
        -1, -1, -1, candidates[i].P, edge);
      stopped = 1; break;
    }
    if (stopped) continue;
    for (int i = 0; i < nrungs; ++i) {
      wipe_tape();
      int ok = tail_ngram_check(nd.sl, ns[i], ts[i]);
      wipe_tape();
      if (!ok) continue;
      int contexts = 0;
      for (uint32_t a = 0; a < (1u << (3+2*ns[i])); ++a) contexts += ng_seen[a] != 0;
      ++counts.ngram; ++counts.ng_rung[i];
      probe_leaf(ledger, &counts, &nd, "tail_ngram_candidate", -1,
        ts[i], -1, "none", ns[i], ts[i], contexts, contexts+1, edge);
      stopped = 1; break;
    }
    if (stopped) continue;
    ++counts.unknown;
    probe_leaf(ledger, &counts, &nd, edge ? "unknown_edge" : "unknown", -1,
      -1, -1, "none", -1, -1, -1, -1, edge);
    probe_family(residual, edge ? "unknown_edge" : "unknown", &nd);
  }
  /* Preserve the exact remaining DFS pop order, including unused-state ptr. */
  for (size_t i = sp; i > 0; --i) {
    probe_family(frontier, "pending", &stack[i-1]);
    probe_family(residual, "pending", &stack[i-1]);
  }
  probe_summary(summary, &counts, maximum, gas, root, seeds, virtual_root, sp, ns, ts, nrungs);
  probe_summary(stdout, &counts, maximum, gas, root, seeds, virtual_root, sp, ns, ts, nrungs);
  int failed = ferror(ledger) || ferror(residual) || ferror(frontier) || ferror(summary) || ferror(stdout);
  failed |= fclose(ledger) != 0;
  failed |= fclose(residual) != 0;
  failed |= fclose(frontier) != 0;
  failed |= fclose(summary) != 0;
  failed |= fflush(stdout) != 0;
  return failed ? 3 : 0;
}
