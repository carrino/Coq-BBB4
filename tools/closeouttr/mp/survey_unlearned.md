# MPU survey: the 103 rows the block-list learner did not learn (2026-10-01)

Rows: `tools/closeouttr/mp/rows_unlearned.txt`. These are the 94 rows that BLC4/BLC5's learner
rejected plus the 9 that timed out (`blc5/sweep191.jsonl`). **All 103 are class DN.** Per row:
`survey_unlearned.tsv` (spec, class, shape group, every route tried with its verdict, result).

**Result: 1 row boarded** (`CBT_MPU_00`, multi-block RepWL). The other 102 stay open. No existing
finder takes them at container budgets. Almost every row had already been through `bl_ti.py`
(all 103), the rank tier at windows 4-6 (all 103), `hy2_batch.py` (59), multi-block RepWL (53),
rank tier window 8 (40) and `hy3_ti.py` (24). This survey ran the remaining untried
(finder, row) pairs, plus wider variants of `hy2` and MB.

## Batch

| batch | rows | route | compile | `Print Assumptions cv_MPU_00_0000` |
|---|---:|---|---:|---|
| `CBT_MPU_00` | 1 (`1RB0LD_1RC0RB_1LA0RC_1LA0LD`) | `RepWLMBTr` (`mb_tier_tr_sound`), 20-cell words, K=1 Y=21 X=41 T=3 t=4096 | 177 s (container, alongside a 1-job finder) | `functional_extensionality_dep` only |

MB's long-period run (§7.4.MB, `mb/mb_found_longper.json`) had already certified this row, at 15,758
nodes, but left it out because the kernel cost was about 7.7 minutes. With `--pmax 64 --polish 900`
the closure is 9,617 nodes, which cuts the cost to about 3 minutes. That is still over the 2-minute
target, so the batch holds this one row. It is not in `_CoqProject` (`gen_closeout_tr.py` was not
run), so it was compiled with `coqc -Q theories BBB4 -w -abstract-large-number` and not through
`make -f Makefile.coq`. CI cost: list it in `ci_costs.tsv` at about 350 s.

## Shape groups

To build the groups:

1. Simulate each row (`survey_sim.c`) and run-length compress its tape (`survey_shapes.py show`) at
   1M, 4M and 16M steps.
2. List the long periodic stretches and the remaining "junk" cells at 1M, 4M, 16M and 64M steps
   (`survey_shapes.py feat`).
3. Assign groups by hand (`survey_groups.py`).

| group | rows | shape (example) | routes tried (this survey **bold**) | result |
|---|---:|---|---|---|
| SPREAD | 19 | irregular tape, no periodic stretch of note, junk ≈ extent (`0RB0RA_0LC1RA_1RB1LD_1LC0LD`) | MB (all, earlier), rk4-6, rk8 (13 earlier), **rk8 300 s (6)**, **hy3_ti** | open: rk8 false or timeout, MB no closure |
| HYB2 | 14 | two long blocks trading length, ends ~20-60 cells growing ~log t: a counter end (`1RB1LD_1RC0RB_0LA1LD_1LC1RB`: `(001)^a (011)^b`). In `1RB0LA_1RC1RA_0RD0RB_1LD0LA` the right end is a clean counter: low digit base 4 (`0000/1100/0011/1111`), higher digits base 2 (`0000/1111`), with the block junction rotating every 2 laps | hy2, **hy2w** (width ≤ 10, bases 2-6, 400 s), **MB pmax 32**, **rk8**, **hy3_ti**, bl_ti | open: "no counter family" / "no anchor" / timeout. The mixed-radix low digit plus the 2-lap junction phase is outside `HybridCtrTr`'s one-base numeration |
| BLKSPR | 11 | one or two long blocks (period 2/8/9) beside an irregular region that grows with the extent (`0RB1RD_1LC0LC_1RA1LB_1RB0RA`: `(10)^1560` + 60% junk) | MB, rk4-8, **rk8 (4)**, **hy3_ti** | open |
| LIST2 | 11 | geometric lists, unit 1 or 2, ratio 2: `(1)^3458 0 (1)^1729 0 (1)^864 ...` (`1RB0RC_0LC1LB_0LD1LC_1RD0RA`); `(10)^27 0101 (10)^54 0101 ...`; `(01)/(10)` lists whose unit flips phase between elements (`(10)^41 11 (10)^82 11 (10)^165 (01)^327 00 ...`) | lx5 (learner: no ratio / no BPS / left samples disagree), bl_ti, **MB**, **hy3_ti** | open: BLC lists whose anchor (head left of every 1) is rare or whose b_0 is mid-rewrite. A learner problem, so it goes back to the BLC workstream |
| LONGPER | 11 | level-2 words: one period of 22-54 cells (`(11011110110)^4 1101101101` = 54) over 50-100% of the tape | MB pmax 64 (all 11, earlier: 10 no closure), **MB pmax 64 polish 900** | **1 boarded** (`CBT_MPU_00`); 10 open |
| LIST4 | 9 | `(011)/(110)` ×4 lists (`(110)^1031 ... (101)^175 ... (011)^65 ...`), and one `(1110)/(0110)` ×3 list | lx5 (timeout at 400 s: these are exactly BLC5's 9 time-outs), **MB**, **hy3_ti** | open: BLC4's multi-cell ratio-4 family ("too many families"). Box: longer lx5 budget |
| TRIO | 5 | `1^a 0^b` trading length, then a binary counter of 4-cell digits (`1100`/`1101`) whose ~950 high zero digits were written in one go (`(1100)^949`) (`0RB0LB_1LC1RA_0LD0LC_1RD1LB` + 4 twins) | hy2, **hy2w**, **rk8**, **MB**, **hy3_ti** | open: rk8 false; hy2 no anchor |
| MULTI14 | 5 | three blocks, no junk: `(10100101001010)^a (10)^b (01)^c`; the head converts `(10)` to and from the 14-word (`1RB0LC_1RC0RA_1LD0RB_1LA0LD` + twins; `1RB0RA_0LC0RD_1LD1LB_1RA0LB` with a 10-word) | MB pmax 64 (earlier), **rk8 (1)**, **hy2w**, **hy3_ti** | open: MB no closure |
| LIST32 | 4 | 5-cell blocks growing ×~1.45 (`(10110)^22 ... (01011)^109 (00011)^157`): Collatz-like | **MB**, **hy3_ti** | open: left alone, TA's shape |
| POW2 | 4 | blocks of 1s and 0s with power-of-two lengths (`(1)^2048 (0)^512 (1)^960 ...`): a counter whose digits are blocks | MB, rk8, **hy3_ti** | open: left alone, counter-like |
| HYB1 | 3 | one long block (the head splits it), counter end ~30 cells growing ~log t (`1RB0LC_1RC0RD_1LA0LC_1RD0RA`; `1RB1LD_1RC0RB_0LA1RB_0LD1LA`: binary counter beside a `(101)` block that rotates every lap) | hy2, **hy2w**, **MB pmax 32 (2 GB: memory; 5 GB 600 s: no closure)**, **rk8**, **hy3_ti** | open: HY3's "counter whose low end moves with a multi-cell block" (needs `HybridCtrTr` with per-phase alphabets) |
| UNARY | 2 | `(1101)^k` (k ~ log t) beside `(0010)^b` (b ~ sqrt t, doubles per k step) | hy2 (timeout), **rk8 (timeout)**, **hy3_ti** (leaf too long) | open |
| OVF2 | 2 | HY2's two-lap overflow (`0RB0LC_1LC1RD_1LA1LB_1RC0RB`) | **hy2w**, **rk8 false**, **MB** | open: needs the parity-aware `HybridCtr2Tr` finder of §7.4.HY3 |
| MULTI4 | 2 | 4-5 blocks of periods 6/8/14 with ~200 junk cells | **rk8 false**, **hy2w**, **MB** | open |
| LISTIRR | 1 | many `(10)/(01)` blocks of irregular length | **MB**, **hy3_ti** | open |

All 103 rows are DN. No row in the survey was a quiet (QH) or sparse (SP) row.

### What the survey's runs gave

| run | rows | budget | verdicts |
|---|---:|---|---|
| `hy3_ti.py find` (`runs/hy3.jsonl`) | 83 (the 79 HY3 never tried, plus 4 of HY3's own 24 re-tried) | 240-300 s, maxfam 200 | 0 certified: 72 "no anchor key", 9 too many families, 2 leaf too long |
| `mb_cert_find.py --pmax 32` (`runs/mb50.json`) | 50 never tried by MB | 240 s | 0: 48 no closure, 2 memory (re-run at 5 GB, 600 s: no closure) |
| `mb_cert_find.py --pmax 64 --polish 900` (`runs/mb_heavy.json`) | 1 | 1,500 s | **certified, 9,617 nodes**: boarded |
| `mp/hy2w.py` (`runs/hy2w.jsonl`), hy2 with digit width ≤ 10 and bases 2-6 | 23 hybrids | 400-600 s | 0: 16 no counter family, 3 no anchor, 3 timeout, 1 no mid |
| `ng_batch.py probe --rungs rk:8:0` (`runs/rk8.json`) | 37 never tried at window 8 (the list rows were skipped) | 300 s | 0: 19 false, 18 timeout |

## Reproduce

```
cc -O2 -o /tmp/mpu_sim tools/closeouttr/mp/survey_sim.c
python3 tools/closeouttr/mp/survey_shapes.py feat tools/closeouttr/mp/rows_unlearned.txt     # ~2 min
python3 tools/closeouttr/mp/survey_shapes.py show 1RB0LC_1RC0RA_1LD0RB_1LA0LD 1000000 16000000
python3 tools/closeouttr/mp/survey_groups.py tools/closeouttr/mp/rows_unlearned.txt         # group counts

# the boarded row (~25 min with polish)
cd tools/censustr && python3 mb_cert_find.py find OUT.json --list ../closeouttr/mp/runs/heavy.txt \
    --jobs 1 --timeout 1500 --pmax 64 --polish 900 && cd ../..
python3 tools/closeouttr/mb_batch.py OUT.json --tag MPU --chunk 1

# the sweeps (2 jobs here; all resumable)
python3 tools/closeouttr/hy3_ti.py find tools/closeouttr/mp/runs/hy3_untried.txt hy3.jsonl --jobs 2 --timeout 240 --maxfam 200   # ~25 min
cd tools/censustr && python3 mb_cert_find.py find mb50.json --list ../closeouttr/mp/runs/mb_untried.txt --jobs 1 --timeout 240 --pmax 32 && cd ../..   # ~45 min
HY2_BUDGET=400 python3 tools/closeouttr/mp/hy2w.py find tools/closeouttr/mp/runs/hy2_sel2.txt hy2w.jsonl --jobs 1   # ~1.5 h
python3 tools/closeouttr/ng_batch.py probe tools/closeouttr/mp/runs/rk8_sel.txt rk8.json --rungs rk:8:0 --jobs 1 --timeout 300   # ~2 h
python3 tools/closeouttr/mp/survey_report.py > tools/closeouttr/mp/survey_unlearned.tsv
```

## Left for the box (14 cores, `--jobs 12`)

These are too slow for this container. Every command resumes from its output file.

```
# the 9 LIST4 rows that time out in lx5 at 400 s: one round of 1,800 s, about 30 min
python3 tools/closeouttr/blc5/lx5.py find tools/closeouttr/mp/runs/list4_lx5_timeout.txt list4.jsonl --jobs 12 --timeout 1800
# the 18 rk:8 time-outs at 1,800 s: 2 rounds, about 1 h (BX: window 8 is the rung that pays on bouncers)
python3 tools/closeouttr/ng_batch.py probe tools/closeouttr/mp/runs/rk8_timeout.txt rk8_1800.json --rungs rk:8:0 --jobs 12 --timeout 1800
python3 tools/closeouttr/ng_batch.py batch rk8_1800.json --tag MPU --chunk 2
# hy2's timeouts (7 rows: HYB2 and UNARY) at 1,800 s: one round, about 30 min
HY2_BUDGET=1800 python3 tools/closeouttr/mp/hy2w.py find tools/closeouttr/mp/runs/hy2_timeout.txt hy2_1800.jsonl --jobs 12
python3 tools/closeouttr/hy2_batch.py batch hy2_1800.jsonl --tag MPU --chunk 20
```

Expect little from these. All three groups failed for structural reasons, not budget, wherever a
verdict was reached.

## What it would take

* **HYB1/HYB2/TRIO (22 rows)** are bouncer + counter hybrids whose counter is clean but one of the
  following:
  * mixed-radix: a base-4 low digit under base-2 digits;
  * read in a frame that rotates with the block phase (2-3 laps a cycle);
  * beside two trading blocks instead of one.

  This is §7.4.HY3's next item 2: `HybridCtrTr` with per-phase digit alphabets and the anchor read
  in the junction's frame. A mixed-radix low digit can be stated as L = 4 phases of a binary counter
  that steps once every 4 laps, which the present one-rank-per-lap anchor cannot express.
* **LIST2/LIST4 (20 rows)** are block lists that BLC's learner rejects at its anchor. On the `1`-list
  `1RB0RC_0LC1LB_0LD1LC_1RD0RA`, the anchor shows `b_0` mid-transfer (`1^2 0 1^1728 0 1^864 ...`),
  and that is why "left samples disagree". That is BLC learner work.
* **LONGPER (10 rows)**: MB at `--pmax 64` reaches no closure. The tape is one long period plus a
  second region whose phase drifts (§7.4.BX's "middle region whose phase changes").
* **SPREAD/BLKSPR (30 rows)**: no route. The rank tier is false or times out at window 8.
