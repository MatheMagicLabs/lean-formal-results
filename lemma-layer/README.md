# The lemma layer: filling lemma gaps with Lean-checked candidates

A *lemma gap* is a Mathlib proof with one explicitly named lemma removed. The prover (DeepSeek-Prover-V2-7B, 4-bit)
has to supply the missing name. Left to itself it fills 11.8 % of the 390 test gaps. The layer instead collects
candidate lemmas from several sources, ranks them by the model's score minus 1.398 · log(1 + usage in Mathlib) to
correct the model's bias towards popular lemmas, and lets Lean check the top 5.

| Version (pre-registered study) | Candidate sources | Gaps filled (pass@5) |
|---|---|---|
| free generation | model samples only | 11.8 % |
| v1 (S2) | Lean's `rw?` / `apply?` suggestions + model samples | 34.6 % |
| v2 (S3) | + `exact?`, `simp?`, lemmas from the same file | 39.0 % |
| v3 (S4) | + Goedel-Prover samples, list of new lemmas | 40.8 % |
| **v2 + BM25 + co-citations + random walk (S5)** | + text search, co-citation and personalised PageRank on the Mathlib dependency graph | **54.1 %** (top-1: 24.4 %) |

Each step was a pre-registered one-sided exact McNemar test on the same 390 gaps; all four S5 hypotheses were
confirmed (p between 2.7·10⁻⁷ and 1.3·10⁻³). The human's lemma is among the S5 candidates in 71.5 % of gaps, so
ranking and checking recover about three quarters of what the candidate list contains.

## Files

- `fills_s5.csv`: one row per test gap with the final ranking's top 5, whether the gap was filled, and by which
  candidate. A candidate counts as valid if Lean accepted the proof with it, or if it is the human's own lemma.
  211 of 390 gaps are filled.
- `data/`: the S5 run (candidates with their sources, the rankings, the patches and Lean's verdict for each).
- `analyse_s5.py`: the pre-registered analysis that produced the numbers above. It expects the original folder layout.
- `docs-de/`: pre-registrations (VORAB) and result notes (ERGEBNIS) in German, as written before and after each run.

Gaps are from Mathlib `d0a050ad6`. The 1,000-gap study that motivated the layer (lemma choice, invented names,
popularity bias) is in [lean-llm-mathlib-eval](https://github.com/MatheMagicLabs/lean-llm-mathlib-eval).
