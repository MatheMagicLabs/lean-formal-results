# Pre-registration S4: symbolic layer v3 – Goedel samples and a post-cutoff ("delta") list as sources (9 Oct 2026, ~17:00)

Before any S4 model or Lean component has run. Points 3 and 6 of the plan. Same 390 test gaps, ranking
(DeepSeek score − 1.398·log(1+uses)) and Lean check as S3 (VORAB_S3.md, 34782b20).
## New candidate sources (added to the S3 candidates; existing candidates keep index and spelling)
- goedel: 8 samples from Goedel-Prover-V2-8B-4bit at each gap (temperature 0.8, top-p 0.95, 24 tokens, same seeds and
  prompts as the DeepSeek samples of S2); the first identifier, resolved to a Mathlib theorem.
- delta: the 10 theorems added after May 2025 with the highest personalized PageRank from the gap theorem's
  neighbourhood, built exactly like condition B of the drift pilot, without looking at the human lemma
  (baue_delta.py). Already computed before this file (no model, no Lean): the human lemma is post-cutoff at 29 of
  the 390 gaps and in the delta list at 2 of them.
All candidates (old and new) are rescored by DeepSeek in one run.
## Hypothesis
- S4a: pass@5 of v3 > pass@5 of v2 (S3 'alle') on the same gaps (one-sided exact McNemar, alpha 0.05).
## Descriptive
Union recall v3 vs v2; recall per new source; pass@5 without goedel and without delta; sanity check: the ranking
restricted to the v2 sources reproduces S3's top 5. Lean results of S3 for unchanged patches are reused.
