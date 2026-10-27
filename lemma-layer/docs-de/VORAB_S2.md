# Pre-registration S2: the symbolic layer, version 1, end to end (8 Oct 2026)

Written before any S2 component has run. Builds on T1 (α̂ DeepSeek = 1.398), T4 and S1 (Lean search recall 24%).

## Pipeline (DeepSeek-Prover-V2-7B, the 390 T4/S1 test gaps)
1. Lean proposes: the resolved lemma names of the S1 `rw?`/`apply?` suggestions at the gap's tactic (already
   computed in S1; order kept).
2. The model proposes: 8 sampled continuations of the gap prefix (temperature 0.8, top-p 0.95, 24 new tokens, seeds
   fixed); the first identifier of each, if it resolves to an existing theorem at d0a050ad6.
3. Candidate set = union of 1 and 2 (deduplicated, at most 20 from Lean in their order plus all model names).
   The human lemma is NOT added.
4. Ranking: teacher-forced model score (as in T1–T3) minus α̂·log(1 + LeanDojo-v2 uses), α̂ = 1.398 from T1.
5. Lean checks the top 5 in the original gap (Variante S, as in Stage 2/T4); success = any of them is "ok"
   (including the human lemma, if it is in the set).
## Hypothesis
- S2a: success of the layer (pass@5) > success of free generation on the same gaps (Stage 1 greedy output is the
  human lemma, or a substitute Lean accepted in Stage 2): one-sided exact McNemar on discordant gaps, alpha 0.05.
## Descriptive
Recall of the human lemma in each source and in the union; top-1 success; success by gap context.
