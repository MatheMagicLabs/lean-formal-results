# Pre-registration S3: symbolic layer v2 – more candidate sources (9 Oct 2026, ~04:15)

Before any S3 component has run. Same 390 test gaps, model, ranking (α = 1.398) and Lean check as S2 (VORAB_S2.md).
## New candidate sources (added to the S2 candidates)
- `exact?` at the same probe position as S1: all theorem names in each suggested term.
- `simp?` at the same probe position: all theorem names in each suggested `simp only [...]` list.
- Same file: the 10 theorems declared closest before the gap's theorem in the same file.
## Hypotheses
- S3a: pass@5 of v2 > pass@5 of v1 (S2) on the same gaps (one-sided exact McNemar, alpha 0.05).
- Descriptive (point 2, ablation): recall of the human lemma and pass@5 when each source is left out
  (rw?/apply?, exact?, simp?, model samples, same file); Lean checks the top 5 of each ablated ranking.
