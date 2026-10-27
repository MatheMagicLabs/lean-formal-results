# Pre-registration S5: symbolic layer v2 + BM25 text retrieval as a candidate source (10 Oct 2026, ~03:45)

Before any S5 model or Lean component has run. Motivated by Q9 (schnell/VORAB_SCHNELL.md, 16354247): BM25 top-10
raised the union recall of the human lemma on the 390 test gaps from 42.1 % to 51.3 % (already computed, no model,
no Lean). Same gaps, ranking (DeepSeek score − 1.398·log(1+uses)) and Lean check as S3 (VORAB_S3.md, 34782b20).
## Candidates
S3 candidates (index and spelling unchanged) ∪ the BM25 top-10 per gap exactly as in Q9 (bm25_top10.json, frozen
before this file), new names written in their shortest unambiguous form, source tag 'bm25'. All candidates are rescored
by DeepSeek in one run. Lean results of S3 for unchanged patches are reused.
## Hypothesis
- S5a: pass@5 of v2 + BM25 > pass@5 of v2 (S3 'alle') on the same gaps (one-sided exact McNemar, alpha 0.05).
## Descriptive
Union recall; share of top-5 slots taken by BM25-only candidates; sanity check: the ranking restricted to v2 sources
reproduces S3's top 5; pass@5 at the "binding" gaps of Q1 once Q1 has run.
