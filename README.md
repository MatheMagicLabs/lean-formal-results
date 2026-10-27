# Lean formal results

Lean 4 disproofs and AI-prover results (Vincent Weinreich, M.Sc. Mathematics), September–October 2026, with the
paper that reports them. Every proof in this repository was accepted by Lean without errors or `sorry`; the
disproofs in `formal-conjectures/` use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

| Folder | Contents | Lean / Mathlib |
|---|---|---|
| [`paper/`](paper/) | *AI in Mathematics, Measured: The Lean Studies* (PDF, LaTeX source and Markdown) | – |
| [`formal-conjectures/`](formal-conjectures/) | Disproofs of two statements listed as open in google-deepmind/formal-conjectures: `rudins_conjecture_unique` and Erdős #70 `omega_one` | Lean 4.33.1, Mathlib `0df444a` |
| [`model-proofs/`](model-proofs/) | 3,262 proofs of Mathlib theorems written by Claude Opus/Sonnet/Haiku, GPT-6 Astra, Leanstral and DeepSeek-Prover in 16 pre-registered experiments (verdicts from the runs, not re-checked) | Mathlib `a02a63c2` and `d0a050ad6` |
| [`lemma-layer/`](lemma-layer/) | Lean-checked lemma candidates for 390 lemma gaps: 11.8 % filled by the prover alone, 54.1 % with the layer | Mathlib `d0a050ad6` |

The two disproofs were re-checked on 27 October 2026 against formal-conjectures `84cf7f8`.

## Authorship

- `formal-conjectures/`: proofs written by GPT-6 Astra during an audit I designed; findings checked by Lean, by hand and
  against the literature.
- `model-proofs/`, `lemma-layer/`: proofs and candidates come from the models named in each file. The experiments
  (task selection, contamination control, pre-registration, checking pipeline, analysis) are mine.
- `paper/`: written with AI assistance (Claude) under my direction; results checked against the raw data.

Related: [lean-llm-mathlib-eval](https://github.com/MatheMagicLabs/lean-llm-mathlib-eval),
[rubiks-cube-lean](https://github.com/MatheMagicLabs/rubiks-cube-lean) (20 ≤ God's number ≤ 28 in Lean 4).

## Licence

- The paper (`paper/`: text, LaTeX source and figures) is licensed under
  [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/); see `paper/LICENSE`.
- Everything else is licensed under Apache-2.0 (`LICENSE`). Files that contain code from formal-conjectures or Mathlib
  keep those projects' Apache-2.0 licences and notices.
