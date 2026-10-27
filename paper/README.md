# AI in Mathematics, Measured: The Lean Studies

Vincent Weinreich, October 2026. Preprint in preparation.

- `AI_in_Mathematics_Measured_Lean.pdf`: the paper (28 pages).
- `AI_in_Mathematics_Measured_Lean.tex`: LaTeX source; compiles with `pdflatex` (or `latexmk -pdf`) in this folder, using the figures in `figures/`.
- `AI_in_Mathematics_Measured_Lean.md`: the same text as Markdown.

This edition covers the studies on Lean, mathlib and AI theorem provers. Before release, an independent check compared
the numbers in the repair, Leanstral and formal-conjectures sections, the abstract, introduction, discussion and
appendix with the raw result files; the counts, McNemar tests and pre-registration hashes matched, and the imprecise
statements it found were corrected.

| Paper section | Folder |
|---|---|
| 4–5 Lemma choice and the lemma layer | [`../lemma-layer/`](../lemma-layer/), [`../model-proofs/O3-lemma-layer/`](../model-proofs/O3-lemma-layer/), [`../model-proofs/O4-layer-with-search/`](../model-proofs/O4-layer-with-search/) |
| 6 Whole proofs | [`../model-proofs/`](../model-proofs/) (D1, UE1, P1) |
| 8 Rubik's cube and supercube | [rubiks-cube-lean](https://github.com/MatheMagicLabs/rubiks-cube-lean) |
| 9 Repair with Lean feedback | [`../model-proofs/`](../model-proofs/) (O2, O5, A1, A2, E1, P1) |
| 10 Leanstral | [`../model-proofs/`](../model-proofs/) (LS1, O3LA, O3LA2, O3LA3) |
| 11 formal-conjectures audit | [`../formal-conjectures/`](../formal-conjectures/) |

© 2026 Vincent Weinreich. The paper is licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) (`LICENSE` in this folder).
