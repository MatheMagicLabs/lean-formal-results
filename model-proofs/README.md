# Model-written proofs of Mathlib theorems

3,262 Lean proofs written by language models during pre-registered experiments (October 2026), one file each.
Every proof here was accepted by Lean during the run: it replaced the human proof in the original Mathlib file,
and Lean reported no errors and no `sorry`. Proofs using `sorry`, `admit`, `native_decide` or search tactics were
rejected, and runs where an agent reached outside its sandbox (for example a web search) count as failed and are
left out.

**Theorems.** The O, A, E and Leanstral experiments use theorems from Mathlib commit `a02a63c2` that were added after
commit `d0a050ad6`, so after the training data of the models tested (contamination-controlled). P1, D1 and UE1 use
Mathlib `d0a050ad6`: P1 its 57 long theorems added after the models' training data, D1 and UE1 160 theorems split into
DRIFT (the human proof cites a lemma added after the 2025-05 snapshot) and STABLE.

**File format.** Each file has a header (theorem, Mathlib file and line, experiment, arm, prover, round), then the
statement with the minimal context needed to read it, then the model's proof. Rounds count from 0 (first attempt).
The files are for reading; they compile in place in the Mathlib file named in the header, not on their own.
`index.csv` lists every file with its metadata; `stats.json` has the counts below.

**Not re-checked for this archive.** The verdicts are the ones recorded during the runs. Re-checking all files
needs builds of Mathlib `a02a63c2` and `d0a050ad6`.

| Folder | Setup | Solved / attempted, by arm | Files |
|---|---|---|---|
| `O2-repair-vs-resample/` | Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean's error messages; arm A = 4 independent attempts per theorem (attempt k) | A: 692/932 attempts; B: 229/233 | 921 |
| `O3-lemma-layer/` | Opus 5.5 with repair loop: R = repair only; RS = repair plus the Lean-checked lemma layer | R: 152/193; RS: 177/191 | 329 |
| `O4-layer-with-search/` | Opus 5.5 with repair loop, lemma layer and name search (RT) | RT: 91/95 | 91 |
| `O5-repair-haiku/` | Haiku 4.5: B = repair loop; A = independent attempts | A: 41/400; B: 21/100 | 62 |
| `O5-repair-sonnet/` | Sonnet 5.5: B = repair loop; A = independent attempts | A: 275/400; B: 98/100 | 373 |
| `A1-astra/` | GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds; RS = R plus lemma layer; RT = R with read-only Mathlib sources; N0–N3 = independent attempts | R: 132/191; RS: 159/191; RT: 93/95; N0–N3: 28–33/191 each | 502 |
| `A2-astra-effort-low/` | GPT-6 Astra, effort low (R, N0) | R: 113/191; N0: 31/191 | 144 |
| `A2-astra-effort-high/` | GPT-6 Astra, effort high (R, N0) | R: 137/191; N0: 33/191 | 170 |
| `E1-repair-decomposition/` | GPT-6 Astra, which part of the feedback makes repair work: V = full error messages, Z = line numbers only, B = only "Lean rejected this proof" | V: 103/191; Z: 51/191; B: 50/191 | 204 |
| `LS1-leanstral-loop/` | Leanstral 1.5 in a fixed check-and-repair loop: L1 = 1 candidate per round, L3 = up to 3 | L1: 31/95; L3: 46/95 | 77 |
| `O3LA-leanstral-agent/` | Leanstral 1.5 as a tool-using agent (Mistral Vibe) | 66/95 | 66 |
| `O3LA2-leanstral-agent-variants/` | Leanstral 1.5 agent on the 29 theorems O3LA left open: neu = restart, fest = fixed instruction, staffel = staged budget | neu: 4/29; fest: 8/29; staffel: 5/29 | 17 |
| `O3LA3-leanstral-agent-feedback/` | Leanstral 1.5 agent with goal-state feedback | 53/95 | 53 |
| `P1-astra-long-proofs/` | GPT-6 Astra on 57 long theorems (25–142 human tactic steps), at most 10 calls: W = whole proof plus repair; WT = W with read-only Mathlib sources; P = Lean-checked skeleton of `have` steps, then one step per call | W: 53/57; WT: 57/57; P: 10/15 | 120 |
| `D1-deepseek-16-samples/` | DeepSeek-Prover-V2-7B (4-bit), 16 independent samples per theorem, no feedback | 165 of 2,560 samples accepted, on 21 of 160 theorems | 65 distinct |
| `UE1-deepseek-8-samples/` | DeepSeek-Prover-V2-7B (4-bit), 8 independent samples per theorem, no feedback | 144 of 1,280 samples accepted, on 35 of 160 theorems | 68 distinct |

Arms are paired on the same theorems within an experiment. The analysis, pre-registrations and statistical tests
are in the paper in [`../paper/`](../paper/). Earlier long and short proofs by Claude (Mathlib
`d0a050ad6`, September) are in [lean-llm-mathlib-eval](https://github.com/MatheMagicLabs/lean-llm-mathlib-eval).
