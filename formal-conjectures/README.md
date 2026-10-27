# Two disproofs of statements listed as open in formal-conjectures

During an audit of the open statements in
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (commit `84cf7f8`,
1,244 statements listed as open; GPT-6 Astra audited them, every finding was checked by Lean and by hand), two statements turned out to be
false as formalised. Each file here proves the negation in Lean.

| File | Statement | Why it is false |
|---|---|---|
| `FcDisproofs/RudinsConjectureUniqueNeg.lean` | `rudins_conjecture_unique` (`FormalConjectures/Wikipedia/RudinsConjecture.lean`): for every N ≥ 6, every nontrivial progression attaining the maximum number of squares Q(N) has difference 24 | At N = 6 the progression 120n + 49 has 4 squares among its first 6 terms (49, 169, 289, 529) and attains the maximum, but its difference is 120. The source (González-Jiménez & Xarles 2014) claims uniqueness only up to equivalence and only for certain N. |
| `FcDisproofs/Erdos70OmegaOneNeg.lean` | `omega_one` (`FormalConjectures/ErdosProblems/70.lean`): 𝔠 → (ω₁, n)³₂ for every n ≥ 2 | False for n = 4 in ZFC: colour a triple blue when its middle element is a "peak" under a bijection with ℝ. No 4 elements are all blue, and every red set splits into a strictly increasing and a strictly decreasing part, so it is countable. This is a classical argument (it appears in Erdős–Hajnal–Rado 1965, Theorem 11), so the statement is a known negative result listed as open. |

The main problem `erdos_70` is not affected.

**Authorship.** The Lean proofs were written by GPT-6 Astra during the audit; the audit design, checking and
literature comparison are mine. Each file contains the unchanged formal-conjectures file up to the statement
(Apache-2.0, © The Formal Conjectures Authors), followed by the negated statement and its proof.

**Status.** A report to the formal-conjectures maintainers is in preparation (October 2026).

## Checking

Lean `v4.33.1`, Mathlib `0df444a` (the versions pinned by formal-conjectures `84cf7f8`).

```bash
git clone https://github.com/google-deepmind/formal-conjectures && cd formal-conjectures
git checkout 84cf7f8adfb0ea8d14c7d00bdf145cc9032bdf88
lake exe cache get
cp /path/to/FcDisproofs/*.lean .
lake env lean RudinsConjectureUniqueNeg.lean
lake env lean Erdos70OmegaOneNeg.lean
```

Add `#print axioms rudins_conjecture_unique_neg` (or `omega_one_neg`) at the end to see the axioms:
only `propext`, `Classical.choice` and `Quot.sound`.
