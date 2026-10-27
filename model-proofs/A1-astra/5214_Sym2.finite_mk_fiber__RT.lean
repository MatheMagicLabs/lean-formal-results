/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.finite_mk_fiber
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 37
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Sym2
open scoped Cardinal
variable {α : Type*}

theorem finite_mk_fiber (z : Sym2 α) : (Sym2.mk.uncurry ⁻¹' {z}).Finite := by
  refine Sym2.inductionOn z fun a b => ?_
  refine ((Set.finite_singleton (b, a)).insert (a, b)).subset ?_
  intro p hp
  change Sym2.mk p.1 p.2 = Sym2.mk a b at hp
  have h := (Sym2.mk_eq_mk_iff (p := p) (q := (a, b))).mp hp
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.swap_prod_mk] using h
