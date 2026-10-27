/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.finite_mk_fiber
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 37
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA-leanstral-agent, arm -, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 as a tool-using agent (Mistral Vibe)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Sym2
open scoped Cardinal
variable {α : Type*}

theorem finite_mk_fiber (z : Sym2 α) : (Sym2.mk.uncurry ⁻¹' {z}).Finite := by
  induction z using Sym2.ind with
  | h a b =>
    rw [mk_fiber]
    simp
