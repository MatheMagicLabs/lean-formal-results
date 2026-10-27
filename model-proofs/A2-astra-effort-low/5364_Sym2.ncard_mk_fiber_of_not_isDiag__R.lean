/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.ncard_mk_fiber_of_not_isDiag
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 45
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Sym2
open scoped Cardinal
variable {α : Type*}

theorem ncard_mk_fiber_of_not_isDiag {z : Sym2 α} (hz : ¬z.IsDiag) :
    (Sym2.mk.uncurry ⁻¹' {z}).ncard = 2 := by
  classical
  induction z using Sym2.inductionOn with
  | _ a b =>
    have hab : a ≠ b := by
      intro h
      subst b
      exact hz (by simp)
    have hf : Sym2.mk.uncurry ⁻¹' {s(a, b)} = {(a, b), (b, a)} := by
      ext ⟨c, d⟩
      simp [Sym2.eq_iff]
    rw [hf]
    simp [hab]
