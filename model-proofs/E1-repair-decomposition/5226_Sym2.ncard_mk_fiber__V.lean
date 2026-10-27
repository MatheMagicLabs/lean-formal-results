/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.ncard_mk_fiber
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 50
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Sym2
open scoped Cardinal
variable {α : Type*}

theorem ncard_mk_fiber [DecidableEq α] (z : Sym2 α) :
    (Sym2.mk.uncurry ⁻¹' {z}).ncard = if z.IsDiag then 1 else 2 := by
  classical
  refine Sym2.inductionOn z ?_
  intro a b
  have hf : Sym2.mk.uncurry ⁻¹' {Sym2.mk a b} =
      ({(a, b), (b, a)} : Set (α × α)) := by
    ext ⟨x, y⟩
    simp [Sym2.eq_iff, Prod.mk.injEq]
  rw [hf]
  by_cases h : a = b
  · subst b
    simp
  · simp [h, Ne.symm h, Set.ncard_insert_of_notMem]
