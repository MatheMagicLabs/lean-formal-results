/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Finset.prod_extend_one_of_injective
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean, line 515
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Function
variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}
namespace Finset
section CommMonoid
variable [CommMonoid M] {f g : ι → M}
open Classical in
set_option backward.isDefEq.respectTransparency.types false in
section bij
variable {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M}
variable [DecidableEq κ]
variable [Fintype κ]
end bij
variable (f s)
variable {f s}

@[to_additive]
theorem prod_extend_one_of_injective [Fintype ι] {t : Finset κ} {f : ι → κ} (g : ι → M)
    (hf : Injective f) (ht : ∀ i, f i ∈ t) :
    ∏ i ∈ t, extend f g 1 i = ∏ i, g i := by
  classical
  have he (i : ι) : extend f g 1 (f i) = g i := by
    unfold Function.extend
    rw [dif_pos ⟨i, rfl⟩]
    exact congrArg g (hf (Classical.choose_spec
      (show ∃ j, f j = f i from ⟨i, rfl⟩)))
  have hs : Finset.univ.image f ⊆ t := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact ht i
  calc
    ∏ x ∈ t, extend f g 1 x =
        ∏ x ∈ Finset.univ.image f, extend f g 1 x := by
      symm
      apply Finset.prod_subset hs
      intro x _ hx
      have hn : ¬ ∃ i, f i = x := by
        rintro ⟨i, rfl⟩
        exact hx (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      simp [Function.extend, hn]
    _ = ∏ i, g i := by
      rw [Finset.prod_image (fun i _ j _ h => hf h)]
      exact Finset.prod_congr rfl (fun i _ => he i)
