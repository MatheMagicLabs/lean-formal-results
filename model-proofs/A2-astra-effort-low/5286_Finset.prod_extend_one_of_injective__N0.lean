/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Finset.prod_extend_one_of_injective
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean, line 515
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm N0, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
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
  have hfg (i : ι) : extend f g 1 (f i) = g i := by
    unfold Function.extend
    split_ifs with h
    · exact congrArg g (hf h.choose_spec)
    · exact False.elim (h ⟨i, rfl⟩)
  calc
    ∏ k ∈ t, extend f g 1 k =
        ∏ k ∈ Finset.univ.image f, extend f g 1 k := by
      symm
      apply Finset.prod_subset
      · intro k hk
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
        exact ht i
      · intro k _ hk
        unfold Function.extend
        split_ifs with h
        · exact False.elim
            (hk (Finset.mem_image.mpr
              ⟨h.choose, Finset.mem_univ _, h.choose_spec⟩))
        · rfl
    _ = ∏ i, g i := by
      rw [Finset.prod_image]
      · simp only [hfg]
      · intro i _ j _ hij
        exact hf hij
