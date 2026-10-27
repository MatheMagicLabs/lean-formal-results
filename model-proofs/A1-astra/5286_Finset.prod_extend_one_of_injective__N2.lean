/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Finset.prod_extend_one_of_injective
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean, line 515
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm N2, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  calc
    ∏ i ∈ t, extend f g 1 i =
        ∏ i ∈ (Finset.univ : Finset ι).image f, extend f g 1 i := by
      symm
      apply Finset.prod_subset
      · intro i hi
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
        exact ht j
      · intro i hi hnot
        have h : ¬ ∃ j, f j = i := by
          rintro ⟨j, rfl⟩
          exact hnot (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
        simp [Function.extend, h]
    _ = ∏ i, g i := by
      rw [Finset.prod_image (fun i _ j _ hij => hf hij)]
      apply Finset.prod_congr rfl
      intro i hi
      unfold Function.extend
      split_ifs with h
      · exact congrArg g (hf (Classical.choose_spec h))
      · exact False.elim (h ⟨i, rfl⟩)
