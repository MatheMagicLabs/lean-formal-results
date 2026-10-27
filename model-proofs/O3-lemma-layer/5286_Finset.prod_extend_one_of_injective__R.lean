/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Finset.prod_extend_one_of_injective
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean, line 515
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  rw [← Finset.prod_subset (s₁ := Finset.univ.map ⟨f, hf⟩) (s₂ := t)]
  · rw [Finset.prod_map]
    exact Finset.prod_congr rfl fun i _ => hf.extend_apply g 1 i
  · intro x hx
    simp only [Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk] at hx
    obtain ⟨i, rfl⟩ := hx
    exact ht i
  · intro x _ hx
    have : ¬ ∃ a, f a = x := by simpa using hx
    rw [extend_apply' _ _ _ this]
    rfl
