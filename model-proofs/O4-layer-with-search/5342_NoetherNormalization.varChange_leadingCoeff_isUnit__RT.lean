/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.varChange_leadingCoeff_isUnit
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 147
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Polynomial MvPolynomial Ideal Nat RingHom List
variable {k : Type*} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k)
variable (v w : Fin (n + 1) →₀ ℕ)
namespace NoetherNormalization
section equivT
local notation3 "up" => 2 + f.totalDegree
variable {f v} in
local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1

lemma varChange_leadingCoeff_isUnit (fne : f ≠ 0) :
    IsUnit (finSuccEquiv k n (varChange f f)).leadingCoeff := by
  set g : (Fin (n + 1) →₀ ℕ) → Polynomial (MvPolynomial (Fin n) k) :=
    fun w ↦ finSuccEquiv k n (varChange f (monomial w (f.coeff w))) with hg
  obtain ⟨v, vin, vmax⟩ := Finset.exists_max_image f.support
    (fun w ↦ (g w).natDegree) (support_nonempty.mpr fne)
  have h1 : finSuccEquiv k n (varChange f f) = ∑ w ∈ f.support, g w := by
    have := congrArg (fun p ↦ finSuccEquiv k n (varChange f p)) f.as_sum
    simp only [map_sum] at this
    rw [hg]
    exact this
  have hlc : (g v).leadingCoeff = algebraMap k _ (f.coeff v) := by
    rw [hg]
    exact leadingCoeff_finSuccEquiv_varChange ..
  have hv0 : g v ≠ 0 := by
    rw [← leadingCoeff_ne_zero, hlc]
    exact (_root_.map_ne_zero _).mpr (mem_support_iff.mp vin)
  have hlt : (∑ w ∈ f.support.erase v, g w).degree < (g v).degree := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (bot_lt_iff_ne_bot.mpr (by rwa [Ne, Polynomial.degree_eq_bot]))]
    intro w hw
    obtain ⟨hwv, hws⟩ := Finset.mem_erase.mp hw
    apply Polynomial.degree_lt_degree
    refine lt_of_le_of_ne (vmax w hws) ?_
    simp only [hg, natDegree_finSuccEquiv]
    exact degreeOf_varChange_ne_of_ne f w v hws vin hwv
  rw [h1, ← Finset.add_sum_erase _ _ vin, Polynomial.leadingCoeff_add_of_degree_lt' hlt, hlc]
  exact (IsUnit.mk0 _ (mem_support_iff.mp vin)).map _
