/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.varChange_leadingCoeff_isUnit
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 147
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  classical
  let p := fun v : Fin (n + 1) →₀ ℕ ↦
    finSuccEquiv k n (varChange f (monomial v (f.coeff v)))
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image f.support
    (fun v ↦ (p v).natDegree) (MvPolynomial.support_nonempty.mpr fne)
  have hu : IsUnit (p v).leadingCoeff := by
    dsimp [p]
    rw [leadingCoeff_finSuccEquiv_varChange]
    exact (isUnit_iff_ne_zero.mpr (mem_support_iff.mp hv)).map (algebraMap k _)
  have hc : (∑ w ∈ f.support, p w).coeff (p v).natDegree =
      (p v).leadingCoeff := by
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single v]
    · exact Polynomial.coeff_natDegree
    · intro w hw hwv
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      refine lt_of_le_of_ne (hmax w hw) ?_
      simpa only [p, natDegree_finSuccEquiv] using
        degreeOf_varChange_ne_of_ne f w v hw hv hwv
    · exact fun h ↦ (h hv).elim
  have hd : (∑ w ∈ f.support, p w).natDegree = (p v).natDegree :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      (Polynomial.natDegree_sum_le_of_forall_le _ _ hmax)
      (by rw [hc]; exact hu.ne_zero)
  have hs : (∑ w ∈ f.support, p w) = finSuccEquiv k n (varChange f f) := by
    simp only [p, ← map_sum, MvPolynomial.support_sum_monomial_coeff]
  rw [← hs, Polynomial.leadingCoeff, hd, hc]
  exact hu
