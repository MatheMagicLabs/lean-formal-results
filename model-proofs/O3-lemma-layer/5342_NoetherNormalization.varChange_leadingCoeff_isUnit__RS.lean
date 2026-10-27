/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.varChange_leadingCoeff_isUnit
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 147
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v ↦ (varChange f ((MvPolynomial.monomial v) (f.coeff v))).degreeOf 0)
    (MvPolynomial.support_nonempty.mpr fne)
  have hv0 : f.coeff v ≠ 0 := MvPolynomial.mem_support_iff.mp vin
  have vs' : ∀ x ∈ f.support \ {v},
      (finSuccEquiv k n (varChange f (MvPolynomial.monomial x (f.coeff x)))).degree <
      (finSuccEquiv k n (varChange f (MvPolynomial.monomial v (f.coeff v)))).degree := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
    apply Polynomial.degree_lt_degree
    rw [MvPolynomial.natDegree_finSuccEquiv, MvPolynomial.natDegree_finSuccEquiv]
    exact lt_of_le_of_ne (vs x h1)
      (degreeOf_varChange_ne_of_ne _ _ _ h1 vin (by simpa using h2))
  have h2 : finSuccEquiv k n (varChange f (MvPolynomial.monomial v (f.coeff v))) ≠ 0 := by
    intro eq
    have := leadingCoeff_finSuccEquiv_varChange f v
    rw [eq, Polynomial.leadingCoeff_zero] at this
    exact hv0 (by simpa using this.symm)
  have hf : f = MvPolynomial.monomial v (f.coeff v) +
      ∑ x ∈ f.support \ {v}, MvPolynomial.monomial x (f.coeff x) := by
    conv_lhs => rw [← f.support_sum_monomial_coeff]
    rw [Finset.sdiff_singleton_eq_erase]
    exact (Finset.add_sum_erase _ _ vin).symm
  rw [show varChange f f = varChange f (MvPolynomial.monomial v (f.coeff v) +
    ∑ x ∈ f.support \ {v}, MvPolynomial.monomial x (f.coeff x)) from congrArg (varChange f) hf]
  simp only [map_add, map_sum]
  rw [add_comm, Polynomial.leadingCoeff_add_of_degree_lt, leadingCoeff_finSuccEquiv_varChange]
  · exact hv0.isUnit.map _
  · exact lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
      ((Finset.sup_lt_iff (Ne.bot_lt (fun x ↦ h2 (Polynomial.degree_eq_bot.mp x)))).mpr vs')
