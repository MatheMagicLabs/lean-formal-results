/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.varChange_leadingCoeff_isUnit
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 147
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA2-leanstral-agent-variants, arm fest, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent on the 29 theorems O3LA left open: neu = fresh restart, fest = fixed instruction, staffel = staged budget
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
  have h_support : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact fne
  -- Pick v_max maximizing degreeOf 0 after varChange
  obtain ⟨v_max, hv_max, h_max⟩ := Finset.exists_max_image f.support
    (fun v => degreeOf 0 (varChange f (monomial v (f.coeff v)))) h_support
  have h_lt (w : Fin (n + 1) →₀ ℕ) (hw : w ∈ f.support) (hne : w ≠ v_max) :
      degreeOf 0 (varChange f (monomial w (f.coeff w))) <
      degreeOf 0 (varChange f (monomial v_max (f.coeff v_max))) := by
    refine lt_of_le_of_ne (h_max w hw) (Ne.symm ?_)
    apply degreeOf_varChange_ne_of_ne f v_max w hv_max hw (Ne.symm hne)
  -- Express f as sum of monomials
  have hf : f = ∑ v ∈ f.support, monomial v (f.coeff v) := MvPolynomial.as_sum _
  have h_ff : varChange f f = varChange f (∑ v ∈ f.support, monomial v (f.coeff v)) :=
    congrArg (varChange f) hf
  rw [h_ff, map_sum (varChange f), map_sum (finSuccEquiv k n)]
  -- Now we have ∑ v ∈ f.support, finSuccEquiv k n (varChange f (monomial v (f.coeff v)))
  let g (v : Fin (n + 1) →₀ ℕ) : Polynomial (MvPolynomial (Fin n) k) :=
    finSuccEquiv k n (varChange f (monomial v (f.coeff v)))
  have h_natDegree (v : Fin (n + 1) →₀ ℕ) (hv : v ∈ f.support) :
      natDegree (g v) = degreeOf 0 (varChange f (monomial v (f.coeff v))) := by
    rw [MvPolynomial.natDegree_finSuccEquiv]
  have h_leadingCoeff (v : Fin (n + 1) →₀ ℕ) (hv : v ∈ f.support) :
      (g v).leadingCoeff = algebraMap k (MvPolynomial (Fin n) k) (f.coeff v) :=
    leadingCoeff_finSuccEquiv_varChange f v
  have h_coeff_ne_zero (v : Fin (n + 1) →₀ ℕ) (hv : v ∈ f.support) : f.coeff v ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hv
  -- Separate v_max from the rest
  let s := f.support.erase v_max
  have h_split : (∑ v ∈ f.support, g v) = g v_max + (∑ v ∈ s, g v) := by
    dsimp [s]
    calc
      (∑ v ∈ f.support, g v) = (∑ v ∈ f.support.erase v_max, g v) + g v_max :=
        (Finset.sum_erase_add f.support g hv_max).symm
      _ = g v_max + (∑ v ∈ f.support.erase v_max, g v) := add_comm _ _
  rw [h_split]
  have h_rest_natDegree_lt : ∀ v ∈ s, natDegree (g v) < natDegree (g v_max) := by
    intro v hv
    rw [h_natDegree v (Finset.mem_of_mem_erase hv), h_natDegree v_max hv_max]
    exact h_lt v (Finset.mem_of_mem_erase hv) (Finset.ne_of_mem_erase hv)
  by_cases hzero : natDegree (g v_max) = 0
  · -- In this case, all other terms have natDegree < 0, which is impossible, so s is empty
    have hs_empty : s = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      intro hne
      obtain ⟨v, hv⟩ := hne
      have h_lt := h_rest_natDegree_lt v hv
      rw [hzero] at h_lt
      exact Nat.not_lt_zero _ h_lt
    rw [hs_empty, Finset.sum_empty, add_zero]
    rw [h_leadingCoeff v_max hv_max]
    have h_coeff_unit : IsUnit (f.coeff v_max) :=
      IsUnit.mk0 (f.coeff v_max) (h_coeff_ne_zero v_max hv_max)
    exact IsUnit.map (algebraMap k (MvPolynomial (Fin n) k)) h_coeff_unit
  · have hpos : 0 < natDegree (g v_max) := Nat.pos_of_ne_zero hzero
    have h_sum_natDegree_lt : natDegree (∑ v ∈ s, g v) < natDegree (g v_max) := by
      have h_le : ∀ v ∈ s, natDegree (g v) ≤ natDegree (g v_max) - 1 := by
        intro v hv
        exact Nat.le_pred_of_lt (h_rest_natDegree_lt v hv)
      have h_sum_le : natDegree (∑ v ∈ s, g v) ≤ natDegree (g v_max) - 1 :=
        Polynomial.natDegree_sum_le_of_forall_le _ _ h_le
      have h_sub_lt : natDegree (g v_max) - 1 < natDegree (g v_max) :=
        Nat.sub_lt hpos (by decide)
      exact Nat.lt_of_le_of_lt h_sum_le h_sub_lt
    have h_leadingCoeff_eq : (g v_max + (∑ v ∈ s, g v)).leadingCoeff = (g v_max).leadingCoeff := by
      rw [add_comm]
      exact Polynomial.leadingCoeff_add_of_degree_lt
        (Polynomial.degree_lt_degree h_sum_natDegree_lt)
    rw [h_leadingCoeff_eq, h_leadingCoeff v_max hv_max]
    have h_coeff_unit : IsUnit (f.coeff v_max) :=
      IsUnit.mk0 (f.coeff v_max) (h_coeff_ne_zero v_max hv_max)
    exact IsUnit.map (algebraMap k (MvPolynomial (Fin n) k)) h_coeff_unit
