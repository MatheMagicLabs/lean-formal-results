/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.varChange_leadingCoeff_isUnit
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 147
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  have hdeg (u : Fin (n + 1) →₀ ℕ) {a : k} (ha : a ≠ 0) :
      (varChange f (monomial u a)).degreeOf 0 =
        ∑ i : Fin (n + 1), r i * u i := by
    rw [← natDegree_finSuccEquiv, monomial_eq, Finsupp.prod_pow u fun a ↦ X a]
    simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, map_mul, map_prod, map_pow,
      AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      ite_eq_left, Fin.succ_ne_zero, ite_false, one_smul, map_add,
      finSuccEquiv_X_zero, finSuccEquiv_X_succ, algebraMap_eq]
    have h (i : Fin n) :
        (Polynomial.C (X (R := k) i) + Polynomial.X ^ r i.succ) ^ u i.succ ≠ 0 :=
      pow_ne_zero (u i.succ) (leadingCoeff_ne_zero.mp <| by
        simp [add_comm, leadingCoeff_X_pow_add_C])
    rw [natDegree_mul (by simp [ha])
        (mul_ne_zero (by simp) (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h i))),
      natDegree_mul (by simp) (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h i)),
      natDegree_prod _ _ (fun i _ ↦ h i), natDegree_finSuccEquiv, degreeOf_C]
    simpa only [natDegree_pow, zero_add, natDegree_X, mul_one, Fin.val_zero,
      pow_zero, one_mul, add_right_inj] using
      Finset.sum_congr rfl (fun i _ ↦ by
        rw [add_comm (Polynomial.C _), natDegree_X_pow_add_C, mul_comm])
  have hbound (u : Fin (n + 1) →₀ ℕ) (hu : u ∈ f.support) :
      ∀ l ∈ ofFn u, l < up := by
    intro l hl
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    exact lt_of_le_of_lt
      ((monomial_le_degreeOf i hu).trans (degreeOf_le_totalDegree f i)) (by omega)
  have hdegree_ne (u z : Fin (n + 1) →₀ ℕ)
      (hu : u ∈ f.support) (hz : z ∈ f.support) (hne : u ≠ z) :
      (varChange f (monomial u (f.coeff u))).degreeOf 0 ≠
        (varChange f (monomial z (f.coeff z))).degreeOf 0 := by
    rw [hdeg u (mem_support_iff.mp hu), hdeg z (mem_support_iff.mp hz)]
    intro he
    refine hne <| Finsupp.ext <| congrFun <| ofFn_inj.mp ?_
    apply ofDigits_inj_of_len_eq (Nat.lt_add_right f.totalDegree one_lt_two)
      (by simp) (hbound u hu) (hbound z hz)
    simpa only [ofDigits_eq_sum_mapIdx, mapIdx_eq_ofFn, get_ofFn, length_ofFn,
      Fin.val_cast, mul_comm, sum_ofFn] using! he
  have hlc (u : Fin (n + 1) →₀ ℕ) :
      (finSuccEquiv k n (varChange f (monomial u (f.coeff u)))).leadingCoeff =
        algebraMap k _ (f.coeff u) := by
    rw [monomial_eq, Finsupp.prod_fintype]
    · simp only [map_mul, map_prod, leadingCoeff_mul, leadingCoeff_prod]
      rw [AlgEquiv.ofAlgHom_apply, algHom_C, algebraMap_eq, finSuccEquiv_apply,
        eval₂Hom_C, coe_comp]
      simp only [AlgEquiv.ofAlgHom_apply, Function.comp_apply, leadingCoeff_C,
        map_pow, leadingCoeff_pow, algebraMap_eq]
      have hx : ∀ j, (finSuccEquiv k n (T1 f 1 (X j))).leadingCoeff = 1 := by
        intro j
        by_cases hj : j = 0
        · simp [hj, finSuccEquiv_apply]
        · simp only [aeval_eq_bind₁, bind₁_X_right, ite_eq_right hj, one_smul,
            map_add, map_pow]
          obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr hj
          simp [finSuccEquiv_X_succ, finSuccEquiv_X_zero, add_comm]
      simp only [hx, one_pow, Finset.prod_const_one, mul_one]
    · exact fun i ↦ pow_zero _
  obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image f.support
    (fun u ↦ (varChange f (monomial u (f.coeff u))).degreeOf 0)
    (support_nonempty.mpr fne)
  set h := fun u ↦ MvPolynomial.monomial u (f.coeff u)
  simp only [← natDegree_finSuccEquiv] at hmax
  have hlt : ∀ x ∈ f.support \ {u},
      (finSuccEquiv k n (varChange f (h x))).degree <
        (finSuccEquiv k n (varChange f (h u))).degree := by
    intro x hx
    obtain ⟨hx, hxu⟩ := Finset.mem_sdiff.mp hx
    apply degree_lt_degree <| lt_of_le_of_ne (hmax x hx) ?_
    simpa only [natDegree_finSuccEquiv] using
      hdegree_ne x u hx hu (ne_of_not_mem_cons hxu)
  have hcoeff :
      (finSuccEquiv k n (varChange f
        (h u + ∑ x ∈ f.support \ {u}, h x))).leadingCoeff =
      (finSuccEquiv k n (varChange f (h u))).leadingCoeff := by
    simp only [map_add, map_sum]
    rw [add_comm]
    apply leadingCoeff_add_of_degree_lt <| (lt_of_le_of_lt <| degree_sum_le _ _) ?_
    have hn : h u ≠ 0 := by
      simpa [h] using mem_support_iff.mp hu
    have hn' : finSuccEquiv k n (varChange f (h u)) ≠ 0 := by
      intro he
      apply hn
      simpa only [map_eq_zero_iff _ (AlgEquiv.injective _)] using he
    exact (Finset.sup_lt_iff
      (Ne.bot_lt (fun he ↦ hn' (degree_eq_bot.mp he)))).mpr hlt
  nth_rw 2 [← f.support_sum_monomial_coeff]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hu h]
  rw [hlc] at hcoeff
  simpa only [hcoeff, algebraMap_eq] using
    (mem_support_iff.mp hu).isUnit.map MvPolynomial.C
