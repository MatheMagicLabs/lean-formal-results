/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.varChange_leadingCoeff_isUnit
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 147
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 2 (round 0 = first attempt)
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
  have hne : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact fne
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v ↦ (varChange f ((MvPolynomial.monomial v) (f.coeff v))).degreeOf 0) hne
  set h := fun w ↦ (MvPolynomial.monomial w) (f.coeff w) with hdef
  simp only [← natDegree_finSuccEquiv] at vs
  replace vs : ∀ x ∈ f.support.erase v, (finSuccEquiv k n ((varChange f) (h x))).degree <
      (finSuccEquiv k n ((varChange f) (h v))).degree := by
    intro x hx
    obtain ⟨h2, h1⟩ := Finset.mem_erase.mp hx
    apply degree_lt_degree <| lt_of_le_of_ne (vs x h1) ?_
    simpa only [natDegree_finSuccEquiv]
      using degreeOf_varChange_ne_of_ne _ _ _ h1 vin h2
  have hcoeff : (finSuccEquiv k n ((varChange f)
      (h v + ∑ x ∈ f.support.erase v, h x))).leadingCoeff =
      (finSuccEquiv k n ((varChange f) (h v))).leadingCoeff := by
    simp only [map_add, map_sum]
    rw [add_comm]
    apply leadingCoeff_add_of_degree_lt <| (lt_of_le_of_lt <| degree_sum_le _ _) ?_
    have h2 : h v ≠ 0 := by simpa [h] using MvPolynomial.mem_support_iff.mp vin
    replace h2 : (finSuccEquiv k n ((varChange f) (h v))) ≠ 0 := fun eq ↦ h2 <|
      by simpa only [map_eq_zero_iff _ (AlgEquiv.injective _)] using eq
    exact (Finset.sup_lt_iff <| Ne.bot_lt (fun x ↦ h2 <| degree_eq_bot.mp x)).mpr vs
  have hsum : f = h v + ∑ x ∈ f.support.erase v, h x := by
    rw [Finset.add_sum_erase _ _ vin]
    exact (f.support_sum_monomial_coeff).symm
  have hf : finSuccEquiv k n (varChange f f) =
      finSuccEquiv k n (varChange f (h v + ∑ x ∈ f.support.erase v, h x)) :=
    congrArg (fun p ↦ finSuccEquiv k n (varChange f p)) hsum
  have hlc : (finSuccEquiv k n (varChange f (h v))).leadingCoeff =
      algebraMap k _ (f.coeff v) := by
    first
      | exact leadingCoeff_finSuccEquiv_varChange f v
      | exact leadingCoeff_finSuccEquiv_varChange v f
      | exact leadingCoeff_finSuccEquiv_varChange
      | simpa [h] using leadingCoeff_finSuccEquiv_varChange f v
  rw [hf, hcoeff, hlc]
  exact ((MvPolynomial.mem_support_iff.mp vin).isUnit).map (algebraMap k _)
