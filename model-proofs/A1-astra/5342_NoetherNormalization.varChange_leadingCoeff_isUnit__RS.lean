/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.varChange_leadingCoeff_isUnit
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 147
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 1 (round 0 = first attempt)
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
  let p := fun v => finSuccEquiv k n (varChange f (monomial v (f.coeff v)))
  have hu (v) (hv : v ∈ f.support) : IsUnit (p v).leadingCoeff := by
    dsimp [p]
    rw [leadingCoeff_finSuccEquiv_varChange]
    exact (isUnit_iff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hv)).map
      (algebraMap k _)
  have hp (v) (hv : v ∈ f.support) : p v ≠ 0 := by
    intro h
    exact (hu v hv).ne_zero (by simp [h])
  have hd (v w) (hv : v ∈ f.support) (hw : w ∈ f.support)
      (hvw : v ≠ w) : (p v).degree ≠ (p w).degree := by
    have hv' : varChange f (monomial v (f.coeff v)) ≠ 0 := by
      intro h
      apply hp v hv
      dsimp only [p]
      rw [h, map_zero]
    have hw' : varChange f (monomial w (f.coeff w)) ≠ 0 := by
      intro h
      apply hp w hw
      dsimp only [p]
      rw [h, map_zero]
    dsimp [p]
    rw [MvPolynomial.degree_finSuccEquiv hv',
      MvPolynomial.degree_finSuccEquiv hw']
    exact_mod_cast
      (degreeOf_varChange_ne_of_ne (f := f) (v := v) (w := w) hv hw hvw)
  have hmax : ∀ s : Finset (Fin (n + 1) →₀ ℕ),
      s ⊆ f.support → s.Nonempty →
      ∃ v ∈ s, (∑ w ∈ s, p w).degree = (p v).degree ∧
        (∑ w ∈ s, p w).leadingCoeff = (p v).leadingCoeff := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      intro hs hn
      by_cases hsn : s.Nonempty
      · obtain ⟨b, hb, hbd, hbl⟩ :=
          ih (fun x hx => hs (Finset.mem_insert_of_mem hx)) hsn
        have hab : a ≠ b := by
          intro h
          exact ha (h ▸ hb)
        have hne : (p a).degree ≠ (∑ w ∈ s, p w).degree := by
          rw [hbd]
          exact hd a b (hs (Finset.mem_insert_self _ _))
            (hs (Finset.mem_insert_of_mem hb)) hab
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · refine ⟨b, Finset.mem_insert_of_mem hb, ?_, ?_⟩
          · rw [Finset.sum_insert ha,
              Polynomial.degree_add_eq_right_of_degree_lt hlt]
            exact hbd
          · rw [Finset.sum_insert ha,
              Polynomial.leadingCoeff_add_of_degree_lt hlt]
            exact hbl
        · refine ⟨a, Finset.mem_insert_self _ _, ?_, ?_⟩
          · rw [Finset.sum_insert ha, add_comm,
              Polynomial.degree_add_eq_right_of_degree_lt hgt]
          · rw [Finset.sum_insert ha, add_comm,
              Polynomial.leadingCoeff_add_of_degree_lt hgt]
      · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsn
        subst s
        refine ⟨a, Finset.mem_insert_self _ _, ?_, ?_⟩ <;> simp
  have hn : f.support.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    apply fne
    simpa using h
  obtain ⟨v, hv, _, hlc⟩ := hmax f.support (fun _ h => h) hn
  have hsum : finSuccEquiv k n (varChange f f) = ∑ v ∈ f.support, p v := by
    have hf : f = ∑ v ∈ f.support, monomial v (f.coeff v) := f.as_sum
    simpa only [map_sum] using
      congrArg (fun g => finSuccEquiv k n (varChange f g)) hf
  rw [hsum, hlc]
  exact hu v hv
