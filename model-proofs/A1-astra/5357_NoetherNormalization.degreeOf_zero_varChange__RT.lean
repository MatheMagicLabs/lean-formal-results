/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.degreeOf_zero_varChange
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 100
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 2 (round 0 = first attempt)
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

private lemma degreeOf_zero_varChange {a : k} (ha : a ≠ 0) :
    ((varChange f) (monomial v a)).degreeOf 0 = ∑ i : Fin (n + 1), (r i) * v i := by
  classical
  have hmul (p q : MvPolynomial (Fin (n + 1)) k)
      (hp : p ≠ 0) (hq : q ≠ 0) :
      (p * q).degreeOf 0 = p.degreeOf 0 + q.degreeOf 0 := by
    simp_rw [MvPolynomial.degreeOf_eq_natDegree, map_mul,
      ← MvPolynomial.renameEquiv_apply]
    rw [Polynomial.natDegree_mul] <;>
      simpa [-MvPolynomial.renameEquiv_apply, EmbeddingLike.map_eq_zero_iff]
  have hpow (p : MvPolynomial (Fin (n + 1)) k) (hp : p ≠ 0)
      (m : ℕ) : (p ^ m).degreeOf 0 = m * p.degreeOf 0 := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, hmul _ _ (pow_ne_zero _ hp) hp, ih, Nat.succ_mul]
  let g : Fin (n + 1) → MvPolynomial (Fin (n + 1)) k :=
    fun i ↦ if i = 0 then X 0 else X i + X 0 ^ r i
  have hr : ∀ i : Fin (n + 1), 0 < r i := by
    intro i
    exact pow_pos (by omega) _
  have hd : ∀ i, (g i).degreeOf 0 = r i := by
    intro i
    by_cases hi : i = 0
    · subst i
      simp [g]
    · have hlt :
          (X i : MvPolynomial (Fin (n + 1)) k).degreeOf 0 <
            (X 0 ^ r i : MvPolynomial (Fin (n + 1)) k).degreeOf 0 := by
        simpa [MvPolynomial.degreeOf_X, hi, Ne.symm hi] using hr i
      simpa [g, hi, add_comm] using
        (MvPolynomial.degreeOf_add_eq_of_degreeOf_lt hlt)
  have hg : ∀ i, g i ≠ 0 := by
    intro i hz
    have hp : 0 < (g i).degreeOf 0 := by
      rw [hd i]
      exact hr i
    simpa [hz] using hp
  have hp : ∀ i, g i ^ v i ≠ 0 :=
    fun i ↦ pow_ne_zero _ (hg i)
  have hprod (s : Finset (Fin (n + 1))) :
      (∏ i ∈ s, g i ^ v i).degreeOf 0 =
        ∑ i ∈ s, (g i ^ v i).degreeOf 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi,
        hmul _ _ (hp i)
          (Finset.prod_ne_zero_iff.mpr (fun j _ ↦ hp j)), ih]
  change
    (MvPolynomial.aeval (fun i : Fin (n + 1) ↦
      if i = 0 then X 0 else X i + (1 : k) • X 0 ^ r i)
      (MvPolynomial.monomial v a)).degreeOf 0 = _
  simp only [one_smul, MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  change (MvPolynomial.C a * v.prod (fun i m ↦ g i ^ m)).degreeOf 0 = _
  rw [v.prod_fintype _ (fun _ ↦ pow_zero _)]
  rw [hmul _ _ (MvPolynomial.C_ne_zero.mpr ha)
    (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hp i)),
    MvPolynomial.degreeOf_C, zero_add, hprod]
  apply Finset.sum_congr rfl
  intro i _
  rw [hpow _ (hg i), hd i, mul_comm]
