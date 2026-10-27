/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Metric.image_homothety_closedBall_of_nonneg
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Affine/AddTorsor.lean, line 159
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

noncomputable section
open NNReal
variable {V P W Q : Type*} [SeminormedAddCommGroup V] [PseudoMetricSpace P] [NormedAddTorsor V P]
section NormedSpace
variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] [NormedSpace 𝕜 W]
open AffineMap
open scoped Pointwise in

theorem Metric.image_homothety_closedBall_of_nonneg (p c : Q) {r : ℝ} (hr : 0 ≤ r) (x : 𝕜) :
    homothety c x '' closedBall p r = closedBall (homothety c x p) (‖x‖ * r) := by
  by_cases hx : x = 0
  · subst x
    have hzero (a : Q) : homothety c (0 : 𝕜) a = c := by
      change (0 : 𝕜) • (a -ᵥ c) +ᵥ c = c
      simp
    calc
      homothety c (0 : 𝕜) '' closedBall p r = {c} := by
        ext q
        constructor
        · rintro ⟨a, _, rfl⟩
          exact Set.mem_singleton_iff.mpr (hzero a)
        · intro hq
          have hqc : q = c := Set.mem_singleton_iff.mp hq
          subst q
          exact ⟨p, by simpa using hr, hzero p⟩
      _ = _ := by
        simp only [hzero, norm_zero, zero_mul, closedBall_zero]
  · have hdist (a b : Q) :
        dist (homothety c x a) (homothety c x b) =
          ‖x‖ * dist a b := by
      have h :
          homothety c x a -ᵥ homothety c x b = x • (a -ᵥ b) := by
        change (x • (a -ᵥ c) +ᵥ c) -ᵥ
            (x • (b -ᵥ c) +ᵥ c) = x • (a -ᵥ b)
        simp only [vadd_vsub_vadd_cancel_right, ← smul_sub,
          vsub_sub_vsub_cancel_right]
      simpa only [dist_eq_norm_vsub, norm_smul] using
        congrArg (fun v => ‖v‖) h
    ext q
    constructor
    · rintro ⟨a, ha, rfl⟩
      change dist (homothety c x a) (homothety c x p) ≤ ‖x‖ * r
      rw [hdist]
      exact mul_le_mul_of_nonneg_left ha (norm_nonneg x)
    · intro hq
      let a := x⁻¹ • (q -ᵥ c) +ᵥ c
      have ha : homothety c x a = q := by
        change x • ((x⁻¹ • (q -ᵥ c) +ᵥ c) -ᵥ c) +ᵥ c = q
        simp [smul_smul, hx]
      refine ⟨a, ?_, ha⟩
      have h : ‖x‖ * dist a p ≤ ‖x‖ * r := by
        rw [← hdist, ha]
        exact hq
      have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      change dist a p ≤ r
      nlinarith
