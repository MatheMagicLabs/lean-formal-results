/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.VectorMeasure.variation_withDensity'
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/VectorMeasure/WithDensityVec.lean, line 106
             (added after the model's training data; human proof 142 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 5 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma variation_withDensity' [CompleteSpace G]
    (hf : μ.Integrable f) (hB : ∀ x y, ‖B x y‖₊ = ‖B.flip y‖₊ * ‖x‖₊) :
    (μ.withDensity f B).variation = (μ.transpose B).variation.withDensity (fun x ↦ ‖f x‖ₑ) := by
  classical
  apply le_antisymm variation_WithDensity_le
  apply Measure.le_iff.2 (fun s hs ↦ ?_)
  rw [MeasureTheory.withDensity_apply _ hs]
  apply ENNReal.le_of_forall_pos_le_add
  rintro ε εpos -
  let δ := ε / 3
  have δpos : 0 < δ := div_pos εpos (by norm_num)
  obtain ⟨g, hg, gmem⟩ : ∃ (g : X →ₛ E), eLpNorm (f - ⇑g) 1 (μ.transpose B).variation ≤ δ ∧ MemLp (⇑g) 1 μ.variation := by {
  obtain ⟨ρ, ρpos, hδ⟩ : ∃ ρ > 0, ‖B‖₊ * ρ ≤ δ := by {
  rcases eq_or_ne (‖B‖₊) 0 with h | h
  { exact ⟨1, zero_lt_one, by simp [h]⟩ }
  refine ⟨‖B‖₊ ⁻¹ * δ, by positivity, ?_⟩
  rw [← mul_assoc]
  apply mul_le_of_le_one_left (by positivity) mul_inv_le_one
  }
  obtain ⟨g, h'g, gmem⟩ : ∃ (g : X →ₛ E), eLpNorm (f - ⇑g) 1 μ.variation < ρ ∧ MemLp (⇑g) 1 μ.variation := (memLp_one_iff_integrable.2 hf).exists_simpleFunc_eLpNorm_sub_lt (by simp) (by simpa using ρpos.ne')
  have hfg : AEStronglyMeasurable (f - ⇑g) μ.variation := aestronglyMeasurable_of_eLpNorm_ne_top (ne_of_lt (h'g.trans_le le_top))
  refine ⟨g, ?_, gmem⟩
  refine (eLpNorm_mono_measure _ (variation_transpose_le μ B)).trans ?_
  rw [eLpNorm_smul_measure_of_ne_top' (p := 1) (μ := μ.variation) (by simp) ‖B‖₊ (f - ⇑g) hfg]
  grw [h'g.le]
  simp only [ENNReal.toReal_one, inv_one, NNReal.rpow_one, ENNReal.smul_def, smul_eq_mul]
  exact_mod_cast hδ
  }
  have I1 : ∫⁻ a in s, ‖f a‖ₑ ∂(μ.transpose B).variation ≤ ∫⁻ a in s, ‖g a‖ₑ ∂(μ.transpose B).variation + δ := by {
  calc
  _ ≤ ∫⁻ a in s, ‖f a - g a‖ₑ + ‖g a‖ₑ ∂(μ.transpose B).variation := by {
  apply lintegral_mono
  intro a
  change ‖f a‖ₑ ≤ ‖f a - g a‖ₑ + ‖g a‖ₑ
  nth_rw 1 [show f a = (f a - g a) + g a by abel]
  exact enorm_add_le (f a - g a) (g a)
  }
  _ = (∫⁻ a in s, ‖g a‖ₑ ∂(μ.transpose B).variation) + ∫⁻ a in s, ‖f a - g a‖ₑ ∂(μ.transpose B).variation := by {
  rw [lintegral_add_right, add_comm]
  exact g.stronglyMeasurable.enorm
  }
  _ ≤ (∫⁻ a in s, ‖g a‖ₑ ∂(μ.transpose B).variation) + ∫⁻ a, ‖f a - g a‖ₑ ∂(μ.transpose B).variation := by {
  refine add_le_add le_rfl ?_
  exact lintegral_mono' Measure.restrict_le_self le_rfl
  }
  _ ≤ (∫⁻ a in s, ‖g a‖ₑ ∂(μ.transpose B).variation) + δ := by {
  rw [eLpNorm_one_eq_lintegral_enorm (aestronglyMeasurable_of_eLpNorm_ne_top (ne_of_lt (hg.trans_lt ENNReal.coe_lt_top)))] at hg
  exact add_le_add le_rfl hg
  }
  }
  have I2 : ∫⁻ a in s, ‖g a‖ₑ ∂(μ.transpose B).variation = ∑ i ∈ g.range, ‖i‖ₑ * ((μ.transpose B).restrict s).variation (g ⁻¹' {i}) := by {
  calc
  _ = (g.map (‖·‖ₑ)).lintegral ((μ.transpose B).variation.restrict s) := SimpleFunc.lintegral_eq_lintegral _ _
  _ = ∑ i ∈ g.range, ‖i‖ₑ * (μ.transpose B).variation.restrict s (g ⁻¹' {i}) := SimpleFunc.map_lintegral _ _
  _ = ∑ i ∈ g.range, ‖i‖ₑ * ((μ.transpose B).restrict s).variation (g ⁻¹' {i}) := by simp_rw [variation_restrict hs]
  }
  obtain ⟨ρ, ρpos, hρ⟩ : ∃ ρ > 0, ∑ i ∈ g.range, ‖i‖ₑ * ρ ≤ δ := by {
  refine ⟨δ * (∑ i ∈ g.range, ‖i‖ₑ)⁻¹, by simp [δpos], ?_⟩
  grw [← Finset.sum_mul, mul_comm (δ : ℝ≥0∞), ← mul_assoc, ENNReal.mul_inv_le_one, one_mul]
  }
  have C i : ∃ (P : Finset (Set X)), (∀ t ∈ P, t ⊆ g ⁻¹' {i}) ∧ ((P : Set (Set X)).PairwiseDisjoint id) ∧ (∀ t ∈ P, MeasurableSet t) ∧ ‖i‖ₑ * ((μ.transpose B).restrict s).variation (g ⁻¹' {i}) ≤ ‖i‖ₑ * (∑ p ∈ P, ‖(μ.transpose B).restrict s p‖ₑ + ρ) := by {
  rcases eq_or_ne i 0 with rfl | hi
  { exact ⟨∅, by simp⟩ }
  suffices ∃ (P : Finset (Set X)), (∀ t ∈ P, t ⊆ g ⁻¹' {i}) ∧ ((P : Set (Set X)).PairwiseDisjoint id) ∧ (∀ t ∈ P, MeasurableSet t) ∧ ((μ.transpose B).restrict s).variation (g ⁻¹' {i}) ≤ (∑ p ∈ P, ‖(μ.transpose B).restrict s p‖ₑ + ρ) by {
  obtain ⟨P, hP, h'P, h''P, h'''P⟩ := this
  exact ⟨P, hP, h'P, h''P, by gcongr⟩
  }
  apply exists_variation_le_add' _ (g.measurableSet_fiber i) ρpos
  rw [variation_restrict hs]
  have : MemLp (⇑g) 1 (μ.transpose B).variation := gmem.of_measure_le_smul (c := ‖B‖₊) (by simp) (variation_transpose_le _ _)
  exact (g.integrable_iff.1 (memLp_one_iff_integrable.1 this).restrict i hi).ne
  }
  choose P Pg Pdisj Pmeas hP using C
  have fibers_disjoint {i j : E} (hij : i ≠ j) : Disjoint (g ⁻¹' {i}) (g ⁻¹' {j}) := by {
  apply disjoint_left.2
  intro x hx hy
  simp only [mem_preimage, mem_singleton_iff] at hx hy
  exact hij (hx.symm.trans hy)
  }
  have I3 : ∑ i ∈ g.range, ‖i‖ₑ * ((μ.transpose B).restrict s).variation (g ⁻¹' {i}) ≤ ∑ i ∈ g.range.sigma P, ‖i.1‖ₑ * ‖(μ.transpose B).restrict s i.2‖ₑ + δ := by {
  calc
  _ ≤ ∑ i ∈ g.range, ‖i‖ₑ * ((∑ p ∈ P i, ‖(μ.transpose B).restrict s p‖ₑ) + ρ) := by {
  apply Finset.sum_le_sum
  intro i hi
  exact hP i
  }
  _ ≤ (∑ i ∈ g.range, ∑ p ∈ P i, ‖i‖ₑ * ‖(μ.transpose B).restrict s p‖ₑ) + δ := by {
  simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  exact add_le_add le_rfl hρ
  }
  _ = (∑ i ∈ g.range.sigma P, ‖i.1‖ₑ * ‖(μ.transpose B).restrict s i.2‖ₑ) + δ := by rw [Finset.sum_sigma']
  }
  have I4 : ∑ i ∈ g.range.sigma P, ‖i.1‖ₑ * ‖(μ.transpose B).restrict s i.2‖ₑ ≤ ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ + δ := by {
  calc
  _ = ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, i.1 ∂[B; μ.restrict s]‖ₑ := by {
  congr! with ⟨i, p⟩ hi
  rcases eq_or_ne i 0 with rfl | h'i
  { simp }
  simp only [Finset.mem_sigma] at hi
  have pmeas : MeasurableSet p := Pmeas i _ hi.2
  have : IsFiniteMeasure ((μ.restrict s).variation.restrict p) := by {
  constructor
  rw [variation_restrict hs, Measure.restrict_restrict pmeas, MeasureTheory.Measure.restrict_apply_univ]
  apply lt_of_le_of_lt ?_ (g.integrable_iff.1 (memLp_one_iff_integrable.1 gmem) i h'i)
  exact measure_mono (inter_subset_left.trans (Pg i _ hi.2))
  }
  rw [setIntegral_const, restrict_apply _ hs pmeas, restrict_apply _ hs pmeas]
  simp [transpose, hB, enorm_eq_nnnorm, mul_comm]
  }
  _ = ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, g x ∂[B; μ.restrict s]‖ₑ := by {
  congr! 2 with ⟨i, p⟩ hi
  simp only [Finset.mem_sigma] at hi
  apply setIntegral_congr_ae
  filter_upwards with x hx using (Pg i _ hi.2 hx).symm
  }
  _ = ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, (g x - f x) + f x ∂[B; μ.restrict s]‖ₑ := by simp
  _ = ∑ i ∈ g.range.sigma P, ‖(∫ᵛ x in i.2, (g x - f x) ∂[B; μ.restrict s]) + ∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ := by {
  congr! with i hi
  rw [integral_fun_add]
  {
  apply Integrable.restrict
  apply Integrable.restrict
  exact Integrable.sub (memLp_one_iff_integrable.1 gmem) hf
  }
  { exact hf.restrict.restrict }
  }
  _ ≤ (∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, (g x - f x) ∂[B; μ.restrict s]‖ₑ) + ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ := by {
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  exact enorm_add_le _ _
  }
  _ ≤ (∑ i ∈ g.range.sigma P, ∫⁻ x in i.2, ‖g x - f x‖ₑ ∂(μ.transpose B).variation) + ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ := by {
  refine add_le_add ?_ le_rfl
  apply Finset.sum_le_sum
  intro i hi
  grw [enorm_setIntegral_le_lintegral_enorm_transpose]
  apply lintegral_mono' _ le_rfl
  apply Measure.restrict_mono le_rfl
  rw [transpose_restrict, variation_restrict hs]
  exact Measure.restrict_le_self
  }
  _ = (∫⁻ x in (⋃ i ∈ g.range.sigma P, i.2), ‖g x - f x‖ₑ ∂(μ.transpose B).variation) + ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ := by {
  rw [lintegral_biUnion_finset]
  {
  rintro ⟨i, p⟩ hi ⟨j, q⟩ hj hijpq
  simp only [Finset.coe_sigma, SimpleFunc.coe_range, mem_sigma_iff, mem_range, SetLike.mem_coe] at hi hj
  rcases eq_or_ne i j with rfl | hij
  {
  simp only [ne_eq, Sigma.mk.injEq, heq_eq_eq, true_and] at hijpq
  exact Pdisj i hi.2 hj.2 hijpq
  }
  { exact (fibers_disjoint hij).mono (Pg i p hi.2) (Pg j q hj.2) }
  }
  {
  rintro ⟨i, p⟩ hip
  simp only [Finset.mem_sigma, SimpleFunc.mem_range, mem_range] at hip
  exact Pmeas i p hip.2
  }
  }
  _ ≤ (∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ) + ∫⁻ x, ‖g x - f x‖ₑ ∂(μ.transpose B).variation := by {
  rw [add_comm]
  refine add_le_add le_rfl ?_
  exact lintegral_mono' Measure.restrict_le_self le_rfl
  }
  _ ≤ (∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ) + δ := by {
  refine add_le_add le_rfl ?_
  simp_rw [enorm_sub_rev]
  change ∫⁻ x, ‖(f - ⇑g) x‖ₑ ∂(μ.transpose B).variation ≤ ↑δ
  rw [← eLpNorm_one_eq_lintegral_enorm (aestronglyMeasurable_of_eLpNorm_ne_top (ne_of_lt (hg.trans_lt ENNReal.coe_lt_top)))]
  exact hg
  }
  }
  have I5 : ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ ≤ (μ.withDensity f B).variation s := by {
  let Q : Finset (Set X) := (g.range.sigma P).image (fun p ↦ p.2 ∩ s)
  calc
  ∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ = ∑ j ∈ Q, ‖∫ᵛ x in j, f x ∂[B; μ]‖ₑ := by {
  simp only [Q]
  rw [Finset.sum_image_of_pairwise_eq_zero]
  swap
  {
  rintro ⟨i, p⟩ hi ⟨j, q⟩ hj hijpq h'ij
  simp only [Finset.coe_sigma, SimpleFunc.coe_range, mem_sigma_iff, mem_range, SetLike.mem_coe] at hi hj
  suffices H : Disjoint p q by {
  have : Disjoint (p ∩ s) (q ∩ s) := H.mono inter_subset_left inter_subset_left
  rw [← h'ij, disjoint_self] at this
  simp [this]
  }
  rcases eq_or_ne i j with rfl | hij
  {
  simp only [ne_eq, Sigma.mk.injEq, heq_eq_eq, true_and] at hijpq
  exact Pdisj i hi.2 hj.2 hijpq
  }
  { exact (fibers_disjoint hij).mono (Pg i p hi.2) (Pg j q hj.2) }
  }
  apply Finset.sum_congr rfl
  rintro ⟨i, p⟩ hi
  simp only [Finset.mem_sigma, SimpleFunc.mem_range, mem_range] at hi
  rw [restrict_restrict _ (Pmeas i p hi.2) hs]
  }
  _ = ∑ j ∈ Q, ‖μ.withDensity f B j‖ₑ := Finset.sum_congr rfl (fun t ht ↦ by rw [withDensity_apply hf])
  _ ≤ (μ.withDensity f B).variation s := by {
  apply le_variation _ hs
  {
  intro t ht
  simp only [Finset.mem_image, Finset.mem_sigma, SimpleFunc.mem_range, mem_range, Sigma.exists, ↓existsAndEq, true_and, exists_and_right, Q] at ht
  rcases ht with ⟨p, -, rfl⟩
  exact inter_subset_right
  }
  {
  intro t ht u hu htu
  simp only [Finset.coe_image, Finset.coe_sigma, SimpleFunc.coe_range, mem_image, mem_sigma_iff, mem_range, SetLike.mem_coe, Sigma.exists, ↓existsAndEq, true_and, exists_and_right, Q] at ht hu
  rcases ht with ⟨p, ⟨i, hi⟩, rfl⟩
  rcases hu with ⟨q, ⟨j, hj⟩, rfl⟩
  have hpq : p ≠ q := fun hpq ↦ htu (congrArg (fun a : Set X ↦ a ∩ s) hpq)
  suffices H : Disjoint p q from H.mono inter_subset_left inter_subset_left
  rcases eq_or_ne (g i) (g j) with hij | hij
  {
  rw [← hij] at hj
  exact Pdisj (g i) hi hj hpq
  }
  { exact (fibers_disjoint hij).mono (Pg (g i) p hi) (Pg (g j) q hj) }
  }
  }
  }
  calc
  ∫⁻ a in s, ‖f a‖ₑ ∂(μ.transpose B).variation ≤ (∫⁻ a in s, ‖g a‖ₑ ∂(μ.transpose B).variation) + δ := I1
  _ = (∑ i ∈ g.range, ‖i‖ₑ * ((μ.transpose B).restrict s).variation (g ⁻¹' {i})) + δ := by rw [I2]
  _ ≤ ((∑ i ∈ g.range.sigma P, ‖i.1‖ₑ * ‖(μ.transpose B).restrict s i.2‖ₑ) + δ) + δ := add_le_add I3 le_rfl
  _ ≤ (((∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ) + δ) + δ) + δ := add_le_add (add_le_add I4 le_rfl) le_rfl
  _ = (∑ i ∈ g.range.sigma P, ‖∫ᵛ x in i.2, f x ∂[B; μ.restrict s]‖ₑ) + 3 * δ := by ring
  _ ≤ (μ.withDensity f B).variation s + 3 * δ := add_le_add I5 le_rfl
  _ ≤ (μ.withDensity f B).variation s + ε := by {
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_div, ENNReal.coe_ofNat, δ]
  rw [ENNReal.mul_div_cancel (by simp) (by simp)]
  }
