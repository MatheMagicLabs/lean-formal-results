/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.VectorMeasure.variation_withDensity'
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/VectorMeasure/WithDensityVec.lean, line 106
             (added after the model's training data; human proof 142 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 6 call(s)
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
  have hsimple (g : X →ₛ E) (hg : μ.Integrable g) : (μ.withDensity g B).variation univ = ∫⁻ x, ‖g x‖ₑ ∂(μ.transpose B).variation := by {
  rw [← g.sum_range_measure_preimage_singleton (μ.withDensity g B).variation];
  change _ = ∫⁻ x, (g.map (fun z ↦ ‖z‖ₑ)) x ∂(μ.transpose B).variation;
  rw [SimpleFunc.lintegral_eq_lintegral, SimpleFunc.map_lintegral];
  apply Finset.sum_congr rfl;
  intro c hc;
  let r := g ⁻¹' {c};
  have hr : MeasurableSet r := g.measurableSet_fiber c;
  have hn : (fun t ↦ ‖((μ.withDensity g B).restrict r) t‖ₑ) = (fun t ↦ ‖(‖c‖ • (μ.transpose B).restrict r) t‖ₑ) := by {
  funext t;
  by_cases ht : MeasurableSet t;
  · {
  rw [restrict_apply _ hr ht, withDensity_apply hg, smul_apply, restrict_apply _ hr ht];
  have hi : ∫ᵛ x in t ∩ r, g x ∂[B; μ] = B c (μ (t ∩ r)) := by {
  rw [setIntegral_congr_fun (g := fun _ ↦ c) (fun x hx ↦ hx.2)];
  by_cases hcz : c = 0;
  · { simp [hcz] }
  · {
  have hfin : μ.variation (t ∩ r) < ∞ := (measure_mono inter_subset_right).trans_lt (g.measure_preimage_lt_top_of_integrable hg hcz);
  haveI : IsFiniteMeasure (μ.variation.restrict (t ∩ r)) := isFiniteMeasure_restrict.mpr hfin.ne;
  exact setIntegral_const c } };
  rw [hi];
  change ‖B c (μ (t ∩ r))‖ₑ = ‖‖c‖ • B.flip (μ (t ∩ r))‖ₑ;
  simp [enorm_eq_nnnorm, nnnorm_smul, hB, mul_comm] }
  · { simp only [not_measurable _ ht, enorm_zero] } };
  have hv : ((μ.withDensity g B).restrict r).variation = (‖c‖ • (μ.transpose B).restrict r).variation := by {
  unfold variation;
  congr 1 };
  simp only [variation_smul, variation_restrict hr] at hv;
  have hv' := congrArg (fun m : Measure X ↦ m univ) hv;
  simpa [Measure.smul_apply, Measure.restrict_apply, enorm_eq_nnnorm, r] using hv' }
  have hfT : MeasureTheory.Integrable f (μ.transpose B).variation := hf.smul_measure_nnreal.mono_measure (variation_transpose_le μ B)
  have hfSum : MeasureTheory.Integrable f (μ.variation + (μ.transpose B).variation) := hf.add_measure hfT
  have hle := variation_WithDensity_le (μ := μ) (f := f) (B := B)
  haveI : IsFiniteMeasure ((μ.transpose B).variation.withDensity (fun x ↦ ‖f x‖ₑ)) := isFiniteMeasure_withDensity (hasFiniteIntegral_iff_enorm.mp hfT.2).ne
  haveI : IsFiniteMeasure (μ.withDensity f B).variation := isFiniteMeasure_of_le _ hle
  apply Measure.eq_of_le_of_measure_univ_eq hle
  apply le_antisymm (hle univ)
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hfin
  have he : (0 : ℝ≥0∞) < ε := by exact_mod_cast hε
  have hehalf : (ε : ℝ≥0∞) / 2 ≠ 0 := (ENNReal.div_pos he.ne' (by norm_num)).ne'
  obtain ⟨g, hgerr, hgmem⟩ := (memLp_one_iff_integrable.mpr hfSum).exists_simpleFunc_eLpNorm_sub_lt ENNReal.one_ne_top hehalf
  have hgSum := memLp_one_iff_integrable.mp hgmem
  have hg : μ.Integrable g := hgSum.mono_measure (Measure.le_add_right le_rfl)
  have hgT : MeasureTheory.Integrable g (μ.transpose B).variation := hgSum.mono_measure (Measure.le_add_left le_rfl)
  rw [eLpNorm_one_eq_lintegral_enorm (hfSum.1.sub hgSum.1)] at hgerr
  let d := ∫⁻ x, ‖f x - g x‖ₑ ∂(μ.transpose B).variation
  have hd : d ≤ (ε : ℝ≥0∞) / 2 := (lintegral_mono' (Measure.le_add_left le_rfl) le_rfl).trans hgerr.le
  have htriangle : (∫⁻ x, ‖f x‖ₑ ∂(μ.transpose B).variation) ≤ (∫⁻ x, ‖g x‖ₑ ∂(μ.transpose B).variation) + d := by {
  rw [← lintegral_enorm_add_left hgT.1];
  apply lintegral_mono;
  intro x;
  have heq : f x = g x + (f x - g x) := by abel;
  calc
  ‖f x‖ₑ = ‖g x + (f x - g x)‖ₑ := congrArg (fun z ↦ ‖z‖ₑ) heq
  _ ≤ ‖g x‖ₑ + ‖f x - g x‖ₑ := enorm_add_le _ _ }
  have hsub : μ.withDensity g B = μ.withDensity f B - μ.withDensity (f - (g : X → E)) B := by {
  ext t ht;
  rw [sub_apply, withDensity_apply hg, withDensity_apply hf, withDensity_apply (hf.sub hg), integral_sub hf.restrict hg.restrict];
  exact (sub_sub_cancel _ _).symm }
  have hbound : (μ.withDensity g B).variation univ ≤ (μ.withDensity f B).variation univ + d := by {
  rw [hsub];
  calc
  (μ.withDensity f B - μ.withDensity (f - (g : X → E)) B).variation univ ≤ (μ.withDensity f B).variation univ + (μ.withDensity (f - (g : X → E)) B).variation univ := variation_sub_le univ
  _ ≤ (μ.withDensity f B).variation univ + d := by {
  refine add_le_add le_rfl ?_;
  simpa [MeasureTheory.withDensity_apply, MeasurableSet.univ, d] using (variation_WithDensity_le (μ := μ) (f := f - (g : X → E)) (B := B)) univ } }
  calc
  (∫⁻ x, ‖f x‖ₑ ∂(μ.transpose B).variation) ≤ (μ.withDensity g B).variation univ + d := by simpa only [hsimple g hg] using htriangle
  _ ≤ ((μ.withDensity f B).variation univ + d) + d := add_le_add hbound le_rfl
  _ = (μ.withDensity f B).variation univ + (d + d) := add_assoc _ _ _
  _ ≤ (μ.withDensity f B).variation univ + ((ε : ℝ≥0∞) / 2 + (ε : ℝ≥0∞) / 2) := add_le_add le_rfl (add_le_add hd hd)
  _ = (μ.withDensity f B).variation univ + ε := by rw [ENNReal.add_halves]
