/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.StronglyMeasurable.setToFun_prod_right
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/Integral/SetToL1/DominatedConvergence.lean, line 253
             (added after the model's training data; human proof 42 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 8 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem StronglyMeasurable.setToFun_prod_right {β : Type*} {mβ : MeasurableSpace β} [SFinite μ]
    (hT : DominatedFinMeasAdditive μ T C)
    (h'T : ∀ (s : Set (β × α)), MeasurableSet s → StronglyMeasurable fun x => T (Prod.mk x ⁻¹' s))
    ⦃f : β → α → E⦄ (hf : StronglyMeasurable (Function.uncurry f)) :
    StronglyMeasurable fun x => setToFun μ T hT (f x) := by
  classical
  by_cases hF : CompleteSpace F
  · letI := hF
    borelize E
    have hzero : T ∅ = 0 := by
      apply norm_eq_zero.mp
      apply le_antisymm _ (norm_nonneg _)
      obtain ⟨hadd, hbound⟩ := hT
      simpa using hbound ∅ MeasurableSet.empty (by simp)
    have hsimple (s : SimpleFunc (β × α) E) :
        StronglyMeasurable fun x => setToFun μ T hT (fun a => s (x, a)) := by
      have hsum :
          StronglyMeasurable fun x =>
            ∑ c ∈ s.range, T (Prod.mk x ⁻¹' (s ⁻¹' {c})) c :=
        s.range.stronglyMeasurable_fun_sum fun c _ =>
          (ContinuousLinearMap.apply ℝ F c).continuous.comp_stronglyMeasurable
            (h'T _ (s.measurableSet_fiber c))
      have hi : MeasurableSet {x | Integrable (fun a => s (x, a)) μ} :=
        measurableSet_integrable s.stronglyMeasurable
      let g : β → F := fun x =>
        if Integrable (fun a => s (x, a)) μ then
          ∑ c ∈ s.range, T (Prod.mk x ⁻¹' (s ⁻¹' {c})) c
        else 0
      have hg : StronglyMeasurable g :=
        hsum.piecewise hi
          (show StronglyMeasurable (fun _ : β => (0 : F)) from
            stronglyMeasurable_const)
      have heq : (fun x => setToFun μ T hT (fun a => s (x, a))) = g := by
        funext x
        by_cases hx : Integrable (fun a => s (x, a)) μ
        · simp only [g, hx, ↓reduceIte]
          let sx : SimpleFunc α E := s.comp (Prod.mk x) measurable_prodMk_left
          change setToFun μ T hT sx = _
          rw [setToFun_simpleFunc hT sx hx]
          change (∑ c ∈ sx.range, T (Prod.mk x ⁻¹' (s ⁻¹' {c})) c) =
            ∑ c ∈ s.range, T (Prod.mk x ⁻¹' (s ⁻¹' {c})) c
          apply Finset.sum_subset
          · intro c hc
            obtain ⟨a, ha⟩ := SimpleFunc.mem_range.mp hc
            exact SimpleFunc.mem_range.mpr ⟨(x, a), ha⟩
          · intro c _ hc
            have hempty : Prod.mk x ⁻¹' (s ⁻¹' {c}) = ∅ := by
              ext a
              simp only [Set.mem_preimage, Set.mem_singleton_iff,
                Set.mem_empty_iff_false, iff_false]
              intro ha
              exact hc (SimpleFunc.mem_range.mpr ⟨a, ha⟩)
            simp [hempty, hzero]
        · simp [g, hx, setToFun_undef _ hx]
      rw [heq]
      exact hg
    have hf' := hf
    obtain ⟨s, hs⟩ := hf'
    let u (n : ℕ) : SimpleFunc (β × α) E :=
      SimpleFunc.piecewise
        {p | ‖s n p‖ ≤ 2 * ‖Function.uncurry f p‖}
        (measurableSet_le (s n).stronglyMeasurable.norm
          (stronglyMeasurable_const.mul hf.norm))
        (s n) 0
    have hu_bound (n : ℕ) (p : β × α) :
        ‖u n p‖ ≤ 2 * ‖Function.uncurry f p‖ := by
      change ‖if ‖s n p‖ ≤ 2 * ‖Function.uncurry f p‖ then s n p else (0 : E)‖ ≤
        2 * ‖Function.uncurry f p‖
      split_ifs with h
      · exact h
      · simp only [norm_zero]
        positivity
    have hu_lim (p : β × α) :
        Tendsto (fun n => u n p) atTop (𝓝 (Function.uncurry f p)) := by
      by_cases hp : Function.uncurry f p = 0
      · have hz (n : ℕ) : u n p = 0 := by
          apply norm_eq_zero.mp
          exact le_antisymm (by simpa [hp] using hu_bound n p) (norm_nonneg _)
        simpa only [hz, hp] using tendsto_const_nhds
      · have he :
            ∀ᶠ n in atTop, ‖s n p‖ < 2 * ‖Function.uncurry f p‖ :=
          (hs p).norm.eventually_lt_const (by
            have := norm_pos_iff.mpr hp
            linarith)
        apply (hs p).congr'
        filter_upwards [he] with n hn
        simp [u, hn.le]
    let A : Set β := {x | Integrable (f x) μ}
    have hA : MeasurableSet A := measurableSet_integrable hf
    have hmeas (n : ℕ) :
        StronglyMeasurable
          (A.indicator fun x => setToFun μ T hT (fun a => u n (x, a))) :=
      (hsimple (u n)).indicator hA
    apply stronglyMeasurable_of_tendsto (atTop : Filter ℕ) hmeas
    rw [tendsto_pi_nhds]
    intro x
    by_cases hx : Integrable (f x) μ
    · simp only [Set.indicator_of_mem (show x ∈ A from hx)]
      exact tendsto_setToFun_of_dominated_convergence hT
        (fs := fun n a => u n (x, a)) (f := f x)
        (fun a => 2 * ‖f x a‖)
        (fun n => ((u n).stronglyMeasurable.comp_measurable
          measurable_prodMk_left).aestronglyMeasurable)
        (hx.norm.const_mul 2)
        (fun n => Filter.Eventually.of_forall fun a => hu_bound n (x, a))
        (Filter.Eventually.of_forall fun a => hu_lim (x, a))
    · simp [A, hx, setToFun_undef _ hx]
  · simpa [setToFun, hF] using
      (stronglyMeasurable_const : StronglyMeasurable (fun _ : β => (0 : F)))
