/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.StronglyMeasurable.setToFun_prod_right
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/Integral/SetToL1/DominatedConvergence.lean, line 253
             (added after the model's training data; human proof 42 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 1 call(s)
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
  swap
  · simpa [setToFun, hF] using (stronglyMeasurable_const : StronglyMeasurable (fun _ : β => (0 : F)))
  letI := hF
  borelize E
  let s : Set E := Set.range (Function.uncurry f) ∪ {0}
  letI : SeparableSpace s := hf.separableSpace_range_union_singleton
  have h0 : (0 : E) ∈ s := Or.inr (Set.mem_singleton 0)
  let g : ℕ → SimpleFunc (β × α) E := SimpleFunc.approxOn _ hf.measurable s 0 h0
  let G : ℕ → β → F := fun n x => ∑ y ∈ (g n).range, T (Prod.mk x ⁻¹' ((g n) ⁻¹' {y})) y
  have hG : ∀ n, StronglyMeasurable (G n) := by
  {
  intro n
  apply Finset.stronglyMeasurable_fun_sum
  intro y hy
  exact (continuous_id.clm_apply continuous_const).comp_stronglyMeasurable
    (h'T _ ((g n).measurableSet_fiber y))
  }
  let A : Set β := {x | Integrable (f x) μ}
  have hA : MeasurableSet A := measurableSet_integrable hf
  apply stronglyMeasurable_of_tendsto (u := atTop)
    (f := fun n => A.indicator (G n))
    (fun n => (hG n).indicator hA)
  apply tendsto_pi_nhds.mpr
  intro x
  by_cases hx : Integrable (f x) μ
  swap
  · simpa [A, hx, setToFun_undef hT hx] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : F)) atTop (𝓝 0))
  have hb : ∀ n a, ‖g n (x, a)‖ ≤ ‖f x a‖ + ‖f x a‖ := by
  {
  intro n a
  exact SimpleFunc.norm_approxOn_zero_le hf.measurable h0 (x, a) n
  }
  have hi : ∀ n, Integrable (fun a => g n (x, a)) μ := by
  {
  intro n
  exact (hx.norm.add hx.norm).mono'
    (((g n).stronglyMeasurable.comp_measurable measurable_prodMk_left).aestronglyMeasurable)
    (Filter.Eventually.of_forall (hb n))
  }
  have heq : ∀ n, G n x = setToFun μ T hT (fun a => g n (x, a)) := by
  {
  intro n
  let q : SimpleFunc α E := (g n).comp (Prod.mk x) measurable_prodMk_left
  change G n x = setToFun μ T hT q
  rw [setToFun_simpleFunc_eq_setToSimpleFunc hT q (hi n)]
  symm
  exact SimpleFunc.setToSimpleFunc_eq_sum_of_subset T hT.1.map_empty_eq_zero
    (Finset.Subset.trans (Finset.filter_subset _ _) ((g n).range_comp_subset_range measurable_prodMk_left))
  }
  have ht : Tendsto (fun n => setToFun μ T hT (fun a => g n (x, a))) atTop
    (𝓝 (setToFun μ T hT (f x))) := by
  {
  apply tendsto_setToFun_of_dominated_convergence hT (fun a => ‖f x a‖ + ‖f x a‖)
  · exact fun n => (hi n).aestronglyMeasurable
  · exact hx.norm.add hx.norm
  · exact fun n => Filter.Eventually.of_forall (hb n)
  · apply Filter.Eventually.of_forall
    intro a
    exact SimpleFunc.tendsto_approxOn hf.measurable h0
      (subset_closure (Or.inl (Set.mem_range_self (x, a))))
  }
  simpa only [Set.indicator_of_mem (show x ∈ A from hx), heq] using ht
