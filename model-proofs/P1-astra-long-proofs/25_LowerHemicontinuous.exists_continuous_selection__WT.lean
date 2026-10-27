/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     LowerHemicontinuous.exists_continuous_selection
Source:      Mathlib @ d0a050ad6, Mathlib/Topology/Semicontinuity/Michael.lean, line 107
             (added after the model's training data; human proof 35 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 2 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem LowerHemicontinuous.exists_continuous_selection (hf : LowerHemicontinuous f)
    (hf_nonempty : ∀ x, (f x).Nonempty) (hf_convex : ∀ x, Convex ℝ (f x))
    (hf_isClosed : ∀ x, IsClosed (f x)) : ∃ g : α → β, Continuous g ∧ ∀ x, g x ∈ f x := by
  classical
  obtain ⟨W, hW, hWp⟩ :=
    exists_nhds_hasAntitoneBasis_absConvex_open_add_closure_subset ℝ β
  have hzero (n : ℕ) : (0 : β) ∈ W n :=
    mem_of_mem_nhds (hW.mem_of_mem trivial)
  let P (n : ℕ) (u : α → β) := Continuous u ∧ ∀ x, u x ∈ f x + W (n + 1)
  have hinit : ∃ u, P 0 u := by {
  apply (hf.hasOpenCGraph_of_add_hasOpenCGraph
    (.const (hWp 1).1)).hasOpenLowerSections.exists_continuous_selection;
  · intro x; obtain ⟨a, ha⟩ := hf_nonempty x
    exact ⟨a + 0, ⟨a, ha, 0, hzero 1, rfl⟩⟩
  · intro x; exact (hf_convex x).add (hWp 1).2.1.2 }
  have hnext (n : ℕ) (u : {u : α → β // P n u}) :
    ∃ v : {v : α → β // P (n + 1) v}, ∀ x, v.val x ∈ {u.val x} + W (n + 1) := by {
  obtain ⟨v, hv, hvW, hvu⟩ :=
    hf.exists_continuous_selection_refine hf_convex u.property.1
      (hWp (n + 1 + 1)).1 (hWp (n + 1 + 1)).2.1.2
      (hWp (n + 1)).1 (hWp (n + 1)).2.1.2
      (hzero (n + 1 + 1)) (hWp (n + 1)).2.1.1.neg_eq.symm u.property.2;
  exact ⟨⟨v, hv, hvW⟩, hvu⟩ }
  choose T hT using hnext
  let u0 : {u : α → β // P 0 u} := ⟨hinit.choose, hinit.choose_spec⟩
  let u : (n : ℕ) → {u : α → β // P n u} :=
    fun n ↦ Nat.rec u0 (fun n v ↦ T n v) n
  let F (n : ℕ) : α → β := (u n).val
  have hcont (n : ℕ) : Continuous (F n) := (u n).property.1
  have happrox (n : ℕ) (x : α) : F n x ∈ f x + W (n + 1) :=
    (u n).property.2 x
  have hstep (n : ℕ) (x : α) : F (n + 1) x - F n x ∈ W (n + 1) := by {
  have h := hT n (u n) x;
  change F (n + 1) x ∈ {F n x} + W (n + 1) at h;
  obtain ⟨a, ha, b, hb, hab⟩ := h;
  have ha' : a = F n x := ha;
  subst a;
  rw [← hab];
  simpa using hb }
  have htail (k n : ℕ) (x : α) : F (n + k) x - F n x ∈ W n := by {
  induction k generalizing n with
  | zero => simpa using hzero n
  | succ k ih =>
    have h := (hWp n).2.2.1
      (add_mem_add (ih (n + 1)) (hstep n x))
    have heq :
        F (n + 1 + k) x - F (n + 1) x + (F (n + 1) x - F n x) =
          F (n + (k + 1)) x - F n x := by {
      rw [show n + 1 + k = n + (k + 1) by omega];
      abel }
    rw [heq] at h
    exact h }
  have hordered {n m : ℕ} (hnm : n ≤ m) (x : α) :
    F m x - F n x ∈ W n := by {
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm;
  exact htail k n x }
  have hpair (N n m : ℕ) (hn : N ≤ n) (hm : N ≤ m) (x : α) :
    F m x - F n x ∈ W N := by {
  rcases le_total n m with h | h;
  · exact hW.antitone hn (hordered h x)
  · have hh := (hWp m).2.1.1.neg_mem_iff.mpr (hordered h x)
    exact hW.antitone hm (by simpa only [neg_sub] using hh) }
  have hU : (uniformity β).HasBasis (fun _ : ℕ ↦ True)
    (fun n ↦ {p : β × β | p.2 - p.1 ∈ W n}) := by {
  rw [uniformity_eq_comap_nhds_zero β];
  exact hW.toHasBasis.comap (fun p : β × β ↦ p.2 - p.1) }
  have hcauchy : UniformCauchySeqOn F Filter.atTop univ := by {
  intro V hV;
  obtain ⟨N, _, hN⟩ := hU.mem_iff.mp hV;
  filter_upwards [(Filter.eventually_ge_atTop N).prod_mk
    (Filter.eventually_ge_atTop N)] with p hp;
  intro x _;
  exact hN (hpair N p.1 p.2 hp.1 hp.2 x) }
  have hlimit (x : α) :
    ∃ y, Filter.Tendsto (fun n ↦ F n x) Filter.atTop (𝓝 y) :=
    cauchySeq_tendsto_of_complete (hcauchy.cauchySeq (mem_univ x))
  choose g hg using hlimit
  have hunif : TendstoUniformly F g Filter.atTop :=
    tendstoUniformlyOn_univ.mp
      (hcauchy.tendstoUniformlyOn_of_tendsto (fun x _ ↦ hg x))
  refine ⟨g, hunif.continuous (Filter.Eventually.of_forall hcont).frequently, ?_⟩
  intro x
  have hdecomp (n : ℕ) :
    ∃ a ∈ f x, ∃ b ∈ W (n + 1), a + b = F n x := happrox n x
  choose a ha b hb hab using hdecomp
  have hbzero : Filter.Tendsto b Filter.atTop (𝓝 (0 : β)) := by {
  apply hW.toHasBasis.tendsto_right_iff.mpr;
  intro N _;
  filter_upwards [Filter.eventually_ge_atTop N] with n hn;
  exact hW.antitone (by omega : N ≤ n + 1) (hb n) }
  have hatend : Filter.Tendsto a Filter.atTop (𝓝 (g x)) := by {
  have h := (hg x).sub hbzero;
  have heq : (fun n ↦ F n x - b n) = a := by {
  funext n;
  rw [← hab n, add_sub_cancel_right] };
  simpa only [sub_zero, heq] using h }
  exact (hf_isClosed x).mem_of_tendsto hatend (Filter.Eventually.of_forall ha)
