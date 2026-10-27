/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_lt_one_iff
Source:      Mathlib @ d0a050ad6, Mathlib/RingTheory/DedekindDomain/AdicValuation.lean, line 1091 (group STABLE)
Experiment:  UE1-deepseek-8-samples, arm sample 0, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
theorem adicAbv_coe_lt_one_iff : v.adicAbv hb (algebraMap R K r) < 1 ↔ r ∈ v.asIdeal := by
  rw [adicAbv_of_algebraMap]
  exact intAdicAbv_lt_one_iff v hb r
