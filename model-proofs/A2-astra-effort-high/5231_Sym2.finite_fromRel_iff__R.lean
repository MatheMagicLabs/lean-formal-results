/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.finite_fromRel_iff
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 140
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Sym2
open scoped Cardinal
variable {α : Type*}
variable (α) in
open scoped Classical in
variable (α) in
variable (α) in
variable (α) in
open scoped Classical in
variable (α) in
variable (α) in
section fromRel
variable {r : α → α → Prop} (sym : Std.Symm r)

theorem finite_fromRel_iff : (fromRel sym).Finite ↔ Finite { p : α × α // r p.fst p.snd } := by
  classical
  rw [← Set.finite_coe_iff]
  let f : {p : α × α // r p.fst p.snd} → ↥(fromRel sym) :=
    fun p => ⟨s(p.1.1, p.1.2), by simpa [fromRel] using p.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨⟨a, b⟩, rfl⟩ := Quot.exists_rep z
    refine ⟨⟨(a, b), ?_⟩, ?_⟩
    · simpa [fromRel] using hz
    · rfl
  constructor
  · intro h
    letI : Finite ↥(fromRel sym) := h
    let rep : ↥(fromRel sym) → α × α :=
      fun z => Quot.out z.1
    have hrep (p : {p : α × α // r p.fst p.snd}) :
        p.1 = rep (f p) ∨ p.1 = (rep (f p)).swap := by
      have he :
          s(p.1.1, p.1.2) =
            s((rep (f p)).1, (rep (f p)).2) :=
        (Quot.out_eq (f p).1).symm
      simpa [Sym2.eq_iff, Prod.ext_iff, Prod.swap] using he
    let g : {p : α × α // r p.fst p.snd} →
        ↥(fromRel sym) × Bool :=
      fun p => (f p, decide (p.1 = rep (f p)))
    apply Finite.of_injective g
    intro p q hpq
    have h₁ : f p = f q := congrArg Prod.fst hpq
    have h₂ :
        decide (p.1 = rep (f p)) = decide (q.1 = rep (f q)) :=
      congrArg Prod.snd hpq
    have hp := hrep p
    have hq := hrep q
    rw [← h₁] at h₂ hq
    apply Subtype.ext
    by_cases hp' : p.1 = rep (f p)
    · have hq' : q.1 = rep (f p) := by
        simpa [hp'] using h₂.symm
      exact hp'.trans hq'.symm
    · have hq' : q.1 ≠ rep (f p) := by
        simpa [hp'] using h₂.symm
      exact (hp.resolve_left hp').trans (hq.resolve_left hq').symm
  · intro h
    letI : Finite {p : α × α // r p.fst p.snd} := h
    exact Finite.of_surjective f hf
