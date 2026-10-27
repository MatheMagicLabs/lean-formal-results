/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.finite_fromRel_iff
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 140
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  constructor
  · intro h
    letI := h.fintype
    have hex (z : fromRel sym) :
        ∃ p : {p : α × α // r p.1 p.2}, s(p.1.1, p.1.2) = z.1 := by
      rcases z with ⟨z, hz⟩
      revert hz
      refine Sym2.inductionOn z ?_
      intro a b hab
      exact ⟨⟨(a, b), hab⟩, rfl⟩
    let rep := fun z => (hex z).choose
    let swap : {p : α × α // r p.1 p.2} →
        {p : α × α // r p.1 p.2} :=
      fun p => ⟨p.1.swap, sym.symm _ _ p.2⟩
    let f : (fromRel sym) × Bool → {p : α × α // r p.1 p.2} :=
      fun z => if z.2 then rep z.1 else swap (rep z.1)
    apply Finite.of_surjective f
    intro p
    let z : fromRel sym := ⟨s(p.1.1, p.1.2), p.2⟩
    have he : s((rep z).1.1, (rep z).1.2) = s(p.1.1, p.1.2) :=
      (hex z).choose_spec
    simp only [Sym2.eq_iff, Prod.mk.injEq] at he
    rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · refine ⟨(z, true), ?_⟩
      change rep z = p
      exact Subtype.ext (Prod.ext h₁ h₂)
    · refine ⟨(z, false), ?_⟩
      change swap (rep z) = p
      exact Subtype.ext (Prod.ext h₂ h₁)
  · intro h
    letI := h
    let f : {p : α × α // r p.1 p.2} → fromRel sym :=
      fun p => ⟨s(p.1.1, p.1.2), p.2⟩
    have hf : Function.Surjective f := by
      rintro ⟨z, hz⟩
      revert hz
      refine Sym2.inductionOn z ?_
      intro a b hab
      exact ⟨⟨(a, b), hab⟩, rfl⟩
    letI := Finite.of_surjective f hf
    exact Set.toFinite _
