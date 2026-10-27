/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_le_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 119
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm N3, verified in round 0 (round 0 = first attempt)
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

theorem cardinalMk_prod_le_two_mul_cardinalMk_fromRel :
    #{ p : α × α // r p.fst p.snd } ≤ 2 * #(fromRel sym) := by
  classical
  let D := { p : α × α // r p.fst p.snd }
  let f : D → fromRel sym := fun p =>
    ⟨s(p.val.1, p.val.2), by simpa using p.property⟩
  have hf (p q : D) (h : f p = f q) :
      p.val = q.val ∨ p.val = (q.val.2, q.val.1) := by
    have h' := congrArg Subtype.val h
    change s(p.val.1, p.val.2) = s(q.val.1, q.val.2) at h'
    rcases Sym2.eq_iff.mp h' with h' | h'
    · exact Or.inl (Prod.ext h'.1 h'.2)
    · exact Or.inr (Prod.ext h'.1 h'.2)
  let rep : Set.range f → D := fun q => Classical.choose q.property
  let e : D → Bool × fromRel sym := fun p =>
    (decide (p = rep ⟨f p, ⟨p, rfl⟩⟩), f p)
  have he : Function.Injective e := by
    intro p q h
    have hv : f p = f q := congrArg Prod.snd h
    let rp : D := rep ⟨f p, ⟨p, rfl⟩⟩
    have hrep : rep ⟨f q, ⟨q, rfl⟩⟩ = rp := by
      apply congrArg rep
      exact Subtype.ext hv.symm
    have hrp : f rp = f p :=
      Classical.choose_spec (show ∃ x, f x = f p from ⟨p, rfl⟩)
    have hb : decide (p = rp) = decide (q = rp) := by
      have hb := congrArg Prod.fst h
      change decide (p = rep ⟨f p, ⟨p, rfl⟩⟩) =
        decide (q = rep ⟨f q, ⟨q, rfl⟩⟩) at hb
      rw [hrep] at hb
      exact hb
    by_cases hp : p = rp
    · have hq : q = rp := by
        simpa [hp] using hb.symm
      exact hp.trans hq.symm
    · have hq : q ≠ rp := by
        intro hq
        simp [hp, hq] at hb
      have hpv := (hf p rp hrp.symm).resolve_left
        (fun h => hp (Subtype.ext h))
      have hqv := (hf q rp (hv.symm.trans hrp.symm)).resolve_left
        (fun h => hq (Subtype.ext h))
      exact Subtype.ext (hpv.trans hqv.symm)
  calc
    #D ≤ #(Bool × fromRel sym) :=
      Cardinal.mk_le_of_injective (f := e) he
    _ = 2 * #(fromRel sym) := by simp
