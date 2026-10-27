/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_le_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 119
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm N0, verified in round 0 (round 0 = first attempt)
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
  have hex (z : fromRel sym) :
      ∃ p : α × α, s(p.1, p.2) = z.val := by
    refine Sym2.inductionOn z.val ?_
    intro a b
    exact ⟨(a, b), rfl⟩
  let rep (z : fromRel sym) : α × α := Classical.choose (hex z)
  have hrep (z : fromRel sym) :
      s((rep z).1, (rep z).2) = z.val :=
    Classical.choose_spec (hex z)
  have hr (z : fromRel sym) : r (rep z).1 (rep z).2 := by
    have hz := z.property
    rw [← hrep z] at hz
    simpa [fromRel] using hz
  have hrs (z : fromRel sym) : r (rep z).2 (rep z).1 := by
    first
    | exact sym.symm (hr z)
    | exact sym.symm _ _ (hr z)
  let f : Bool × fromRel sym → {p : α × α // r p.1 p.2} :=
    fun q =>
      if q.1 then
        ⟨((rep q.2).2, (rep q.2).1), hrs q.2⟩
      else
        ⟨rep q.2, hr q.2⟩
  have hf : Function.Surjective f := by
    intro p
    let z : fromRel sym :=
      ⟨s(p.val.1, p.val.2), by
        simpa [fromRel] using p.property⟩
    have h := hrep z
    change s((rep z).1, (rep z).2) = s(p.val.1, p.val.2) at h
    have hp : rep z = p.val ∨ rep z = (p.val.2, p.val.1) := by
      simpa [Prod.ext_iff] using (Sym2.eq_iff.mp h)
    rcases hp with hp | hp
    · refine ⟨(false, z), ?_⟩
      apply Subtype.ext
      change rep z = p.val
      exact hp
    · refine ⟨(true, z), ?_⟩
      apply Subtype.ext
      change ((rep z).2, (rep z).1) = p.val
      simp [hp]
  simpa [Cardinal.mk_prod] using Cardinal.mk_le_of_surjective hf
