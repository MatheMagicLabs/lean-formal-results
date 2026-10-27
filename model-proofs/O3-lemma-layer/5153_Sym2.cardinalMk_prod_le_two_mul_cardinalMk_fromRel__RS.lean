/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_le_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 119
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  have hs : Function.Surjective (fun p : α × α => s(p.1, p.2)) := fun z =>
    Sym2.ind (fun a b => ⟨(a, b), rfl⟩) z
  let g := Function.surjInv hs
  let f : {p : α × α // r p.1 p.2} → Bool × fromRel sym := fun p =>
    (decide (p.1 = g s(p.1.1, p.1.2)),
      ⟨s(p.1.1, p.1.2), (fromRel_prop (sym := sym)).mpr p.2⟩)
  have hf : Function.Injective f := by
    rintro ⟨⟨a, b⟩, hp⟩ ⟨⟨c, d⟩, hq⟩ h
    apply Subtype.ext
    show (a, b) = (c, d)
    have h1 := congrArg Prod.fst h
    have h2 : s(a, b) = s(c, d) := congrArg (fun x => (x.2 : Sym2 α)) h
    dsimp only [f] at h1
    rw [h2] at h1
    have ho : s((g s(c, d)).1, (g s(c, d)).2) = s(c, d) := Function.surjInv_eq hs _
    generalize g s(c, d) = o at h1 ho
    obtain ⟨o1, o2⟩ := o
    by_cases hp' : (a, b) = (o1, o2)
    · by_cases hq' : (c, d) = (o1, o2)
      · rw [hp', hq']
      · simp [hp', hq'] at h1
    · by_cases hq' : (c, d) = (o1, o2)
      · simp [hp', hq'] at h1
      · have hp2 : s(a, b) = s(o1, o2) := h2.trans ho.symm
        rcases Sym2.eq_iff.mp hp2 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
          rcases Sym2.eq_iff.mp ho with ⟨e3, e4⟩ | ⟨e3, e4⟩ <;>
          simp_all
  calc #{ p : α × α // r p.fst p.snd } ≤ #(Bool × fromRel sym) :=
        Cardinal.mk_le_of_injective hf
    _ = 2 * #(fromRel sym) := by
        simp [Cardinal.mk_prod, Cardinal.mk_bool]
