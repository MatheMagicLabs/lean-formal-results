/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_eq_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 130
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 1 (round 0 = first attempt)
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

theorem cardinalMk_prod_eq_two_mul_cardinalMk_fromRel [Std.Irrefl r] :
    #{ p : α × α // r p.fst p.snd } = 2 * #(fromRel sym) := by
  classical
  rw [← Equiv.sigmaSubtypeFiberEquivSubtype Sym2.mk.uncurry
    (q := (· ∈ fromRel sym)) (by simp) |>.cardinal_eq,
    Cardinal.mk_sigma, mul_comm]
  have h (z : fromRel sym) :
      #{p : α × α // Sym2.mk.uncurry p = z.val} = 2 := by
    rw [← Set.coe_ofPred, ← Set.preimage_singleton,
      ← Set.cast_ncard (finite_mk_fiber z.val),
      ncard_mk_fiber_of_not_isDiag
        (fromRel_irrefl.mp ‹Std.Irrefl r› z.property)]
    simp
  calc
    _ = Cardinal.sum (fun _ : fromRel sym => (2 : Cardinal)) :=
      congrArg Cardinal.sum (funext h)
    _ = _ := Cardinal.sum_const' _ _
