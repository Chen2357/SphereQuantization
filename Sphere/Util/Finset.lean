import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin

namespace Finset

@[elab_as_elim]
theorem fin_induction {α : Type*} [DecidableEq α] {motive : Finset α → Prop}
  (s : Finset α)
  (h : ∀ (n) (f : Fin n → α), (Function.Injective f) → motive (image f .univ))
  : motive s := by
  have equiv := s.equivFin
  let f i := (equiv.symm i).val
  have : s = image f .univ := by
    ext a
    constructor
    . intro ha
      simp [f]
      use equiv ⟨a, ha⟩
      simp
    . intro ha
      simp at ha
      rcases ha with ⟨i, hi⟩
      rw [←hi]
      simp [f]
  rw [this]
  apply h
  intros i j hij
  simp [f] at hij
  exact hij
