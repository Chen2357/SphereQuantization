import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Algebra.DirectSum.Basic

namespace AlternatingMap

variable {R : Type*} [Semiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable {ι : Type*} {α : Type*}

@[simp]
theorem sum_apply [DecidableEq ι] (s : Finset ι) (f : ι → M [⋀^α]→ₗ[R] N) (m : α → M) :
    (∑ c ∈ s, f c) m = ∑ c ∈ s, f c m := by
  induction s using Finset.induction_on
  case empty => simp
  case insert b s h ih =>
    simp [Finset.sum_insert h, ih]

end AlternatingMap

namespace DirectSum

variable (α : Type*) (β : α → Type*) [∀ a, AddCommMonoid (β a)]
variable {ι : Type*}

@[simp]
theorem sum_apply [DecidableEq ι] (a : α) (s : Finset ι) (f : ι → ⨁ a, β a) : (∑ c ∈ s, f c) a = ∑ c ∈ s, (f c) a := by
  induction s using Finset.induction_on
  case empty => simp
  case insert b s h ih =>
    simp [Finset.sum_insert h, ih]

end DirectSum
