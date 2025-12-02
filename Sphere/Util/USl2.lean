import Sphere.Util.Sl2
import Sphere.Util.Ring
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.DirectSum.Algebra

open Sl2
open UniversalEnvelopingAlgebra

variable (R : Type*) [CommRing R] [Nontrivial R]

abbrev USl2 := UniversalEnvelopingAlgebra R (Sl2 R)

def h_half_weight (m : ℤ) : Submodule R (USl2 R) where
  carrier := { x | ⁅ι R (h R), x⁆ = (2 * m) • x }
  zero_mem' := by simp
  add_mem' := by
    intros
    simp at *
    simp [*, mul_add]
  smul_mem' := by
    intros
    simp at *
    simp [*]

@[simp]
theorem h_mem_iff {m : ℤ} {x : USl2 R} : x ∈ h_half_weight R m ↔ ⁅ι R (h R), x⁆ = (2 * m) • x := by rfl

theorem h_mem_mul {n m : ℤ} {x : USl2 R} (hx : x ∈ h_half_weight R n) {y : USl2 R} (hy : y ∈ h_half_weight R m) : x * y ∈ h_half_weight R (n + m) := by
  simp [-zsmul_eq_mul] at *
  simp [lie_mul, *, -zsmul_eq_mul, ←add_smul]
  ring_nf

theorem h_mem_h : ι R (h R) ∈ h_half_weight R 0 := by
  simp

theorem h_mem_e : ι R (e R) ∈ h_half_weight R 1 := by
  simp [-zsmul_eq_mul, -ι_apply, ←LieHom.map_lie]
  simp [-zsmul_eq_mul, -nsmul_eq_mul]
  norm_cast

theorem h_mem_f : ι R (f R) ∈ h_half_weight R (-1) := by
  simp [-zsmul_eq_mul, -ι_apply, ←LieHom.map_lie]
  simp [-zsmul_eq_mul, -nsmul_eq_mul]
  norm_cast

/-- The multiplicative identity 1 belongs to the zero weight space h_half_weight R 0.
This is a fundamental property for graded algebras. -/
theorem h_mem_one : (1 : USl2 R) ∈ h_half_weight R 0 := by
  simp

instance : SetLike.GradedOne (h_half_weight R) where
  one_mem := h_mem_one R

instance : SetLike.GradedMul (h_half_weight R) where
  mul_mem := h_mem_mul R

/-- The decomposition of USl2 into h-weight spaces.
This requires the PBW theorem and weight space decomposition for sl₂ representations.
TODO: Prove this using the PBW basis {e^a h^b f^c} and weight analysis. -/
def h_half_weight_decompose : USl2 R →ₐ[R] ⨁ i, h_half_weight R i := sorry

/-- The decomposition is a left inverse of the canonical embedding.
This establishes that composing the decomposition with the canonical embedding
gives the identity, i.e., decomposing and reassembling an element returns the original. -/
theorem h_half_weight_decompose_left_inv :
    Function.LeftInverse (DirectSum.coeAlgHom (A := USl2 R) (h_half_weight R))
      (h_half_weight_decompose R) := sorry

/-- The decomposition is a right inverse of the canonical embedding.
This establishes that every element of the direct sum, when embedded into USl2
and then decomposed, returns to the original element. -/
theorem h_half_weight_decompose_right_inv :
    Function.RightInverse (DirectSum.coeAlgHom (A := USl2 R) (h_half_weight R))
      (h_half_weight_decompose R) := sorry

instance : GradedAlgebra (h_half_weight R) :=
  GradedAlgebra.ofAlgHom (h_half_weight R) (h_half_weight_decompose R)
    (h_half_weight_decompose_left_inv R) (h_half_weight_decompose_right_inv R)
