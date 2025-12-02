import Sphere.Util.Sl2
import Sphere.Util.Ring
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.DirectSum.Algebra

open Sl2
open UniversalEnvelopingAlgebra

section General

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

/-- Key observation: If x is in two different weight spaces, then 2(m-n) • x = 0.
This is the first step toward showing weight spaces are disjoint. -/
theorem h_half_weight_eq_smul {m n : ℤ} {x : USl2 R}
    (hm : x ∈ h_half_weight R m) (hn : x ∈ h_half_weight R n) :
    (2 * (m - n)) • x = 0 := by
  simp only [h_mem_iff] at hm hn
  have : (2 * m) • x = (2 * n) • x := by rw [← hm, ← hn]
  calc (2 * (m - n)) • x = (2 * m - 2 * n) • x := by ring_nf
    _ = (2 * m) • x - (2 * n) • x := by rw [sub_smul]
    _ = 0 := by rw [this, sub_self]

end General

section Field

variable (K : Type*) [Field K] [CharZero K]

/-- Over a field of characteristic zero, weight spaces for different weights have trivial intersection.
This follows because 2(m-n) ≠ 0 when m ≠ n, so 2(m-n) • x = 0 implies x = 0. -/
theorem h_half_weight_disjoint {m n : ℤ} (hmn : m ≠ n) {x : USl2 K}
    (hm : x ∈ h_half_weight K m) (hn : x ∈ h_half_weight K n) : x = 0 := by
  have h_eq := h_half_weight_eq_smul K hm hn
  have h_ne : (2 : K) * (m - n) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true,
               Int.cast_eq_zero, sub_eq_zero, true_and]
    exact fun h => hmn (Int.cast_injective h)
  rw [← Int.cast_mul, zsmul_eq_smul_cast K] at h_eq
  exact (smul_eq_zero.mp h_eq).resolve_left h_ne

/-- The decomposition of USl2 K into h-weight spaces over a field K.
Since weight spaces are disjoint and span USl2 K, we can define a unique decomposition. -/
def h_half_weight_decompose : USl2 K →ₐ[K] ⨁ i, h_half_weight K i := sorry

/-- The decomposition is a left inverse of the canonical embedding. -/
theorem h_half_weight_decompose_left_inv :
    Function.LeftInverse (DirectSum.coeAlgHom (A := USl2 K) (h_half_weight K))
      (h_half_weight_decompose K) := sorry

/-- The decomposition is a right inverse of the canonical embedding. -/
theorem h_half_weight_decompose_right_inv :
    Function.RightInverse (DirectSum.coeAlgHom (A := USl2 K) (h_half_weight K))
      (h_half_weight_decompose K) := sorry

instance : GradedAlgebra (h_half_weight K) :=
  GradedAlgebra.ofAlgHom (h_half_weight K) (h_half_weight_decompose K)
    (h_half_weight_decompose_left_inv K) (h_half_weight_decompose_right_inv K)

end Field
