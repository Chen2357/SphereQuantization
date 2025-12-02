import Sphere.Util.Sl2
import Sphere.Util.Ring
import Mathlib.Algebra.Lie.UniversalEnveloping

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
