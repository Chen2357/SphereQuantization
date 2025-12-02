import Sphere.Util.Sl2
import Sphere.Util.Ring
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.LinearAlgebra.Vandermonde

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
  simp

theorem h_mem_f : ι R (f R) ∈ h_half_weight R (-1) := by
  simp [-zsmul_eq_mul, -ι_apply, ←LieHom.map_lie]
  simp

instance : SetLike.GradedMonoid (h_half_weight R) where
  one_mem := by simp
  mul_mem _ _ _ _ hx hy := h_mem_mul R hx hy

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

/-- Applying `ad(h)` to an element of weight space m gives 2m times that element.
This is the eigenvalue property that enables the Vandermonde argument for independence. -/
theorem h_half_weight_ad_h {m : ℤ} {x : USl2 R} (hx : x ∈ h_half_weight R m) :
    ⁅ι R (h R), x⁆ = (2 * m) • x := by
  simp only [h_mem_iff] at hx
  exact hx

section Field

variable (K : Type*) [Field K] [CharZero K]

instance : IsAddTorsionFree (USl2 K) where
  nsmul_right_injective n hn x y hxy := by
    have hne : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
    exact smul_right_injective (USl2 K) hne hxy

/-- Over a field of characteristic zero, weight spaces for different weights have trivial intersection.
This follows because 2(m-n) ≠ 0 when m ≠ n, so 2(m-n) • x = 0 implies x = 0. -/
theorem h_half_weight_disjoint {m n : ℤ} (hmn : m ≠ n) {x : USl2 K}
    (hm : x ∈ h_half_weight K m) (hn : x ∈ h_half_weight K n) : x = 0 := by
  have h_eq := h_half_weight_eq_smul K hm hn
  have h_ne : (2 : K) * (m - n) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, sub_eq_zero]
    intro h
    simp at h
    cases h
    trivial
  norm_cast at h_ne
  apply (smul_eq_zero.mp h_eq).resolve_left h_ne

/-- The weight spaces are independent: if m ≠ n then h_half_weight K m ⊓ h_half_weight K n = ⊥.
This is the key property for the graded structure derived from the Vandermonde argument. -/
theorem h_half_weight_inf_eq_bot {m n : ℤ} (hmn : m ≠ n) :
    h_half_weight K m ⊓ h_half_weight K n = ⊥ := by
  ext x
  simp only [Submodule.mem_inf, Submodule.mem_bot]
  constructor
  · intro ⟨hm, hn⟩
    exact h_half_weight_disjoint K hmn hm hn
  · intro hx
    simp [hx]

theorem h_half_weight_iSupIndep : iSupIndep (h_half_weight K) := by
  apply (iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero _).mpr
  sorry


theorem h_half_weight_iSup : iSup (h_half_weight K) = ⊤ := by
  sorry

theorem h_half_weight_directSum: DirectSum.IsInternal (h_half_weight K) := by
  apply (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
  constructor
  apply h_half_weight_iSupIndep
  apply h_half_weight_iSup

end Field
