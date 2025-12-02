import Mathlib.Algebra.Lie.Sl2
import Mathlib.Data.Complex.Basic

def Sl2 (R : Type*) [CommRing R] [Nontrivial R] := Fin 3 → R

namespace Sl2

section

variable (R : Type*) [CommRing R] [Nontrivial R]

def h : Sl2 R := ![1, 0, 0]
def e : Sl2 R := ![0, 1, 0]
def f : Sl2 R := ![0, 0, 1]

@[simp] theorem h_0 : (h R) 0 = 1 := by rfl
@[simp] theorem h_1 : (h R) 1 = 0 := by rfl
@[simp] theorem h_2 : (h R) 2 = 0 := by rfl
@[simp] theorem e_0 : (e R) 0 = 0 := by rfl
@[simp] theorem e_1 : (e R) 1 = 1 := by rfl
@[simp] theorem e_2 : (e R) 2 = 0 := by rfl
@[simp] theorem f_0 : (f R) 0 = 0 := by rfl
@[simp] theorem f_1 : (f R) 1 = 0 := by rfl
@[simp] theorem f_2 : (f R) 2 = 1 := by rfl

instance : AddCommGroup (Sl2 R) := by unfold Sl2; infer_instance
instance : Module R (Sl2 R) := by unfold Sl2; infer_instance

@[simp] theorem zero_apply (i) : (0 : Sl2 R) i = 0 := by rfl
@[simp] theorem add_apply (x y : Sl2 R) (i : Fin 3) : (x + y) i = x i + y i := by rfl
@[simp] theorem smul_apply (r : R) (x : Sl2 R) (i : Fin 3) : (r • x) i = r * x i := by rfl
@[simp] theorem neg_apply (x : Sl2 R) (i : Fin 3) : (-x) i = -(x i) := by rfl
@[simp] theorem sub_apply (x y : Sl2 R) (i : Fin 3) : (x - y) i = x i - y i := by rfl
@[simp] theorem nsmul_apply (n : ℕ) (x : Sl2 R) (i : Fin 3) : (n • x) i = n • x i := by rfl
@[simp] theorem zsmul_apply (n : ℤ) (x : Sl2 R) (i : Fin 3) : (n • x) i = n • x i := by rfl

instance : LieRing (Sl2 R) where
  bracket x y := ![
    x 1 * y 2 - x 2 * y 1,
    2 * x 0 * y 1 - 2 * x 1 * y 0,
    2 * x 2 * y 0 - 2 * x 0 * y 2
  ]
  add_lie x y z := by
    unfold Sl2
    ext i
    fin_cases i
    all_goals simp; ring
  lie_add x y z := by
    unfold Sl2
    ext i
    fin_cases i
    all_goals simp; ring
  lie_self x := by
    unfold Sl2
    ring_nf
    simp
  leibniz_lie x y z := by
    unfold Sl2
    ext i
    fin_cases i
    all_goals simp; ring

instance : LieAlgebra R (Sl2 R) where
  lie_smul r x y := by
    unfold Sl2
    simp [Bracket.bracket]
    ring_nf
    trivial

@[simp] theorem lie_e_f : ⁅e R, f R⁆ = h R := by
  unfold Sl2
  simp [Bracket.bracket, h, e, f]

@[simp] theorem lie_f_e : ⁅f R, e R⁆ = -(h R) := by
  rw [←lie_skew, lie_e_f]

@[simp] theorem lie_h_e_nsmul : ⁅h R, e R⁆ = 2 • e R := by
  unfold Sl2
  simp [Bracket.bracket, h, e]

@[simp] theorem lie_e_h_nsmul : ⁅e R, h R⁆ = -(2 • e R) := by
  rw [←lie_skew, lie_h_e_nsmul]

@[simp] theorem lie_h_f_nsmul : ⁅h R, f R⁆ = -(2 • f R) := by
  unfold Sl2
  simp [Bracket.bracket, h, f]

@[simp] theorem lie_f_h_nsmul : ⁅f R, h R⁆ = 2 • f R := by
  rw [←lie_skew, lie_h_f_nsmul, neg_neg]

def is_triple : IsSl2Triple (h R) (e R) (f R) where
  h_ne_zero := by
    intro h
    have := congr_fun h 0
    simp at this
  lie_e_f := lie_e_f R
  lie_h_e_nsmul := lie_h_e_nsmul R
  lie_h_f_nsmul := lie_h_f_nsmul R

end

open LinearMap

theorem add_apply_smul_h_e_f {R : Type*} [CommRing R] [Nontrivial R] (x : Sl2 R) : (x 0) • h R + (x 1) • e R + (x 2) • f R = x := by
  unfold Sl2
  ext i
  fin_cases i
  all_goals simp

variable (R : Type*) [CommRing R] [Nontrivial R]

def lift {M : Type*} [LieRing M] [LieAlgebra R M]
    (toLinear : (Sl2 R) →ₗ[R] M)
    (e_f : ⁅toLinear (e R), toLinear (f R)⁆ = toLinear (h R))
    (h_e : ⁅toLinear (h R), toLinear (e R)⁆ = 2 • toLinear (e R))
    (h_f : ⁅toLinear (h R), toLinear (f R)⁆ = -(2 • toLinear (f R)))
    : Sl2 R →ₗ⁅R⁆ M where
    toFun := toLinear
    map_add' := by simp
    map_smul' := by simp
    map_lie' {x y} := by
      have : ⁅toLinear (f R), toLinear (e R)⁆ = -toLinear (h R) := by
        rw [←lie_skew, e_f]
      have : ⁅toLinear (e R), toLinear (h R)⁆ = -(2 • toLinear (e R)) := by
        rw [←lie_skew, h_e]
      have : ⁅toLinear (f R), toLinear (h R)⁆ = 2 • toLinear (f R) := by
        rw [←lie_skew, h_f, neg_neg]
      rw [←add_apply_smul_h_e_f x, ←add_apply_smul_h_e_f y]
      simp [*, smul_smul, smul_comm (N:=ℕ)]

end Sl2
