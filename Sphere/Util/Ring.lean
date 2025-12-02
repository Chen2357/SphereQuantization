import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Algebra.Basic

section

variable {R : Type*}

instance [NonUnitalRing R] : LieRing R where
  lie_add := by intros; simp [Bracket.bracket, mul_add, add_mul]; abel
  add_lie := by intros; simp [Bracket.bracket, mul_add, add_mul]; abel
  lie_self := by intros; simp [Bracket.bracket]
  leibniz_lie := by
    intros
    simp [Bracket.bracket, mul_sub, sub_mul, mul_assoc]
    abel

theorem lie_mul [NonUnitalRing R] {x y z : R} : ⁅x, y * z⁆ = ⁅x, y⁆ * z + y * ⁅x, z⁆ := by
  simp [Bracket.bracket, sub_mul, mul_sub, mul_assoc]

theorem mul_lie [NonUnitalRing R] {x y z : R} : ⁅x * y, z⁆ = x * ⁅y, z⁆ + ⁅x, z⁆ * y := by
  simp [Bracket.bracket, mul_sub, sub_mul, mul_assoc]

@[simp]
theorem lie_one [Ring R] {x : R} : ⁅x, (1 : R)⁆ = 0 := by simp [Bracket.bracket]

@[simp]
theorem one_lie [Ring R] {x : R} : ⁅(1 : R), x⁆ = 0 := by simp [Bracket.bracket]

end

section

variable {R : Type*} [CommRing R]
variable {A : Type*} [Ring A] [Algebra R A]

instance : LieAlgebra R A where
  lie_smul := by simp [Bracket.bracket, smul_sub]

@[simp]
theorem lie_algebraMap {r : R} {x : A} : ⁅algebraMap R A r, x⁆ = 0 := by
  simp [Bracket.bracket, Algebra.commutes]

end
