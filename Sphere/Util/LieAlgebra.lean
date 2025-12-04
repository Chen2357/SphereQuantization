import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Nat.Choose.Multinomial
import Sphere.Util.Finset

-- Will appear in a future Mathlib update in Batteries.Data.Fin.Basic
@[inline] protected def Fin.prod [One α] [Mul α] (x : Fin n → α) : α := foldr n (x · * ·) 1

@[simp]
theorem Fin.prod_zero [One α] [Mul α] (x : Fin 0 → α) : Fin.prod x = 1 := rfl

@[simp]
theorem Fin.prod_cons' [One α] [Mul α] (x : α) (y : Fin n → α) : Fin.prod (cons x y) = x * (Fin.prod y) := by simp [Fin.prod, foldr_succ]

@[simp]
theorem Fin.prod_succ [One α] [Mul α] (x : Fin (n + 1) → α) : Fin.prod x = x 0 * (Fin.prod (tail x)) := by
  simp [Fin.prod, foldr_succ, Fin.tail]

open LieAlgebra
open Function

variable {R : Type*} {A : Type*} [CommRing R] [Ring A] [Algebra R A]

@[simp]
theorem prod_const (x : A) (n : ℕ) : Fin.prod (const (Fin n) x) = x ^ n := by
  induction n
  case zero => simp
  case succ n ih =>
    conv_rhs => rw [add_comm, pow_add]
    simp [Fin.prod_succ]
    congr

@[simp]
theorem lie_apply_one (x : A) : ⁅x, (1 : A)⁆ = 0 := by simp [Bracket.bracket]

@[simp]
theorem lie_apply_nat_cast (x : A) (n : ℕ) : ⁅x, (n : A)⁆ = 0 := by
  simp [Bracket.bracket]
  show x * (algebraMap ℕ A n) - (algebraMap ℕ A n) * x = 0
  rw [Algebra.commutes]
  simp

@[simp]
theorem lie_apply_mul (x y z : A) : ⁅x, y * z⁆ = ⁅x, y⁆ * z + y * ⁅x, z⁆ := by
  simp [Bracket.bracket]
  noncomm_ring

theorem lie_apply_prod_eq_sum (x : A) {m : ℕ} (y : Fin m → A) :
  ⁅x, Fin.prod y⁆ = ∑ i : Fin m, (Fin.prod (update y i ⁅x, y i⁆)) := by
  induction m
  case zero => simp
  case succ m ih =>
    simp [ih, Fin.sum_univ_succ, Finset.mul_sum]
    rfl

theorem lie_apply_ad_pow (x : A) (n : ℕ) (y : A) :
  ⁅x, ((ad R A x)^n) y⁆ = ((ad R A x)^(n + 1)) y := by
  rw [add_comm]
  simp [pow_add]

theorem ad_pow_prod_eq_sum_piAntidiag (x : A) (n : ℕ) {m : ℕ} (y : Fin m → A) :
  ((ad R A x)^n) (Fin.prod y) = ∑ k ∈ ((.univ : Finset (Fin m)).piAntidiag n), (Nat.multinomial .univ k) * (Fin.prod (fun i => ((ad R A x)^(k i)) (y i))) := by
  induction n
  case zero => simp [Nat.multinomial]
  case succ n ih =>
    conv_lhs =>
      rw [add_comm, pow_add]
    simp [ih, lie_apply_prod_eq_sum, Finset.mul_sum, lie_apply_ad_pow]
    sorry

theorem ad_pow_pow_eq_sum_piAntidiag (x : A) (n : ℕ) (y : A) (m : ℕ) :
  ((ad R A x)^n) (y ^ m) = ∑ k ∈ ((.univ : Finset (Fin m)).piAntidiag n), (Nat.multinomial .univ k) * (Fin.prod (fun i => ((ad R A x)^(k i)) y)) := by
  convert ad_pow_prod_eq_sum_piAntidiag x n (fun _ => y)
  rw [←prod_const]
  congr
