import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Star.Basic

noncomputable section

namespace LaurentPolynomial

section

variable (R : Type u) [Semiring R]

@[simp]
theorem C_mul_T_apply (r : R) (n m : ℤ) : (C r * T n : R[T;T⁻¹]) m = if n = m then r else 0 := by
  simp [←single_eq_C_mul_T, Finsupp.single_apply]

instance [StarAddMonoid R] : Star R[T;T⁻¹] where
  star f := f.mapRange star (star_zero R)

@[simp]
theorem star_apply (f : R[T;T⁻¹]) (n : ℤ) [StarAddMonoid R] : star f n = star (f n) := by
  simp [star]

instance [StarAddMonoid R] : StarAddMonoid R[T;T⁻¹] where
  star_involutive f := by
    ext n
    simp [star]
  star_add f g := by
    ext n
    simp [star]

@[simp]
theorem star_C (r : R) [StarAddMonoid R] : star (C r : R[T;T⁻¹]) = C (star r) := by
  ext n
  simp [star]
  split
  all_goals simp

@[simp]
theorem star_T (n : ℤ) [StarRing R] : star (T n : R[T;T⁻¹]) = T n := by
  ext m
  simp [star]
  split
  all_goals simp

@[simp]
lemma star_C_mul_T (r : R) (n : ℤ) [StarRing R] : star (C r * T n : R[T;T⁻¹]) = C (star r) * T n := by
  simp [star, ←single_eq_C_mul_T]

instance [StarRing R] : StarRing R[T;T⁻¹] where
  star_add := star_add
  star_mul f g := by
    induction f using LaurentPolynomial.induction_on'
    case add => simp [add_mul, mul_add, *]
    case C_mul_T n r =>
    induction g using LaurentPolynomial.induction_on'
    case add => simp [add_mul, mul_add, *]
    case C_mul_T m s =>
      conv_lhs => rw [←T_mul, mul_assoc, T_mul, mul_assoc, mul_assoc, ←mul_assoc, ←map_mul, ←T_add]
      simp only [star_C_mul_T]
      conv_rhs => rw [←T_mul, mul_assoc, T_mul, mul_assoc, mul_assoc, ←mul_assoc, ←map_mul, ←T_add, add_comm]
      simp

end

variable (R : Type u) [CommSemiring R]

instance [StarRing R] : StarModule R R[T;T⁻¹] where
  star_smul c f := by
    induction f using LaurentPolynomial.induction_on'
    case add => simp [smul_add, star_add, *]
    case C_mul_T n r =>
      ext m
      simp
      split
      all_goals simp

end LaurentPolynomial
