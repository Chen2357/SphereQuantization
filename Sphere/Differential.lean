import Sphere.Basis
import Sphere.Util.Collect

noncomputable section

open Cochain

-- The theorems below express d Ω.H', d Ω.X', d Ω.Y' in terms of products of Ω.H', Ω.X', Ω.Y'.
-- These are derived from the relationships:
--   H' = Complex.I • α         (so α = -Complex.I • H')
--   X' = l1 + Complex.I • l2   (which equals l)
--   Y' = -l1 + Complex.I • l2  (which equals -l_bar)

theorem dH'_eq : d Ω.H' = -Ω.X' * Ω.Y' := by
  unfold Ω.H' Ω.X' Ω.Y' Ω.α Ω.l1 Ω.l2
  simp only [d_smul, smul_add, smul_sub, smul_smul]
  simp only [neg_mul, mul_neg, neg_neg, mul_add, add_mul, sub_mul, mul_sub]
  rw [graded_comm Ω]
  simp only [smul_smul, smul_add, smul_sub]
  ring_nf
  abel

theorem dX'_eq : d Ω.X' = (2 : ℂ) • (Ω.X' * Ω.H') := by
  unfold Ω.X' Ω.H' Ω.α Ω.l1 Ω.l2
  simp only [d_add, d_smul, smul_add, smul_sub, smul_smul]
  simp only [mul_add, add_mul, sub_mul, mul_sub]
  simp only [smul_smul, smul_add, smul_sub]
  ring_nf
  simp
  abel_nf
  ring_nf
  abel

theorem dY'_eq : d Ω.Y' = (-2 : ℂ) • (Ω.Y' * Ω.H') := by
  unfold Ω.Y' Ω.H' Ω.α Ω.l1 Ω.l2
  simp only [d_neg, d_smul, smul_add, smul_sub, smul_smul]
  simp only [neg_mul, mul_neg, neg_neg, mul_add, add_mul, sub_mul, mul_sub]
  simp only [smul_smul, smul_add, smul_sub]
  ring_nf
  simp
  abel_nf
  ring_nf
  abel
