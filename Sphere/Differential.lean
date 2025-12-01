import Sphere.Basis

noncomputable section

open Cochain

-- The theorems below express d Ω.H', d Ω.X', d Ω.Y' in terms of products of Ω.H', Ω.X', Ω.Y'.
-- These are derived from the relationships:
--   H' = Complex.I • α
--   X' = l1 + Complex.I • l2
--   Y' = -l1 + Complex.I • l2

theorem dH'_eq : d Ω.H' = -Ω.X' * Ω.Y' := by
  sorry

theorem dX'_eq : d Ω.X' = (2 : ℂ) • (Ω.X' * Ω.H') := by
  sorry

theorem dY'_eq : d Ω.Y' = (-2 : ℂ) • (Ω.Y' * Ω.H') := by
  sorry
