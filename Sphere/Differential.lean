-- import Sphere.Basis

-- noncomputable section

-- abbrev ν := x0 • d x0 + x1 • d x1 + x2 • d x2 + x3 • d x3

-- lemma ν_eq_zero : ν = 0 := by
--     rw [←two_nsmul_eq_zero ℂ]
--     calc
--     _ = (2 : ℂ) • (x0 * d x0 + x1 * d x1 + x2 * d x2 + x3 * d x3) := by
--         norm_cast
--     _ = d (x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3) := by
--         simp [ν, d_mul]
--         norm_cast
--         abel_nf
--     _ = d 1 := by congr; norm_cast; rw [con]
--     _ = 0 := by simp

-- lemma l1_mul_l2_eq : l1 * l2 = d x1 * d x2 - d x0 * d x3 := by
--     suffices l1 * l2 + α * ν = d x1 * d x2 - d x0 * d x3 by
--         simp [ν_eq_zero] at this
--         exact this
--     unfold l1 l2 α ν
--     simp [mul_add, mul_sub, add_mul, sub_mul]
--     custom_rewrite

--     collect d x0 * d x3
--     collect d x1 * d x2
--     calc
--     _ = (x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3) • (d x1 * d x2) + -(x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3) • (d x0 * d x3) := by simp; ring_nf
--     _ = _ := by simp [con]; abel

-- lemma l1_mul_α_eq : l1 * α = d x1 * d x3 + d x0 * d x2 := by
--     suffices l1 * α - l2 * ν = d x1 * d x3 + d x0 * d x2 by
--         simp [ν_eq_zero] at this
--         exact this
--     unfold l1 l2 α ν
--     simp [mul_add, mul_sub, add_mul, sub_mul]
--     custom_rewrite

--     collect d x0 * d x2
--     collect d x1 * d x3
--     calc
--     _ = (x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3) • (d x1 * d x3) + (x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3) • (d x0 * d x2) := by ring_nf
--     _ = _ := by simp [con]

-- lemma l2_mul_α_eq : l2 * α = d x2 * d x3 - d x0 * d x1 := by
--     suffices l2 * α + l1 * ν = d x2 * d x3 - d x0 * d x1 by
--         simp [ν_eq_zero] at this
--         exact this
--     unfold l1 l2 α ν
--     simp [mul_add, mul_sub, add_mul, sub_mul]
--     custom_rewrite

--     collect d x0 * d x1
--     collect d x2 * d x3
--     calc
--     _ = (x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3) • (d x2 * d x3) + (-(x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3)) • (d x0 * d x1) := by simp; ring_nf
--     _ = _ := by simp [con]; abel

-- theorem dα_eq : d α = -Complex.I • (l * l_bar) := by
--     unfold α l l_bar
--     simp [smul_smul, smul_add, smul_sub, d_smul]
--     simp [mul_add, mul_sub, add_mul, sub_mul]
--     rw [graded_comm Λ l2 l1]
--     simp [l1_mul_l2_eq]
--     simp [smul_smul, smul_add, smul_sub]
--     abel

-- theorem dl_eq : d l = (2 * Complex.I) • (l * α) := by
--     unfold l
--     simp [d_smul, smul_smul, smul_add, smul_sub]
--     simp [mul_add, mul_sub, add_mul, sub_mul]
--     simp [l1_mul_α_eq, l2_mul_α_eq]
--     unfold l1 l2
--     simp [d_smul, smul_smul, smul_add, smul_sub]
--     ring_nf
--     simp
--     abel_nf
--     custom_rewrite
--     ring_nf
--     abel

-- theorem dl_bar_eq : d l_bar = -(2 * Complex.I) • (l_bar * α) := by
--     unfold l_bar
--     simp [d_smul, smul_smul, smul_add, smul_sub]
--     simp [mul_add, mul_sub, add_mul, sub_mul]
--     simp [l1_mul_α_eq, l2_mul_α_eq]
--     unfold l1 l2
--     simp [d_smul, smul_smul, smul_add, smul_sub]
--     ring_nf
--     simp
--     abel_nf
--     custom_rewrite
--     ring_nf
--     abel

-- The theorems below express d Ω.H', d Ω.X', d Ω.Y' in terms of products of Ω.H', Ω.X', Ω.Y'.
-- These are derived from the relationships:
--   H' = Complex.I * α         (so α = -Complex.I * H')
--   X' = l1 + Complex.I * l2   (which equals l)
--   Y' = -l1 + Complex.I * l2  (which equals -l_bar)

-- theorem dH'_eq : d Ω.H' = -Ω.X' * Ω.Y' := by
--     unfold Ω.H' Ω.X' Ω.Y'
--     simp [d_smul, smul_smul, smul_add, smul_sub]
--     simp [mul_add, mul_sub, add_mul, sub_mul]
--     rw [graded_comm Λ Ω.l2 Ω.l1]
--     simp [l1_mul_l2_eq]
--     simp [smul_smul, smul_add, smul_sub]
--     ring_nf
--     abel

-- theorem dX'_eq : d Ω.X' = 2 • (Ω.X' * Ω.H') := by
--     unfold Ω.X' Ω.H'
--     simp [d_smul, smul_smul, smul_add, smul_sub]
--     simp [mul_add, mul_sub, add_mul, sub_mul]
--     simp [l1_mul_α_eq, l2_mul_α_eq]
--     unfold Ω.l1 Ω.l2
--     simp [d_smul, smul_smul, smul_add, smul_sub]
--     ring_nf
--     simp
--     abel_nf
--     custom_rewrite
--     ring_nf
--     abel

-- theorem dY'_eq : d Ω.Y' = -2 • (Ω.Y' * Ω.H') := by
--     unfold Ω.Y' Ω.H'
--     simp [d_smul, smul_smul, smul_add, smul_sub]
--     simp [mul_add, mul_sub, add_mul, sub_mul]
--     simp [l1_mul_α_eq, l2_mul_α_eq]
--     unfold Ω.l1 Ω.l2
--     simp [d_smul, smul_smul, smul_add, smul_sub]
--     ring_nf
--     simp
--     abel_nf
--     custom_rewrite
--     ring_nf
--     abel
