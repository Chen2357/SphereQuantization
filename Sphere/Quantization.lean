-- import Sphere.Basis
-- import Sphere.Operator
-- import Sphere.Flatness

-- noncomputable section

-- namespace Example

-- def f : Λ0 := x2 * x3 - x0 * x1

-- @[simp] lemma ρf_eq : der ρ f = 0 := by
--   unfold ρ f
--   simp [der_mul]
--   ring

-- @[simp] lemma φ1φ1f_eq : der φ1 (der φ1 f) = (-4 : ℂ) • f := by
--   unfold φ1 f
--   simp [der_mul]
--   simp [Algebra.smul_def, OfNat.ofNat]
--   ring

-- @[simp] lemma φ2φ2f_eq : der φ2 (der φ2 f) = (-4 : ℂ) • f := by
--   unfold φ2 f
--   simp [der_mul]
--   simp [Algebra.smul_def, OfNat.ofNat]
--   ring

-- @[simp] lemma φ1φ2f_eq : der φ1 (der φ2 f) = 0 := by
--   unfold φ1 φ2 f
--   simp [der_mul]
--   simp [Algebra.smul_def, OfNat.ofNat]
--   ring

-- @[simp] lemma φ2φ1f_eq : der φ2 (der φ1 f) = 0 := by
--   unfold φ2 φ1 f
--   simp [der_mul]
--   simp [Algebra.smul_def, OfNat.ofNat]
--   ring

-- @[simp] lemma φφf_eq : der φ (der φ f) = 0 := by
--   unfold φ
--   simp [der_mul]
--   custom_rewrite
--   simp

-- @[simp] lemma φ_bar_φ_bar_f_eq : der φ_bar (der φ_bar f) = 0 := by
--   unfold φ_bar
--   simp [der_mul]
--   custom_rewrite
--   simp

-- @[simp] lemma φφ_bar_f_eq : der φ (der φ_bar f) = (-2 : ℂ) • f := by
--   unfold φ φ_bar
--   simp [der_mul]
--   custom_rewrite
--   simp
--   rw [two_smul]
--   ring

-- @[simp] lemma φ_bar_φ_f_eq : der φ_bar (der φ f) = (-2 : ℂ) • f := by
--   unfold φ_bar φ
--   simp [der_mul]
--   custom_rewrite
--   simp
--   rw [two_smul]
--   ring

-- def fp := (-Complex.I) • (der φ_bar f)
-- def fm := (Complex.I) • (der φ f)

-- open TensorProduct

-- def f_hat : EOp := (f : E) ⊗ₜ[ℂ] k3 + (fp : E) ⊗ₜ[ℂ] kp + (fm : E) ⊗ₜ[ℂ] km

-- theorem del_f_hat_eq_zero : del f_hat = 0 := by
--   simp [del, f_hat, d_lift, d_lift', A]
--   simp only [mul_add, mul_sub, add_mul, sub_mul]
--   sorry

-- end Example
