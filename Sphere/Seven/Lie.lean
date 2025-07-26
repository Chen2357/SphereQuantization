import Sphere.Seven.Alpha
import Sphere.Seven.DifferentialAlpha

@[simp]
lemma L_ξ_k1_α : L (ξ k1) α = 0 := by
  simp [L, ι_ξ_k1_α, ι_ξ_k1_dα, d_mul, subalgebra_smul_eq_cast_mul]
  abel

@[simp]
lemma L_ξ_k2_α : L (ξ k2) α = 0 := by
  simp [L, ι_ξ_k2_α, ι_ξ_k2_dα, d_mul, subalgebra_smul_eq_cast_mul]
  abel

@[simp]
lemma L_ξ_k3_α : L (ξ k3) α = 0 := by
  simp [L, ι_ξ_k3_α, ι_ξ_k3_dα, d_mul, ←smul_add, ←two_smul ℂ, smul_smul, smul_add, smul_sub, subalgebra_smul_eq_cast_mul]
  abel

@[simp]
lemma L_ξ_j1_α : L (ξ j1) α = 0 := by
  simp [L, ι_ξ_j1_α, ι_ξ_j1_dα, d_mul, subalgebra_smul_eq_cast_mul]
  abel

@[simp]
lemma L_ξ_j2_α : L (ξ j2) α = 0 := by
  simp [L, ι_ξ_j2_α, ι_ξ_j2_dα, d_mul, subalgebra_smul_eq_cast_mul]
  abel

@[simp]
lemma L_ξ_j3_α : L (ξ j3) α = 0 := by
  simp [L, ι_ξ_j3_α, ι_ξ_j3_dα, d_mul, ←smul_add, ←two_smul ℂ, smul_smul, smul_add, smul_sub, subalgebra_smul_eq_cast_mul]
  abel

@[simp]
lemma L_ξ_p0_α : L (ξ p0) α = 0 := by
  simp [L, ι_ξ_p0_α, ι_ξ_p0_dα, d_mul, subalgebra_smul_eq_cast_mul]
  abel

@[simp]
lemma L_ξ_p1_α : L (ξ p1) α = 0 := by
  simp [L, ι_ξ_p1_α, ι_ξ_p1_dα, d_mul, subalgebra_smul_eq_cast_mul]
  abel

@[simp]
lemma L_ξ_p2_α : L (ξ p2) α = 0 := by
  simp [L, ι_ξ_p2_α, ι_ξ_p2_dα, d_mul, subalgebra_smul_eq_cast_mul]
  abel

@[simp]
lemma L_ξ_p3_α : L (ξ p3) α = 0 := by
  simp [L, ι_ξ_p3_α, ι_ξ_p3_dα, d_mul, subalgebra_smul_eq_cast_mul]
  abel
