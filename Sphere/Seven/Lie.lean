import Sphere.Seven.Alpha
import Sphere.Seven.DifferentialAlpha
import Sphere.Seven.Reeb

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

@[simp]
lemma lie_ξ_j1_R : ⁅ξ j1, R⁆ = 0 := by
  simp only [ξ_j1, R, lie_smul, smul_lie]
  simp only [lie_add, add_lie, lie_sub, sub_lie, lie_Λ0smul, Λ0smul_lie]
  simp [smul_smul]
  abel

@[simp]
lemma lie_ξ_j2_R : ⁅ξ j2, R⁆ = 0 := by
  simp only [ξ_j2, R, lie_smul, smul_lie]
  simp only [lie_add, add_lie, lie_sub, sub_lie, lie_Λ0smul, Λ0smul_lie]
  simp [smul_smul]
  abel

@[simp]
lemma lie_ξ_j3_R : ⁅ξ j3, R⁆ = 0 := by
  simp only [ξ_j3, R, lie_smul, smul_lie]
  simp only [lie_add, add_lie, lie_sub, sub_lie, lie_Λ0smul, Λ0smul_lie]
  simp [smul_smul]

@[simp]
lemma lie_ξ_k1_R : ⁅ξ k1, R⁆ = 0 := by
  simp only [ξ_k1, R, lie_smul, smul_lie]
  simp only [lie_add, add_lie, lie_sub, sub_lie, lie_Λ0smul, Λ0smul_lie]
  simp [smul_smul]
  abel

@[simp]
lemma lie_ξ_k2_R : ⁅ξ k2, R⁆ = 0 := by
  simp only [ξ_k2, R, lie_smul, smul_lie]
  simp only [lie_add, add_lie, lie_sub, sub_lie, lie_Λ0smul, Λ0smul_lie]
  simp [smul_smul]
  abel

@[simp]
lemma lie_ξ_k3_R : ⁅ξ k3, R⁆ = 0 := by
  simp only [ξ_k3, R, lie_smul, smul_lie]
  simp only [lie_add, add_lie, lie_sub, sub_lie, lie_Λ0smul, Λ0smul_lie]
  simp [smul_smul]
  abel

@[simp]
lemma lie_ξ_p0_R : ⁅ξ p0, R⁆ = 0 := by
  simp only [ξ_p0, R, lie_smul, smul_lie]
  simp only [lie_add, add_lie, lie_sub, sub_lie, lie_Λ0smul, Λ0smul_lie]
  simp [smul_smul, lie_Λ0smul]
  abel

@[simp]
lemma lie_ξ_p1_R : ⁅ξ p1, R⁆ = 0 := by
  simp only [ξ_p1, R, lie_smul, smul_lie]
  simp only [lie_add, add_lie, lie_sub, sub_lie, lie_Λ0smul, Λ0smul_lie]
  simp [smul_smul, lie_Λ0smul]
  abel

@[simp]
lemma lie_ξ_p2_R : ⁅ξ p2, R⁆ = 0 := by
  simp only [ξ_p2, R, lie_smul, smul_lie]
  simp only [lie_add, add_lie, lie_sub, sub_lie, lie_Λ0smul, Λ0smul_lie]
  simp [smul_smul, lie_Λ0smul]
  abel

@[simp]
lemma lie_ξ_p3_R : ⁅ξ p3, R⁆ = 0 := by
  simp only [ξ_p3, R, lie_smul, smul_lie]
  simp only [lie_add, add_lie, lie_sub, sub_lie, lie_Λ0smul, Λ0smul_lie]
  simp [smul_smul, lie_Λ0smul]
  abel
