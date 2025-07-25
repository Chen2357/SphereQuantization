import Sphere.Seven.Alpha
import Sphere.Seven.DifferentialAlpha

lemma L_ξ_k1_α : L (ξ k1) α = -(x[6] • d x[4]) + (x[7] • d x[5] + (x[4] • d x[6] + -(x[5] • d x[7]))) := by
  simp [L, ι_ξ_k1_α, ι_ξ_k1_dα]

lemma L_ξ_k2_α : L (ξ k2) α = x[5] • d x[4] + (x[7] • d x[6] + (-(x[4] • d x[5]) + -(x[6] • d x[7]))) := by
  simp [L, ι_ξ_k2_α, ι_ξ_k2_dα]

lemma L_ξ_k3_α : L (ξ k3) α = 0 := by
  simp [L, ι_ξ_k3_α, ι_ξ_k3_dα, d_mul, ←smul_add, ←two_smul ℂ, subalgebra_smul_eq_cast_mul]
  abel

lemma L_ξ_j1_α : L (ξ j1) α = x[0] • d x[2] + (-(x[1] • d x[3]) + (-(x[2] • d x[0]) + x[3] • d x[1])) := by
  simp [L, ι_ξ_j1_α, ι_ξ_j1_dα]

lemma L_ξ_j2_α : L (ξ j2) α = -(x[0] • d x[1]) + (x[1] • d x[0] + (-(x[2] • d x[3]) + x[3] • d x[2])) := by
  simp [L, ι_ξ_j2_α, ι_ξ_j2_dα]

lemma L_ξ_j3_α : L (ξ j3) α = 0 := by
  simp [L, ι_ξ_j3_α, ι_ξ_j3_dα, d_mul, ←smul_add, ←two_smul ℂ, subalgebra_smul_eq_cast_mul]
  abel

lemma L_ξ_p0_α : L (ξ p0) α = 0 := by
  simp [L, ι_ξ_p0_α, ι_ξ_p0_dα, d_mul, subalgebra_smul_eq_cast_mul]
  abel

lemma L_ξ_p1_α : L (ξ p1) α = x[0] • d ↑x[6] +
    (-(x[1] • d ↑x[7]) +
      (-(x[2] • d ↑x[4]) +
        (x[3] • d ↑x[5] + (x[4] • d ↑x[2] + (-(x[5] • d ↑x[3]) + (-(x[6] • d ↑x[0]) + x[7] • d ↑x[1])))))) := by
  simp [L, ι_ξ_p1_α, ι_ξ_p1_dα]

lemma L_ξ_p2_α : L (ξ p2) α = -(x[0] • d ↑x[5]) +
    (x[1] • d ↑x[4] +
      (-(x[2] • d ↑x[7]) +
        (x[3] • d ↑x[6] + (-(x[4] • d ↑x[1]) + (x[5] • d ↑x[0] + (-(x[6] • d ↑x[3]) + x[7] • d ↑x[2])))))) := by
  simp [L, ι_ξ_p2_α, ι_ξ_p2_dα]

lemma L_ξ_p3_α : L (ξ p3) α = 0 := by
  simp [L, ι_ξ_p3_α, ι_ξ_p3_dα, d_mul, subalgebra_smul_eq_cast_mul]
  abel
