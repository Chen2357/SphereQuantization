import Sphere.Seven.Fundamental

lemma ι_ξ_k1_α : ι (ξ k1) α = x[4] * x[6] + x[5] * x[7] := by
  simp [ξ_k1, α, ι_d]
  simp [subalgebra_smul_eq_cast_mul]
  norm_cast
  ring_nf
  simp [mul_two, ←smul_add, ←two_smul ℂ, smul_smul]

lemma ι_ξ_k2_α : ι (ξ k2) α = -(x[4] * x[5]) + x[6] * x[7] := by
  simp [ξ_k2, α, ι_d]
  simp [subalgebra_smul_eq_cast_mul]
  norm_cast
  ring_nf
  simp [mul_two, ←smul_add, ←two_smul ℂ, smul_smul]

lemma ι_ξ_k3_α : ι (ξ k3) α = (2⁻¹ : ℂ) • (x[4] * x[4] - x[5] * x[5] - x[6] * x[6] + x[7] * x[7]) := by
  simp [ξ_k3, α, ι_d]
  simp [subalgebra_smul_eq_cast_mul, smul_add, smul_sub]
  abel

lemma ι_ξ_j1_α : ι (ξ j1) α =  x[0] * x[2] + x[1] * x[3] := by
  simp [ξ_j1, α, ι_d]
  simp [subalgebra_smul_eq_cast_mul]
  norm_cast
  ring_nf
  simp [mul_two, ←smul_add, ←two_smul ℂ, smul_smul]

lemma ι_ξ_j2_α : ι (ξ j2) α = -(x[0] * x[1]) + x[2] * x[3] := by
  simp [ξ_j2, α, ι_d]
  simp [subalgebra_smul_eq_cast_mul]
  norm_cast
  ring_nf
  simp [mul_two, ←smul_add, ←two_smul ℂ, smul_smul]

lemma ι_ξ_j3_α : ι (ξ j3) α = (2⁻¹ : ℂ) • (x[0] * x[0] - x[1] * x[1] - x[2] * x[2] + x[3] * x[3]) := by
  simp [ξ_j3, α, ι_d]
  simp [subalgebra_smul_eq_cast_mul, smul_add, smul_sub]
  norm_cast
  ring

lemma ι_ξ_p0_α : ι (ξ p0) α = x[0] * x[7] - x[1] * x[6] + x[2] * x[5] - x[3] * x[4] := by
  simp [ξ_p0, α, ι_d]
  simp [subalgebra_smul_eq_cast_mul]
  norm_cast
  ring_nf
  simp only [mul_two, ←smul_add, ←smul_sub, ←smul_neg]
  simp only [←two_smul ℂ, smul_add, smul_sub, smul_neg, smul_smul]
  simp

lemma ι_ξ_p1_α : ι (ξ p1) α = x[0] * x[6] + x[1] * x[7] + x[2] * x[4] + x[3] * x[5] := by
  simp [ξ_p1, α, ι_d]
  simp [subalgebra_smul_eq_cast_mul]
  norm_cast
  ring_nf
  simp only [mul_two, ←smul_add, ←smul_sub, ←smul_neg]
  simp only [←two_smul ℂ, smul_add, smul_sub, smul_neg, smul_smul]
  simp

lemma ι_ξ_p2_α : ι (ξ p2) α = -(x[0] * x[5]) - x[1] * x[4] + x[2] * x[7] + x[3] * x[6] := by
  simp [ξ_p2, α, ι_d]
  simp [subalgebra_smul_eq_cast_mul]
  norm_cast
  ring_nf
  simp only [mul_two, ←smul_add, ←smul_sub, ←smul_neg]
  simp only [←two_smul ℂ, smul_add, smul_sub, smul_neg, smul_smul]
  simp

lemma ι_ξ_p3_α : ι (ξ p3) α = x[0] * x[4] - x[1] * x[5] - x[2] * x[6] + x[3] * x[7] := by
  simp [ξ_p3, α, ι_d]
  simp [subalgebra_smul_eq_cast_mul]
  norm_cast
  ring_nf
  simp [mul_two, ←smul_add, ←two_smul ℂ, smul_smul]
