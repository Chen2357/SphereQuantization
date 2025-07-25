import Sphere.Seven.Fundamental

lemma ι_ξ_k1_dα : ι (ξ k1) (d α) = -(x[6] • d x[4]) + (x[7] • d x[5] + (x[4] • d x[6] + -(x[5] • d x[7]))) := by
  rw [ξ_k1, α]
  simp [d_smul, ι_mul, ι_d]
  abel_nf
  custom_rewrite
  simp

lemma ι_ξ_k2_dα : ι (ξ k2) (d α) = x[5] • d x[4] + (x[7] • d x[6] + (-(x[4] • d x[5]) + -(x[6] • d x[7]))) := by
  rw [ξ_k2, α]
  simp [d_smul, ι_mul, ι_d]
  abel_nf
  custom_rewrite
  simp

lemma ι_ξ_k3_dα : ι (ξ k3) (d α) =  -(x[4] • d x[4]) + -(x[5] • d x[5]) + -(x[6] • d x[6]) + -(x[7] • d x[7]) := by
  rw [ξ_k3, α]
  simp [d_smul, ι_mul, ι_d]
  abel_nf
  custom_rewrite
  simp
  abel

lemma ι_ξ_j1_dα : ι (ξ j1) (d α) = x[0] • d x[2] + (-(x[1] • d x[3]) + (-(x[2] • d x[0]) + x[3] • d x[1])) := by
  rw [ξ_j1, α]
  simp [d_smul, ι_mul, ι_d]
  abel_nf
  custom_rewrite

lemma ι_ξ_j2_dα : ι (ξ j2) (d α) = -(x[0] • d x[1]) + (x[1] • d x[0] + (-(x[2] • d x[3]) + x[3] • d x[2])) := by
  rw [ξ_j2, α]
  simp [d_smul, ι_mul, ι_d]
  abel_nf
  custom_rewrite

lemma ι_ξ_j3_dα : ι (ξ j3) (d α) = -(x[0] • d ↑x[0]) + (-(x[1] • d ↑x[1]) + (-(x[2] • d ↑x[2]) + -(x[3] • d ↑x[3]))) := by
  rw [ξ_j3, α]
  simp [d_smul, ι_mul, ι_d]
  abel_nf
  custom_rewrite

lemma ι_ξ_p0_dα : ι (ξ p0) (d α) = -(x[0] • d ↑x[7]) +
    (-(x[1] • d ↑x[6]) +
      (x[2] • d ↑x[5] +
        (x[3] • d ↑x[4] + (x[4] • d ↑x[3] + (x[5] • d ↑x[2] + (-(x[6] • d ↑x[1]) + -(x[7] • d ↑x[0]))))))) := by
  rw [ξ_p0, α]
  simp [d_smul, ι_mul, ι_d]
  abel_nf
  custom_rewrite

lemma ι_ξ_p1_dα : ι (ξ p1) (d α) = x[0] • d ↑x[6] +
    (-(x[1] • d ↑x[7]) +
      (-(x[2] • d ↑x[4]) +
        (x[3] • d ↑x[5] + (x[4] • d ↑x[2] + (-(x[5] • d ↑x[3]) + (-(x[6] • d ↑x[0]) + x[7] • d ↑x[1])))))) := by
  rw [ξ_p1, α]
  simp [d_smul, ι_mul, ι_d]
  abel_nf
  custom_rewrite

lemma ι_ξ_p2_dα : ι (ξ p2) (d α) = -(x[0] • d ↑x[5]) +
    (x[1] • d ↑x[4] +
      (-(x[2] • d ↑x[7]) +
        (x[3] • d ↑x[6] + (-(x[4] • d ↑x[1]) + (x[5] • d ↑x[0] + (-(x[6] • d ↑x[3]) + x[7] • d ↑x[2])))))) := by
  rw [ξ_p2, α]
  simp [d_smul, ι_mul, ι_d]
  abel_nf
  custom_rewrite

lemma ι_ξ_p3_dα : ι (ξ p3) (d α) = -(x[0] • d ↑x[4]) +
    (-(x[1] • d ↑x[5]) +
      (-(x[2] • d ↑x[6]) +
        (-(x[3] • d ↑x[7]) + (-(x[4] • d ↑x[0]) + (-(x[5] • d ↑x[1]) + (-(x[6] • d ↑x[2]) + -(x[7] • d ↑x[3]))))))) := by
  rw [ξ_p3, α]
  simp [d_smul, ι_mul, ι_d]
  abel_nf
  custom_rewrite
