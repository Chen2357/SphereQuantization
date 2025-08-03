import Sphere.Seven.Basis
import Sphere.Seven.Commutation

open Matrix

private lemma h' (X : S) (Y : M) : ∑ k, decomp (X) k • (Y *ᵥ (basis k)) = Y *ᵥ X := by
  simp [Finset.sum]
  ext1 j
  fin_cases j
  all_goals simp [mulVec, vecHead, vecTail, mul_apply]
  all_goals ext

  all_goals simp only [
    Quaternion.add_re, Quaternion.add_imI, Quaternion.add_imJ, Quaternion.add_imK,
    Quaternion.smul_re, Quaternion.smul_imI, Quaternion.smul_imJ, Quaternion.smul_imK,
    Quaternion.mul_re, Quaternion.mul_imI, Quaternion.mul_imJ, Quaternion.mul_imK,
    mul_one, mul_zero, sub_zero, smul_eq_mul, zero_sub, mul_neg, sub_self, zero_add, add_zero
  ]
  all_goals ring

private lemma h (i j : Fin 8) (X Y : M) : ∑ k, decomp (X *ᵥ (basis i)) k * decomp (Y *ᵥ (basis k)) j = decomp ((Y * X) *ᵥ (basis i)) j := by
  conv_rhs =>
    arg 2
    rw [←mulVec_mulVec, ←h']
  simp

lemma lie_ξ (x y : M) : ⁅ξ x, ξ y⁆ = ξ ⁅y, x⁆ := by
  conv_lhs =>
    simp [ξ, -basis, -decomp]
    simp only [lie_sum, sum_lie]
    arg 2; intro i
    arg 2; intro j
    arg 2; intro i'
    arg 2; intro j'
    simp only [lie_smul, smul_lie, Λ0smul_lie, lie_Λ0smul, lie_px_px]
    simp [-basis, -decomp]

  conv_lhs =>
    simp only [Finset.sum_add_distrib]
    congr
    . arg 2; intro i
      arg 2; intro j
      arg 2; intro i'
      rw [Finset.sum_eq_single_of_mem i (by apply Finset.mem_univ) (by
        intro k _ hk
        simp [-basis, -decomp]
        intro h
        refine absurd ?_ hk
        exact Fin.eq_of_val_eq h
      )]
      . simp [-basis, -decomp]
    . arg 2; intro i
      arg 2; intro j
      rw [Finset.sum_eq_single_of_mem j (by apply Finset.mem_univ) (by
        intro k _ hk
        simp [-basis, -decomp]
        intro h
        refine absurd ?_ hk
        exact Fin.eq_of_val_eq (Eq.symm h)
      )]
      simp only [reduceIte]

  conv_lhs =>
    congr
    . rw [Finset.sum_comm, Finset.sum_comm_cycle]
    . rw [Finset.sum_comm_cycle, Finset.sum_comm]

  conv_lhs =>
    simp only [Finset.sum_neg_distrib, ←sub_eq_add_neg]

  conv_rhs =>
    simp [ξ, -basis, -decomp]
    rw [Ring.lie_def]
    simp [sub_mulVec, -basis, -decomp, ←Finset.sum_neg_distrib]
    arg 2; intro i
    arg 2; intro j
    rw [sub_smul]

  conv_rhs =>
    simp only [Finset.sum_sub_distrib]

  congr
  . ext i
    congr; ext j
    conv_lhs =>
      simp only [←smul_assoc]
      rw [←Finset.sum_smul, ←Finset.sum_smul]
    rw [smul_assoc]
    congr
    simp only [HSMul.hSMul, SMul.smul, mul_comm]
    apply h
  . ext i
    congr; ext j
    conv_lhs =>
      simp only [←smul_assoc]
      rw [←Finset.sum_smul, ←Finset.sum_smul]
    rw [smul_assoc]
    congr
    apply h

lemma ξ_lie (x y : M) : ξ ⁅x, y⁆ = ⁅ξ y, ξ x⁆ := by
  simp [lie_ξ]

section lie_ξ_j_ξ_j

lemma lie_ξ_j1_ξ_j2 : ⁅ξ j1, ξ j2⁆ = -ξ j3 := by
  simp [lie_ξ, lie_j2_j1]

lemma lie_ξ_j2_ξ_j1 : ⁅ξ j2, ξ j1⁆ = ξ j3 := by
  simp [lie_ξ, lie_j1_j2]

lemma lie_ξ_j1_ξ_j3 : ⁅ξ j1, ξ j3⁆ = ξ j2 := by
  simp [lie_ξ, lie_j3_j1]

lemma lie_ξ_j3_ξ_j1 : ⁅ξ j3, ξ j1⁆ = -ξ j2 := by
  simp [lie_ξ, lie_j1_j3]

lemma lie_ξ_j2_ξ_j3 : ⁅ξ j2, ξ j3⁆ = -ξ j1 := by
  simp [lie_ξ, lie_j3_j2]

lemma lie_ξ_j3_ξ_j2 : ⁅ξ j3, ξ j2⁆ = ξ j1 := by
  simp [lie_ξ, lie_j2_j3]

end lie_ξ_j_ξ_j

section lie_ξ_k_ξ_k

lemma lie_ξ_k1_ξ_k2 : ⁅ξ k1, ξ k2⁆ = -ξ k3 := by
  simp [lie_ξ, lie_k2_k1]

lemma lie_ξ_k2_ξ_k1 : ⁅ξ k2, ξ k1⁆ = ξ k3 := by
  simp [lie_ξ, lie_k1_k2]

lemma lie_ξ_k1_ξ_k3 : ⁅ξ k1, ξ k3⁆ = ξ k2 := by
  simp [lie_ξ, lie_k3_k1]

lemma lie_ξ_k3_ξ_k1 : ⁅ξ k3, ξ k1⁆ = -ξ k2 := by
  simp [lie_ξ, lie_k1_k3]

lemma lie_ξ_k2_ξ_k3 : ⁅ξ k2, ξ k3⁆ = -ξ k1 := by
  simp [lie_ξ, lie_k3_k2]

lemma lie_ξ_k3_ξ_k2 : ⁅ξ k3, ξ k2⁆ = ξ k1 := by
  simp [lie_ξ, lie_k2_k3]

end lie_ξ_k_ξ_k

section lie_ξ_p0_ξ_j

lemma lie_ξ_p0_ξ_j1 : ⁅ξ p0, ξ j1⁆ = (2⁻¹ : ℂ) • ξ p1 := by
  simp [lie_ξ, lie_j1_p0]

lemma lie_ξ_j1_ξ_p0 : ⁅ξ j1, ξ p0⁆ = (-2⁻¹ : ℂ) • ξ p1 := by
  simp [lie_ξ, lie_p0_j1]

lemma lie_ξ_p0_ξ_j2 : ⁅ξ p0, ξ j2⁆ = (2⁻¹ : ℂ) • ξ p2 := by
  simp [lie_ξ, lie_j2_p0]

lemma lie_ξ_j2_ξ_p0 : ⁅ξ j2, ξ p0⁆ = (-2⁻¹ : ℂ) • ξ p2 := by
  simp [lie_ξ, lie_p0_j2]

lemma lie_ξ_p0_ξ_j3 : ⁅ξ p0, ξ j3⁆ = (2⁻¹ : ℂ) • ξ p3 := by
  simp [lie_ξ, lie_j3_p0]

lemma lie_ξ_j3_ξ_p0 : ⁅ξ j3, ξ p0⁆ = (-2⁻¹ : ℂ) • ξ p3 := by
  simp [lie_ξ, lie_p0_j3]

end lie_ξ_p0_ξ_j

section lie_ξ_p0_ξ_k

lemma lie_ξ_p0_ξ_k1 : ⁅ξ p0, ξ k1⁆ = (-2⁻¹ : ℂ) • ξ p1 := by
  simp [lie_ξ, lie_k1_p0]

lemma lie_ξ_k1_ξ_p0 : ⁅ξ k1, ξ p0⁆ = (2⁻¹ : ℂ) • ξ p1 := by
  simp [lie_ξ, lie_p0_k1]

lemma lie_ξ_p0_ξ_k2 : ⁅ξ p0, ξ k2⁆ = (-2⁻¹ : ℂ) • ξ p2 := by
  simp [lie_ξ, lie_k2_p0]

lemma lie_ξ_k2_ξ_p0 : ⁅ξ k2, ξ p0⁆ = (2⁻¹ : ℂ) • ξ p2 := by
  simp [lie_ξ, lie_p0_k2]

lemma lie_ξ_p0_ξ_k3 : ⁅ξ p0, ξ k3⁆ = (-2⁻¹ : ℂ) • ξ p3 := by
  simp [lie_ξ, lie_k3_p0]

lemma lie_ξ_k3_ξ_p0 : ⁅ξ k3, ξ p0⁆ = (2⁻¹ : ℂ) • ξ p3 := by
  simp [lie_ξ, lie_p0_k3]

end lie_ξ_p0_ξ_k

section lie_ξ_p0_ξ_p

lemma lie_ξ_p0_ξ_p1 : ⁅ξ p0, ξ p1⁆ = -ξ j1 + ξ k1 := by
  simp [lie_ξ, lie_p1_p0]

lemma lie_ξ_p1_ξ_p0 : ⁅ξ p1, ξ p0⁆ = ξ j1 - ξ k1 := by
  simp [lie_ξ, lie_p0_p1]

lemma lie_ξ_p0_ξ_p2 : ⁅ξ p0, ξ p2⁆ = -ξ j2 + ξ k2 := by
  simp [lie_ξ, lie_p2_p0]

lemma lie_ξ_p2_ξ_p0 : ⁅ξ p2, ξ p0⁆ = ξ j2 - ξ k2 := by
  simp [lie_ξ, lie_p0_p2]

lemma lie_ξ_p0_ξ_p3 : ⁅ξ p0, ξ p3⁆ = -ξ j3 + ξ k3 := by
  simp [lie_ξ, lie_p3_p0]

lemma lie_ξ_p3_ξ_p0 : ⁅ξ p3, ξ p0⁆ = ξ j3 - ξ k3 := by
  simp [lie_ξ, lie_p0_p3]

end lie_ξ_p0_ξ_p

section lie_ξ_p_ξ_j

lemma lie_ξ_p1_ξ_j1 : ⁅ξ p1, ξ j1⁆ = (-2⁻¹ : ℂ) • ξ p0 := by
  simp [lie_ξ, lie_j1_p1]

lemma lie_ξ_j1_ξ_p1 : ⁅ξ j1, ξ p1⁆ = (2⁻¹ : ℂ) • ξ p0 := by
  simp [lie_ξ, lie_p1_j1]

lemma lie_ξ_p2_ξ_j2 : ⁅ξ p2, ξ j2⁆ = (-2⁻¹ : ℂ) • ξ p0 := by
  simp [lie_ξ, lie_j2_p2]

lemma lie_ξ_j2_ξ_p2 : ⁅ξ j2, ξ p2⁆ = (2⁻¹ : ℂ) • ξ p0 := by
  simp [lie_ξ, lie_p2_j2]

lemma lie_ξ_p3_ξ_j3 : ⁅ξ p3, ξ j3⁆ = (-2⁻¹ : ℂ) • ξ p0 := by
  simp [lie_ξ, lie_j3_p3]

lemma lie_ξ_j3_ξ_p3 : ⁅ξ j3, ξ p3⁆ = (2⁻¹ : ℂ) • ξ p0 := by
  simp [lie_ξ, lie_p3_j3]

lemma lie_ξ_p1_ξ_j2 : ⁅ξ p1, ξ j2⁆ = (-2⁻¹ : ℂ) • ξ p3 := by
  simp [lie_ξ, lie_j2_p1]

lemma lie_ξ_j2_ξ_p1 : ⁅ξ j2, ξ p1⁆ = (2⁻¹ : ℂ) • ξ p3 := by
  simp [lie_ξ, lie_p1_j2]

lemma lie_ξ_p1_ξ_j3 : ⁅ξ p1, ξ j3⁆ = (2⁻¹ : ℂ) • ξ p2 := by
  simp [lie_ξ, lie_j3_p1]

lemma lie_ξ_j3_ξ_p1 : ⁅ξ j3, ξ p1⁆ = (-2⁻¹ : ℂ) • ξ p2 := by
  simp [lie_ξ, lie_p1_j3]

lemma lie_ξ_p2_ξ_j1 : ⁅ξ p2, ξ j1⁆ = (2⁻¹ : ℂ) • ξ p3 := by
  simp [lie_ξ, lie_j1_p2]

lemma lie_ξ_j1_ξ_p2 : ⁅ξ j1, ξ p2⁆ = (-2⁻¹ : ℂ) • ξ p3 := by
  simp [lie_ξ, lie_p2_j1]

lemma lie_ξ_p2_ξ_j3 : ⁅ξ p2, ξ j3⁆ = (-2⁻¹ : ℂ) • ξ p1 := by
  simp [lie_ξ, lie_j3_p2]

lemma lie_ξ_j3_ξ_p2 : ⁅ξ j3, ξ p2⁆ = (2⁻¹ : ℂ) • ξ p1 := by
  simp [lie_ξ, lie_p2_j3]

lemma lie_ξ_p3_ξ_j1 : ⁅ξ p3, ξ j1⁆ = (-2⁻¹ : ℂ) • ξ p2 := by
  simp [lie_ξ, lie_j1_p3]

lemma lie_ξ_j1_ξ_p3 : ⁅ξ j1, ξ p3⁆ = (2⁻¹ : ℂ) • ξ p2 := by
  simp [lie_ξ, lie_p3_j1]

lemma lie_ξ_p3_ξ_j2 : ⁅ξ p3, ξ j2⁆ = (2⁻¹ : ℂ) • ξ p1 := by
  simp [lie_ξ, lie_j2_p3]

lemma lie_ξ_j2_ξ_p3 : ⁅ξ j2, ξ p3⁆ = (-2⁻¹ : ℂ) • ξ p1 := by
  simp [lie_ξ, lie_p3_j2]

end lie_ξ_p_ξ_j

section lie_ξ_p_ξ_p

lemma lie_ξ_p1_ξ_p2 : ⁅ξ p1, ξ p2⁆ = ξ (-j3 - k3) := by
  simp [lie_ξ, lie_p2_p1]

lemma lie_ξ_p2_ξ_p1 : ⁅ξ p2, ξ p1⁆ = ξ (j3 + k3) := by
  simp [lie_ξ, lie_p1_p2]

lemma lie_ξ_p1_ξ_p3 : ⁅ξ p1, ξ p3⁆ = ξ (j2 + k2) := by
  simp [lie_ξ, lie_p3_p1]

lemma lie_ξ_p3_ξ_p1 : ⁅ξ p3, ξ p1⁆ = ξ (-j2 - k2) := by
  simp [lie_ξ, lie_p1_p3]

lemma lie_ξ_p2_ξ_p3 : ⁅ξ p2, ξ p3⁆ = ξ (-j1 - k1) := by
  simp [lie_ξ, lie_p3_p2]

lemma lie_ξ_p3_ξ_p2 : ⁅ξ p3, ξ p2⁆ = ξ (j1 + k1) := by
  simp [lie_ξ, lie_p2_p3]

end lie_ξ_p_ξ_p

section lie_ξ_p_ξ_k

lemma lie_ξ_p1_ξ_k1 : ⁅ξ p1, ξ k1⁆ = (2⁻¹ : ℂ) • ξ p0 := by
  simp [lie_ξ, lie_k1_p1]

lemma lie_ξ_k1_ξ_p1 : ⁅ξ k1, ξ p1⁆ = (-2⁻¹ : ℂ) • ξ p0 := by
  simp [lie_ξ, lie_p1_k1]

lemma lie_ξ_p2_ξ_k2 : ⁅ξ p2, ξ k2⁆ = (2⁻¹ : ℂ) • ξ p0 := by
  simp [lie_ξ, lie_k2_p2]

lemma lie_ξ_k2_ξ_p2 : ⁅ξ k2, ξ p2⁆ = (-2⁻¹ : ℂ) • ξ p0 := by
  simp [lie_ξ, lie_p2_k2]

lemma lie_ξ_p3_ξ_k3 : ⁅ξ p3, ξ k3⁆ = (2⁻¹ : ℂ) • ξ p0 := by
  simp [lie_ξ, lie_k3_p3]

lemma lie_ξ_k3_ξ_p3 : ⁅ξ k3, ξ p3⁆ = (-2⁻¹ : ℂ) • ξ p0 := by
  simp [lie_ξ, lie_p3_k3]

lemma lie_ξ_p1_ξ_k2 : ⁅ξ p1, ξ k2⁆ = (-2⁻¹ : ℂ) • ξ p3 := by
  simp [lie_ξ, lie_k2_p1]

lemma lie_ξ_k2_ξ_p1 : ⁅ξ k2, ξ p1⁆ = (2⁻¹ : ℂ) • ξ p3 := by
  simp [lie_ξ, lie_p1_k2]

lemma lie_ξ_p1_ξ_k3 : ⁅ξ p1, ξ k3⁆ = (2⁻¹ : ℂ) • ξ p2 := by
  simp [lie_ξ, lie_k3_p1]

lemma lie_ξ_k3_ξ_p1 : ⁅ξ k3, ξ p1⁆ = (-2⁻¹ : ℂ) • ξ p2 := by
  simp [lie_ξ, lie_p1_k3]

lemma lie_ξ_p2_ξ_k1 : ⁅ξ p2, ξ k1⁆ = (2⁻¹ : ℂ) • ξ p3 := by
  simp [lie_ξ, lie_k1_p2]

lemma lie_ξ_k1_ξ_p2 : ⁅ξ k1, ξ p2⁆ = (-2⁻¹ : ℂ) • ξ p3 := by
  simp [lie_ξ, lie_p2_k1]

lemma lie_ξ_p2_ξ_k3 : ⁅ξ p2, ξ k3⁆ = (-2⁻¹ : ℂ) • ξ p1 := by
  simp [lie_ξ, lie_k3_p2]

lemma lie_ξ_k3_ξ_p2 : ⁅ξ k3, ξ p2⁆ = (2⁻¹ : ℂ) • ξ p1 := by
  simp [lie_ξ, lie_p2_k3]

lemma lie_ξ_p3_ξ_k1 : ⁅ξ p3, ξ k1⁆ = (-2⁻¹ : ℂ) • ξ p2 := by
  simp [lie_ξ, lie_k1_p3]

lemma lie_ξ_k1_ξ_p3 : ⁅ξ k1, ξ p3⁆ = (2⁻¹ : ℂ) • ξ p2 := by
  simp [lie_ξ, lie_p3_k1]

lemma lie_ξ_p3_ξ_k2 : ⁅ξ p3, ξ k2⁆ = (2⁻¹ : ℂ) • ξ p1 := by
  simp [lie_ξ, lie_k2_p3]

lemma lie_ξ_k2_ξ_p3 : ⁅ξ k2, ξ p3⁆ = (-2⁻¹ : ℂ) • ξ p1 := by
  simp [lie_ξ, lie_p3_k2]

end lie_ξ_p_ξ_k
