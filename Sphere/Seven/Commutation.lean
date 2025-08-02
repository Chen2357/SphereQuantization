import Sphere.Seven.Basis
import Mathlib.Algebra.Lie.Matrix

open Matrix

section lie_j_j

lemma lie_j1_j2 : ⁅j1, j2⁆ = j3 := by
  rw [Ring.lie_def]
  unfold j1 j2 j3
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  ext
  all_goals simp
  ring

lemma lie_j2_j1 : ⁅j2, j1⁆ = -j3 := by
  rw [←lie_skew, lie_j1_j2]

lemma lie_j1_j3 : ⁅j1, j3⁆ = -j2 := by
  rw [Ring.lie_def]
  unfold j1 j2 j3
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  ext
  all_goals simp
  ring

lemma lie_j3_j1 : ⁅j3, j1⁆ = j2 := by
  rw [←lie_skew, lie_j1_j3, neg_neg]

lemma lie_j2_j3 : ⁅j2, j3⁆ = j1 := by
  rw [Ring.lie_def]
  unfold j1 j2 j3
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  ext
  all_goals simp
  ring

lemma lie_j3_j2 : ⁅j3, j2⁆ = -j1 := by
  rw [←lie_skew, lie_j2_j3]

end lie_j_j

section lie_k_k

lemma lie_k1_k2 : ⁅k1, k2⁆ = k3 := by
  rw [Ring.lie_def]
  unfold k1 k2 k3
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  ext
  all_goals simp
  ring

lemma lie_k2_k1 : ⁅k2, k1⁆ = -k3 := by
  rw [←lie_skew, lie_k1_k2]

lemma lie_k1_k3 : ⁅k1, k3⁆ = -k2 := by
  rw [Ring.lie_def]
  unfold k1 k2 k3
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  ext
  all_goals simp
  ring

lemma lie_k3_k1 : ⁅k3, k1⁆ = k2 := by
  rw [←lie_skew, lie_k1_k3, neg_neg]

lemma lie_k2_k3 : ⁅k2, k3⁆ = k1 := by
  rw [Ring.lie_def]
  unfold k1 k2 k3
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  ext
  all_goals simp
  ring

lemma lie_k3_k2 : ⁅k3, k2⁆ = -k1 := by
  rw [←lie_skew, lie_k2_k3]

end lie_k_k

section lie_p0_j

lemma lie_p0_j1 : ⁅p0, j1⁆ = (-2⁻¹ : ℂ) • p1 := by
  rw [Ring.lie_def]
  unfold p0 j1 p1
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  any_goals rw [DistribMulAction.smul_zero]
  all_goals ext
  all_goals simp

lemma lie_j1_p0 : ⁅j1, p0⁆ = (2⁻¹ : ℂ) • p1 := by
  rw [←lie_skew, lie_p0_j1, neg_smul (2⁻¹ : ℂ) p1, neg_neg]

lemma lie_p0_j2 : ⁅p0, j2⁆ = (-2⁻¹ : ℂ) • p2 := by
  rw [Ring.lie_def]
  unfold p0 j2 p2
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  any_goals rw [DistribMulAction.smul_zero]
  all_goals ext
  all_goals simp

lemma lie_j2_p0 : ⁅j2, p0⁆ = (2⁻¹ : ℂ) • p2 := by
  rw [←lie_skew, lie_p0_j2, neg_smul (2⁻¹ : ℂ) p2, neg_neg]

lemma lie_p0_j3 : ⁅p0, j3⁆ = (-2⁻¹ : ℂ) • p3 := by
  rw [Ring.lie_def]
  unfold p0 j3 p3
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  any_goals rw [DistribMulAction.smul_zero]
  all_goals ext
  all_goals simp

lemma lie_j3_p0 : ⁅j3, p0⁆ = (2⁻¹ : ℂ) • p3 := by
  rw [←lie_skew, lie_p0_j3, neg_smul (2⁻¹ : ℂ) p3, neg_neg]

end lie_p0_j

section lie_p0_k

lemma lie_p0_k1 : ⁅p0, k1⁆ = (2⁻¹ : ℂ) • p1 := by
  rw [Ring.lie_def]
  unfold p0 k1 p1
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  any_goals rw [DistribMulAction.smul_zero]
  all_goals ext
  all_goals simp

lemma lie_k1_p0 : ⁅k1, p0⁆ = (-2⁻¹ : ℂ) • p1 := by
  rw [←lie_skew, lie_p0_k1, neg_smul (2⁻¹ : ℂ) p1]

lemma lie_p0_k2 : ⁅p0, k2⁆ = (2⁻¹ : ℂ) • p2 := by
  rw [Ring.lie_def]
  unfold p0 k2 p2
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  any_goals rw [DistribMulAction.smul_zero]
  all_goals ext
  all_goals simp

lemma lie_k2_p0 : ⁅k2, p0⁆ = (-2⁻¹ : ℂ) • p2 := by
  rw [←lie_skew, lie_p0_k2, neg_smul (2⁻¹ : ℂ) p2]

lemma lie_p0_k3 : ⁅p0, k3⁆ = (2⁻¹ : ℂ) • p3 := by
  rw [Ring.lie_def]
  unfold p0 k3 p3
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  any_goals rw [DistribMulAction.smul_zero]
  all_goals ext
  all_goals simp

lemma lie_k3_p0 : ⁅k3, p0⁆ = (-2⁻¹ : ℂ) • p3 := by
  rw [←lie_skew, lie_p0_k3, neg_smul (2⁻¹ : ℂ) p3]

end lie_p0_k

section lie_p_p

lemma lie_p0_p1 : ⁅p0, p1⁆ = j1 - k1 := by
  rw [Ring.lie_def]
  unfold p0 p1 j1 k1
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  all_goals ext
  all_goals simp
  all_goals ring

lemma lie_p1_p0 : ⁅p1, p0⁆ = -j1 + k1 := by
  rw [←lie_skew, lie_p0_p1]
  abel

lemma lie_p0_p2 : ⁅p0, p2⁆ = j2 - k2 := by
  rw [Ring.lie_def]
  unfold p0 p2 j2 k2
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  all_goals ext
  all_goals simp
  all_goals ring

lemma lie_p2_p0 : ⁅p2, p0⁆ = -j2 + k2 := by
  rw [←lie_skew, lie_p0_p2]
  abel

lemma lie_p0_p3 : ⁅p0, p3⁆ = j3 - k3 := by
  rw [Ring.lie_def]
  unfold p0 p3 j3 k3
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  all_goals ext
  all_goals simp
  all_goals ring

lemma lie_p3_p0 : ⁅p3, p0⁆ = -j3 + k3 := by
  rw [←lie_skew, lie_p0_p3]
  abel

end lie_p_p

section lie_p_j

lemma lie_p1_j1 : ⁅p1, j1⁆ = (2⁻¹ : ℂ) • p0 := by
  rw [Ring.lie_def]
  unfold p1 j1 p0
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  any_goals rw [DistribMulAction.smul_zero]
  all_goals ext
  all_goals simp

lemma lie_j1_p1 : ⁅j1, p1⁆ = (-2⁻¹ : ℂ) • p0 := by
  rw [←lie_skew, lie_p1_j1, neg_smul (2⁻¹ : ℂ) p0]

lemma lie_p2_j2 : ⁅p2, j2⁆ = (2⁻¹ : ℂ) • p0 := by
  rw [Ring.lie_def]
  unfold p2 j2 p0
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  any_goals rw [DistribMulAction.smul_zero]
  all_goals ext
  all_goals simp

lemma lie_j2_p2 : ⁅j2, p2⁆ = (-2⁻¹ : ℂ) • p0 := by
  rw [←lie_skew, lie_p2_j2, neg_smul (2⁻¹ : ℂ) p0]

lemma lie_p3_j3 : ⁅p3, j3⁆ = (2⁻¹ : ℂ) • p0 := by
  rw [Ring.lie_def]
  unfold p3 j3 p0
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  any_goals rw [DistribMulAction.smul_zero]
  all_goals ext
  all_goals simp

lemma lie_j3_p3 : ⁅j3, p3⁆ = (-2⁻¹ : ℂ) • p0 := by
  rw [←lie_skew, lie_p3_j3, neg_smul (2⁻¹ : ℂ) p0]

lemma lie_p1_j2 : ⁅p1, j2⁆ = (2⁻¹ : ℂ) • p3 := by
  rw [Ring.lie_def]
  unfold p1 j2 p3
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  any_goals rw [DistribMulAction.smul_zero]
  all_goals ext
  all_goals simp

lemma lie_j2_p1 : ⁅j2, p1⁆ = (-2⁻¹ : ℂ) • p3 := by
  rw [←lie_skew, lie_p1_j2, neg_smul (2⁻¹ : ℂ) p3]

lemma lie_p1_j3 : ⁅p1, j3⁆ = (-2⁻¹ : ℂ) • p2 := by
  rw [Ring.lie_def]
  unfold p1 j3 p2
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  any_goals rw [DistribMulAction.smul_zero]
  all_goals ext
  all_goals simp

lemma lie_j3_p1 : ⁅j3, p1⁆ = (2⁻¹ : ℂ) • p2 := by
  rw [←lie_skew, lie_p1_j3, neg_smul (2⁻¹ : ℂ) p2, neg_neg]

lemma lie_p2_j1 : ⁅p2, j1⁆ = (-2⁻¹ : ℂ) • p3 := by
  rw [Ring.lie_def]
  unfold p2 j1 p3
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  any_goals rw [DistribMulAction.smul_zero]
  all_goals ext
  all_goals simp

lemma lie_j1_p2 : ⁅j1, p2⁆ = (2⁻¹ : ℂ) • p3 := by
  rw [←lie_skew, lie_p2_j1, neg_smul (2⁻¹ : ℂ) p3, neg_neg]

lemma lie_p2_j3 : ⁅p2, j3⁆ = (2⁻¹ : ℂ) • p1 := by
  rw [Ring.lie_def]
  unfold p2 j3 p1
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  any_goals rw [DistribMulAction.smul_zero]
  all_goals ext
  all_goals simp

lemma lie_j3_p2 : ⁅j3, p2⁆ = (-2⁻¹ : ℂ) • p1 := by
  rw [←lie_skew, lie_p2_j3, neg_smul (2⁻¹ : ℂ) p1]

lemma lie_p3_j1 : ⁅p3, j1⁆ = (2⁻¹ : ℂ) • p2 := by
  rw [Ring.lie_def]
  unfold p3 j1 p2
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  any_goals rw [DistribMulAction.smul_zero]
  all_goals ext
  all_goals simp

lemma lie_j1_p3 : ⁅j1, p3⁆ = (-2⁻¹ : ℂ) • p2 := by
  rw [←lie_skew, lie_p3_j1, neg_smul (2⁻¹ : ℂ) p2]

lemma lie_p3_j2 : ⁅p3, j2⁆ = (-2⁻¹ : ℂ) • p1 := by
  rw [Ring.lie_def]
  unfold p3 j2 p1
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  any_goals rw [DistribMulAction.smul_zero]
  all_goals ext
  all_goals simp

lemma lie_j2_p3 : ⁅j2, p3⁆ = (2⁻¹ : ℂ) • p1 := by
  rw [←lie_skew, lie_p3_j2, neg_smul (2⁻¹ : ℂ) p1, neg_neg]

end lie_p_j

section lie_p_p

lemma lie_p1_p2 : ⁅p1, p2⁆ = j3 + k3 := by
  rw [Ring.lie_def]
  unfold p1 p2 j3 k3
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  all_goals ext
  all_goals simp
  all_goals ring

lemma lie_p2_p1 : ⁅p2, p1⁆ = -j3 - k3 := by
  rw [←lie_skew, lie_p1_p2]
  abel

lemma lie_p1_p3 : ⁅p1, p3⁆ = -j2 - k2 := by
  rw [Ring.lie_def]
  unfold p1 p3 j2 k2
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  all_goals ext
  all_goals simp
  all_goals ring

lemma lie_p3_p1 : ⁅p3, p1⁆ = j2 + k2 := by
  rw [←lie_skew, lie_p1_p3]
  abel

lemma lie_p2_p3 : ⁅p2, p3⁆ = j1 + k1 := by
  rw [Ring.lie_def]
  unfold p2 p3 j1 k1
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  all_goals ext
  all_goals simp
  all_goals ring

lemma lie_p3_p2 : ⁅p3, p2⁆ = -j1 - k1 := by
  rw [←lie_skew, lie_p2_p3]
  abel

end lie_p_p

section lie_p_k

lemma lie_p1_k1 : ⁅p1, k1⁆ = (-2⁻¹ : ℂ) • p0 := by
  rw [Ring.lie_def]
  unfold p1 k1 p0
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  any_goals rw [DistribMulAction.smul_zero]
  all_goals ext
  all_goals simp

lemma lie_k1_p1 : ⁅k1, p1⁆ = (2⁻¹ : ℂ) • p0 := by
  rw [←lie_skew, lie_p1_k1, neg_smul (2⁻¹ : ℂ) p0, neg_neg]

lemma lie_p2_k2 : ⁅p2, k2⁆ = (-2⁻¹ : ℂ) • p0 := by
  rw [Ring.lie_def]
  unfold p2 k2 p0
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  any_goals rw [DistribMulAction.smul_zero]
  all_goals ext
  all_goals simp

lemma lie_k2_p2 : ⁅k2, p2⁆ = (2⁻¹ : ℂ) • p0 := by
  rw [←lie_skew, lie_p2_k2, neg_smul (2⁻¹ : ℂ) p0, neg_neg]

lemma lie_p3_k3 : ⁅p3, k3⁆ = (-2⁻¹ : ℂ) • p0 := by
  rw [Ring.lie_def]
  unfold p3 k3 p0
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  any_goals rw [DistribMulAction.smul_zero]
  all_goals ext
  all_goals simp

lemma lie_k3_p3 : ⁅k3, p3⁆ = (2⁻¹ : ℂ) • p0 := by
  rw [←lie_skew, lie_p3_k3, neg_smul (2⁻¹ : ℂ) p0, neg_neg]

lemma lie_p1_k2 : ⁅p1, k2⁆ = (2⁻¹ : ℂ) • p3 := by
  rw [Ring.lie_def]
  unfold p1 k2 p3
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  any_goals rw [DistribMulAction.smul_zero]
  all_goals ext
  all_goals simp

lemma lie_k2_p1 : ⁅k2, p1⁆ = (-2⁻¹ : ℂ) • p3 := by
  rw [←lie_skew, lie_p1_k2, neg_smul (2⁻¹ : ℂ) p3]

lemma lie_p1_k3 : ⁅p1, k3⁆ = (-2⁻¹ : ℂ) • p2 := by
  rw [Ring.lie_def]
  unfold p1 k3 p2
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  any_goals rw [DistribMulAction.smul_zero]
  all_goals ext
  all_goals simp

lemma lie_k3_p1 : ⁅k3, p1⁆ = (2⁻¹ : ℂ) • p2 := by
  rw [←lie_skew, lie_p1_k3, neg_smul (2⁻¹ : ℂ) p2, neg_neg]

lemma lie_p2_k1 : ⁅p2, k1⁆ = (-2⁻¹ : ℂ) • p3 := by
  rw [Ring.lie_def]
  unfold p2 k1 p3
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  any_goals rw [DistribMulAction.smul_zero]
  all_goals ext
  all_goals simp

lemma lie_k1_p2 : ⁅k1, p2⁆ = (2⁻¹ : ℂ) • p3 := by
  rw [←lie_skew, lie_p2_k1, neg_smul (2⁻¹ : ℂ) p3, neg_neg]

lemma lie_p2_k3 : ⁅p2, k3⁆ = (2⁻¹ : ℂ) • p1 := by
  rw [Ring.lie_def]
  unfold p2 k3 p1
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  any_goals rw [DistribMulAction.smul_zero]
  all_goals ext
  all_goals simp

lemma lie_k3_p2 : ⁅k3, p2⁆ = (-2⁻¹ : ℂ) • p1 := by
  rw [←lie_skew, lie_p2_k3, neg_smul (2⁻¹ : ℂ) p1]

lemma lie_p3_k1 : ⁅p3, k1⁆ = (2⁻¹ : ℂ) • p2 := by
  rw [Ring.lie_def]
  unfold p3 k1 p2
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  any_goals rw [DistribMulAction.smul_zero]
  all_goals ext
  all_goals simp

lemma lie_k1_p3 : ⁅k1, p3⁆ = (-2⁻¹ : ℂ) • p2 := by
  rw [←lie_skew, lie_p3_k1, neg_smul (2⁻¹ : ℂ) p2]

lemma lie_p3_k2 : ⁅p3, k2⁆ = (-2⁻¹ : ℂ) • p1 := by
  rw [Ring.lie_def]
  unfold p3 k2 p1
  ext1 i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [mul_apply']
  any_goals rw [DistribMulAction.smul_zero]
  all_goals ext
  all_goals simp

lemma lie_k2_p3 : ⁅k2, p3⁆ = (2⁻¹ : ℂ) • p1 := by
  rw [←lie_skew, lie_p3_k2, neg_smul (2⁻¹ : ℂ) p1, neg_neg]

end lie_p_k
