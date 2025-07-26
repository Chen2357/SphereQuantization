import Sphere.Seven.Basis

open Quaternion Matrix

lemma ξ_p0 : ξ p0 = (2⁻¹ : ℂ) • (-(x[0] • px[4]) + x[4] • px[0] - x[1] • px[5] + x[5] • px[1] - x[2] • px[6] + x[6] • px[2] + x[7] • px[3] - x[3] • px[7]) := by
  simp [ξ, p0, Finset.sum, mulVec, dotProduct]
  simp [smul_add, smul_sub, smul_neg]
  abel

lemma ξ_p1 : ξ p1 = (2⁻¹ : ℂ) • (x[0] • px[5] - x[5] • px[0] - x[1] • px[4] + x[4] • px[1] + x[2] • px[7] - x[7] • px[2] - x[3] • px[6] + x[6] • px[3]) := by
  simp [ξ, p1, Finset.sum, mulVec, dotProduct]
  simp [smul_add, smul_sub, smul_neg]
  abel

lemma ξ_p2 : ξ p2 = (2⁻¹ : ℂ) • (x[0] • px[6] - x[6] • px[0] - x[1] • px[7] + x[7] • px[1] - x[2] • px[4] + x[4] • px[2] + x[3] • px[5] - x[5] • px[3]) := by
  simp [ξ, p2, Finset.sum, mulVec, dotProduct]
  simp [smul_add, smul_sub, smul_neg]
  abel

lemma ξ_p3 : ξ p3 = (2⁻¹ : ℂ) • (x[0] • px[7] - x[7] • px[0] + x[1] • px[6] - x[6] • px[1] - x[2] • px[5] + x[5] • px[2] - x[3] • px[4] + x[4] • px[3]) := by
  simp [ξ, p3, Finset.sum, mulVec, dotProduct]
  simp [smul_add, smul_sub, smul_neg]
  abel

lemma ξ_j1 : ξ j1 = (2⁻¹ : ℂ) • (x[0] • px[1] - x[1] • px[0] + x[2] • px[3] - x[3] • px[2]) := by
  simp [ξ, j1, Finset.sum, mulVec, dotProduct]
  simp [smul_add, smul_sub, smul_neg]
  abel

lemma ξ_j2 : ξ j2 = (2⁻¹ : ℂ) • (x[0] • px[2] - x[2] • px[0] - x[1] • px[3] + x[3] • px[1]) := by
  simp [ξ, j2, Finset.sum, mulVec, dotProduct]
  simp [smul_add, smul_sub, smul_neg]
  abel

lemma ξ_j3 : ξ j3 = (2⁻¹ : ℂ) • (x[0] • px[3] - x[3] • px[0] + x[1] • px[2] - x[2] • px[1]) := by
  simp [ξ, j3, Finset.sum, mulVec, dotProduct]
  simp [smul_add, smul_sub, smul_neg]
  abel

lemma ξ_k1 : ξ k1 = (2⁻¹ : ℂ) • (x[6] • px[7] - x[7] • px[6] + x[4] • px[5] - x[5] • px[4]) := by
  simp [ξ, k1, Finset.sum, mulVec, dotProduct]
  simp only [smul_add, smul_sub, smul_neg]
  abel

lemma ξ_k2 : ξ k2 = (2⁻¹ : ℂ) • (-x[5] • px[7] + x[7] • px[5] + x[4] • px[6] - x[6] • px[4]) := by
  simp [ξ, k2, Finset.sum, mulVec, dotProduct]
  simp only [smul_add, smul_sub, smul_neg]
  abel

lemma ξ_k3 : ξ k3 = (2⁻¹ : ℂ) • (-x[7] • px[4] + x[4] • px[7] - x[6] • px[5] + x[5] • px[6]) := by
  simp [ξ, k3, Finset.sum, mulVec, dotProduct]
  simp only [smul_add, smul_sub, smul_neg]
  abel
