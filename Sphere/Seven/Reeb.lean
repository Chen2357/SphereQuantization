import Sphere.Seven.Alpha
import Sphere.Seven.DifferentialAlpha

noncomputable section

def R := 2 • (ξ j3) + 2 • (ξ k3)

lemma ι_R_dα : ι R (d α) = 0 := by
  simp [R, ι_ξ_j3_dα, ι_ξ_k3_dα]
  calc
  _ = -2 • ν := by
    simp [subalgebra_smul_eq_cast_mul]
    abel
  _ = _ := by simp [ν_eq_zero]

lemma ι_R_α : ι R α = 1 := by
  simp [R, ι_ξ_j3_α, ι_ξ_k3_α]
  simp [two_mul, ←two_smul ℂ, smul_smul]
  norm_cast
  calc
  _ = x[0] * x[0] + x[1] * x[1] + x[2] * x[2] + x[3] * x[3] + x[4] * x[4] + x[5] * x[5] + x[6] * x[6] + x[7] * x[7] := by abel
  _ = 1 := con
