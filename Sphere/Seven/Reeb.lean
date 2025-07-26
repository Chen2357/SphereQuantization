import Sphere.Seven.Alpha
import Sphere.Seven.DifferentialAlpha

noncomputable section

def R := x[0] • px[3] - x[3] • px[0] - x[1] • px[2] + x[2] • px[1] + x[4] • px[7] - x[7] • px[4] - x[5] • px[6] + x[6] • px[5]

lemma ι_R_dα : ι R (d α) = 0 := by
  simp [R, α, d_smul, ι_mul, ι_d]
  calc
  _ = -2 • ν := by
    unfold ν
    abel_nf
    simp [subalgebra_smul_eq_cast_mul]
    abel
  _ = 0 := by simp [ν_eq_zero]

lemma ι_R_α : ι R α = 1 := by
  simp [R, α, ι_d]
  simp only [subalgebra_smul_eq_cast_mul]
  simp [two_mul, ←two_smul ℂ, smul_smul]
  norm_cast
  calc
  _ = x[0] * x[0] + x[1] * x[1] + x[2] * x[2] + x[3] * x[3] + x[4] * x[4] + x[5] * x[5] + x[6] * x[6] + x[7] * x[7] := by abel
  _ = 1 := con
