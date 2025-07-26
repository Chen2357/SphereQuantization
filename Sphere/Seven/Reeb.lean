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

private abbrev ι_ξ_k1_α'' : Λ0 := (4 : ℂ) • (x[4] * x[6] + x[5] * x[7])
private abbrev ι_ξ_k2_α'' : Λ0 := (4 : ℂ) • (-(x[4] * x[5]) + x[6] * x[7])
private abbrev ι_ξ_k3_α'' : Λ0 := (2 : ℂ) • (x[4] * x[4] - x[5] * x[5] - x[6] * x[6] + x[7] * x[7])
private abbrev ι_ξ_j1_α'' : Λ0 := (4 : ℂ) • (x[0] * x[2] + x[1] * x[3])
private abbrev ι_ξ_j2_α'' : Λ0 := (4 : ℂ) • (-(x[0] * x[1]) + x[2] * x[3])
private abbrev ι_ξ_j3_α'' : Λ0 := (2 : ℂ) • (x[0] * x[0] - x[1] * x[1] - x[2] * x[2] + x[3] * x[3])
private abbrev ι_ξ_p0_α'' : Λ0 := (2 : ℂ) • (x[0] * x[7] - x[1] * x[6] + x[2] * x[5] - x[3] * x[4])
private abbrev ι_ξ_p1_α'' : Λ0 := (2 : ℂ) • (x[0] * x[6] + x[1] * x[7] + x[2] * x[4] + x[3] * x[5])
private abbrev ι_ξ_p2_α'' : Λ0 := (2 : ℂ) • (-(x[0] * x[5]) - x[1] * x[4] + x[2] * x[7] + x[3] * x[6])
private abbrev ι_ξ_p3_α'' : Λ0 := (2 : ℂ) • (x[0] * x[4] - x[1] * x[5] - x[2] * x[6] + x[3] * x[7])

private abbrev R' : T :=
ι_ξ_p0_α'' • (ξ p0) +
ι_ξ_p1_α'' • (ξ p1) +
ι_ξ_p2_α'' • (ξ p2) +
ι_ξ_p3_α'' • (ξ p3) +
ι_ξ_j1_α'' • (ξ j1) +
ι_ξ_j2_α'' • (ξ j2) +
ι_ξ_j3_α'' • (ξ j3) +
ι_ξ_k1_α'' • (ξ k1) +
ι_ξ_k2_α'' • (ξ k2) +
ι_ξ_k3_α'' • (ξ k3)

private lemma R'_eq_R : R' = R := by
  simp only [R', ξ_p0, ξ_p1, smul_add, ξ_p2, ξ_p3, ξ_j1, ξ_j2, ξ_j3, ξ_k1, ξ_k2, neg_smul, ξ_k3, R]
  simp only [smul_sub, smul_add, smul_neg, @smul_comm Λ0 ℂ T, smul_smul]
  simp only [←@smul_assoc T ℂ Λ0, @smul_mul_assoc, ←@smul_add ℂ Λ0, ←@smul_sub ℂ Λ0, ←@smul_neg ℂ Λ0, ←@smul_assoc Λ0 ℂ ℂ]
  simp only [←add_assoc, sub_eq_add_neg, ←neg_smul]

  have h : (2⁻¹ : ℂ) * 4 = 2 := by ring

  collect' px[0]
  congr 1
  pick_goal 2
  . congr
    simp only [smul_eq_mul, neg_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_mul_cancel₀,
      neg_smul, one_smul, h, two_smul]
    ring_nf
    calc
    _ = -(x[0] * x[0] + x[1] * x[1] + x[2] * x[2] + x[3] * x[3] + x[4] * x[4] + x[5] * x[5] + x[6] * x[6] + x[7] * x[7]) * x[3] := by
      ring
    _ = _ := by simp only [con, neg_mul, one_mul]

  collect' px[1]
  congr 1
  pick_goal 2
  . congr
    simp only [smul_eq_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_mul_cancel₀,
      one_smul, neg_mul, neg_smul, h, two_smul]
    ring_nf
    calc
    _ = (x[0] * x[0] + x[1] * x[1] + x[2] * x[2] + x[3] * x[3] + x[4] * x[4] + x[5] * x[5] + x[6] * x[6] + x[7] * x[7]) * x[2] := by
      ring
    _ = _ := by simp only [con, one_mul]

  collect' px[2]
  congr 1
  pick_goal 2
  . congr
    simp only [smul_eq_mul, neg_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_mul_cancel₀,
      neg_smul, one_smul, h, two_smul]
    ring_nf
    calc
    _ = -(x[0] * x[0] + x[1] * x[1] + x[2] * x[2] + x[3] * x[3] + x[4] * x[4] + x[5] * x[5] + x[6] * x[6] + x[7] * x[7]) * x[1] := by
      ring
    _ = _ := by simp only [con, neg_mul, one_mul]

  collect' px[3]
  congr 1
  pick_goal 2
  . congr
    simp only [smul_eq_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_mul_cancel₀,
      one_smul, neg_mul, neg_smul, h, two_smul]
    ring_nf
    calc
    _ = (x[0] * x[0] + x[1] * x[1] + x[2] * x[2] + x[3] * x[3] + x[4] * x[4] + x[5] * x[5] + x[6] * x[6] + x[7] * x[7]) * x[0] := by
      ring
    _ = _ := by simp only [con, one_mul]

  collect' px[4]
  congr 1
  pick_goal 2
  . congr
    simp only [smul_eq_mul, neg_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_mul_cancel₀,
      neg_smul, one_smul, h, two_smul]
    ring_nf
    calc
    _ = -(x[0] * x[0] + x[1] * x[1] + x[2] * x[2] + x[3] * x[3] + x[4] * x[4] + x[5] * x[5] + x[6] * x[6] + x[7] * x[7]) * x[7] := by
      ring
    _ = _ := by simp only [con, neg_mul, one_mul]

  collect' px[5]
  congr 1
  pick_goal 2
  . congr
    simp only [smul_eq_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_mul_cancel₀,
      one_smul, neg_mul, neg_smul, h, two_smul]
    ring_nf
    calc
    _ = (x[0] * x[0] + x[1] * x[1] + x[2] * x[2] + x[3] * x[3] + x[4] * x[4] + x[5] * x[5] + x[6] * x[6] + x[7] * x[7]) * x[6] := by
      ring
    _ = _ := by simp only [con, one_mul]

  collect' px[6]
  congr 1
  pick_goal 2
  . congr
    simp only [smul_eq_mul, neg_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_mul_cancel₀,
      neg_smul, one_smul, h, two_smul]
    ring_nf
    calc
    _ = -(x[0] * x[0] + x[1] * x[1] + x[2] * x[2] + x[3] * x[3] + x[4] * x[4] + x[5] * x[5] + x[6] * x[6] + x[7] * x[7]) * x[5] := by
      ring
    _ = _ := by simp only [con, neg_mul, one_mul]

  collect' px[7]
  congr
  simp only [smul_eq_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_mul_cancel₀, one_smul,
    neg_mul, neg_smul, h, two_smul]
  ring_nf
  calc
  _ = (x[0] * x[0] + x[1] * x[1] + x[2] * x[2] + x[3] * x[3] + x[4] * x[4] + x[5] * x[5] + x[6] * x[6] + x[7] * x[7]) * x[4] := by
    ring
  _ = _ := by simp only [con, one_mul]

lemma R_eq : R =
  ((2 : ℂ) • ι_ξ_p0_α') • (ξ p0) +
  ((2 : ℂ) • ι_ξ_p1_α') • (ξ p1) +
  ((2 : ℂ) • ι_ξ_p2_α') • (ξ p2) +
  ((2 : ℂ) • ι_ξ_p3_α') • (ξ p3) +
  ((4 : ℂ) • ι_ξ_j1_α') • (ξ j1) +
  ((4 : ℂ) • ι_ξ_j2_α') • (ξ j2) +
  ((4 : ℂ) • ι_ξ_j3_α') • (ξ j3) +
  ((4 : ℂ) • ι_ξ_k1_α') • (ξ k1) +
  ((4 : ℂ) • ι_ξ_k2_α') • (ξ k2) +
  ((4 : ℂ) • ι_ξ_k3_α') • (ξ k3)
  := by
  rw [←R'_eq_R]
  unfold R'
  simp only [@smul_smul ℂ]
  ring_nf
