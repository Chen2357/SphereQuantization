import Sphere.Duality
import Sphere.Differential

theorem Lρα_eq : L ρ α = 0 := by
  simp [L, dα_eq, ι_mul]

theorem Lρl : L ρ l = (-2 * Complex.I) • l := by
  simp [L, dl_eq, ι_mul]

theorem Lρl_bar : L ρ l_bar = (2 * Complex.I) • l_bar := by
  simp [L, dl_bar_eq, ι_mul]

theorem Lφl_eq : L φ l = (2 * Complex.I) • α := by
  simp [L, dl_eq, ι_mul]

theorem Lφ_bar_l_bar_eq : L φ_bar l_bar = (-2 * Complex.I) • α := by
  simp [L, dl_bar_eq, ι_mul]

lemma Lφ1φ2_eq : ⁅φ1, φ2⁆ = (2 : ℂ) • ρ := by
  unfold φ1 φ2 ρ
  simp only [lie_Λ0smul, Λ0smul_lie, lie_add, add_lie, lie_sub, sub_lie]
  simp
  norm_cast
  abel_nf

theorem Lρφ1_eq : ⁅ρ, φ1⁆ = (2 : ℂ) • φ2 := by
  unfold φ1 φ2 ρ
  simp only [lie_Λ0smul, Λ0smul_lie, lie_add, add_lie, lie_sub, sub_lie]
  simp
  norm_cast
  abel_nf

theorem Lρφ2_eq : ⁅ρ, φ2⁆ = (-2 : ℂ) • φ1 := by
  unfold φ1 φ2 ρ
  simp only [lie_Λ0smul, Λ0smul_lie, lie_add, add_lie, lie_sub, sub_lie]
  simp
  norm_cast
  abel_nf

theorem Lρφ_eq : ⁅ρ, φ⁆ = (2 * Complex.I) • φ := by
  unfold φ
  simp only [lie_Λ0smul, Λ0smul_lie, lie_add, add_lie, lie_sub, sub_lie, lie_smul, smul_lie, Lρφ1_eq, Lρφ2_eq]
  simp [smul_smul]
  ring_nf
  simp [smul_sub, smul_smul]
  abel

theorem Lρφ_bar_eq : ⁅ρ, φ_bar⁆ = (-2 * Complex.I) • φ_bar := by
  unfold φ_bar
  simp only [lie_Λ0smul, Λ0smul_lie, lie_add, add_lie, lie_sub, sub_lie, lie_smul, smul_lie, Lρφ1_eq, Lρφ2_eq]
  simp [smul_smul]
  ring_nf
  simp [smul_sub, smul_smul]
  abel

theorem Lφφ_bar_eq : ⁅φ, φ_bar⁆ = Complex.I • ρ := by
  unfold φ φ_bar
  simp [lie_Λ0smul, Λ0smul_lie]
  rw [←lie_skew]
  simp only [Lφ1φ2_eq, smul_smul, smul_neg]
  ring_nf
  abel_nf
  calc
  _ = (2 : ℂ) • (Complex.I * (1 / 2)) • ρ := by norm_cast
  _ = _ := by rw [smul_smul]; ring_nf
