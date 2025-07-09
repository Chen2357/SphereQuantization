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

lemma Lφ1φ2_eq : Lie φ1 φ2 = 2 • ρ := by
  unfold φ1 φ2 ρ
  simp [Lie_smul, smul_Lie]
  abel_nf

theorem Lρφ1_eq : Lie ρ φ1 = 2 • φ2 := by
  unfold φ1 φ2 ρ
  simp [Lie_smul, smul_Lie]
  abel_nf

theorem Lρφ2_eq : Lie ρ φ2 = -2 • φ1 := by
  unfold φ1 φ2 ρ
  simp [Lie_smul, smul_Lie]
  abel_nf

theorem Lρφ_eq : Lie ρ φ = (2 * Complex.I) • φ := by
  unfold φ
  simp [Lie_smul, smul_Lie, Lρφ1_eq, Lρφ2_eq, smul_sub]
  custom_rewrite
  simp
  abel

theorem Lρφ_bar_eq : Lie ρ φ_bar = (-2 * Complex.I) • φ_bar := by
  unfold φ_bar
  simp [Lie_smul, smul_Lie, Lρφ1_eq, Lρφ2_eq, smul_sub]
  custom_rewrite
  simp
  abel

theorem Lφφ_bar_eq : Lie φ φ_bar = Complex.I • ρ := by
  unfold φ φ_bar
  simp [Lie_smul, smul_Lie, Lφ1φ2_eq, smul_sub]
  rw [Lie_antisymm, Lφ1φ2_eq]
  custom_rewrite
  collect ρ
  congr
  ring_nf
  simp
  ring
