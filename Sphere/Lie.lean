import Sphere.Basis

namespace 𝒳

syntax "lie_basis_px_eq" : tactic
macro_rules
| `(tactic| lie_basis_px_eq) => `(tactic|
    simp [lier_smul, smul_add, smul_sub, ←smul_assoc];
    abel_nf;
    simp [-smul_assoc];
    simp only [←neg_smul];
    collect px 0;
    congr 1;
    ring_nf;
    collect px 1;
    congr 1;
    ring_nf;
    collect px 2;
    congr 1;
    ring_nf;
    collect px 3;
    congr 1;
    ring_nf
  )

@[simp]
lemma lie_ρ_φ1 : ⁅ρ, φ1⁆ = (2 : ℤ) • φ2 := by
  unfold ρ φ1 φ2
  lie_basis_px_eq

@[simp]
lemma lie_φ1_ρ : ⁅φ1, ρ⁆ = -2 • φ2 := by
  rw [←lie_skew]
  simp

@[simp]
lemma lie_ρ_φ2 : ⁅ρ, φ2⁆ = -2 • φ1 := by
  unfold ρ φ1 φ2
  lie_basis_px_eq

@[simp]
lemma lie_φ2_ρ : ⁅φ2, ρ⁆ = (2 : ℤ) • φ1 := by
  rw [←lie_skew]
  simp

@[simp]
lemma lie_φ1_φ2 : ⁅φ1, φ2⁆ = (2 : ℤ) • ρ := by
  unfold ρ φ1 φ2
  lie_basis_px_eq

@[simp]
lemma lie_φ2_φ1 : ⁅φ2, φ1⁆ = -2 • ρ := by
  rw [←lie_skew]
  simp

@[simp]
theorem lie_H_X : ⁅H, X⁆ = (2 : ℤ) • X := by
  unfold H X
  simp [←smul_assoc, smul_comm (N:=ℤ), -neg_smul]
  ring_nf
  simp
  abel

@[simp]
theorem lie_X_H : ⁅X, H⁆ = -2 • X := by
  rw [←lie_skew]
  simp

@[simp]
theorem lie_H_Y : ⁅H, Y⁆ = -2 • Y := by
  unfold H Y
  simp [←smul_assoc, smul_comm (N:=ℤ), -neg_smul]
  ring_nf
  simp

@[simp]
theorem lie_Y_H : ⁅Y, H⁆ = (2 : ℤ) • Y := by
  rw [←lie_skew]
  simp

@[simp]
theorem lie_X_Y : ⁅X, Y⁆ = H := by
  unfold H X Y
  simp [←smul_assoc, smul_comm (N:=ℤ)]
  simp only [←neg_smul, ←sub_smul, smul_smul]
  ring_nf

@[simp]
theorem lie_Y_X : ⁅Y, X⁆ = -H := by
  rw [←lie_skew]
  simp

end 𝒳
