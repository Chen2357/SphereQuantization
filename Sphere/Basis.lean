import Sphere.Basic
import Cochain.Algebra
import Sphere.Util.Collect

noncomputable section

def 𝒳.ρ : 𝒳 := fx 2 • px 1 - fx 1 • px 2 + fx 0 • px 3 - fx 3 • px 0
def 𝒳.φ1 : 𝒳 := fx 0 • px 1 - fx 1 • px 0 + fx 3 • px 2 - fx 2 • px 3
def 𝒳.φ2 : 𝒳 := fx 0 • px 2 - fx 2 • px 0 + fx 1 • px 3 - fx 3 • px 1

def Ω.α : Ω := fx 0 • dx 3 - fx 3 • dx 0 + fx 2 • dx 1 - fx 1 • dx 2
def Ω.l1 : Ω := fx 0 • dx 1 - fx 1 • dx 0 + fx 3 • dx 2 - fx 2 • dx 3
def Ω.l2 : Ω := fx 0 • dx 2 - fx 2 • dx 0 + fx 1 • dx 3 - fx 3 • dx 1

def 𝒳.H : 𝒳 := (-Complex.I) • ρ
def 𝒳.X : 𝒳 := (2⁻¹ : ℂ) • (φ1 - Complex.I • φ2)
def 𝒳.Y : 𝒳 := (2⁻¹ : ℂ) • (-φ1 - Complex.I • φ2)

def Ω.H' : Ω := Complex.I • α
def Ω.X' : Ω := Ω.l1 + Complex.I • Ω.l2
def Ω.Y' : Ω := -Ω.l1 + Complex.I • Ω.l2

open Cochain

syntax "ι_basis_eq_one_or_zero" : tactic
macro_rules
| `(tactic| ι_basis_eq_one_or_zero) => `(tactic|
    simp [-map_mul];
    simp only [Algebra.smul_def (A:=Ω), ←map_mul, ←map_one (algebraMap 𝒜 Ω), ←map_zero (algebraMap 𝒜 Ω), ←map_sub, ←map_add, ←map_neg];
    congr;
    ring_nf;
    try rw [←sum_eq_one]; simp [Finset.sum]; ring
  )

@[simp] lemma ι_ρ_α : ι (𝒳.ρ) Ω.α = 1 := by
  unfold 𝒳.ρ Ω.α
  ι_basis_eq_one_or_zero

@[simp] lemma ι_ρ_l1 : ι (𝒳.ρ) Ω.l1 = 0 := by
  unfold 𝒳.ρ Ω.l1
  ι_basis_eq_one_or_zero

@[simp] lemma ι_ρ_l2 : ι (𝒳.ρ) Ω.l2 = 0 := by
  unfold 𝒳.ρ Ω.l2
  ι_basis_eq_one_or_zero

@[simp] lemma ι_φ1_α : ι (𝒳.φ1) Ω.α = 0 := by
  unfold 𝒳.φ1 Ω.α
  ι_basis_eq_one_or_zero

@[simp] lemma ι_φ1_l1 : ι (𝒳.φ1) Ω.l1 = 1 := by
  unfold 𝒳.φ1 Ω.l1
  ι_basis_eq_one_or_zero

@[simp] lemma ι_φ1_l2 : ι (𝒳.φ1) Ω.l2 = 0 := by
  unfold 𝒳.φ1 Ω.l2
  ι_basis_eq_one_or_zero

@[simp] lemma ι_φ2_α : ι (𝒳.φ2) Ω.α = 0 := by
  unfold 𝒳.φ2 Ω.α
  ι_basis_eq_one_or_zero

@[simp] lemma ι_φ2_l1 : ι (𝒳.φ2) Ω.l1 = 0 := by
  unfold 𝒳.φ2 Ω.l1
  ι_basis_eq_one_or_zero

@[simp] lemma ι_φ2_l2 : ι (𝒳.φ2) Ω.l2 = 1 := by
  unfold 𝒳.φ2 Ω.l2
  ι_basis_eq_one_or_zero

@[simp] theorem ι_H_H' : ι (𝒳.H) Ω.H' = 1 := by
  unfold 𝒳.H Ω.H'
  simp [smul_smul]

@[simp] theorem ι_H_X' : ι (𝒳.H) Ω.X' = 0 := by
  unfold 𝒳.H Ω.X'
  simp

@[simp] theorem ι_H_Y' : ι (𝒳.H) Ω.Y' = 0 := by
  unfold 𝒳.H Ω.Y'
  simp

@[simp] theorem ι_X_H' : ι (𝒳.X) Ω.H' = 0 := by
  unfold 𝒳.X Ω.H'
  simp

@[simp] theorem ι_X_X' : ι (𝒳.X) Ω.X' = 1 := by
  unfold 𝒳.X Ω.X'
  simp [smul_smul, ←add_smul]
  ring_nf
  simp

@[simp] theorem ι_X_Y' : ι (𝒳.X) Ω.Y' = 0 := by
  unfold 𝒳.X Ω.Y'
  simp [smul_smul]

@[simp] theorem ι_Y_H' : ι (𝒳.Y) Ω.H' = 0 := by
  unfold 𝒳.Y Ω.H'
  simp

@[simp] theorem ι_Y_X' : ι (𝒳.Y) Ω.X' = 0 := by
  unfold 𝒳.Y Ω.X'
  simp [smul_smul]

@[simp] theorem ι_Y_Y' : ι (𝒳.Y) Ω.Y' = 1 := by
  unfold 𝒳.Y Ω.Y'
  simp [smul_smul, ←add_smul]
  ring_nf
  simp

theorem d_eq_in_αl (f : 𝒜) : d (algebraMap 𝒜 Ω f) = (𝒳.ρ f) • Ω.α + (𝒳.φ1 f) • Ω.l1 + (𝒳.φ2 f) • Ω.l2 := by
  rw [d_eq_in_dx]
  unfold 𝒳.ρ 𝒳.φ1 𝒳.φ2 Ω.α Ω.l1 Ω.l2
  simp [Finset.sum, smul_add, smul_sub, smul_smul]
  ring_nf
  simp only [sub_eq_add_neg, ←neg_smul]
  abel_nf
  collect dx 0
  conv_rhs =>
    enter [1, 1]
    ring_nf
    equals px 0 f =>
      calc _ = (∑ (i ≠ 0), fx i ^ 2) * px 0 f - fx 0 * (∑ (i ≠ 0), fx i • px i) f := by {
        simp [Finset.sum_erase_eq_sub, -sum_eq_one, -N_eq_zero]
        simp [Finset.sum]
        ring_nf
      }
      _ = (∑ i, fx i ^ 2) * px 0 f := by {
        simp [Finset.sum_erase_eq_sub]
        ring_nf
      }
      _ = _ := by simp
  congr 1
  collect dx 1
  conv_rhs =>
    enter [1, 1]
    ring_nf
    equals px 1 f =>
      calc _ = (∑ (i ≠ 1), fx i ^ 2) * px 1 f - fx 1 * (∑ (i ≠ 1), fx i • px i) f := by {
        simp [Finset.sum_erase_eq_sub, -sum_eq_one, -N_eq_zero]
        simp [Finset.sum]
        ring_nf
      }
      _ = (∑ i, fx i ^ 2) * px 1 f := by {
        simp [Finset.sum_erase_eq_sub]
        ring_nf
      }
      _ = _ := by simp
  congr 1
  collect dx 2
  conv_rhs =>
    enter [1, 1]
    ring_nf
    equals px 2 f =>
      calc _ = (∑ (i ≠ 2), fx i ^ 2) * px 2 f - fx 2 * (∑ (i ≠ 2), fx i • px i) f := by {
        simp [Finset.sum_erase_eq_sub, -sum_eq_one, -N_eq_zero]
        simp [Finset.sum]
        ring_nf
      }
      _ = (∑ i, fx i ^ 2) * px 2 f := by {
        simp [Finset.sum_erase_eq_sub]
        ring_nf
      }
      _ = _ := by simp
  congr 1
  collect dx 3
  conv_rhs =>
    enter [1]
    ring_nf
    equals px 3 f =>
      calc _ = (∑ (i ≠ 3), fx i ^ 2) * px 3 f - fx 3 * (∑ (i ≠ 3), fx i • px i) f := by {
        simp [Finset.sum_erase_eq_sub, -sum_eq_one, -N_eq_zero]
        simp [Finset.sum]
        ring_nf
      }
      _ = (∑ i, fx i ^ 2) * px 3 f := by {
        simp [Finset.sum_erase_eq_sub]
        ring_nf
      }
      _ = _ := by simp

theorem d_eq_in_HXY (f : 𝒜) : d (algebraMap 𝒜 Ω f) = (𝒳.H f) • Ω.H' + (𝒳.X f) • Ω.X' + (𝒳.Y f) • Ω.Y' := by
  rw [d_eq_in_αl]
  unfold 𝒳.H 𝒳.X 𝒳.Y Ω.H' Ω.X' Ω.Y'
  simp [smul_add, smul_sub, smul_smul, smul_comm (M:=𝒜) (N:=ℂ)]
  abel_nf
  congr 1
  simp [←neg_smul]
  collect Ω.l1
  congr
  . abel_nf
    simp
    rw [←smul_assoc]
    simp
  . rw [←smul_assoc, ←smul_assoc, ←add_smul]
    congr
    simp [←smul_assoc]
    abel_nf
    simp [←smul_assoc]
    ring_nf
    simp
