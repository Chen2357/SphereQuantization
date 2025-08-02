import Sphere.Basic
import Mathlib.Algebra.Quaternion
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Lie.Matrix

noncomputable section

open Quaternion Matrix

-- Using ℂ instead of ℝ purely to minimize the need for type conversions.
-- We will always be working with ℝ entries.
abbrev M := Matrix (Fin 2) (Fin 2) ℍ[ℂ]

def p0 : M := ![![0, ⟨2⁻¹, 0, 0, 0⟩], ![⟨-2⁻¹, 0, 0, 0⟩, 0]]
def p1 : M := ![![0, ⟨0, 2⁻¹, 0, 0⟩], ![⟨0, 2⁻¹, 0, 0⟩, 0]]
def p2 : M := ![![0, ⟨0, 0, 2⁻¹, 0⟩], ![⟨0, 0, 2⁻¹, 0⟩, 0]]
def p3 : M := ![![0, ⟨0, 0, 0, 2⁻¹⟩], ![⟨0, 0, 0, 2⁻¹⟩, 0]]

def j1 : M := ![![⟨0, 2⁻¹, 0, 0⟩, 0], ![0, 0]]
def j2 : M := ![![⟨0, 0, 2⁻¹, 0⟩, 0], ![0, 0]]
def j3 : M := ![![⟨0, 0, 0, 2⁻¹⟩, 0], ![0, 0]]

def k1 : M := ![![0, 0], ![0, ⟨0, 2⁻¹, 0, 0⟩]]
def k2 : M := ![![0, 0], ![0, ⟨0, 0, 2⁻¹, 0⟩]]
def k3 : M := ![![0, 0], ![0, ⟨0, 0, 0, 2⁻¹⟩]]

abbrev S := (Fin 2) → ℍ[ℂ]

@[simp] abbrev basis (i : Fin 8) : S :=
  match i with
  | 0 => ![⟨1, 0, 0, 0⟩, 0]
  | 1 => ![⟨0, 1, 0, 0⟩, 0]
  | 2 => ![⟨0, 0, 1, 0⟩, 0]
  | 3 => ![⟨0, 0, 0, 1⟩, 0]
  | 4 => ![0, ⟨1, 0, 0, 0⟩]
  | 5 => ![0, ⟨0, 1, 0, 0⟩]
  | 6 => ![0, ⟨0, 0, 1, 0⟩]
  | 7 => ![0, ⟨0, 0, 0, 1⟩]

abbrev decomp : S →ₗ[ℂ] (Fin 8) → ℂ := {
  toFun := fun s i => match i with
    | 0 => (s 0).re
    | 1 => (s 0).imI
    | 2 => (s 0).imJ
    | 3 => (s 0).imK
    | 4 => (s 1).re
    | 5 => (s 1).imI
    | 6 => (s 1).imJ
    | 7 => (s 1).imK
  map_add' := by
    intro x y
    ext i
    fin_cases i
    all_goals simp
  map_smul' := by
    intro c x
    ext i
    fin_cases i
    all_goals simp
}

axiom x : Vector Λ0 8
axiom px : Vector T 8
@[simp] axiom der_px_x (n m : ℕ) (h1 : n < 8) (h2 : m < 8) : der px[n] x[m] = if n = m then 1 else 0
@[simp] axiom lie_px_px (n m : ℕ) (h1 : n < 8) (h2 : m < 8) : ⁅px[n], px[m]⁆ = 0

def ξ : M →ₗ[ℂ] T := {
  toFun := fun X => ∑ i : Fin 8, (∑ j : Fin 8, (decomp (X *ᵥ (basis i))) j • (x[i] • px[j]))
  map_add' := by
    intros X Y
    rw [←Finset.sum_add_distrib]
    congr 1
    ext i
    rw [←Finset.sum_add_distrib]
    congr 1
    ext j
    rw [←add_smul]
    congr
    rw [add_mulVec]
    fin_cases j
    all_goals simp
  map_smul' := by
    intros c X
    rw [Finset.smul_sum]
    congr 1
    ext i
    rw [Finset.smul_sum]
    congr 1
    ext j
    rw [←smul_assoc ((RingHom.id ℂ) c)]
    congr
    rw [smul_mulVec_assoc c X]
    fin_cases j
    all_goals simp
}

def α : Λ 1 := ⟨
  x[3] • d x[0] - x[2] • d x[1] + x[1] • d x[2] - x[0] • d x[3] +
  x[7] • d x[4] - x[6] • d x[5] + x[5] • d x[6] - x[4] • d x[7],
  by linear_homogeneous
⟩

axiom con : x[0] * x[0] + x[1] * x[1] + x[2] * x[2] + x[3] * x[3] + x[4] * x[4] + x[5] * x[5] + x[6] * x[6] + x[7] * x[7] = 1

abbrev ν := x[0] • d x[0] + x[1] • d x[1] + x[2] • d x[2] + x[3] • d x[3] + x[4] * d x[4] + x[5] * d x[5] + x[6] * d x[6] + x[7] * d x[7]

lemma ν_eq_zero : ν = 0 := by
  rw [←two_nsmul_eq_zero ℂ]
  calc
  _ = (2 : ℂ) • (x[0] * d x[0] + x[1] * d x[1] + x[2] * d x[2] + x[3] * d x[3] + x[4] * d x[4] + x[5] * d x[5] + x[6] * d x[6] + x[7] * d x[7]) := by
      norm_cast
  _ = d (x[0] * x[0] + x[1] * x[1] + x[2] * x[2] + x[3] * x[3] + x[4] * x[4] + x[5] * x[5] + x[6] * x[6] + x[7] * x[7]) := by
      simp [ν, d_mul]
      norm_cast
      abel_nf
  _ = d 1 := by congr; norm_cast; rw [con]
  _ = 0 := by simp
