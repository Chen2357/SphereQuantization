import Sphere.Basic
import Mathlib.Algebra.Quaternion
import Mathlib.Data.Matrix.Mul

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

abbrev basis : Vector S 8 := ⟨#[
  ![⟨1, 0, 0, 0⟩, 0],
  ![⟨0, 1, 0, 0⟩, 0],
  ![⟨0, 0, 1, 0⟩, 0],
  ![⟨0, 0, 0, 1⟩, 0],
  ![0, ⟨1, 0, 0, 0⟩],
  ![0, ⟨0, 1, 0, 0⟩],
  ![0, ⟨0, 0, 1, 0⟩],
  ![0, ⟨0, 0, 0, 1⟩],
], rfl⟩

@[simp] def decomp (s : S) : Vector ℂ 8 := ⟨#[
  (s 0).re, (s 0).imI, (s 0).imJ, (s 0).imK,
  (s 1).re, (s 1).imI, (s 1).imJ, (s 1).imK
], rfl⟩

axiom x : Vector Λ0 8
axiom px : Vector T 8
@[simp] axiom der_px_x (n m : ℕ) (h1 : n < 8) (h2 : m < 8) : der px[n] x[m] = if n = m then 1 else 0

def ξ (X : M) : T := ∑ i : Fin 8, (∑ j : Fin 8, (decomp (X *ᵥ basis[i]))[j] • (x[i] • px[j]))

def α : Λ 1 := ⟨
  x[0] • d x[3] - x[3] • d x[0] - x[1] • d x[2] + x[2] • d x[1] + x[4] • d x[7] - x[7] • d x[4] - x[5] • d x[6] + x[6] • d x[5],
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
