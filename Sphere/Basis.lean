import Sphere.Basic

noncomputable section

axiom x0 : Λ0
axiom x1 : Λ0
axiom x2 : Λ0
axiom x3 : Λ0

axiom con : x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3 = 1

@[simp] lemma I_pow_two : Complex.I ^ 2 = -1 := by simp
@[simp] lemma I_I : Complex.I * Complex.I = -1 := by simp

def l1 : Λ 1 := ⟨x0 • d x1 - x1 • d x0 + x3 • d x2 - x2 • d x3, by linear_homogeneous⟩
def l2 : Λ 1 := ⟨x0 • d x2 - x2 • d x0 + x1 • d x3 - x3 • d x1, by linear_homogeneous⟩
def α : Λ 1 := ⟨x0 • d x3 - x3 • d x0 + x2 • d x1 - x1 • d x2, by linear_homogeneous⟩
def l : Λ 1 := ⟨l1 + Complex.I • l2, by linear_homogeneous⟩
def l_bar : Λ 1 := ⟨l1 - Complex.I • l2, by linear_homogeneous⟩

axiom px0 : T
axiom px1 : T
axiom px2 : T
axiom px3 : T

@[simp] axiom px00: der px0 x0 = 1
@[simp] axiom px01: der px0 x1 = 0
@[simp] axiom px02: der px0 x2 = 0
@[simp] axiom px03: der px0 x3 = 0

@[simp] axiom px10: der px1 x0 = 0
@[simp] axiom px11: der px1 x1 = 1
@[simp] axiom px12: der px1 x2 = 0
@[simp] axiom px13: der px1 x3 = 0

@[simp] axiom px20: der px2 x0 = 0
@[simp] axiom px21: der px2 x1 = 0
@[simp] axiom px22: der px2 x2 = 1
@[simp] axiom px23: der px2 x3 = 0

@[simp] axiom px30: der px3 x0 = 0
@[simp] axiom px31: der px3 x1 = 0
@[simp] axiom px32: der px3 x2 = 0
@[simp] axiom px33: der px3 x3 = 1

def ρ := x2 • px1 - x1 • px2 + x0 • px3 - x3 • px0
def φ1 := x0 • px1 - x1 • px0 + x3 • px2 - x2 • px3
def φ2 := x0 • px2 - x2 • px0 + x1 • px3 - x3 • px1
def φ := (2⁻¹ : ℂ) • (φ1 - Complex.I • φ2)
def φ_bar := (2⁻¹ : ℂ) • (φ1 + Complex.I • φ2)

axiom d_eq_in_basis (f : Λ0) : d f = (der ρ f) • α + (der φ f) • l + (der φ_bar f) • l_bar

@[simp] lemma Lie00 : ⁅px0, px0⁆ = 0 := lie_self px0
@[simp] axiom Lie01 : ⁅px0, px1⁆ = 0
@[simp] axiom Lie02 : ⁅px0, px2⁆ = 0
@[simp] axiom Lie03 : ⁅px0, px3⁆ = 0

@[simp] axiom Lie10 : ⁅px1, px0⁆ = 0
@[simp] lemma Lie11 : ⁅px1, px1⁆ = 0 := lie_self px1
@[simp] axiom Lie12 : ⁅px1, px2⁆ = 0
@[simp] axiom Lie13 : ⁅px1, px3⁆ = 0

@[simp] axiom Lie20 : ⁅px2, px0⁆ = 0
@[simp] axiom Lie21 : ⁅px2, px1⁆ = 0
@[simp] lemma Lie22 : ⁅px2, px2⁆ = 0 := lie_self px2
@[simp] axiom Lie23 : ⁅px2, px3⁆ = 0

@[simp] axiom Lie30 : ⁅px3, px0⁆ = 0
@[simp] axiom Lie31 : ⁅px3, px1⁆ = 0
@[simp] axiom Lie32 : ⁅px3, px2⁆ = 0
@[simp] lemma Lie33 : ⁅px3, px3⁆ = 0 := lie_self px3

@[simp] lemma dx1_mul_dx0 : d x1 * d x0 = -(d x0 * d x1) := by rw [graded_comm Λ]; simp
@[simp] lemma dx2_mul_dx0 : d x2 * d x0 = -(d x0 * d x2) := by rw [graded_comm Λ]; simp
@[simp] lemma dx2_mul_dx1 : d x2 * d x1 = -(d x1 * d x2) := by rw [graded_comm Λ]; simp
@[simp] lemma dx3_mul_dx0 : d x3 * d x0 = -(d x0 * d x3) := by rw [graded_comm Λ]; simp
@[simp] lemma dx3_mul_dx1 : d x3 * d x1 = -(d x1 * d x3) := by rw [graded_comm Λ]; simp
@[simp] lemma dx3_mul_dx2 : d x3 * d x2 = -(d x2 * d x3) := by rw [graded_comm Λ]; simp
