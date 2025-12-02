import Mathlib.Data.Complex.Basic
import Sphere.Util.Polynomial
import Sphere.Util.Ring
import Mathlib.Tactic.NoncommRing

noncomputable section

abbrev ℂℏ := LaurentPolynomial ℂ

def sqrt_ℏ (n : ℤ) : ℂℏ := LaurentPolynomial.T n

@[simp]
theorem star_sqrt_ℏ (n : ℤ) : star (sqrt_ℏ n) = sqrt_ℏ n := by simp [sqrt_ℏ]

@[simp]
theorem sqrt_ℏ_zero : sqrt_ℏ 0 = 1 := by simp [sqrt_ℏ]

theorem sqrt_ℏ_add (m n : ℤ) : sqrt_ℏ (m + n) = sqrt_ℏ m * sqrt_ℏ n := by
  unfold sqrt_ℏ
  apply LaurentPolynomial.T_add

axiom Op : Type
@[instance] axiom Op.Ring : Ring Op
@[instance] axiom Op.Algebra : Algebra ℂℏ Op
@[instance] axiom Op.StarRing : StarRing Op
@[instance] axiom Op.StarModule : StarModule ℂℏ Op

instance : Algebra ℂ Op := Algebra.compHom Op (algebraMap ℂ ℂℏ)

instance : SMulCommClass ℂ ℂℏ Op where
    smul_comm c x y := by
        show (algebraMap ℂ ℂℏ c) • (x • y) = x • ((algebraMap ℂ ℂℏ c) • y)
        rw [smul_smul, mul_comm, ←smul_smul]

instance : IsScalarTower ℂ ℂℏ Op where
  smul_assoc := by
    intros c x y
    show (c • x) • y = (algebraMap ℂ (ℂℏ) c) • (x • y)
    simp [Algebra.smul_def]
    rw [mul_assoc]

axiom a : Op
axiom Z : Op

def N : Op := (star a) * a

axiom Z_mul_Z : Z * Z = 1 - (sqrt_ℏ 2) • (N + (2⁻¹ : ℂ) • 1)
lemma Z_sq : Z ^ 2 = 1 - (sqrt_ℏ 2) • (N + (2⁻¹ : ℂ) • 1) := by rw [sq]; exact Z_mul_Z

@[simp] lemma star_N : star N = N := by rw [N]; simp
@[simp] axiom star_Z : star Z = Z

axiom Z_mul_N : Z * N = N * Z
@[simp] lemma lie_N_Z : ⁅N, Z⁆ = 0 := by
  simp [Bracket.bracket, Z_mul_N]
@[simp] axiom lie_a_star_a : ⁅a, star a⁆ = 1
lemma a_mul_star_a : a * star a = N + 1 := by
  simp [←lie_a_star_a, Bracket.bracket, N]
@[simp] lemma lie_star_a_a : ⁅star a, a⁆ = -1 := by rw [←lie_skew]; simp
@[simp] lemma lie_N_a : ⁅N, a⁆ = -a := by
  simp [N, mul_lie]
@[simp] lemma lie_a_N : ⁅a, N⁆ = a := by
  rw [←lie_skew, lie_N_a, neg_neg]
@[simp] lemma lie_N_star_a : ⁅N, star a⁆ = star a := by
  simp [N, mul_lie]
@[simp] lemma lie_star_a_N : ⁅star a, N⁆ = -star a := by
  rw [←lie_skew, lie_N_star_a]

def Op.H : Op := -(sqrt_ℏ (-2) • 1) + (2 : ℤ) • N + (2⁻¹ : ℂ) • 1
def Op.X : Op := Complex.I • sqrt_ℏ (-1) • ((star a) * Z)
def Op.Y : Op := -Complex.I • sqrt_ℏ (-1) • (Z * a)

open Op

@[simp]
theorem lie_H_X : ⁅H, X⁆ = (2 : ℤ) • X := by
  simp [H, X, -zsmul_eq_mul, lie_mul, smul_comm (N:=ℤ)]

@[simp]
theorem lie_X_H : ⁅X, H⁆ = -2 • X := by
  rw [←lie_skew]
  simp

@[simp]
theorem lie_H_Y : ⁅H, Y⁆ = -(2 : ℤ) • Y := by
  simp [H, Y, -zsmul_eq_mul, lie_mul, smul_comm (N:=ℤ)]

@[simp]
theorem lie_Y_H : ⁅Y, H⁆ = (2 : ℤ) • Y := by
  rw [←lie_skew]
  simp

@[simp]
theorem lie_X_Y : ⁅X, Y⁆ = H := by
  simp [H, X, Y, Bracket.bracket]
  have h₁ : star a * Z * (Z * a) = N * (1 - (sqrt_ℏ 2) • (N + (2⁻¹ : ℂ) • 1)) + (sqrt_ℏ 2) • N := by
    calc _ = star a * (Z * Z) * a := by noncomm_ring
    _ = star a * (1 - (sqrt_ℏ 2) • (N + (2⁻¹ : ℂ) • 1)) * a := by rw [Z_mul_Z]
    _ = star a * (a * (1 - (sqrt_ℏ 2) • (N + (2⁻¹ : ℂ) • 1)) - ⁅a, 1 - (sqrt_ℏ 2) • (N + (2⁻¹ : ℂ) • 1)⁆) := by
      simp [Bracket.bracket]
      rw [mul_assoc]
    _ = _ := by
      rw [mul_sub, ←mul_assoc, sub_eq_add_neg]
      congr
      simp
      rfl
  have h₂ : Z * a * (star a * Z) = (N + 1) * (1 - sqrt_ℏ 2 • (N + (2⁻¹ : ℂ) • 1)) := by
    calc _ = Z * (a * star a) * Z := by noncomm_ring
    _ = Z * (N + 1) * Z := by rw [a_mul_star_a]
    _ = (N + 1) * (Z * Z) := by
      simp [mul_add, add_mul]
      rw [←mul_assoc, Z_mul_N]
    _ = _ := by
      rw [Z_mul_Z]
  rw [h₁, h₂]
  simp [smul_comm (M:=ℂℏ) (N:=ℂ), mul_add, mul_sub, smul_add, smul_sub, add_mul]
  simp [smul_smul, ←sqrt_ℏ_add]
  ring_nf
  simp
  abel_nf
  simp
  abel

@[simp]
theorem lie_Y_X : ⁅Y, X⁆ = -H := by
  rw [←lie_skew]
  simp [lie_X_Y]
