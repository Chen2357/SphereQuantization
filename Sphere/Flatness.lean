import Sphere.Differential
import Sphere.Operator
import Mathlib.RingTheory.TensorProduct.Basic

noncomputable section

open TensorProduct

abbrev EOp := TensorProduct ℂ E Op
-- We have the opportunity to make EOp a graded algebra.

def d_lift' : E →ₗ[ℂ] (Op →ₗ[ℂ] EOp) := {
  toFun := fun x => LinearMap.comp (Algebra.TensorProduct.mul ((Algebra.TensorProduct.includeLeft : E →ₐ[ℂ] EOp) (d x))) (Algebra.TensorProduct.includeRight.toLinearMap : Op →ₗ[ℂ] EOp)
  map_add' := by intros; ext; simp [add_tmul]
  map_smul' := by intros; ext; simp [smul_tmul]
}

def d_lift : EOp →ₗ[ℂ] EOp := TensorProduct.lift d_lift'

def A : EOp := α.val ⊗ₜ[ℂ] k3 + l.val ⊗ₜ[ℂ] kp + l_bar.val ⊗ₜ[ℂ] km

lemma C_nat_eq_cast (x : ℕ) : (@LaurentPolynomial.C ℂ _ x) = (Algebra.cast x) := by norm_cast

lemma tmul_cast_smul (x : E) (c : ℂ) (y : Op) : x ⊗ₜ[ℂ] ((Algebra.cast c : ℂℏ) • y) = c • (x ⊗ₜ[ℂ] y) := by
  suffices (Algebra.cast c : ℂℏ) • y = c • y by rw [this]; simp
  norm_cast

lemma cast_mul_cast (x : ℂ) (y : ℂ) : (Algebra.cast x : ℂℏ) * (Algebra.cast y : ℂℏ) = Algebra.cast (x * y) := by simp

lemma cast'_mul_cast (x : ℕ) (y : ℂ) : (Algebra.cast x : ℂℏ) * (Algebra.cast y : ℂℏ) = Algebra.cast (x * y) := by simp

theorem connection_flat : d_lift A + A * A = 0 := by
  unfold A
  simp [add_mul, mul_add, d_lift, d_lift']
  simp [graded_comm Λ α l, graded_comm Λ α l_bar, graded_comm Λ l_bar l]
  simp only [neg_tmul, ←tmul_neg]
  calc
  _ = (d α ⊗ₜ[ℂ] k3 + d l ⊗ₜ[ℂ] kp + d l_bar ⊗ₜ[ℂ] km) +
  ((l * l_bar : E) ⊗ₜ[ℂ] (kp * km) + (l * l_bar : E) ⊗ₜ[ℂ] (-(km * kp))) +
  ((l * α : E) ⊗ₜ[ℂ] (kp * k3) + (l * α : E) ⊗ₜ[ℂ] (-(k3 * kp))) +
  ((l_bar * α : E) ⊗ₜ[ℂ] (km * k3) + (l_bar * α : E) ⊗ₜ[ℂ] (-(k3 * km))) := by
    abel
  _ = 0 := by
    simp [dα_eq, dl_eq, dl_bar_eq]
    simp [←tmul_add, ←sub_eq_add_neg]
    have := commutator_kp_km
    simp [commutator] at this
    have := commutator_kp_k3
    simp [commutator] at this
    have := commutator_km_k3
    simp [commutator] at this
    simp [*]
    simp only [C_eq_cast]
    simp only [OfNat.ofNat, C_nat_eq_cast]
    simp only [tmul_smul, smul_tmul, neg_tmul, tmul_neg, tmul_cast_smul, cast'_mul_cast]
    abel

def del : EOp →ₗ[ℂ] EOp := d_lift + {
  toFun := fun x => A * x - x * A
  map_add' := by intros; noncomm_ring
  map_smul' := by intros; simp [smul_sub]
}
