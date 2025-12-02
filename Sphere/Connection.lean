import Sphere.Operator
import Sphere.Basis
import Mathlib.RingTheory.TensorProduct.Basic

open TensorProduct

abbrev ΩOp := Ω ⊗[ℂ] Op

noncomputable section

instance : Algebra ℂ Ω := by infer_instance

def d_lift : ΩOp →ₗ[ℂ] ΩOp := TensorProduct.lift {
  toFun x := LinearMap.comp
    (Algebra.TensorProduct.mul ((Algebra.TensorProduct.includeLeft : Ω →ₐ[ℂ] ΩOp) (Cochain.d x)))
    (Algebra.TensorProduct.includeRight.toLinearMap : Op →ₗ[ℂ] ΩOp)
  map_add' := by intros; ext; simp [add_tmul]
  map_smul' := by intros; ext; simp
}

def A : ΩOp := Ω.H' ⊗ₜ[ℂ] Op.H + Ω.X' ⊗ₜ[ℂ] Op.X + Ω.Y' ⊗ₜ[ℂ] Op.Y

def del : ΩOp →ₗ[ℂ] ΩOp := d_lift + {
  toFun x := A * x - x * A
  map_add' := by intros; noncomm_ring
  map_smul' := by intros; simp [smul_sub]; rw [smul_mul_assoc, mul_smul_comm]
}
