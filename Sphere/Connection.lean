import Sphere.Operator
import Sphere.Basis
import Mathlib.RingTheory.TensorProduct.Basic

open TensorProduct

abbrev ΩOp := Ω ⊗[ℂ] Op

noncomputable section

instance : SMulCommClass ℂ Ω Ω := by infer_instance
instance : IsScalarTower ℂ Ω Ω := by infer_instance

def d_lift : Module.End ℂ ΩOp := TensorProduct.lift {
  toFun x := LinearMap.comp
    (Algebra.TensorProduct.mul ((Algebra.TensorProduct.includeLeft : Ω →ₐ[ℂ] ΩOp) (Cochain.d x)))
    (Algebra.TensorProduct.includeRight.toLinearMap : Op →ₗ[ℂ] ΩOp)
  map_add' := by intros; ext; simp [add_tmul]
  map_smul' := by intros; ext; simp
}

instance : Ring ΩOp := by infer_instance

set_option synthInstance.maxHeartbeats 200000 in
instance : SMulCommClass ℂ ΩOp ΩOp := by infer_instance

def A : ΩOp := Ω.H' ⊗ₜ[ℂ] Op.H + Ω.X' ⊗ₜ[ℂ] Op.X + Ω.Y' ⊗ₜ[ℂ] Op.Y

def del : Module.End ℂ ΩOp := d_lift + {
  toFun x := A * x - x * A
  map_add' := by intros; noncomm_ring
  map_smul' := by intros; simp [smul_sub]; rw [smul_mul_assoc, mul_smul_comm]
}
