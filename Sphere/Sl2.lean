import Sphere.Util.USl2
import Sphere.Operator
import Sphere.Lie
import Mathlib.Algebra.Lie.UniversalEnveloping

noncomputable section

def to_Op : (USl2 ℂ) →ₐ[ℂ] Op := UniversalEnvelopingAlgebra.lift ℂ <| Sl2.lift ℂ {
  toFun x := x 0 • Op.H + x 1 • Op.X + x 2 • Op.Y
  map_add' := by intros; simp [add_smul]; abel
  map_smul' := by  simp [smul_smul]
} (by simp) (by simp) (by simp)

@[simp] def to_end_𝒜_linear : Sl2 ℂ →ₗ[ℂ] (𝒜 →ₗ[ℂ] 𝒜) := {
  toFun x := {
    toFun f := (x 0 • 𝒳.H + x 1 • 𝒳.X + x 2 • 𝒳.Y) f
    map_add' := by intros; simp [map_add]
    map_smul' := by intros; simp
  }
  map_add' := by intros; ext; simp [add_smul]; abel
  map_smul' := by intros; ext; simp [smul_smul]
}

def to_end_𝒜 : (USl2 ℂ) →ₐ[ℂ] (𝒜 →ₗ[ℂ] 𝒜) := UniversalEnvelopingAlgebra.lift ℂ <| Sl2.lift ℂ to_end_𝒜_linear (by
    ext
    simp [←𝒳.lie_X_Y]
    rfl
  ) (by
    ext f
    simp
    conv_rhs => equals (2 • 𝒳.X) f => simp
    rw [←𝒳.lie_H_X]
    rfl
  ) (by
    ext f
    simp
    conv_rhs => equals (-(2 • 𝒳.Y)) f => simp
    rw [←𝒳.lie_H_Y]
    rfl
  )
