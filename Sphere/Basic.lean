import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import LieRinehart.Derivation
import Cochain.Cartan
import Sphere.Util.Sum

open TensorProduct
open Cochain
open AlternatingMap
open DirectSum

noncomputable section

abbrev S3 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

@[irreducible] def 𝒜 := ℂ ⊗[ℝ] ContMDiffMap (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) (modelWithCornersSelf ℝ ℝ) S3 ℝ ⊤

instance : CommRing 𝒜 := by unfold 𝒜; infer_instance
instance : Algebra ℂ 𝒜 := by unfold 𝒜; infer_instance

abbrev 𝒳 := Derivation ℂ 𝒜 𝒜
abbrev Ω := Cochain 𝒜 𝒳 𝒜

instance : Module ℂ Ω := by infer_instance

def fx (i : Fin 4) : 𝒜 := by
  unfold 𝒜
  exact 1 ⊗ₜ {
    val x := (x : EuclideanSpace ℝ (Fin 4)) i
    property := by
      have : (fun (x : S3) => (x : EuclideanSpace ℝ (Fin 4)) i) = (fun x => x i) ∘ (fun (x : S3) => (x : EuclideanSpace ℝ (Fin 4))) := by
        ext; simp
      rw [this]
      apply ContDiff.comp_contMDiff
      exact contDiff_piLp_apply 2
      have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := by simp; trivial
      exact contMDiff_coe_sphere
  }

@[simp] theorem sum_eq_one : ∑ i, fx i ^ 2 = 1 := by
  unfold 𝒜 fx id
  simp [Finset.sum, ←TensorProduct.tmul_add]
  congr
  ext x
  simp
  rcases x with ⟨x, hx⟩
  simp [norm] at hx
  have := congr_arg (fun x => x ^ (2 : ℝ)) hx
  dsimp at this
  rw [←Real.rpow_mul] at this
  simp [Finset.sum] at this
  linarith
  apply Finset.sum_nonneg
  intro i
  simp [sq_nonneg]

@[simp] theorem defining_eq : fx 0 * fx 0 + fx 1 * fx 1 + fx 2 * fx 2 + fx 3 * fx 3 = 1 := by
  rw [←sum_eq_one]
  simp [Finset.sum]
  ring

axiom px (i : Fin 4) : 𝒳
@[simp] axiom px_def (i j : Fin 4) : px i (fx j) = (ite (i = j) 1 0) - fx i * fx j

axiom eq_of_apply_fx {x y : 𝒳} (h : ∀ i, x (fx i) = y (fx i)) : x = y

@[simp] theorem N_eq_zero : ∑ i : Fin 4, fx i • px i = 0 := by
  apply eq_of_apply_fx
  intro j
  simp [Finset.sum]
  fin_cases j <;> simp
  · calc _ = fx 0 - fx 0 * ∑ i, fx i ^ 2 := by simp [Finset.sum]; ring
    _ = _ := by simp
  · calc _ = fx 1 - fx 1 * ∑ i, fx i ^ 2 := by simp [Finset.sum]; ring
    _ = _ := by simp
  · calc _ = fx 2 - fx 2 * ∑ i, fx i ^ 2 := by simp [Finset.sum]; ring
    _ = _ := by simp
  · calc _ = fx 3 - fx 3 * ∑ i, fx i ^ 2 := by simp [Finset.sum]; ring
    _ = _ := by simp

@[simp] theorem lie_px (i j : Fin 4) : ⁅px i, px j⁆ = fx i • px j - fx j • px i := by
  apply eq_of_apply_fx
  intro k
  conv_lhs =>
    equals px i (px j (fx k)) - px j (px i (fx k)) => rfl
  simp
  split <;> simp <;> rename_i h1
  rw [h1]
  all_goals split <;> rename_i h2 <;> try rw [h2]
  all_goals simp [h1]
  all_goals simp [Ne.symm h2]
  . ring
  . split_ifs with h3
    . simp; ring
    . simp; ring

def dx (i : Fin 4) : Ω := d (algebraMap 𝒜 Ω (fx i))
axiom d_eq_in_dx (f : 𝒜) : d (algebraMap 𝒜 Ω f) = ∑ i : Fin 4, px i f • (dx i)

@[simp] theorem ι_px_dx (i j : Fin 4) : ι (px i) (dx j) = (ite (i = j) 1 0) - algebraMap 𝒜 Ω (fx i * fx j) := by simp [dx, ι_d]

@[simp] theorem ν_eq_zero : ∑ i : Fin 4, fx i • (dx i) = 0 := by
  suffices (2 : ℂ) • ∑ i : Fin 4, fx i • (dx i) = 0 by
    have := congr_arg (fun x => (2⁻¹ : ℂ) • x) this
    dsimp at this
    rw [smul_smul] at this
    ring_nf at this
    simp at this
    exact this
  calc _ = d (∑ i, algebraMap 𝒜 Ω (fx i ^ 2)) := by {
    ext1 n
    by_cases h : n = 1
    case pos =>
      cases h
      ext v
      simp [DirectSum.smul_apply, -map_pow, AlternatingMap.sum_apply, dx, Finset.smul_sum]
      simp [ofNat_smul_eq_nsmul]
    case neg =>
      simp [DirectSum.smul_apply, -map_pow, dx]
      conv_lhs =>
        enter [2, 2, i, 2]
        simp [h, -map_pow]
      conv_rhs =>
        enter [2, i]
        simp [h, -map_pow]
      simp
  }
  _ = d 1 := by simp [←map_sum, -map_pow]
  _ = 0 := by simp
