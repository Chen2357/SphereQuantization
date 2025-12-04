import Sphere.Util.Sl2
import Sphere.Util.Ring
import Sphere.Util.Finset
import Sphere.Util.UniversalEnveloping
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.LinearAlgebra.Vandermonde

open Sl2
open UniversalEnvelopingAlgebra
open LieAlgebra

variable (R : Type*) [CommRing R] [Nontrivial R]

abbrev USl2 := UniversalEnvelopingAlgebra R (Sl2 R)

def h_half_weight (m : ℤ) : Submodule R (USl2 R) where
  carrier := { x | ad R _ (ι R (h R)) x = (2 * m) • x }
  zero_mem' := by simp
  add_mem' := by
    intros
    simp at *
    simp [*, mul_add]
  smul_mem' := by
    intros
    simp at *
    simp [*]

@[simp]
theorem h_mem_iff {m : ℤ} {x : USl2 R} : x ∈ h_half_weight R m ↔ ad R _ (ι R (h R)) x = (2 * m) • x := by rfl

theorem h_mem_algebraMap {r : R} : algebraMap R (USl2 R) r ∈ h_half_weight R 0 := by
  simp [h_mem_iff, Bracket.bracket, Algebra.commutes]

theorem h_mem_mul {n m : ℤ} {x : USl2 R} (hx : x ∈ h_half_weight R n) {y : USl2 R} (hy : y ∈ h_half_weight R m) : x * y ∈ h_half_weight R (n + m) := by
  simp [-zsmul_eq_mul] at *
  simp [lie_mul, *, -zsmul_eq_mul, ←add_smul]
  ring_nf

theorem h_mem_h : ι R (h R) ∈ h_half_weight R 0 := by
  simp

theorem h_mem_e : ι R (e R) ∈ h_half_weight R 1 := by
  simp [-zsmul_eq_mul, -ι_apply, ←LieHom.map_lie]
  simp

theorem h_mem_f : ι R (f R) ∈ h_half_weight R (-1) := by
  simp [-zsmul_eq_mul, -ι_apply, ←LieHom.map_lie]
  simp

instance : SetLike.GradedMonoid (h_half_weight R) where
  one_mem := by simp
  mul_mem _ _ _ _ hx hy := h_mem_mul R hx hy

-- Key observation: If x is in two different weight spaces, then 2(m-n) • x = 0.
-- This is the first step toward showing weight spaces are disjoint.
theorem h_half_weight_eq_smul {m n : ℤ} {x : USl2 R}
    (hm : x ∈ h_half_weight R m) (hn : x ∈ h_half_weight R n) :
    (2 * (m - n)) • x = 0 := by
  simp only [h_mem_iff] at hm hn
  have : (2 * m) • x = (2 * n) • x := by rw [← hm, ← hn]
  calc (2 * (m - n)) • x = (2 * m - 2 * n) • x := by ring_nf
    _ = (2 * m) • x - (2 * n) • x := by rw [sub_smul]
    _ = 0 := by rw [this, sub_self]

-- Applying `ad(h)` to an element of weight space m gives 2m times that element.
-- This is the eigenvalue property that enables the Vandermonde argument for independence.
theorem h_half_weight_ad_h {m : ℤ} {x : USl2 R} (hx : x ∈ h_half_weight R m) :
    ⁅ι R (h R), x⁆ = (2 * m) • x := by
  simp only [h_mem_iff] at hx
  exact hx

section Field

variable (K : Type*) [Field K] [CharZero K]

-- instance : IsAddTorsionFree (USl2 K) where
--   nsmul_right_injective n hn x y hxy := by
--     have hne : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
--     exact smul_right_injective (USl2 K) hne hxy

open Matrix in
theorem h_half_weight_iSupIndep : iSupIndep (h_half_weight K) := by
  apply (iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero _).mpr
  intros s v h_weight h_sum_zero i hi
  induction s using Finset.fin_induction
  rename_i n f f_inj
  simp at hi
  rcases hi with ⟨i, rfl⟩
  simp [f_inj] at h_sum_zero
  simp [-ad_apply, -ι_apply] at h_weight
  let van := vandermonde fun j => (algebraMap ℤ K (2 * f j))
  let V : Fin n → USl2 K := v ∘ f
  have : ∀ j, v (f j) = V j := by intro; rfl
  rw [this]
  conv_lhs at h_sum_zero => enter [2, x]; rw [this]
  conv at h_weight => ext; rw [this]

  have van_det : van.det ≠ 0 := by
    apply det_vandermonde_ne_zero_iff.mpr
    intro j1 j2 h_eq
    simp at h_eq
    exact f_inj h_eq

  suffices V = 0 by simp [this]
  suffices V ᵥ* van.map (algebraMap K (USl2 K)) ᵥ* van⁻¹.map (algebraMap K (USl2 K)) = 0 by
    simp [←Matrix.map_mul, van_det] at this
    exact this
  suffices V ᵥ* van.map (algebraMap K (USl2 K)) = 0 by
    rw [this]
    simp

  ext i
  simp [vecMul, dotProduct, van, -algebraMap_int_eq, -eq_intCast, -map_mul, ←map_pow, ←Algebra.commutes]
  have : ∀ i j, (algebraMap K (USl2 K)) ((algebraMap ℤ K) ((2 * f j) ^ i)) * V j = ((ad K _ (ι K (h K)))^i) (V j) := by
    intros i j
    induction i
    case zero => simp
    case succ i ih =>
      conv_rhs => rw [add_comm]; simp [pow_add, -ad_apply, -ι_apply, ←ih, -map_pow]
      conv_rhs =>
        enter [2]
        equals (2 * f j) ^ i • V j => simp [mul_pow]; rfl
      rw [map_zsmul, h_weight]
      simp [pow_succ, mul_assoc]
      rfl
  conv_lhs => enter [2, _]; rw [this]
  rw [←map_sum, h_sum_zero]
  simp

open Submodule in
lemma h_half_weight_finite_iSup (x : USl2 K) : ∃ s : Finset ℤ, x ∈ ⨆ (i ∈ s), h_half_weight K i := by
  induction x using UniversalEnvelopingAlgebra.induction
  case algebraMap r =>
    use {0}
    simp [-ι_apply, -ad_apply]
    simp [Bracket.bracket, Algebra.commutes]
  case ι x =>
    use {1, 0, -1}
    rw [←add_apply_smul_h_e_f x]
    simp
    apply add_mem
    · apply add_mem
      · apply smul_mem
        apply (show h_half_weight K 0 ≤ _ from _)
        exact h_mem_h K
        intro x hx
        apply mem_iSup_of_mem 0
        simp [hx]
      · apply smul_mem
        apply (show h_half_weight K 1 ≤ _ from _)
        exact h_mem_e K
        intro x hx
        apply mem_iSup_of_mem 1
        simp [hx]
    · apply smul_mem
      apply (show h_half_weight K (-1) ≤ _ from _)
      exact h_mem_f K
      intro x hx
      apply mem_iSup_of_mem (-1)
      simp [hx]
  case add a b ha hb =>
    rcases ha with ⟨s_a, ha'⟩
    rcases hb with ⟨s_b, hb'⟩
    use s_a ∪ s_b
    apply add_mem
    · apply (show ⨆ (i ∈ s_a), h_half_weight K ↑i ≤ _ from _) ha'
      rw [Finset.iSup_union]
      simp
    · apply (show ⨆ (i ∈ s_b), h_half_weight K ↑i ≤ _ from _) hb'
      rw [Finset.iSup_union]
      simp
  case mul a b ha hb =>
    rcases ha with ⟨s_a, ha'⟩
    rcases hb with ⟨s_b, hb'⟩
    use Finset.image₂ (· + ·) s_a s_b
    rw [iSup_eq_span] at ha' hb' ⊢
    induction ha' using span_induction with
    | mem a ha =>
      simp only [Set.mem_iUnion] at ha
      rcases ha with ⟨i, hi, ha⟩
      induction hb' using span_induction with
      | mem b hb =>
        simp only [Set.mem_iUnion] at hb
        rcases hb with ⟨j, hj, hb⟩
        apply subset_span
        simp only [Set.mem_iUnion]
        exact ⟨i + j, Finset.mem_image₂_of_mem hi hj, h_mem_mul K ha hb⟩
      | zero => simp
      | add b₁ b₂ _ _ ih₁ ih₂ =>
        rw [mul_add]
        exact add_mem ih₁ ih₂
      | smul c b _ ih =>
        rw [mul_smul_comm]
        exact smul_mem _ c ih
    | zero => simp
    | add a₁ a₂ _ _ ih₁ ih₂ =>
      rw [add_mul]
      exact add_mem ih₁ ih₂
    | smul c a _ ih =>
      rw [smul_mul_assoc]
      exact smul_mem _ c ih

open Submodule in
theorem h_half_weight_iSup : iSup (h_half_weight K) = ⊤ := by
  simp [eq_top_iff']
  intro x
  rcases h_half_weight_finite_iSup K x with ⟨s, hx⟩
  apply (show (⨆ (i ∈ s), h_half_weight K i) ≤ iSup (h_half_weight K) from ?_) hx
  apply iSup₂_le
  intro i _
  exact le_iSup (h_half_weight K) i

theorem h_half_weight_directSum: DirectSum.IsInternal (h_half_weight K) := by
  apply (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
  constructor
  apply h_half_weight_iSupIndep
  apply h_half_weight_iSup

end Field
