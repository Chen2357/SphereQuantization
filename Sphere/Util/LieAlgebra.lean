import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Sphere.Util.Finset
import LieRinehart.Basic
import Mathlib.LinearAlgebra.PiTensorProduct

open LieAlgebra
open Function

section

variable {R : Type*} [CommRing R]
variable {A : Type*} [Ring A] [Algebra R A]

def prodLifted {n : ℕ} : PiTensorProduct R (fun (_ : Fin n) => A) →ₗ[R] A := PiTensorProduct.lift {
  toFun v := (List.ofFn v).prod
  map_update_add' := by
    induction n
    case zero => simp
    case succ n ih =>
      intros deq m i x y
      cases (show deq = instDecidableEqFin _ from Subsingleton.elim _ _)
      cases i using Fin.cases
      case zero =>
        simp [add_mul]
      case succ i =>
        simp [ih, mul_add, show 0 ≠ i.succ from by symm; simp, ←Fin.tail_def]
  map_update_smul' := by
    induction n
    case zero => simp
    case succ n ih =>
      intros deq m i x y
      cases (show deq = instDecidableEqFin _ from Subsingleton.elim _ _)
      cases i using Fin.cases
      case zero =>
        simp
      case succ i =>
        simp [ih, ←Fin.tail_def, show 0 ≠ i.succ from by symm; simp]
}

def adLifted_i (x : A) (n : ℕ) (i : Fin n) : Module.End R (PiTensorProduct R (fun (_ : Fin n) => A)) := PiTensorProduct.lift {
  toFun v := PiTensorProduct.tprod R (update v i ⁅x, v i⁆)
  map_update_add' := by
    intros deq m j y z
    cases (show deq = instDecidableEqFin _ from Subsingleton.elim _ _)
    by_cases h : i = j
    . rw [h]; simp
    . simp [h, update_comm (Ne.symm h)]
  map_update_smul' := by
    intros deq m j y z
    cases (show deq = instDecidableEqFin _ from Subsingleton.elim _ _)
    by_cases h : i = j
    . rw [h]; simp
    . simp [h, update_comm (Ne.symm h)]
}

def adLifted (x : A) (n : ℕ) : Module.End R (PiTensorProduct R (fun (_ : Fin n) => A)) := ∑ i : Fin n, adLifted_i x n i

theorem lie_prodr_eq_sum (x : A) {n : ℕ} (y : Fin n → A) : ⁅x, (List.ofFn y).prod⁆ = ∑ i : Fin n, (List.ofFn (update y i ⁅x, y i⁆)).prod := by
  induction n
  case zero => simp
  case succ n ih =>
    simp [lier_mul, Fin.sum_univ_succ, ih, Finset.mul_sum]
    rw [add_comm]
    conv_rhs => enter [2, 2, i]; simp [show 0 ≠ i.succ from by symm; simp]
    simp [←Fin.tail_def]

lemma ad_prodr (x : A) {n : ℕ} (y : Fin n → A) : ad R A x (List.ofFn y).prod = prodLifted (adLifted x n (PiTensorProduct.tprod R y)) := by
  simp [prodLifted, adLifted, adLifted_i, lie_prodr_eq_sum]

lemma ad_prodLifted (x : A) {n : ℕ} (y : PiTensorProduct R (fun (_ : Fin n) => A)) :
    ad R A x (prodLifted y) = prodLifted (adLifted x n y) := by
  induction y using PiTensorProduct.induction_on
  case smul_tprod r y =>
    simp [-ad_apply, ←ad_prodr]
    simp [prodLifted]
  case add y1 y2 ih1 ih2 =>
    simp [-ad_apply, *]

lemma ad_pow_prod (x : A) (n : ℕ) {m : ℕ} (y : Fin m → A) : ((ad R A x)^n) (List.ofFn y).prod = prodLifted (((adLifted x m)^n) (PiTensorProduct.tprod R y)) := by
  induction n
  case zero => simp [prodLifted]
  case succ n ih =>
    rw [add_comm]
    simp [pow_add, ih, -ad_apply]
    rw [ad_prodLifted]

lemma adLifted_i_pairwise_comm (x : A) (n : ℕ) (s : Set (Fin n)) : s.Pairwise (Commute on adLifted_i (R:=R) x n) := by
  intro i _ j _ hne
  ext v
  simp [adLifted_i, update_comm hne, hne, Ne.symm hne]

lemma adLifted_i_tprod (x : A) (n : ℕ) (i : Fin n) (y : Fin n → A) : adLifted_i x n i (PiTensorProduct.tprod R y) = PiTensorProduct.tprod R (update y i ⁅x, y i⁆) := by
  simp [adLifted_i]

open PiTensorProduct in
lemma prod_adLifted_i (x : A) (n : ℕ) (k : Fin n → ℕ) (y) : (List.ofFn (fun i => adLifted_i x n i ^ k i)).prod (tprod R y) = tprod R (fun i => ((ad R A x) ^ (k i)) (y i)) := by
  suffices ∀ (j : Fin (n + 1)), (List.ofFn (fun i => adLifted_i x n i ^ (if i < j.val then k i else 0))).prod (tprod R y) = tprod R (fun (i : Fin n) => ((ad R A x) ^ (if i < j.val then k i else 0)) (y i)) by
    specialize this (Fin.last n)
    simp at this
    exact this
  rintro ⟨j, hj⟩
  induction j
  case zero => simp
  case succ j ih =>
    simp
    simp at *
    specialize ih (by exact Nat.lt_add_right 1 hj)
    sorry

theorem ad_pow_prod_eq_sum_piAntidiag (x : A) (n : ℕ) {m : ℕ} (y : Fin m → A) :
  ((ad R A x)^n) (List.ofFn y).prod = ∑ k ∈ ((.univ : Finset (Fin m)).piAntidiag n), (Nat.multinomial .univ k) * (List.ofFn (fun i => ((ad R A x)^(k i)) (y i))).prod := by
  rw [ad_pow_prod, adLifted, Finset.sum_pow_eq_sum_piAntidiag_of_commute]
  simp [Finset.noncommProd]
  cases m with
  | zero =>
    simp [prodLifted]
  | succ m =>
    conv_lhs => enter [2, k]; rw [prod_adLifted_i]
    simp [prodLifted]
  apply adLifted_i_pairwise_comm
