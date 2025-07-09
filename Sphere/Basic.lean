import Sphere.Utilities
import Mathlib.RingTheory.GradedAlgebra.Basic

noncomputable section

-- Exterior algebra
axiom E : Type
@[instance] axiom E.Ring: Ring E
@[instance] axiom E.Algebra : Algebra ℂ E

axiom Λ : ℤ → Submodule ℂ E
@[instance] axiom Λ.GradedCommAlgebra : GradedCommAlgebra Λ

abbrev Λ0 := SetLike.GradeZero.subalgebra Λ

axiom d : E →ₗ[ℂ] E
axiom d_mem {n : ℤ} (x : Λ n) : d x ∈ Λ (n + 1)

@[simp] instance (x : E) [Homogeneous Λ x] : Homogeneous Λ (d x) where
    deg := Homogeneous.deg Λ x + 1
    mem := d_mem { val := x, property := Homogeneous.mem }

@[simp] axiom d_d (x : E) : d (d x) = 0
axiom d_mul {n m : ℤ} (x : Λ n) (y : Λ m) : d (x * y) = (-1 : ℂ)^(m) • y * (d x) + (-1 : ℂ)^(n) • x * (d y)
@[simp] axiom d_one : d 1 = 0

lemma d_smul (c : Λ0) (x : E) [h : Homogeneous Λ x] : d (c • x) = (-1 : ℂ)^(h.deg) • (x * (d c)) +  c • (d x) := by
    show d (c * x) = (-1 : ℂ)^(h.deg) • (x * (d c)) +  c * (d x)
    rw [d_mul { val := c, property := Homogeneous.mem } { val := x, property := h.mem }]
    simp
@[simp] lemma d_const (x : ℂ) : d (algebraMap ℂ E x) = 0 := by
    have : algebraMap ℂ E x = x • (1 : E) := Algebra.algebraMap_eq_smul_one x
    rw [this]
    simp

@[simp] lemma mul_self_d (x : Λ0) : (d x) * (d x) = 0 := by
    rw [mul_self Λ]
    simp

-- Tangent space
axiom T : Type
@[instance] axiom T.AddGroup : AddCommGroup T
@[instance] axiom T.Module : Module (Λ0) T
instance : Module ℂ T := Module.compHom T (algebraMap ℂ (Λ0))

instance : SMulCommClass ℂ (Λ0) T where
    smul_comm c x y := by
        show (algebraMap ℂ Λ0 c) • (x • y) = x • ((algebraMap ℂ Λ0 c) • y)
        rw [smul_smul, mul_comm, ←smul_smul]

instance : IsScalarTower ℂ (Λ0) T where
    smul_assoc := by
        intros c x y
        show (c • x) • y = (algebraMap ℂ (Λ0) c) • (x • y)
        simp [smul_smul, Algebra.smul_def]

-- Interior product
axiom ι : T →ₗ[Λ0] (E →ₗ[Λ0] E)
@[simp] axiom ι_deg_zero (p : T) (x : Λ0) : ι p x = 0
axiom ι_mem {n : ℤ} (p : T) (x : Λ n) : ι p x ∈ Λ (n - 1)

@[simp] instance (p : T) (x : E) [Homogeneous Λ x] : Homogeneous Λ (ι p x) where
    deg := Homogeneous.deg Λ x - 1
    mem := ι_mem p { val := x, property := Homogeneous.mem }

axiom ι_mul (p : T) (x y : E) [hx : Homogeneous Λ x] [hy : Homogeneous Λ y] : ι p (x * y) = (ι p x) * y + (-1 : ℂ) ^ (hy.deg) • ((ι p y) * x)

-- Interior product
def L : T →ₗ[ℂ] (E →ₗ[ℂ] E) := {
    toFun := fun x => {
        toFun := fun y => ι x (d y) + d (ι x y)
        map_add' := by intros; simp; abel
        map_smul' := by simp
    }
    map_add' := by intros; ext; simp; abel
    map_smul' := by intros; ext; simp
}

@[simp] instance (p : T) (x : E) [Homogeneous Λ x] : Homogeneous Λ (L p x) where
    deg := Homogeneous.deg Λ x
    mem := by apply Submodule.add_mem; all_goals apply Homogeneous.mem_if; simp

def der : T →ₗ[Λ0] (Λ0 →ₗ[ℂ] Λ0) := {
    toFun := fun x => {
        toFun := fun y => {
            val := ι x (d y),
            property := by apply Homogeneous.mem_if; simp
        }
        map_add' := by intros; simp
        map_smul' := by intros; simp
    }
    map_add' := by intros; ext; simp
    map_smul' := by
        intros c x
        ext z
        show (ι (c • x) (d z)) = c • (ι x (d z))
        simp
}
lemma ι_d (x : T) (y : Λ0) : ι x (d y) = der x y := rfl

axiom Lie : T →ₗ[ℂ] (T →ₗ[ℂ] T)
axiom Lie_antisymm (x : T) (y : T) : Lie x y = (-1 : ℂ) • Lie y x
axiom Lie_smul (x : T) (y : Λ0) (z : T) : Lie x (y • z) = (der x y) • z + y • Lie x z

lemma smul_Lie (x : Λ0) (y : T) (z : T) : Lie (x • y) z = (-(der z x)) • y + x • Lie y z := by
    rw [Lie_antisymm, Lie_smul, smul_add]
    congr 1
    simp
    rw [Lie_antisymm]
    simp

@[simp] lemma Lie_self (x : T) : Lie x x = 0 := by
    have := Lie_antisymm x x
    have : (2 : ℂ) • Lie x x = 0 := by
        rw [two_smul]
        nth_rewrite 1 [this]
        simp
    exact (smul_eq_zero_iff_right (by simp)).mp this

-- custom_rewrite

private lemma Int_smul_Complex_module {M : Type*} [AddCommGroup M] [Module ℂ M] (x : ℤ) (y : M) : (x • y) = (x : ℂ) • y := by norm_cast

-- Rewrite each term involving mul and smul of terms of ℕ, ℤ, ℂ, Λ0, E in the preferred way:
-- ((_ : ℂ) • (_ : Λ0)) • (_ : E)
-- where the term of E has no ℕ, ℤ, ℂ, Λ0 factors
--       the term of Λ0 has no ℕ, ℤ, ℂ factors
-- The point is that we want to use the `ring` and `simp` tactic on `Λ0` which is a commutative ring.
-- It also setups for the use of the `collect` tactic.
syntax "custom_rewrite" : tactic
macro_rules
| `(tactic| custom_rewrite) => `(tactic| simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ←smul_assoc, Int_smul_Complex_module] <;> ring_nf <;> try simp [-neg_smul, -smul_assoc] <;> abel_nf <;> try simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ←smul_assoc, Int_smul_Complex_module])
