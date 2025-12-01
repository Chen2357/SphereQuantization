-- import Sphere.Utilities
-- import Sphere.Basis
-- import Mathlib.Algebra.Group.Center
-- import Mathlib.Algebra.Star.Basic
-- import Mathlib.Algebra.Star.SelfAdjoint
-- import Mathlib.Algebra.Polynomial.Laurent

-- noncomputable section

-- abbrev ℂℏ := LaurentPolynomial ℂ
-- -- We could provide these instances, but it is cumbersome.
-- @[instance] axiom ℂℏ.StarRing : StarRing ℂℏ
-- @[instance] axiom ℂℏ.StarModule : StarModule ℂ ℂℏ

-- def sqrt_ℏ : ℂℏˣ := {
--   val := LaurentPolynomial.T 1,
--   inv := ⅟ (LaurentPolynomial.T 1),
--   val_inv := mul_invOf_self _,
--   inv_val := invOf_mul_self _
-- }
-- @[simp] axiom star_sqrt_ℏ : star sqrt_ℏ = sqrt_ℏ
-- @[simp] lemma star_ℏ_inv : star (sqrt_ℏ⁻¹) = sqrt_ℏ⁻¹ := IsSelfAdjoint.inv star_sqrt_ℏ

-- axiom Op : Type
-- @[instance] axiom Op.Ring : Ring Op
-- @[instance] axiom Op.Algebra : Algebra ℂℏ Op
-- @[instance] axiom Op.StarRing : StarRing Op
-- @[instance] axiom Op.StarModule : StarModule ℂℏ Op

-- instance : Algebra ℂ Op := Algebra.compHom Op (algebraMap ℂ ℂℏ)

-- instance : SMulCommClass ℂ ℂℏ Op where
--     smul_comm c x y := by
--         show (algebraMap ℂ ℂℏ c) • (x • y) = x • ((algebraMap ℂ ℂℏ c) • y)
--         rw [smul_smul, mul_comm, ←smul_smul]

-- instance : IsScalarTower ℂ ℂℏ Op where
--   smul_assoc := by
--     intros c x y
--     show (c • x) • y = (algebraMap ℂ (ℂℏ) c) • (x • y)
--     simp [smul_smul, Algebra.smul_def]
--     rw [mul_assoc]

-- axiom a : Op
-- axiom X : Op

-- def N : Op := (star a) * a

-- axiom X_X : X * X = (1 : Op) - (sqrt_ℏ.val^2) • (N + Algebra.cast (2⁻¹ : ℂ))
-- lemma X_sq : X ^ 2 = (1 : Op) - (sqrt_ℏ.val^2) • (N + Algebra.cast (2⁻¹ : ℂ)) := by rw [sq]; exact X_X

-- @[simp] lemma star_N : star N = N := by rw [N]; simp
-- @[simp] axiom star_X : star X = X

-- def k3 : Op := Algebra.cast ((-Complex.I) • (sqrt_ℏ⁻¹.val)^2) + (Algebra.cast Complex.I : ℂℏ) • ((2 : ℂℏ) • N + Algebra.cast (2⁻¹ : ℂ))
-- def kp : Op := (Complex.I • sqrt_ℏ⁻¹.val) • ((star a) * X)
-- def km : Op := (Complex.I • sqrt_ℏ⁻¹.val) • (X * a)

-- def commutator : Op →ₗ[ℂℏ] Op →ₗ[ℂℏ] Op := {
--   toFun := fun x => {
--     toFun := fun y => x * y - y * x,
--     map_add' := by intros; noncomm_ring
--     map_smul' := by intros; simp [Algebra.mul_smul_comm, smul_sub]
--   },
--   map_add' := by intros; ext; simp; noncomm_ring
--   map_smul' := by intros; ext; simp [Algebra.mul_smul_comm, smul_sub]
-- }

-- lemma commutator_comm (x y : Op) : commutator x y = -commutator y x := by simp [commutator]

-- @[simp] lemma commutator_self (x : Op) : commutator x x = 0 := by simp [commutator]

-- @[simp] lemma commutator_nat (x : Op) : commutator x 1 = 0 := by simp [commutator]

-- @[simp] lemma algebraMap_commutator' (x : ℂ) (y : Op) : commutator (algebraMap ℂ Op x) y = 0 := by simp [commutator, Algebra.algebraMap_eq_smul_one]

-- @[simp] lemma commutator_algebraMap' (x : Op) (y : ℂ) : commutator x (algebraMap ℂ Op y) = 0 := by simp [commutator, Algebra.algebraMap_eq_smul_one]

-- @[simp] lemma algebraMap_commutator (x : ℂℏ) (y : Op) : commutator (algebraMap ℂℏ Op x) y = 0 := by simp [commutator, Algebra.algebraMap_eq_smul_one]

-- @[simp] lemma commutator_algebraMap (x : Op) (y : ℂℏ) : commutator x (algebraMap ℂℏ Op y) = 0 := by simp [commutator, Algebra.algebraMap_eq_smul_one]

-- lemma commutator_mul (x y z : Op) : commutator x (y * z) = commutator x y * z + y * commutator x z := by
--   simp [commutator, mul_sub, sub_mul]
--   noncomm_ring

-- lemma mul_commutator (x y z : Op) : commutator (x * y) z = x * commutator y z + commutator x z * y := by
--   simp [commutator, mul_sub, sub_mul]
--   noncomm_ring

-- @[simp] axiom commutator_N_X : commutator N X = 0
-- @[simp] axiom commutator_a_star_a : commutator a (star a) = 1
-- @[simp] lemma commutator_star_a_a : commutator (star a) a = -1 := by rw [commutator_comm]; simp

-- lemma commutator_N_star_a : commutator N (star a) = star a := by
--   simp [N, mul_commutator]

-- theorem commutator_k3_kp : commutator k3 kp = (Algebra.cast (2 * Complex.I) : ℂℏ) • kp := by
--   unfold k3 kp
--   simp
--   simp [commutator_mul, commutator_N_star_a, smul_smul]
--   congr 1
--   norm_cast
--   ring_nf
--   simp [OfNat.ofNat]

-- lemma commutator_kp_k3 : commutator kp k3 = (Algebra.cast (-2 * Complex.I) : ℂℏ) • kp := by
--   rw [commutator_comm]
--   simp [commutator_k3_kp]

-- lemma commutator_N_a : commutator N a = -a := by
--   simp [N, mul_commutator]

-- -- attribute [-simp] AddMonoidAlgebra.coe_algebraMap

-- theorem commutator_k3_km : commutator k3 km = (Algebra.cast (-2 * Complex.I) : ℂℏ) • km := by
--   unfold k3 km
--   simp
--   simp [commutator_mul, commutator_N_a, smul_smul]
--   congr 1
--   simp [OfNat.ofNat]
--   ring

-- theorem commutator_km_k3 : commutator km k3 = (Algebra.cast (2 * Complex.I) : ℂℏ) • km := by
--   rw [commutator_comm]
--   simp [commutator_k3_km]

-- lemma mul_eq_add_commutator (x y : Op) : x * y = y * x + commutator x y := by simp [commutator]

-- lemma nat_mul_eq_smul {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (n : ℕ) (x : A) : (n : A) * x = (n : R) • x := by
--   show (algebraMap ℕ A n) * x = (algebraMap ℕ R n) • x
--   suffices (algebraMap ℕ A n) * x = (algebraMap R A (algebraMap ℕ R n)) * x by
--     rw [this, ←Algebra.smul_def]
--   rw [←IsScalarTower.algebraMap_apply]

-- lemma nat_mul_eq_smul' {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (n : ℕ) [n.AtLeastTwo] (x : A) : (OfNat.ofNat n : A) * x = (n : R) • x := by exact nat_mul_eq_smul n x

-- lemma C_eq_cast : (LaurentPolynomial.C Complex.I) = (Algebra.cast Complex.I) := by norm_cast

-- private lemma h1 : star a * X * (X * a) = (1 + (-1 • sqrt_ℏ.val ^ 2 • N + -1 • sqrt_ℏ.val ^ 2 • (Algebra.cast (2⁻¹ : ℂ) : Op))) * N + sqrt_ℏ.val ^ 2 • N := by
--   simp [N]
--   rw [mul_assoc]
--   nth_rewrite 2 [←mul_assoc]
--   simp [X_X]
--   rw [mul_eq_add_commutator]
--   simp [commutator_mul]
--   rw [commutator_comm, commutator_N_star_a]
--   rw [mul_assoc]
--   rw [mul_eq_add_commutator a (star a)]
--   simp [mul_add, N, smul_mul_assoc]
--   abel_nf

-- private lemma h2 : X * a * (star a * X) = (1 + (-1 • sqrt_ℏ.val ^ 2 • N + -1 • sqrt_ℏ.val ^ 2 • (Algebra.cast (2⁻¹ : ℂ) : Op))) + (1 - sqrt_ℏ.val ^ 2 • (N + (Algebra.cast (2⁻¹ : ℂ) : Op))) * N := by
--   rw [mul_assoc]
--   nth_rewrite 2 [←mul_assoc]
--   rw [mul_eq_add_commutator a (star a)]
--   have : N = star a * a := by rfl
--   simp [←this, add_mul]
--   rw [mul_eq_add_commutator N X]
--   simp [mul_add, ←mul_assoc, X_X, sub_mul, add_mul]
--   abel_nf

-- theorem commutator_kp_km : commutator kp km = (Algebra.cast (Complex.I) : ℂℏ) • k3 := by
--   unfold kp km
--   simp
--   custom_rewrite
--   simp [commutator]
--   rw [h1, h2]
--   unfold k3
--   simp [mul_add, mul_sub, add_mul, sub_mul, smul_smul]
--   abel_nf
--   simp only [C_eq_cast]
--   custom_rewrite
--   simp only [C_eq_cast]
--   norm_cast
--   simp [-AddMonoidAlgebra.coe_algebraMap]
--   norm_cast
--   simp only [@Algebra.smul_def ℂ ℂℏ]
--   ring_nf
--   norm_cast
--   simp
--   push_cast
--   rw [←add_assoc]
--   nth_rewrite 2 [add_comm]
--   rw [add_assoc]
--   congr 1
--   simp [Algebra.cast, Algebra.algebraMap_eq_smul_one, sq, mul_smul]

-- lemma commutator_km_kp : commutator km kp = (Algebra.cast (-Complex.I) : ℂℏ) • k3 := by
--   rw [commutator_comm]
--   simp [commutator_kp_km]
