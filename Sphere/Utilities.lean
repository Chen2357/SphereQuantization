-- import Mathlib.Data.Complex.Basic
-- import Mathlib.RingTheory.GradedAlgebra.Basic

-- instance {F A : Type*} [Field F] [AddCommMonoid A] [Module F A] : NoZeroSMulDivisors F A where
--     eq_zero_or_eq_zero_of_smul_eq_zero := by
--         intros c x h
--         by_cases hc : c = 0
--         exact Or.inl hc
--         right
--         calc x
--         _ = (c⁻¹) • (c • x) := by
--             simp [smul_smul, inv_mul_cancel₀ hc]
--         _ = 0 := by
--             simp [h]

-- lemma subalgebra_smul_one_eq_cast {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {S : Subalgebra R A} (x : S) : x • (1 : A) = x := by
--     show x.val * (1 : A) = x.val
--     simp

-- lemma subalgebra_smul_eq_cast_mul {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {S : Subalgebra R A} (x : S) (y : A) : x • y = x.val * y := by rfl

-- lemma nat_smul_eq_smul {R A: Type*}  [CommSemiring R] [Semiring A] [Algebra R A] (x : ℕ) (y : A) : x • y = (x : R) • y := by norm_cast

-- section Homogeneous

-- variable {ι R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
-- variable (𝒜 : ι → Submodule R A)

-- class Homogeneous (x : A) where
--     deg : ι
--     mem : x ∈ 𝒜 deg

-- lemma Homogeneous.mem_if (x : A) (n : ι) [Homogeneous 𝒜 x] : (deg 𝒜 x = n) → (x ∈ 𝒜 n) := by
--     intro h
--     rw [←h]
--     exact mem

-- variable [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜]

-- instance Homogeneous.add  (x y : A) [Homogeneous 𝒜 x] [Homogeneous 𝒜 y] (h : deg 𝒜 x = deg 𝒜 y) : Homogeneous 𝒜 (x + y) where
--     deg := deg 𝒜 x
--     mem := by
--         apply Submodule.add_mem
--         exact Homogeneous.mem
--         rw [h]
--         exact Homogeneous.mem

-- @[simp] instance Homogeneous.one : Homogeneous 𝒜 1 where
--     deg := 0
--     mem := SetLike.GradedOne.one_mem

-- @[simp] instance Homogeneous.algebraMap (x : R) : Homogeneous 𝒜 (algebraMap R A x) where
--     deg := 0
--     mem := by
--         simp [Algebra.algebraMap_eq_smul_one]
--         apply Submodule.smul_mem
--         exact SetLike.GradedOne.one_mem

-- @[simp] instance Homogeneous.smul (c : R) (x: A) [Homogeneous 𝒜 x]  : Homogeneous 𝒜 (c • x) where
--     deg := deg 𝒜 x
--     mem := by apply Submodule.smul_mem; exact mem

-- @[simp] instance Homogeneous.mul (x y : A) [Homogeneous 𝒜 x] [Homogeneous 𝒜 y] : Homogeneous 𝒜 (x * y) where
--     deg := deg 𝒜 x + deg 𝒜 y
--     mem := by apply SetLike.GradedMul.mul_mem; all_goals exact mem

-- @[simp] instance Homogeneous.subtype {n : ι} (x : 𝒜 n) : Homogeneous 𝒜 x where
--     deg := n
--     mem := x.property

-- variable {ι R A : Type*} [DecidableEq ι] [AddMonoid ι] [CommRing R] [Ring A] [Algebra R A]
-- variable (𝒜 : ι → Submodule R A)
-- variable [GradedAlgebra 𝒜]

-- instance Homogeneous.sub  (x y : A) [Homogeneous 𝒜 x] [Homogeneous 𝒜 y] (h : deg 𝒜 x = deg 𝒜 y) : Homogeneous 𝒜 (x - y) where
--     deg := deg 𝒜 x
--     mem := by
--         apply Submodule.sub_mem (𝒜 (deg 𝒜 x))
--         exact Homogeneous.mem
--         rw [h]
--         exact Homogeneous.mem

-- @[simp] instance Homogeneous.neg (x: A) [Homogeneous 𝒜 x]  : Homogeneous 𝒜 (-x) where
--     deg := deg 𝒜 x
--     mem := by apply Submodule.neg_mem; exact mem

-- syntax "linear_homogeneous" : tactic

-- macro_rules
-- | `(tactic| linear_homogeneous) => `(tactic| apply Homogeneous.mem)

-- macro_rules
-- | `(tactic| linear_homogeneous) => `(tactic| apply Homogeneous.mem_if; simp)

-- macro_rules
-- | `(tactic| linear_homogeneous) => `(tactic| apply Submodule.add_mem <;> linear_homogeneous)

-- macro_rules
-- | `(tactic| linear_homogeneous) => `(tactic| apply Submodule.sub_mem <;> linear_homogeneous)

-- macro_rules
-- | `(tactic| linear_homogeneous) => `(tactic| apply Submodule.smul_mem <;> linear_homogeneous)

-- macro_rules
-- | `(tactic| linear_homogeneous) => `(tactic| apply Submodule.neg_mem <;> linear_homogeneous)

-- end Homogeneous

-- variable {R A : Type*} [CommRing R] [Semiring A] [Algebra R A]

-- class GradedCommRing (𝒜 : ℤ → Submodule R A) extends GradedRing 𝒜 where
--     graded_comm {n m : ℤ} (x y : A) : (x ∈ 𝒜 n) → (y ∈ 𝒜 m) → x * y = (if Even (n * m) then 1 else -1 : R) • (y * x)

-- variable (𝒜 : ℤ → Submodule R A) [GradedCommRing 𝒜]

-- abbrev GradedCommAlgebra := GradedCommRing 𝒜

-- lemma graded_comm (x y : A) [Homogeneous 𝒜 x] [Homogeneous 𝒜 y] : x * y = (if Even ((Homogeneous.deg 𝒜 x) * (Homogeneous.deg 𝒜 y)) then 1 else -1 : R) • (y * x) := GradedCommRing.graded_comm x y (Homogeneous.mem) (Homogeneous.mem)

-- instance : CommSemiring (SetLike.GradeZero.subalgebra 𝒜) where
--     mul_comm := by
--         intros x y
--         have := graded_comm 𝒜 x y
--         simp at this
--         norm_cast at this

-- instance : SMulCommClass R (SetLike.GradeZero.subalgebra 𝒜) A where
--     smul_comm c x y := by
--         show c • (x.val * y) = x.val * (c • y)
--         simp only [Algebra.smul_def]
--         rw [←mul_assoc, Algebra.commutes, mul_assoc]

-- lemma mul_deg_zero (x : A) (y : (SetLike.GradeZero.subalgebra 𝒜)) : x * y = y * x := by
--     have (i : ℤ) (m : ↥(𝒜 i)) : m.val * y = y * m := by
--         simp [graded_comm 𝒜 m y]
--     have (m m' : A) : m * ↑y = ↑y * m → m' * ↑y = ↑y * m' → (m + m') * ↑y = ↑y * (m + m') := by
--         intro h h'
--         rw [add_mul, mul_add, h, h']
--     exact DirectSum.Decomposition.inductionOn 𝒜 (by simp) (by assumption) (by assumption) x

-- instance : SMulCommClass (SetLike.GradeZero.subalgebra 𝒜) A A where
--     smul_comm c x y := by
--         show c * (x * y) = x * (c * y)
--         rw [←mul_assoc, ←mul_deg_zero, mul_assoc]

-- @[simp] instance Homogeneous.smul' (c : SetLike.GradeZero.subalgebra 𝒜) (x: A) [Homogeneous 𝒜 x]  : Homogeneous 𝒜 (c • x) where
--     deg := deg 𝒜 x
--     mem := by
--         show c * x ∈ 𝒜 (deg 𝒜 x)
--         apply Homogeneous.mem_if
--         simp

-- lemma mul_self_of_mem {𝒜 : ℤ → Submodule R A} [GradedCommRing 𝒜] [CharZero R] [NoZeroSMulDivisors R A] (x : A) (n : ℤ) : x ∈ 𝒜 n → x * x = (if Even n then 1 else 0) • (x * x) := by
--     cases Int.even_or_odd n with
--     | inl h => simp [*]
--     | inr h => ?_
--     intro mem
--     simp at h
--     simp [Int.not_even_iff_odd.mpr h]
--     have comm := GradedCommRing.graded_comm x x mem mem
--     have : ¬Even (n * n) := by simp [*]
--     simp [this] at comm
--     have : (2 : R) • (x * x) = 0 := by
--         rw [two_smul]
--         nth_rewrite 1 [comm]
--         nth_rewrite 2 [←one_smul R (x * x)]
--         rw [←add_smul]
--         simp
--     exact (smul_eq_zero_iff_right (by simp)).mp this

-- lemma mul_self [CharZero R] [NoZeroSMulDivisors R A] (x : A) [Homogeneous 𝒜 x] : x * x = (if Even (Homogeneous.deg 𝒜 x) then 1 else 0) • (x * x) := mul_self_of_mem x (Homogeneous.deg 𝒜 x) (Homogeneous.mem)

-- lemma mul_self_odd_deg_of_mem {𝒜 : ℤ → Submodule R A} [GradedCommRing 𝒜] [CharZero R] [NoZeroSMulDivisors R A] (x : A) (n : ℤ) (mem : x ∈ 𝒜 n) : Odd n → x * x = 0 := by
--     intro
--     rw [mul_self_of_mem x n mem]
--     simp [*]

-- @[simp] lemma mul_self_deg_one {𝒜 : ℤ → Submodule R A} [GradedCommRing 𝒜] [CharZero R] [NoZeroSMulDivisors R A] (x : 𝒜 1) : x.val * x.val = 0 := mul_self_odd_deg_of_mem x.val 1 x.property (by simp)

-- lemma mul_self_odd_deg [CharZero R] [NoZeroSMulDivisors R A] (x : A) [Homogeneous 𝒜 x] : Odd (Homogeneous.deg 𝒜 x) → x * x = 0 := mul_self_odd_deg_of_mem x (Homogeneous.deg 𝒜 x) (Homogeneous.mem)

-- section collect

-- private lemma t0 {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (t : M) (r : R) (s : R) : r • t + s • t = (r + s) • t := by rw [add_smul]
-- private lemma t1 {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (t : M) (r : R) (s : R) (y : M) : r • t + (s • t + y) = (r + s) • t + y := by rw [add_smul]; abel
-- private lemma t2 {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (t : M) (x : M) (r : R) (y : M) : x + (r • t + y) = r • t + (x + y) := by abel
-- private lemma t3 {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (t : M) (r : R) (x : M) : x + r • t = r • t + x := by rw [add_comm]

-- syntax "collect" term : tactic
-- macro_rules
-- | `(tactic| collect $x:term) => `(tactic| simp only [t0 $x:term, t1 $x:term, t2 $x:term, t3 $x:term])

-- private lemma t0' {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (t : M) (r : R) (s : R) : r • t + s • t = (r + s) • t := by rw [add_smul]
-- private lemma t1' {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (t : M) (r : R) (s : R) (y : M) : y + r • t + s • t = y + (r + s) • t := by rw [add_smul]; abel
-- private lemma t2' {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (t : M) (x : M) (r : R) (y : M) : x + r • t + y = x + y + r • t := by abel
-- private lemma t3' {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (t : M) (r : R) (x : M) : r • t + x = x + r • t := by rw [add_comm]

-- syntax "collect'" term : tactic
-- macro_rules
-- | `(tactic| collect' $x:term) => `(tactic| simp only [t0' $x:term, t1' $x:term, t2' $x:term, t3' $x:term])

-- end collect
