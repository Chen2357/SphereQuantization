-- import Sphere.Basis

-- noncomputable section

-- @[simp] lemma ιρα : ι ρ α = (1 : Λ0) := by
--     unfold ρ α
--     simp [ι_d, smul_smul, smul_add, smul_sub]
--     simp [←add_smul]
--     rw [subalgebra_smul_one_eq_cast]
--     norm_cast
--     rw [←con]
--     abel

-- @[simp] lemma ιρl : ι ρ l = 0 := by
--     unfold ρ l l1 l2
--     simp [ι_d, smul_smul, smul_add, smul_sub]
--     custom_rewrite
--     abel

-- @[simp] lemma ιρl_bar : ι ρ l_bar = 0 := by
--     unfold ρ l_bar l1 l2
--     simp [ι_d, smul_smul, smul_add, smul_sub]
--     custom_rewrite
--     abel

-- @[simp] lemma ιφα : ι φ α = 0 := by
--     unfold φ φ1 φ2 α
--     simp [ι_d, smul_smul, smul_add, smul_sub]
--     custom_rewrite

-- @[simp] lemma ιφl : ι φ l = (1 : Λ0) := by
--     unfold φ φ1 φ2 l l1 l2
--     simp [ι_d, smul_smul, smul_add, smul_sub]
--     custom_rewrite
--     collect (1 : E)
--     rw [subalgebra_smul_one_eq_cast]
--     norm_cast
--     simp
--     abel_nf
--     custom_rewrite
--     rw [←con]
--     ring

-- @[simp] lemma ιφl_bar : ι φ l_bar = 0 := by
--     unfold φ φ1 φ2 l_bar l1 l2
--     simp [ι_d, smul_smul, smul_add, smul_sub]
--     custom_rewrite
--     simp
--     abel

-- @[simp] lemma ιφ_bar_α : ι φ_bar α = 0 := by
--     unfold φ_bar φ1 φ2 α
--     simp [ι_d, smul_smul, smul_add, smul_sub]
--     custom_rewrite

-- @[simp] lemma ιφ_bar_l : ι φ_bar l = 0 := by
--     unfold φ_bar φ1 φ2 l l1 l2
--     simp [ι_d, smul_smul, smul_add, smul_sub]
--     custom_rewrite
--     simp
--     abel

-- @[simp] lemma ιφ_bar_l_bar : ι φ_bar l_bar = (1 : Λ0) := by
--     unfold φ_bar φ1 φ2 l_bar l1 l2
--     simp [ι_d, smul_smul, smul_add, smul_sub]
--     custom_rewrite
--     simp
--     custom_rewrite
--     collect (1 : E)
--     rw [subalgebra_smul_one_eq_cast]
--     norm_cast
--     simp
--     rw [←con]
--     ring
