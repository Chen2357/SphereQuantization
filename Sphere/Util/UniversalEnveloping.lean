import Mathlib.Algebra.Lie.UniversalEnveloping

variable (R : Type u₁)  (L : Type u₂)  [CommRing R]  [LieRing L] [LieAlgebra R L]

namespace UniversalEnvelopingAlgebra

theorem mkAlgHom_surjective : Function.Surjective (mkAlgHom R L) :=
  RingQuot.mkAlgHom_surjective R (Rel R L)

@[elab_as_elim]
theorem induction
  {motive : UniversalEnvelopingAlgebra R L → Prop}
  (x : UniversalEnvelopingAlgebra R L)
  (algebraMap : ∀ (r : R), motive (algebraMap R (UniversalEnvelopingAlgebra R L) r))
  (ι : ∀ (x : L), motive (ι R x))
  (mul : ∀ y z, motive y → motive z → motive (y * z))
  (add : ∀ y z, motive y → motive z → motive (y + z))
  : motive x := by
  rcases mkAlgHom_surjective R L x with ⟨a, rfl⟩
  induction a using TensorAlgebra.induction
  case algebraMap r =>
    convert algebraMap r
    simp
  case ι x =>
    convert ι x
  case add a b ih_a ih_b =>
    convert add _ _ ih_a ih_b
    simp
  case mul a b ih_a ih_b =>
    convert mul _ _ ih_a ih_b
    simp

end UniversalEnvelopingAlgebra
