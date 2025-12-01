import Mathlib.Algebra.Module.Basic

private lemma t0 {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (t : M) (r : R) (s : R) : r • t + s • t = (r + s) • t := by rw [add_smul]
private lemma t1 {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (t : M) (r : R) (s : R) (y : M) : r • t + (s • t + y) = (r + s) • t + y := by rw [add_smul, add_assoc]
private lemma t2 {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (t : M) (x : M) (r : R) (y : M) : x + (r • t + y) = r • t + (x + y) := by rw [add_comm, add_assoc, add_comm y]
private lemma t3 {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (t : M) (r : R) (x : M) : x + r • t = r • t + x := by rw [add_comm]

syntax "collect" term : tactic
macro_rules
| `(tactic| collect $x:term) => `(tactic| simp only [t0 $x:term, t1 $x:term, t2 $x:term, t3 $x:term])
