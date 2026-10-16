module

public import LeanResearch.RepulsiveCoulomb.FiniteUnitaryAverage
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.Group.Units.Hom

@[expose] public section

/-! Real sign characters and their genuine orthogonal twists. -/
noncomputable section
open scoped BigOperators
namespace RepulsiveCoulomb
variable {G E : Type*} [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def realCharacterTwist (U : G →* (E →L[ℝ] E)) (χ : G →* ℝ) : G →* (E →L[ℝ] E) where
  toFun g := χ g • U g
  map_one' := by simp
  map_mul' g h := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [map_mul, ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply,
      map_smul, smul_smul, mul_comm]

theorem realCharacterTwist_apply (U : G →* (E →L[ℝ] E)) (χ : G →* ℝ) (g : G) (x : E) :
    realCharacterTwist U χ g x = χ g • U g x := rfl

theorem realCharacterTwist_inner (U : G →* (E →L[ℝ] E)) (χ : G →* ℝ)
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y)
    (hχ : ∀ g, χ g ^ 2 = 1) (g : G) (x y : E) :
    inner ℝ (realCharacterTwist U χ g x) (realCharacterTwist U χ g y) = inner ℝ x y := by
  rw [realCharacterTwist_apply, realCharacterTwist_apply, real_inner_smul_left, real_inner_smul_right,
    hU, ← mul_assoc, ← pow_two, hχ, one_mul]

def permSignReal (N : ℕ) : Equiv.Perm (Fin N) →* ℝ :=
  (Int.castRingHom ℝ).toMonoidHom.comp ((Units.coeHom ℤ).comp Equiv.Perm.sign)

theorem permSignReal_apply (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    permSignReal N σ = (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) := rfl

theorem permSignReal_sq (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    permSignReal N σ ^ 2 = 1 := by
  rw [permSignReal_apply]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> norm_num

theorem permSignReal_swap {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    permSignReal N (Equiv.swap i j) = -1 := by
  rw [permSignReal_apply, Equiv.Perm.sign_swap hij]
  norm_num

end RepulsiveCoulomb
