import LeanResearch.RepulsiveCoulomb.PoleBranchHyperplaneHartogs
import LeanResearch.RepulsiveCoulomb.LabeledCoulombModel

/-! The actual Coulomb collision hyperplanes are distinct. Hence the proved
finite-hyperplane Hartogs theorem removes every simultaneous collision once
the generic, single-collision points have been filled. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

abbrev PoleBranchCoulombPair (N : ℕ) := {p : Fin N × Fin N // p.1 < p.2}

def poleBranchCoulombNormal {N : ℕ} (p : PoleBranchCoulombPair N) : CoulombConfig N →L[ℂ] ℂ :=
  EuclideanSpace.proj p.1.1 - EuclideanSpace.proj p.1.2

theorem poleBranchCoulombNormal_apply {N : ℕ} (p : PoleBranchCoulombPair N) (z : CoulombConfig N) :
    poleBranchCoulombNormal p z = z p.1.1 - z p.1.2 := rfl

theorem poleBranchCoulombNormal_ne_zero {N : ℕ} (p : PoleBranchCoulombPair N) :
    poleBranchCoulombNormal p ≠ 0 := by
  intro h
  have H := congrArg (fun A : CoulombConfig N →L[ℂ] ℂ => A (EuclideanSpace.single p.1.1 1)) h
  simp [poleBranchCoulombNormal_apply, PiLp.single_apply, ne_of_lt p.2, (ne_of_lt p.2).symm] at H

theorem poleBranchCoulombNormal_kernel_injective (N : ℕ) :
    Function.Injective (fun p : PoleBranchCoulombPair N => (poleBranchCoulombNormal p).ker) := by
  intro p q hpq
  dsimp only at hpq
  have hsupport (m : Fin N) (hm : m = p.1.1 ∨ m = p.1.2) : m = q.1.1 ∨ m = q.1.2 := by
    by_contra h
    push_neg at h
    have hq : EuclideanSpace.single m (1 : ℂ) ∈ (poleBranchCoulombNormal q).ker := by
      change (EuclideanSpace.single m (1 : ℂ)) q.1.1 -
        (EuclideanSpace.single m (1 : ℂ)) q.1.2 = 0
      simp [PiLp.single_apply, h.1, h.2, Ne.symm h.1, Ne.symm h.2]
    have hp : EuclideanSpace.single m (1 : ℂ) ∈ (poleBranchCoulombNormal p).ker := by
      rw [hpq]
      exact hq
    change (EuclideanSpace.single m (1 : ℂ)) p.1.1 -
      (EuclideanSpace.single m (1 : ℂ)) p.1.2 = 0 at hp
    rcases hm with rfl | rfl
    · simp [PiLp.single_apply, ne_of_lt p.2, (ne_of_lt p.2).symm] at hp
    · simp [PiLp.single_apply, ne_of_lt p.2, (ne_of_lt p.2).symm] at hp
  have hi := hsupport p.1.1 (Or.inl rfl)
  have hj := hsupport p.1.2 (Or.inr rfl)
  apply Subtype.ext
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact False.elim ((ne_of_lt p.2) (hi.trans hj.symm))
  · exact Prod.ext hi hj
  · exfalso
    have hlt : q.1.2 < q.1.1 := by simpa only [hi, hj] using p.2
    exact (not_lt_of_ge q.2.le) hlt
  · exact False.elim ((ne_of_lt p.2) (hi.trans hj.symm))

def poleBranchCoulombRegular (N : ℕ) : Set (CoulombConfig N) :=
  poleBranchHyperplaneRegular (fun p : PoleBranchCoulombPair N => poleBranchCoulombNormal p)

theorem poleBranchCoulombRegular_iff {N : ℕ} (z : CoulombConfig N) :
    z ∈ poleBranchCoulombRegular N ↔
      ∀ p q : PoleBranchCoulombPair N, p ≠ q →
        z p.1.1 ≠ z p.1.2 ∨ z q.1.1 ≠ z q.1.2 := by
  simp only [poleBranchCoulombRegular, poleBranchHyperplaneRegular, mem_setOf_eq,
    poleBranchCoulombNormal_apply, sub_ne_zero]

theorem poleBranch_coulomb_multiple_collision_removable
    {N : ℕ} {f : CoulombConfig N → ℂ}
    (hf : DifferentiableOn ℂ f (poleBranchCoulombRegular N)) :
    ∃ F : CoulombConfig N → ℂ, Differentiable ℂ F ∧ EqOn F f (poleBranchCoulombRegular N) :=
  poleBranch_finite_hyperplane_hartogs poleBranchCoulombNormal poleBranchCoulombNormal_ne_zero
    (poleBranchCoulombNormal_kernel_injective N) hf

end RepulsiveCoulomb
