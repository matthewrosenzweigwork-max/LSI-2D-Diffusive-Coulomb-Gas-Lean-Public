module

public import LeanResearch.RepulsiveCoulomb.CoulombRelativeGeometry

@[expose] public section

/-! Algebraic chart support for the manuscript's all-particle center of mass.
The sole chart hypothesis says that the inverse first axis is diagonal. This
is an algebraic property of the explicit Helmert matrix, not a factorization,
functional inequality, domain, or entropy assumption. -/
noncomputable section
open Set MeasureTheory InnerProductSpace
open scoped Topology BigOperators
namespace RepulsiveCoulomb

variable {n : ℕ}

/-- The real isometry underlying a unitary particle-coordinate transform. -/
abbrev CoulombCenterRotation (n : ℕ) :=
  CoulombConfig (n + 1) ≃ₗᵢ[ℝ] CoulombConfig (n + 1)

/-- The exact algebraic condition needed to separate all particle differences. -/
def CoulombCenterAxis (e : CoulombCenterRotation n) : Prop :=
  ∀ c : ℂ, ∀ i j : Fin (n + 1),
    e.symm (coulombInsertZero c (0 : CoulombConfig n)) i =
      e.symm (coulombInsertZero c (0 : CoulombConfig n)) j

def coulombCenterInsert (e : CoulombCenterRotation n) (c : ℂ)
    (r : CoulombConfig n) : CoulombConfig (n + 1) :=
  e.symm (coulombInsertZero c r)

def coulombCenterChart (e : CoulombCenterRotation n) :
    CoulombConfig (n + 1) ≃ᵐ ℂ × CoulombConfig n :=
  e.toMeasurableEquiv.trans (coulombSplitZero n)

theorem coulombCenterChart_symm_apply (e : CoulombCenterRotation n)
    (c : ℂ) (r : CoulombConfig n) :
    (coulombCenterChart e).symm (c, r) = coulombCenterInsert e c r := by
  change e.symm ((coulombSplitZero n).symm (c, r)) = _
  rw [coulombSplitZero_symm_apply]
  rfl

theorem coulombCenterChart_insert (e : CoulombCenterRotation n)
    (c : ℂ) (r : CoulombConfig n) :
    coulombCenterChart e (coulombCenterInsert e c r) = (c, r) := by
  change coulombSplitZero n (e (e.symm (coulombInsertZero c r))) = _
  rw [e.apply_symm_apply, coulombSplitZero_insert]

theorem coulombCenterChart_measurePreserving (e : CoulombCenterRotation n) :
    MeasurePreserving (coulombCenterChart e)
      (volume : Measure (CoulombConfig (n + 1))) volume :=
  (coulombSplitZero_measurePreserving n).comp e.measurePreserving

theorem coulombCenterInsert_norm_sq (e : CoulombCenterRotation n)
    (c : ℂ) (r : CoulombConfig n) :
    ‖coulombCenterInsert e c r‖ ^ 2 = ‖c‖ ^ 2 + ‖r‖ ^ 2 := by
  rw [coulombCenterInsert, e.symm.norm_map, coulombInsertZero_norm_sq]

theorem coulombInsertZero_add_axes (c : ℂ) (r : CoulombConfig n) :
    coulombInsertZero c r =
      coulombInsertZero c (0 : CoulombConfig n) + coulombInsertZero 0 r := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [coulombInsertZero_zero, PiLp.add_apply, add_zero]
  · simp only [coulombInsertZero_succ, PiLp.add_apply, PiLp.zero_apply, zero_add]

theorem coulombCenterInsert_difference (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) (c : ℂ) (r : CoulombConfig n)
    (i j : Fin (n + 1)) :
    coulombCenterInsert e c r i - coulombCenterInsert e c r j =
      coulombCenterInsert e 0 r i - coulombCenterInsert e 0 r j := by
  rw [coulombCenterInsert, coulombInsertZero_add_axes, map_add]
  simp only [PiLp.add_apply]
  rw [he c i j]
  simp only [coulombCenterInsert]
  abel

theorem coulombCenterInsert_interaction (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) (α : ℝ) (c : ℂ) (r : CoulombConfig n) :
    coulombInteraction α (coulombCenterInsert e c r) =
      coulombInteraction α (coulombCenterInsert e 0 r) := by
  unfold coulombInteraction
  apply Finset.prod_congr rfl
  intro p hp
  rw [coulombCenterInsert_difference e he]

/-- Collision freedom is independent of the center, with no exceptional set. -/
theorem coulombCenterInsert_mem_domain_iff (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) (c : ℂ) (r : CoulombConfig n) :
    coulombCenterInsert e c r ∈ coulombDomain (n + 1) ↔
      coulombCenterInsert e 0 r ∈ coulombDomain (n + 1) := by
  change coulombVandermonde (coulombCenterInsert e c r) ≠ 0 ↔
    coulombVandermonde (coulombCenterInsert e 0 r) ≠ 0
  have hw : coulombVandermonde (coulombCenterInsert e c r) =
      coulombVandermonde (coulombCenterInsert e 0 r) := by
    unfold coulombVandermonde
    apply Finset.prod_congr rfl
    intro p hp
    exact coulombCenterInsert_difference e he c r p.1 p.2
  rw [hw]

/-- Exact raw density splitting: the relative factor is the original density
restricted to the zero-center plane, with its original exponent β/(n+1). -/
theorem coulombCenterInsert_weight (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) (β : ℝ) (c : ℂ) (r : CoulombConfig n) :
    coulombWeight β (coulombCenterInsert e c r) =
      Real.exp (-β * ‖c‖ ^ 2 / 2) *
        coulombWeight β (coulombCenterInsert e 0 r) := by
  rw [coulombWeight_eq_atExponent, coulombWeight_eq_atExponent]
  unfold coulombWeightAtExponent
  rw [coulombCenterInsert_interaction e he,
    coulombCenterInsert_norm_sq, coulombCenterInsert_norm_sq]
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add]
  rw [← mul_assoc, ← Real.exp_add]
  congr 1
  congr 1
  ring

end RepulsiveCoulomb
