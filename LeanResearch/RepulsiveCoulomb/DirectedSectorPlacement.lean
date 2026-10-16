import LeanResearch.RepulsiveCoulomb.ComplexDirectMotionRigidity
import LeanResearch.RepulsiveCoulomb.PointFlatLinkNormalizedPolar

/-! SOURCE-ONLY, UNCOMPILED. Explicit direct/reflected placement of a new
Euclidean sector in a prescribed ordered target angular interval. The same
derived Boolean as the old polar trace chooses the two endpoint assignments.
This is a genuine Euclidean motion, not an assumed overlap transition. -/
noncomputable section
namespace RepulsiveCoulomb

def directedSectorPlacement (lo width : ℝ) (forward : Bool) : ℂ ≃ᵢ ℂ :=
  if forward then complexDirectMotion (conePhase lo) 0 (conePhase_norm lo)
  else Complex.conjLIE.toIsometryEquiv.trans
    (complexDirectMotion (conePhase (lo + width)) 0 (conePhase_norm (lo + width)))

@[simp] theorem directedSectorPlacement_zero (lo width : ℝ) (forward : Bool) :
    directedSectorPlacement lo width forward 0 = 0 := by
  cases forward <;> simp [directedSectorPlacement, complexDirectMotion]

theorem complex_conj_sectorPolar (r θ : ℝ) :
    star (sectorPolar r θ) = sectorPolar r (-θ) := by
  apply Complex.ext
  · simp [Complex.star_def, sectorPolar_re]
  · simp [Complex.star_def, sectorPolar_im]

theorem directedSectorPlacement_polar (lo width r θ : ℝ) (forward : Bool) :
    directedSectorPlacement lo width forward (sectorPolar r θ) =
      sectorPolar r (lo + (if forward then θ else width - θ)) := by
  cases forward
  · change conePhase (lo + width) * star (sectorPolar r θ) + 0 = _
    rw [complex_conj_sectorPolar, add_zero, conePhase_mul_sectorPolar]
    apply congrArg (sectorPolar r)
    change (lo + width) + -θ = lo + (width - θ)
    ring
  · change conePhase lo * sectorPolar r θ + 0 = _
    rw [add_zero, conePhase_mul_sectorPolar]
    rfl

/-- Both sides have exactly the same ordered target endpoint convention. -/
theorem directedSectorPlacement_polar_unitInterval
    (lo width r : ℝ) (forward : Bool) (t : unitInterval) :
    directedSectorPlacement lo width forward (sectorPolar r (width * t.1)) =
      sectorPolar r (lo + flatLinkOrientedAngle forward width t) := by
  rw [directedSectorPlacement_polar]
  congr 2
  cases forward <;> simp only [flatLinkOrientedAngle, Bool.false_eq_true, ↓reduceIte] <;> ring

end RepulsiveCoulomb
