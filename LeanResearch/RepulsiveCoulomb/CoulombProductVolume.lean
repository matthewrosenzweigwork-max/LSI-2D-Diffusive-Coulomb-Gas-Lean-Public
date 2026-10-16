import LeanResearch.RepulsiveCoulomb.LabeledCoulombModel
import LeanResearch.RepulsiveCoulomb.FiniteProductCurrying

/-! The real Euclidean volume on complex l2 configurations is exactly the
product of planar Lebesgue measures in particle coordinates. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

def coulombRealCoordinates (N : ℕ) :
    (Fin N → ℂ) ≃ᵐ ((p : Sigma (fun _ : Fin N => Fin 2)) → ℝ) :=
  (MeasurableEquiv.piCongrRight (fun _ : Fin N => Complex.measurableEquivPi)).trans
    (MeasurableEquiv.piCurry (fun (_ : Fin N) (_ : Fin 2) => ℝ)).symm

theorem coulombRealCoordinates_measurePreserving (N : ℕ) :
    MeasurePreserving (coulombRealCoordinates N) := by
  have h1 : MeasurePreserving (MeasurableEquiv.piCongrRight (fun _ : Fin N => Complex.measurableEquivPi)) :=
    volume_preserving_pi (fun _ => Complex.volume_preserving_equiv_pi)
  have h2 : MeasurePreserving (MeasurableEquiv.piCurry (fun (_ : Fin N) (_ : Fin 2) => ℝ)).symm := by
    simpa only [volume_pi] using
      finite_pi_uncurry_measurePreserving (fun (_ : Fin N) (_ : Fin 2) => (volume : Measure ℝ))
  exact h1.trans h2

theorem coulomb_coordinates_volume_preserving (N : ℕ) :
    MeasurePreserving (@WithLp.ofLp 2 (Fin N → ℂ)) := by
  let b := Pi.orthonormalBasis (fun _ : Fin N => Complex.orthonormalBasisOneI)
  have hb := (PiLp.volume_preserving_ofLp (Sigma (fun _ : Fin N => Fin 2))).comp
    b.measurePreserving_repr
  apply (coulombRealCoordinates_measurePreserving N).comp_left_iff.mp
  have heq : (coulombRealCoordinates N) ∘ (@WithLp.ofLp 2 (Fin N → ℂ)) =
      (@WithLp.ofLp 2 ((p : Sigma (fun _ : Fin N => Fin 2)) → ℝ)) ∘ b.repr := by
    funext z
    funext p
    rfl
  rw [heq]
  exact hb

theorem coulomb_volume_map_coordinates (N : ℕ) :
    Measure.map (@WithLp.ofLp 2 (Fin N → ℂ)) (volume : Measure (CoulombConfig N)) =
      Measure.pi (fun _ : Fin N => (volume : Measure ℂ)) := by
  simpa only [volume_pi] using (coulomb_coordinates_volume_preserving N).map_eq

end RepulsiveCoulomb
