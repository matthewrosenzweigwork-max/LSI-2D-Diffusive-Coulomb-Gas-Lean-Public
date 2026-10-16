module

public import LeanResearch.RepulsiveCoulomb.PlaneJordanSeparation
public import LeanResearch.RepulsiveCoulomb.PointConformalCompleteness

@[expose] public section

/-! Actual Jordan separation for the completed point-conformal metric plane.
All open sets, components, frontiers and compactness in the conclusion use the
constructed metric, explicitly. The input curve is continuous in Euclidean topology. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

def pointConformalPlaneHomeomorph {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    @Homeomorph ℂ Schoenflies.Plane
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace
      inferInstance := by
  rw [pointSmoothConformalMetricSpace_topology ha y]
  exact Complex.orthonormalBasisOneI.repr.toHomeomorph

theorem exists_pointConformal_jordan_regions {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (f : ℝ → ℂ)
    (hc : ContinuousOn f (Icc 0 1)) (hclose : f 0 = f 1)
    (hinj : InjOn f (Ico 0 1)) :
    letI : TopologicalSpace ℂ :=
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace
    ∃ U V : Set ℂ,
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
      U ∪ V = (f '' Icc 0 1)ᶜ ∧
      frontier U = f '' Icc 0 1 ∧ frontier V = f '' Icc 0 1 ∧
      IsCompact (closure U) ∧
      (∀ x ∈ U, connectedComponentIn (f '' Icc 0 1)ᶜ x = U) ∧
      (∀ x ∈ V, connectedComponentIn (f '' Icc 0 1)ᶜ x = V) := by
  have hc' : @ContinuousOn ℝ ℂ _
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace
      f (Icc 0 1) := by
    rwa [pointSmoothConformalMetricSpace_topology ha y]
  exact @jordan_separation_of_homeomorph ℂ
    (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace
    (pointConformalPlaneHomeomorph ha y) f hc' hclose hinj

end RepulsiveCoulomb
