import LeanResearch.RepulsiveCoulomb.PointActualBigonExclusion
import LeanResearch.RepulsiveCoulomb.PointActualTriangleExclusion
import LeanResearch.RepulsiveCoulomb.PointPrescribedLineObstruction
import LeanResearch.RepulsiveCoulomb.PointLocalGeodesicObstruction

/-! Eliminate the actual Jordan obstructions to local-to-global minimizing
continuation. Every literal prescribed segment extends to an actual proper
minimizing ray and complete line. No uniqueness of line continuation at a cone
vertex, balance, or halfplane metric identification is asserted. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

theorem not_pointJordanGeodesicObstruction
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    ¬ PointJordanGeodesicObstruction a y := by
  intro hobs
  unfold PointJordanGeodesicObstruction at hobs
  rcases hobs with hB | hT
  · obtain ⟨B⟩ := hB
    have hdR := B.right.geodesic
    rw [← B.start_eq, ← B.finish_eq] at hdR
    exact not_pointConformal_simple_geodesic_bigon ha y B.left.distinct B.left.curve B.right.curve
      B.left.curve_start B.left.curve_finish
      (B.right.curve_start.trans B.start_eq.symm) (B.right.curve_finish.trans B.finish_eq.symm)
      B.left.geodesic hdR B.intersection
  · obtain ⟨q, r, hr, T, hJ, hlocal⟩ := hT
    exact not_pointSimpleGeodesicTriangle_locally_minimizing_corner ha y T hr hlocal

/-- A locally minimizing constant-speed actual curve minimizes between every
pair of its parameters. Its hypothetical first shortcut would produce one
of the genuine Jordan configurations already excluded. -/
theorem pointConformal_local_geodesic_global
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (γ : Icc (0 : ℝ) 1 → ℂ) {c : ℝ}
    (hlocal : ∀ t, ∃ U : Set (Icc (0 : ℝ) 1), IsOpen U ∧ t ∈ U ∧
      ∀ s ∈ U, ∀ t ∈ U,
        (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = c * |t.1 - s.1|) :
    ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = c * |t.1 - s.1| := by
  let M := pointSmoothConformalMetricSpace ha y
  have hloc : @LocallyConstantSpeedInterval ℂ M.toPseudoMetricSpace c γ := hlocal
  have hle := @locallyConstantSpeedInterval_dist_le ℂ M.toPseudoMetricSpace c γ hloc
    ⟨0, by norm_num⟩ ⟨1, by norm_num⟩
  change (pointSmoothConformalEDist a y (γ ⟨0, by norm_num⟩) (γ ⟨1, by norm_num⟩)).toReal ≤
    c * |(1 : ℝ) - 0| at hle
  simp only [sub_zero, abs_one, mul_one] at hle
  have hnot : ¬ (pointSmoothConformalEDist a y (γ ⟨0, by norm_num⟩)
      (γ ⟨1, by norm_num⟩)).toReal < c := by
    intro hshort
    exact not_pointJordanGeodesicObstruction ha y (pointLocalGeodesic_shortcut_obstruction ha y γ hlocal hshort)
  have hfull := le_antisymm hle (le_of_not_gt hnot)
  intro s t
  exact @locallyConstantSpeedInterval_prefix_distance ℂ M.toPseudoMetricSpace c γ hloc
    ⟨1, by norm_num⟩ (by
      change (pointSmoothConformalEDist a y (γ ⟨0, by norm_num⟩)
        (γ ⟨1, by norm_num⟩)).toReal = c * (1 : ℝ)
      simpa only [mul_one] using hfull) s t s.2.2 t.2.2

/-- Every actual prescribed minimizing edge is literally contained in an
actual infinite minimizing ray, including the seed's closed endpoint. -/
theorem exists_pointConformal_prescribed_complete_ray
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (E : PointGeodesicTreeEdge a y) :
    ∃ γ : NNReal → ℂ, γ 0 = E.start ∧ IsClosedEmbedding γ ∧ IsProperMap γ ∧
      (∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = dist s t) ∧
      ∀ t : Icc (0 : ℝ) 1,
        γ ⟨(pointSmoothConformalEDist a y E.start E.finish).toReal * t.1,
          mul_nonneg ENNReal.toReal_nonneg t.2.1⟩ = E.curve t := by
  rcases pointPrescribedRay_or_jordan_obstruction ha y E with hray | hobs
  · obtain ⟨γ, h0, hc, hd, hseed⟩ := hray
    have hclosed := pointMetricRay_isClosedEmbedding ha y γ hd
    exact ⟨γ, h0, hclosed, hclosed.isProperMap, hd,
      pointMetricRay_closed_preservation y E γ hc hseed⟩
  · exact False.elim (not_pointJordanGeodesicObstruction ha y hobs)

/-- Every actual prescribed minimizing edge is literally contained in an
actual proper minimizing complete line. This is an existence theorem;
it imposes no balance or uniqueness of continuation through a cone atom. -/
theorem exists_pointConformal_prescribed_complete_line
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (E : PointGeodesicTreeEdge a y) :
    ∃ ℓ : ℝ → ℂ, ℓ 0 = E.start ∧ IsClosedEmbedding ℓ ∧ IsProperMap ℓ ∧
      (∀ s t, (pointSmoothConformalEDist a y (ℓ s) (ℓ t)).toReal = dist s t) ∧
      ∀ t : Icc (0 : ℝ) 1,
        ℓ ((pointSmoothConformalEDist a y E.start E.finish).toReal * t.1) = E.curve t := by
  rcases pointPrescribedLine_or_jordan_obstruction ha y E with hline | hobs
  · exact hline
  · exact False.elim (not_pointJordanGeodesicObstruction ha y hobs)

end RepulsiveCoulomb
