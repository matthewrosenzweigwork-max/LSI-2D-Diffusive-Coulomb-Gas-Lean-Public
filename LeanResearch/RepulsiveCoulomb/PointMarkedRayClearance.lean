module

public import LeanResearch.RepulsiveCoulomb.FiniteMarkedUniformClearance
public import LeanResearch.RepulsiveCoulomb.PointMetricRaySegments

@[expose] public section

/-! Actual old-metric uniform clearance for the entire bottom ray or line.
The marked set is the actual finite set (including budget-only boundary marks),
not merely the set of positive ambient cone exponents. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- One positive width for every finite prefix of an actual clean minimizing
ray. The auxiliary positive bounds are the first edge mark and corner-chart
bound; if an edge has no mark, any positive number can be used for L. -/
theorem pointMetricRay_exists_uniform_marked_clearance {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (ρ : NNReal → ℂ)
    (hρ : ∀ s t, (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t)
    {S : Set ℂ} (hS : S.Finite) (hclean : Disjoint (S \ {ρ 0}) (range ρ))
    {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < L ∧ δ < ε ∧
      ∀ z ∈ S \ {ρ 0}, ∀ r : NNReal,
        δ < (pointSmoothConformalEDist a y z (ρ r)).toReal := by
  let M := pointSmoothConformalMetricSpace ha y
  have hi : @Isometry NNReal ℂ (inferInstance : PseudoEMetricSpace NNReal)
      M.toPseudoEMetricSpace ρ :=
    @Isometry.of_dist_eq NNReal ℂ inferInstance M.toPseudoMetricSpace ρ hρ
  obtain ⟨d, hd, hclear⟩ := @finite_isometric_range_uniform_clearance
    NNReal ℂ inferInstance inferInstance M ρ hi (S \ {ρ 0}) hS.sdiff hclean
  let δ := min d (min L ε) / 2
  have hm : 0 < min d (min L ε) := lt_min hd (lt_min hL hε)
  have hδ : 0 < δ := half_pos hm
  have hδm : δ < min d (min L ε) := half_lt_self hm
  refine ⟨δ, hδ, hδm.trans_le ((min_le_right _ _).trans (min_le_left _ _)),
    hδm.trans_le ((min_le_right _ _).trans (min_le_right _ _)), ?_⟩
  intro z hz r
  exact (hδm.trans_le (min_le_left _ _)).trans (hclear z hz r)

/-- Full unmarked old-boundary lines have the identical global-width bound. -/
theorem pointMetricLine_exists_uniform_marked_clearance {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (ℓ : ℝ → ℂ)
    (hℓ : ∀ s t, (pointSmoothConformalEDist a y (ℓ s) (ℓ t)).toReal = dist s t)
    {S : Set ℂ} (hS : S.Finite) (hclean : Disjoint S (range ℓ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ S, ∀ r : ℝ,
      δ < (pointSmoothConformalEDist a y z (ℓ r)).toReal := by
  let M := pointSmoothConformalMetricSpace ha y
  have hi : @Isometry ℝ ℂ (inferInstance : PseudoEMetricSpace ℝ)
      M.toPseudoEMetricSpace ℓ :=
    @Isometry.of_dist_eq ℝ ℂ inferInstance M.toPseudoMetricSpace ℓ hℓ
  exact @finite_isometric_range_uniform_clearance ℝ ℂ inferInstance inferInstance M ℓ hi S hS hclean

/-- No marked point can occur anywhere within the common distance cutoff of
the full ray, including at any finite-rectangle width limit. -/
theorem pointMetricRay_uniform_tube_unmarked {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {ρ : NNReal → ℂ}
    {S : Set ℂ} {δ : ℝ}
    (hclear : ∀ z ∈ S \ {ρ 0}, ∀ r : NNReal,
      δ < (pointSmoothConformalEDist a y z (ρ r)).toReal)
    {p : ℂ} {r : NNReal}
    (hp : (pointSmoothConformalEDist a y p (ρ r)).toReal ≤ δ) :
    p ∉ S \ {ρ 0} := by
  intro hpS
  exact (hclear p hpS r).not_ge hp

end RepulsiveCoulomb
