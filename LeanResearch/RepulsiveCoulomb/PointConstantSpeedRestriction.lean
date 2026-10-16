module

public import LeanResearch.RepulsiveCoulomb.PointGeodesicSubedge
public import LeanResearch.RepulsiveCoulomb.PointGeodesicBigonExtraction

@[expose] public section

/-! A minimizing restriction of an actual constant-speed curve is converted
into the existing exact geodesic edge type by its explicit affine parameter.
Continuity and nondegeneracy follow from actual point-metric equalities. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def pointConstantSpeedRestriction {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (γ : Icc (0 : ℝ) 1 → ℂ)
    {c : ℝ} (hc : 0 < c) (s t : Icc (0 : ℝ) 1) (hst : s < t)
    (hd : ∀ u ∈ Icc s t, ∀ v ∈ Icc s t,
      (pointSmoothConformalEDist a y (γ u) (γ v)).toReal = c * |v.1 - u.1|) :
    PointGeodesicTreeEdge a y := by
  have hend := hd s ⟨le_rfl, hst.le⟩ t ⟨hst.le, le_rfl⟩
  have hneq : γ s ≠ γ t := by
    intro he
    rw [he, pointSmoothConformalEDist_self, ENNReal.toReal_zero] at hend
    have hp : 0 < c * |t.1 - s.1| :=
      mul_pos hc (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt (show s.1 < t.1 from hst))))
    linarith
  have hgeo : ∀ u v : Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ (pointEdgeSubparam s t u))
        (γ (pointEdgeSubparam s t v))).toReal =
      |v.1 - u.1| * (pointSmoothConformalEDist a y (γ s) (γ t)).toReal := by
    intro u v
    rw [hd _ (pointEdgeSubparam_mem hst.le u) _ (pointEdgeSubparam_mem hst.le v),
      pointEdgeSubparam_sub, abs_mul, hend]
    ring
  exact ⟨γ s, γ t, hneq, γ ∘ pointEdgeSubparam s t,
    by simp only [Function.comp_apply, pointEdgeSubparam_zero],
    by simp only [Function.comp_apply, pointEdgeSubparam_one],
    pointConformal_geodesic_continuous ha y (γ ∘ pointEdgeSubparam s t) hgeo, hgeo⟩

theorem pointConstantSpeedRestriction_range {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (γ : Icc (0 : ℝ) 1 → ℂ)
    {c : ℝ} (hc : 0 < c) (s t : Icc (0 : ℝ) 1) (hst : s < t)
    (hd : ∀ u ∈ Icc s t, ∀ v ∈ Icc s t,
      (pointSmoothConformalEDist a y (γ u) (γ v)).toReal = c * |v.1 - u.1|) :
    range (pointConstantSpeedRestriction ha y γ hc s t hst hd).curve = γ '' Icc s t := by
  change range (γ ∘ pointEdgeSubparam s t) = _
  rw [range_comp, pointEdgeSubparam_range hst]

end RepulsiveCoulomb
