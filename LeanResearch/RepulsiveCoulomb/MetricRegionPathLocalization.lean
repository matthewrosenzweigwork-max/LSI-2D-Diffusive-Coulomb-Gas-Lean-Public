import LeanResearch.RepulsiveCoulomb.MetricRegionPathDistance

/-! An exact exit-cost localization of the constrained path metric. A supplied
short actual path in a closed metric ball prevents outside excursions from
lowering the infimum. This precedes all ambient-convexity assertions. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace RepulsiveCoulomb
variable {X : Type*} [MetricSpace X]

def MetricRegionLengthPath.mono {P Q : Set X} (hPQ : P ⊆ Q) {x z : X}
    (γ : MetricRegionLengthPath P x z) : MetricRegionLengthPath Q x z where
  toFun := γ.toFun
  continuous := γ.continuous
  source := γ.source
  target := γ.target
  mapsTo := fun t ht ↦ hPQ (γ.mapsTo ht)

theorem metricRegionPathEDist_antitone {P Q : Set X} (hPQ : P ⊆ Q) (x z : X) :
    metricRegionPathEDist Q x z ≤ metricRegionPathEDist P x z := by
  apply le_iInf
  intro γ
  exact metricRegionPathEDist_le_length (γ.mono hPQ)

theorem metricRegionPathEDist_closedBall_localization {P : Set X} (p x z : X) (R : ℝ)
    (η : MetricRegionLengthPath (P ∩ closedBall p R) x z)
    (hη : η.length ≤ ENNReal.ofReal (R - dist x p)) :
    metricRegionPathEDist P x z = metricRegionPathEDist (P ∩ closedBall p R) x z := by
  apply le_antisymm (metricRegionPathEDist_antitone inter_subset_left x z)
  apply le_iInf
  intro γ
  by_cases hstay : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ closedBall p R
  · let γ' : MetricRegionLengthPath (P ∩ closedBall p R) x z :=
      ⟨γ.toFun, γ.continuous, γ.source, γ.target, fun t ht ↦ ⟨γ.mapsTo ht, hstay t ht⟩⟩
    exact metricRegionPathEDist_le_length γ'
  · push_neg at hstay
    obtain ⟨t, ht, hout⟩ := hstay
    have hfar : R < dist (γ.toFun t) p := not_le.mp hout
    have htri := dist_triangle (γ.toFun t) x p
    have hcost : ENNReal.ofReal (R - dist x p) ≤ edist x (γ.toFun t) := by
      rw [edist_dist]
      apply ENNReal.ofReal_le_ofReal
      rw [dist_comm x (γ.toFun t)]
      linarith
    have hsub : edist x (γ.toFun t) ≤ γ.length := by
      simpa only [MetricRegionLengthPath.length, γ.source] using eVariationOn.edist_le γ.toFun
        (by norm_num : (0 : ℝ) ∈ Icc 0 1) ht
    exact (metricRegionPathEDist_le_length η).trans (hη.trans (hcost.trans hsub))

end RepulsiveCoulomb
