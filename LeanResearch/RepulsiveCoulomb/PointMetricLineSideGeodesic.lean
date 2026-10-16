import LeanResearch.RepulsiveCoulomb.PointMetricLineSideRegions
import LeanResearch.RepulsiveCoulomb.SeparatedRegionCurveHits
import LeanResearch.RepulsiveCoulomb.MetricIntervalGeodesicReplacement

/-! A minimizing curve contained in either actual closed side of a minimizing
line. An ambient minimizer's entire middle portion between its first and last
line hits is replaced by the line segment with those endpoints. This needs no
global geodesic uniqueness and no finite-crossing premise. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- Existence of actual constant-speed ambient minimizers contained in a set. -/
def PointGeodesicallyConvex {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (P : Set ℂ) : Prop :=
  ∀ x ∈ P, ∀ z ∈ P, ∃ γ : unitInterval → ℂ,
    γ 0 = x ∧ γ 1 = z ∧ Continuous γ ∧ (∀ u, γ u ∈ P) ∧
    ∀ u v, (pointSmoothConformalEDist a y (γ u) (γ v)).toReal =
      |v.1 - u.1| * (pointSmoothConformalEDist a y x z).toReal

/-- A closed side is intrinsically geodesic with exactly the ambient distance.
The replacement minimizing curve is constructed from actual first/last hits. -/
theorem pointMetricLine_closed_side_geodesicallyConvex {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (ℓ : ℝ → ℂ)
    (hℓ : ∀ s t, (pointSmoothConformalEDist a y (ℓ s) (ℓ t)).toReal = dist s t)
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcover : U ∪ V = (range ℓ)ᶜ) (hfront : frontier U = range ℓ) :
    PointGeodesicallyConvex a y (closure U) := by
  intro x hx z hz
  obtain ⟨γ, h0, h1, hc, hd⟩ := exists_pointConformal_geodesic ha y x z
  have hlineclosed : IsClosed (range ℓ) := (pointMetricLine_isClosedEmbedding ha y ℓ hℓ).isClosed_range
  have hlineP : range ℓ ⊆ closure U := hfront ▸ frontier_subset_closure
  rcases exists_first_last_boundary_hits_with_side_tails hU hV hUV hcover hfront
    hlineclosed γ hc (h0.symm ▸ hx) (h1.symm ▸ hz) with hcontained | ⟨s, t, hst, hs, ht, hleft, hright⟩
  · exact ⟨γ, h0, h1, hc, hcontained, hd⟩
  · rcases eq_or_lt_of_le hst with heq | hst'
    · refine ⟨γ, h0, h1, hc, ?_, hd⟩
      intro u
      rcases le_total u s with hu | hu
      · exact hleft u hu
      · exact hright u (heq ▸ hu)
    · obtain ⟨α, hα⟩ := hs
      obtain ⟨β, hβ⟩ := ht
      let c := (pointSmoothConformalEDist a y x z).toReal
      let D := t.1 - s.1
      have hD : 0 < D := sub_pos.mpr (show s.1 < t.1 from hst')
      have hab : |β - α| = c * D := by
        have h := hd s t
        rw [← hα, ← hβ, hℓ, Real.dist_eq,
          abs_of_nonneg (sub_nonneg.mpr (show s.1 ≤ t.1 from hst)), abs_sub_comm] at h
        exact h.trans (mul_comm _ _)
      let k := (β - α) / D
      have hk : |k| = c := by
        rw [abs_div, abs_of_pos hD, hab, mul_div_cancel_right₀ _ hD.ne']
      let δ : unitInterval → ℂ := fun u ↦ ℓ (α + k * (u.1 - s.1))
      have hδs : γ s = δ s := by
        change γ s = ℓ (α + k * (s.1 - s.1))
        rw [sub_self, mul_zero, add_zero, hα]
      have hδt : δ t = γ t := by
        change ℓ (α + ((β - α) / D) * D) = γ t
        rw [div_mul_cancel₀ _ hD.ne']
        have he : α + (β - α) = β := by ring
        rw [he, hβ]
      have hδ : ∀ u v : unitInterval, u ≤ v →
          (pointSmoothConformalEDist a y (δ u) (δ v)).toReal ≤ c * (v.1 - u.1) := by
        intro u v huv
        change (pointSmoothConformalEDist a y
          (ℓ (α + k * (u.1 - s.1))) (ℓ (α + k * (v.1 - s.1)))).toReal ≤ _
        rw [hℓ, Real.dist_eq,
          show (α + k * (u.1 - s.1)) - (α + k * (v.1 - s.1)) = k * (u.1 - v.1) by ring,
          abs_mul, hk, abs_of_nonpos (sub_nonpos.mpr (show u.1 ≤ v.1 from huv)), neg_sub]
      have hd' : ∀ u v : unitInterval,
          (pointSmoothConformalEDist a y (γ u) (γ v)).toReal = c * |v.1 - u.1| := by
        intro u v
        exact (hd u v).trans (mul_comm _ _)
      obtain ⟨η, hη0, hη1, hηleft, hηright, hηmiddle, hηd⟩ :=
        @exists_metricInterval_geodesic_replacement ℂ
          (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace c γ δ hd' hδ s t hst' hδs hδt
      have hηgeo : ∀ u v : unitInterval,
          (pointSmoothConformalEDist a y (η u) (η v)).toReal =
            |v.1 - u.1| * (pointSmoothConformalEDist a y x z).toReal := by
        intro u v
        exact (hηd u v).trans (mul_comm _ _)
      refine ⟨η, hη0.trans h0, hη1.trans h1,
        pointConformal_geodesic_continuous ha y η hηgeo, ?_, hηgeo⟩
      intro u
      by_cases hus : u ≤ s
      · rw [hηleft u hus]
        exact hleft u hus
      · by_cases htu : t ≤ u
        · rw [hηright u htu]
          exact hright u htu
        · rw [hηmiddle u (lt_of_not_ge hus).le (lt_of_not_ge htu).le]
          exact hlineP ⟨α + k * (u.1 - s.1), rfl⟩

/-- Both genuine sides, their genuine separating boundary, and contained
minimizers are obtained from the actual line with no supplied side regions. -/
theorem exists_pointMetricLine_intrinsically_geodesic_sides {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (ℓ : ℝ → ℂ)
    (hℓ : ∀ s t, (pointSmoothConformalEDist a y (ℓ s) (ℓ t)).toReal = dist s t) :
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = (range ℓ)ᶜ ∧ frontier U = range ℓ ∧ frontier V = range ℓ ∧
      PointGeodesicallyConvex a y (closure U) ∧ PointGeodesicallyConvex a y (closure V) := by
  obtain ⟨U, V, hU, hV, hUc, hVc, hUV, hcover, hfu, hfv⟩ :=
    exists_pointMetricLine_side_regions ha y ℓ hℓ
  exact ⟨U, V, hU, hV, hUc, hVc, hUV, hcover, hfu, hfv,
    pointMetricLine_closed_side_geodesicallyConvex ha y ℓ hℓ hU hV hUV hcover hfu,
    pointMetricLine_closed_side_geodesicallyConvex ha y ℓ hℓ hV hU hUV.symm
      (by simpa only [union_comm] using hcover) hfv⟩

end RepulsiveCoulomb
