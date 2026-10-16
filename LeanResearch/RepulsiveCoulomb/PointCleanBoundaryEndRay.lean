import LeanResearch.RepulsiveCoulomb.PointFlatBoundaryClockArc
import LeanResearch.RepulsiveCoulomb.PointUnmarkedBoundaryLine

/-! SOURCE-ONLY, UNCOMPILED. Convert an actual clean topological boundary end
into a complete ambient minimizing ray. The initial point may be a corner;
only strictly positive clock points are flattened in the proof. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- Genuine retained charts and a clean topological end construct all metric
properties. The old clock need not be rectifiable, Lipschitz, or unit speed. -/
theorem point_exists_clean_boundary_end_metric_ray
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (hP : IsClosed P) {ν α : ℂ →₀ ℝ}
    (hboundary : ∀ p ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P p,
      ν p = Real.pi - C.flatPhysicalWidth)
    (β : ℝ → ℂ) (hβ : IsClosedEmbedding β) (hfront : range β = frontier P)
    (hclean : ∀ t : ℝ, 0 < t → ν (β t) = 0 ∧ α (β t) = 0) :
    ∃ ρ : NNReal → ℂ,
      (∀ s t, (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t) ∧
      ρ 0 = β 0 ∧ range ρ = β '' Ici (0 : ℝ) ∧
      IsClosedEmbedding ρ ∧ IsProperMap ρ ∧
      (∀ t, ρ t ∈ frontier P) ∧
      (∀ t : NNReal, 0 < t → ν (ρ t) = 0 ∧ α (ρ t) = 0) ∧
      Disjoint ((↑(pointSignedMarked ν α) : Set ℂ) \ {ρ 0}) (range ρ) := by
  have hflat (t : ℝ) (ht : 0 < t) :
      ∃ C : PointRetainedConeNeighborhood a y P (β t), C.flatPhysicalWidth = Real.pi := by
    obtain ⟨C, hC⟩ := hboundary (β t) (hfront ▸ mem_range_self t)
    rw [(hclean t ht).1] at hC
    exact ⟨C, by linarith⟩
  have hβ' : @IsClosedEmbedding ℝ ℂ _
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace β := by
    rwa [pointSmoothConformalMetricSpace_topology ha y]
  have hadd : ∀ s t u : ℝ, 0 < s → s ≤ t → t ≤ u →
      @dist ℂ (pointSmoothConformalMetricSpace ha y).toDist (β s) (β u) =
        @dist ℂ (pointSmoothConformalMetricSpace ha y).toDist (β s) (β t) +
        @dist ℂ (pointSmoothConformalMetricSpace ha y).toDist (β t) (β u) := by
    intro s t u hs hst htu
    have hsu : s ≤ u := hst.trans htu
    have hconv := pointFlatBoundaryClockArc_geodesicallyConvex ha y hP β hβ hfront hsu
      (fun v hv ↦ hflat v (hs.trans_le hv.1))
    obtain ⟨γ, h0, h1, hc, hγarc, hd⟩ := hconv (β s) ⟨s, ⟨le_rfl, hsu⟩, rfl⟩
      (β u) ⟨u, ⟨hsu, le_rfl⟩, rfl⟩
    have hc' : @Continuous unitInterval ℂ _
        (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace γ := by
      rwa [pointSmoothConformalMetricSpace_topology ha y]
    have hrange : range γ ⊆ range β := by
      rintro x ⟨v, rfl⟩
      obtain ⟨q, _, hq⟩ := hγarc v
      exact ⟨q, hq⟩
    have hβi' : @IsEmbedding ℝ ℂ _
        (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace β := by
      rw [pointSmoothConformalMetricSpace_topology ha y]
      exact hβ.isEmbedding
    exact @ProperBoundaryEndClock.dist_additive_of_one_contained_segment ℂ
      (pointSmoothConformalMetricSpace ha y) β hβi' s t u hst htu
      γ hc' h0 h1 hrange (fun v w ↦ by
        change (pointSmoothConformalEDist a y (γ v) (γ w)).toReal =
          |(v : ℝ) - (w : ℝ)| * (pointSmoothConformalEDist a y (β s) (β u)).toReal
        rw [abs_sub_comm]
        exact hd v w)
  obtain ⟨ρ, hρ, hρ0, hrange, _⟩ :=
    @ProperBoundaryEndClock.exists_isometry_of_positive_additivity ℂ
      (pointSmoothConformalMetricSpace ha y) (pointSmoothConformalMetricSpace_proper ha y)
      β hβ' hadd
  have hd : ∀ s t, (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t :=
    @Isometry.dist_eq NNReal ℂ _ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace ρ hρ
  have he := pointMetricRay_isClosedEmbedding ha y ρ hd
  have hzerooff : ∀ x ∈ range ρ, x ≠ ρ 0 → ν x = 0 ∧ α x = 0 := by
    intro x hx hne
    obtain ⟨t, ht, rfl⟩ := hrange ▸ hx
    have htne : t ≠ 0 := fun heq ↦ hne (by rw [heq, hρ0])
    exact hclean t (lt_of_le_of_ne ht (Ne.symm htne))
  refine ⟨ρ, hd, hρ0, hrange, he, he.isProperMap, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨u, _, hu⟩ := hrange ▸ mem_range_self t
    rw [← hu, ← hfront]
    exact mem_range_self u
  · intro t ht
    exact hzerooff (ρ t) (mem_range_self t) (he.injective.ne (ne_of_gt ht))
  · apply disjoint_left.mpr
    intro x hx hr
    have hz := hzerooff x hr (by simpa only [mem_singleton_iff] using hx.2)
    rcases (mem_pointSignedMarked ν α x).mp hx.1 with hν | hα
    · exact hν hz.1
    · exact hα hz.2

end RepulsiveCoulomb
