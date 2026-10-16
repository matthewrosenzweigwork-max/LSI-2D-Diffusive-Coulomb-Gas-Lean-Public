import LeanResearch.RepulsiveCoulomb.DevelopedPathMetricLocalIsometry
import LeanResearch.RepulsiveCoulomb.PointConformalGeodesic
import LeanResearch.RepulsiveCoulomb.PointRectifiableConformalMetric

/-!
SOURCE-ONLY, UNCOMPILED. Conditional assembly boundary for the ACTUAL finite
surgery. Local chart data are sufficient; new-metric completeness, properness,
minimizing segments, local/global distance preservation, injectivity and
surjectivity are not hypotheses. The final actual finite-sector chart producer
is still pending and is not asserted here.
-/
noncomputable section
open Set Filter
open scoped ENNReal NNReal Topology
namespace RepulsiveCoulomb

/-- Genuine locally rigid charts with local c/1 metric estimates yield a
continuous open bijective global development with the same sharp constants. -/
theorem exists_bijective_development_of_locally_bilipschitz_atlas
    {X : Type*} [MetricSpace X] [ProperSpace X] [SimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] (x₀ : X)
    (hsegment : HasMinimizingSegments X) (c : ℝ≥0) (hc : 0 < c)
    (C : X → OpenPartialHomeomorph X ℂ) (hC : ∀ x, x ∈ (C x).source)
    (hrigid : ∀ i j x, x ∈ (C i).source ∩ (C j).source →
      ∃ e : ℂ ≃ᵢ ℂ, (C i : X → ℂ) =ᶠ[𝓝 x] (fun y ↦ e (C j y)))
    (hmetric : ∀ x, ∀ u ∈ (C x).source, ∀ v ∈ (C x).source,
      (c : ℝ) * dist u v ≤ dist (C x u) (C x v) ∧
        dist (C x u) (C x v) ≤ dist u v) :
    ∃ D : X → ℂ, Continuous D ∧ IsOpenMap D ∧ Function.Bijective D ∧
      (∀ x, ∃ e : ℂ ≃ᵢ ℂ, D =ᶠ[𝓝 x] (fun y ↦ e (C x y))) ∧
      (∀ x z, developedPathEDist D x z = edist (D x) (D z)) ∧
      ∀ x z, (c : ℝ) * dist x z ≤ dist (D x) (D z) ∧
        dist (D x) (D z) ≤ dist x z := by
  letI : Nonempty X := ⟨x₀⟩
  obtain ⟨D, hD, hopen, hformula⟩ :=
    exists_development_of_localRigidOverlaps C hC hrigid x₀
  have hlocal : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ u ∈ U, ∀ v ∈ U, (c : ℝ) * dist u v ≤ dist (D u) (D v) ∧
        dist (D u) (D v) ≤ dist u v := by
    intro x
    obtain ⟨e, he⟩ := hformula x
    obtain ⟨U, hUeq, hUopen, hxU⟩ := mem_nhds_iff.mp he
    refine ⟨U ∩ (C x).source, hUopen.inter (C x).open_source, ⟨hxU, hC x⟩, ?_⟩
    intro u hu v hv
    rw [hUeq hu.1, hUeq hv.1, e.dist_eq]
    exact hmetric x u hu.2 v hv.2
  have hlower : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ u ∈ U, ∀ v ∈ U, (c : ℝ≥0∞) * edist u v ≤ edist (D u) (D v) := by
    intro x
    obtain ⟨U, ho, hx, hb⟩ := hlocal x
    refine ⟨U, ho, hx, fun u hu v hv ↦ ?_⟩
    have h := ENNReal.ofReal_le_ofReal (hb u hu v hv).1
    simpa only [ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal,
      ← edist_dist] using h
  have hupper : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ u ∈ U, ∀ v ∈ U, dist (D u) (D v) ≤ dist u v := by
    intro x
    obtain ⟨U, ho, hx, hb⟩ := hlocal x
    exact ⟨U, ho, hx, fun u hu v hv ↦ (hb u hu v hv).2⟩
  obtain ⟨hbij, heq, hbounds⟩ := developedPathMetricSpace_isometry_bijective
    D hD hopen c hc hsegment hlower hupper C hC hformula
  exact ⟨D, hD, hopen, hbij, hformula, heq, hbounds⟩

/-- Original conformal geometry supplies the minimizing-path premise; the
continuity is transported using the proved old-metric topology equality. -/
theorem pointSmoothConformalMetricSpace_hasMinimizingSegments
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    @HasMinimizingSegments ℂ (pointSmoothConformalMetricSpace ha y) := by
  intro x z
  obtain ⟨γ, h0, h1, hc, hd⟩ := exists_pointConformal_geodesic ha y x z
  refine ⟨γ, h0, h1, ?_, hd⟩
  change @Continuous (Icc (0 : ℝ) 1) ℂ _
    (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace γ
  rwa [pointSmoothConformalMetricSpace_topology]

/-- An original-input interface awaiting only the actual finite-sector atlas.
Charts are stated in the old conformal metric topology, which the selected
sources already prove equal to the ordinary Euclidean topology. No assumption
about a new metric, its completeness, or a global developing map is added. -/
theorem exists_pointRectifiable_bijective_development_of_actual_atlas
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ≥0) (hc : 0 < c)
    (C : ℂ → @OpenPartialHomeomorph ℂ ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace inferInstance)
    (hC : ∀ x, x ∈ (C x).source)
    (hrigid : ∀ i j x, x ∈ (C i).source ∩ (C j).source →
      ∃ e : ℂ ≃ᵢ ℂ,
        @Filter.EventuallyEq ℂ ℂ
          (@nhds ℂ (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace x)
          (C i : ℂ → ℂ) (fun z ↦ e (C j z)))
    (hmetric : ∀ x, ∀ u ∈ (C x).source, ∀ v ∈ (C x).source,
      (c : ℝ) * (pointSmoothConformalEDist a y u v).toReal ≤ dist (C x u) (C x v) ∧
        dist (C x u) (C x v) ≤ (pointSmoothConformalEDist a y u v).toReal) :
    ∃ D : ℂ → ℂ, Continuous D ∧ IsOpenMap D ∧ Function.Bijective D ∧
      ∀ x z, (c : ℝ) * (pointRectifiableConformalEDist a y x z).toReal ≤ dist (D x) (D z) ∧
        dist (D x) (D z) ≤ (pointRectifiableConformalEDist a y x z).toReal := by
  let euclideanMetric : MetricSpace ℂ := inferInstance
  let old := pointSmoothConformalMetricSpace ha y
  letI : MetricSpace ℂ := euclideanMetric
  have hproper := pointSmoothConformalMetricSpace_proper ha y
  have hsimply : @SimplyConnectedSpace ℂ old.toUniformSpace.toTopologicalSpace := by
    change @SimplyConnectedSpace ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace
    rw [pointSmoothConformalMetricSpace_topology]
    infer_instance
  have hlocally : @LocallyPathConnectedSpace ℂ old.toUniformSpace.toTopologicalSpace := by
    change @LocallyPathConnectedSpace ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace
    rw [pointSmoothConformalMetricSpace_topology]
    infer_instance
  obtain ⟨D, hD, hopen, hbij, _, _, hb⟩ :=
    @exists_bijective_development_of_locally_bilipschitz_atlas ℂ old hproper hsimply hlocally
      0 (pointSmoothConformalMetricSpace_hasMinimizingSegments ha y) c hc C hC hrigid hmetric
  have hD' : Continuous D := by
    change @Continuous ℂ ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace inferInstance D at hD
    rwa [pointSmoothConformalMetricSpace_topology] at hD
  have hopen' : IsOpenMap D := by
    change @IsOpenMap ℂ ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace inferInstance D at hopen
    rwa [pointSmoothConformalMetricSpace_topology] at hopen
  refine ⟨D, hD', hopen', hbij, fun x z ↦ ?_⟩
  simpa only [pointRectifiableConformalEDist_eq_smooth ha y,
    pointSmoothConformalMetricSpace_dist] using hb x z

end RepulsiveCoulomb
