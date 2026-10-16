import LeanResearch.RepulsiveCoulomb.PointMetricLineSideGeodesic
import LeanResearch.RepulsiveCoulomb.PointConformalIntrinsicLength
import Mathlib.Topology.Order.ProjIcc

/-! The actual intrinsic metric of a closed line side. The infimum runs over
all continuous curves in the actual subset and uses genuine metric variation.
Contained minimizing paths prove equality with the ambient restriction; this
equality is not assumed. Properness, completeness and the ordinary subspace
topology are then transported to this identified intrinsic metric. -/
noncomputable section
open Set Topology
open scoped ENNReal
namespace RepulsiveCoulomb

/-- Actual constrained continuous-curve path distance. -/
def pointRegionIntrinsicEDist {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (P : Set ℂ) (x z : ℂ) : ℝ≥0∞ :=
  ⨅ γ : {γ : ℝ → ℂ // γ 0 = x ∧ γ 1 = z ∧ ContinuousOn γ (Icc (0 : ℝ) 1) ∧
      MapsTo γ (Icc (0 : ℝ) 1) P}, pointConformalMetricLength ha y γ.1 0 1

/-- The genuine variation length of any constant-speed minimizing interval
curve is its endpoint distance. -/
theorem pointConformalMetricLength_of_geodesic {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (γ : ℝ → ℂ)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
        |t - s| * (pointSmoothConformalEDist a y (γ 0) (γ 1)).toReal) :
    pointConformalMetricLength ha y γ 0 1 = pointSmoothConformalEDist a y (γ 0) (γ 1) := by
  have hbound {E : Type} [PseudoMetricSpace E] (f : ℝ → E) (C : NNReal)
      (hf : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (f s) (f t) ≤ (C : ℝ) * dist s t) :
      eVariationOn f (Icc (0 : ℝ) 1) ≤ (C : ℝ≥0∞) := by
    have hLip : LipschitzOnWith C f (Icc (0 : ℝ) 1) :=
      LipschitzOnWith.of_dist_le_mul hf
    have hvar := hLip.comp_eVariationOn_le (g := id) (s := Icc (0 : ℝ) 1)
      (fun t ht ↦ ht)
    simpa only [Function.comp_id, eVariationOn_id_Icc, sub_zero, ENNReal.ofReal_one, mul_one]
      using hvar
  let K := (pointSmoothConformalEDist a y (γ 0) (γ 1)).toNNReal
  have hK : (K : ℝ≥0∞) = pointSmoothConformalEDist a y (γ 0) (γ 1) :=
    ENNReal.coe_toNNReal (pointSmoothConformalEDist_lt_top ha y _ _).ne
  have hKr : (K : ℝ) = (pointSmoothConformalEDist a y (γ 0) (γ 1)).toReal := by
    simpa only [ENNReal.coe_toReal] using congrArg ENNReal.toReal hK
  have hupper := @hbound ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace γ K
    (by
      intro s hs t ht
      change (pointSmoothConformalEDist a y (γ s) (γ t)).toReal ≤ (K : ℝ) * dist s t
      rw [hKr, hd s hs t ht, Real.dist_eq, abs_sub_comm, mul_comm])
  change pointConformalMetricLength ha y γ 0 1 ≤ (K : ℝ≥0∞) at hupper
  exact le_antisymm (hupper.trans_eq hK)
    (pointConformalMetricLength_endpoint_le ha y γ (by norm_num))

/-- Every contained minimizing interval gives an actual continuous real-line
representative of the same length, with the same constrained image. -/
theorem exists_pointRegion_minimizing_path {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {P : Set ℂ}
    (hP : PointGeodesicallyConvex a y P) {x z : ℂ} (hx : x ∈ P) (hz : z ∈ P) :
    ∃ γ : ℝ → ℂ, γ 0 = x ∧ γ 1 = z ∧ ContinuousOn γ (Icc (0 : ℝ) 1) ∧
      MapsTo γ (Icc (0 : ℝ) 1) P ∧
      pointConformalMetricLength ha y γ 0 1 = pointSmoothConformalEDist a y x z := by
  obtain ⟨η, h0, h1, hc, hηP, hd⟩ := hP x hx z hz
  let γ := IccExtend (show (0 : ℝ) ≤ 1 by norm_num) η
  have hγc : Continuous γ := continuous_IccExtend_iff.mpr hc
  have hγ0 : γ 0 = x := (IccExtend_of_mem _ _ (by norm_num)).trans h0
  have hγ1 : γ 1 = z := (IccExtend_of_mem _ _ (by norm_num)).trans h1
  have hγ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t = η ⟨t, ht⟩ :=
    IccExtend_of_mem _ _ ht
  have hγP : MapsTo γ (Icc (0 : ℝ) 1) P := by
    intro t ht
    rw [hγ t ht]
    exact hηP ⟨t, ht⟩
  refine ⟨γ, hγ0, hγ1, hγc.continuousOn, hγP, ?_⟩
  rw [← hγ0, ← hγ1]
  apply pointConformalMetricLength_of_geodesic ha y
  intro s hs t ht
  rw [hγ0, hγ1, hγ s hs, hγ t ht]
  exact hd ⟨s, hs⟩ ⟨t, ht⟩

/-- The infimum over actual paths in the region equals ambient distance,
because a path attaining that distance has been constructed in the region. -/
theorem pointRegionIntrinsicEDist_eq_ambient {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {P : Set ℂ}
    (hP : PointGeodesicallyConvex a y P) {x z : ℂ} (hx : x ∈ P) (hz : z ∈ P) :
    pointRegionIntrinsicEDist ha y P x z = pointSmoothConformalEDist a y x z := by
  apply le_antisymm
  · obtain ⟨γ, h0, h1, hc, hγP, hlen⟩ := exists_pointRegion_minimizing_path ha y hP hx hz
    exact (iInf_le _ ⟨γ, h0, h1, hc, hγP⟩).trans_eq hlen
  · apply le_iInf
    intro γ
    have h := pointConformalMetricLength_endpoint_le ha y γ.1 (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [γ.2.1, γ.2.2.1] using h

/-- A concrete metric on the actual region. The preceding theorem identifies
it with the constrained path metric whenever contained minimizers exist. -/
def pointRegionMetricSpace {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (P : Set ℂ) : MetricSpace P :=
  MetricSpace.induced Subtype.val Subtype.val_injective (pointSmoothConformalMetricSpace ha y)

theorem pointRegionMetricSpace_intrinsic_edist {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {P : Set ℂ}
    (hP : PointGeodesicallyConvex a y P) (x z : P) :
    @edist P (pointRegionMetricSpace ha y P).toEDist x z =
      pointRegionIntrinsicEDist ha y P x.1 z.1 := by
  rw [pointRegionIntrinsicEDist_eq_ambient ha y hP x.2 z.2]
  rfl

theorem pointRegionMetricSpace_topology {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (P : Set ℂ) :
    (pointRegionMetricSpace ha y P).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace P) := by
  change TopologicalSpace.induced Subtype.val
    (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace =
      TopologicalSpace.induced Subtype.val (inferInstance : TopologicalSpace ℂ)
  rw [pointSmoothConformalMetricSpace_topology ha y]

theorem pointRegionMetricSpace_proper {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {P : Set ℂ} (hP : IsClosed P) :
    @ProperSpace P (pointRegionMetricSpace ha y P).toPseudoMetricSpace := by
  have hP' : @IsClosed ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace P := by
    rwa [pointSmoothConformalMetricSpace_topology ha y]
  exact @ProperSpace.of_isClosed ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace
    (pointSmoothConformalMetricSpace_proper ha y) P hP'

theorem pointRegionMetricSpace_complete {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {P : Set ℂ} (hP : IsClosed P) :
    @CompleteSpace P (pointRegionMetricSpace ha y P).toUniformSpace := by
  exact @complete_of_proper P (pointRegionMetricSpace ha y P).toPseudoMetricSpace
    (pointRegionMetricSpace_proper ha y hP)


/-- Construct both actual side metrics and prove their intrinsic distance,
ordinary subspace topology, properness, completeness and attained minimizing
path length together. No side set or polyhedral certificate is an input. -/
theorem exists_pointMetricLine_intrinsic_closed_sides {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (ℓ : ℝ → ℂ)
    (hℓ : ∀ s t, (pointSmoothConformalEDist a y (ℓ s) (ℓ t)).toReal = dist s t) :
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = (range ℓ)ᶜ ∧ frontier U = range ℓ ∧ frontier V = range ℓ ∧
      ∀ P : Set ℂ, (P = closure U ∨ P = closure V) →
        (∀ x ∈ P, ∀ z ∈ P, pointRegionIntrinsicEDist ha y P x z =
          pointSmoothConformalEDist a y x z) ∧
        (pointRegionMetricSpace ha y P).toUniformSpace.toTopologicalSpace =
          (inferInstance : TopologicalSpace P) ∧
        @ProperSpace P (pointRegionMetricSpace ha y P).toPseudoMetricSpace ∧
        @CompleteSpace P (pointRegionMetricSpace ha y P).toUniformSpace ∧
        ∀ x ∈ P, ∀ z ∈ P, ∃ γ : ℝ → ℂ,
          γ 0 = x ∧ γ 1 = z ∧ ContinuousOn γ (Icc (0 : ℝ) 1) ∧
          MapsTo γ (Icc (0 : ℝ) 1) P ∧
          pointConformalMetricLength ha y γ 0 1 = pointSmoothConformalEDist a y x z := by
  obtain ⟨U, V, hU, hV, hUc, hVc, hUV, hcover, hfu, hfv, hUP, hVP⟩ :=
    exists_pointMetricLine_intrinsically_geodesic_sides ha y ℓ hℓ
  refine ⟨U, V, hU, hV, hUc, hVc, hUV, hcover, hfu, hfv, ?_⟩
  intro P hP
  have hclosed : IsClosed P := by
    rcases hP with rfl | rfl <;> exact isClosed_closure
  have hgeod : PointGeodesicallyConvex a y P := by
    rcases hP with rfl | rfl
    · exact hUP
    · exact hVP
  exact ⟨fun x hx z hz ↦ pointRegionIntrinsicEDist_eq_ambient ha y hgeod hx hz,
    pointRegionMetricSpace_topology ha y P, pointRegionMetricSpace_proper ha y hclosed,
    pointRegionMetricSpace_complete ha y hclosed,
    fun x hx z hz ↦ exists_pointRegion_minimizing_path ha y hgeod hx hz⟩

end RepulsiveCoulomb
