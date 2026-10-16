module

public import LeanResearch.RepulsiveCoulomb.FiniteClosedContactComponents
public import LeanResearch.RepulsiveCoulomb.PointActualGeodesicUniqueness
public import LeanResearch.RepulsiveCoulomb.PointRetainedIntrinsicAmbientConvexity
public import LeanResearch.RepulsiveCoulomb.PointLineCapJordan

@[expose] public section

/-! Source-only draft. Old boundary pieces are actual isometrically parametrized
closed real intervals, not a claim that the whole boundary is geodesic. Closed
segments, half-lines and complete lines are all permitted. A finite union can
have positive-turn corners. All contact connectedness below is proved using
the accepted actual fixed-endpoint uniqueness theorem. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- Geometric input for a single old boundary piece. No cap, side, angle,
intersection-connectedness, or residual-set assertion is a field. -/
structure PointClosedBoundaryGeodesicPiece {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) where
  interval : Set ℝ
  interval_closed : IsClosed interval
  interval_convex : Convex ℝ interval
  curve : interval → ℂ
  metric : ∀ s t, (pointSmoothConformalEDist a y (curve s) (curve t)).toReal = dist s t

namespace PointClosedBoundaryGeodesicPiece

/-- Closed embeddedness of a supplied geodesic parameter interval is a conclusion
of its actual isometry and completeness, not an extra topological certificate. -/
theorem closedEmbedding {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j)
    (y : Fin m → ℂ) (E : PointClosedBoundaryGeodesicPiece a y) :
    IsClosedEmbedding E.curve := by
  letI : CompleteSpace E.interval := E.interval_closed.isComplete.completeSpace_coe
  have hi := @Isometry.of_dist_eq E.interval ℂ inferInstance
    (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace E.curve E.metric
  have hc := @Isometry.isClosedEmbedding E.interval ℂ
    (inferInstance : EMetricSpace E.interval)
    (inferInstance : CompleteSpace E.interval)
    (pointSmoothConformalMetricSpace ha y).toEMetricSpace E.curve hi
  change @IsClosedEmbedding E.interval ℂ _
    (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace E.curve at hc
  rwa [pointSmoothConformalMetricSpace_topology ha y] at hc

/-- Affine restriction of the actual old piece gives contained minimizing
segments, even if the containing boundary has corners elsewhere. -/
theorem geodesicallyConvex {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j)
    (y : Fin m → ℂ) (E : PointClosedBoundaryGeodesicPiece a y) :
    PointGeodesicallyConvex a y (range E.curve) := by
  rintro p ⟨s, rfl⟩ q ⟨t, rfl⟩
  let τ : unitInterval → E.interval := fun u =>
    ⟨(1 - u.1) * s.1 + u.1 * t.1,
      E.interval_convex s.2 t.2 (sub_nonneg.mpr u.2.2) u.2.1 (by ring)⟩
  let γ : unitInterval → ℂ := E.curve ∘ τ
  have h0 : γ 0 = E.curve s := by simp [γ, τ]
  have h1 : γ 1 = E.curve t := by simp [γ, τ]
  have hd : ∀ u v, (pointSmoothConformalEDist a y (γ u) (γ v)).toReal =
      |v.1 - u.1| * (pointSmoothConformalEDist a y (E.curve s) (E.curve t)).toReal := by
    intro u v
    change (pointSmoothConformalEDist a y (E.curve (τ u)) (E.curve (τ v))).toReal = _
    rw [E.metric, E.metric]
    change |((1 - u.1) * s.1 + u.1 * t.1) - ((1 - v.1) * s.1 + v.1 * t.1)| =
      |v.1 - u.1| * |s.1 - t.1|
    rw [show ((1 - u.1) * s.1 + u.1 * t.1) - ((1 - v.1) * s.1 + v.1 * t.1) =
      (v.1 - u.1) * (s.1 - t.1) by ring, abs_mul]
  exact ⟨γ, h0, h1, pointConformal_geodesic_continuous ha y γ hd,
    fun u => mem_range_self (τ u), hd⟩

end PointClosedBoundaryGeodesicPiece

/-- Local-on-an-interval variant of the accepted line restriction metric lemma.
It deliberately does not extend a ray to a fictitious isometric full line. -/
theorem lineCapSegment_metricOn {m : ℕ} {a : Fin m → ℝ} (y : Fin m → ℂ)
    (r : ℝ → ℂ) {s t : ℝ} (hst : s ≤ t)
    (hd : ∀ u ∈ Icc s t, ∀ v ∈ Icc s t,
      (pointSmoothConformalEDist a y (r u) (r v)).toReal = dist u v) :
    ∀ u v, (pointSmoothConformalEDist a y (lineCapSegment r s t u)
      (lineCapSegment r s t v)).toReal =
      |v.1 - u.1| * (pointSmoothConformalEDist a y (r s) (r t)).toReal := by
  have hmem (u : unitInterval) : s + u.1 * (t - s) ∈ Icc s t := by
    have hlow := mul_nonneg u.2.1 (sub_nonneg.mpr hst)
    have hhigh := mul_le_mul_of_nonneg_right u.2.2 (sub_nonneg.mpr hst)
    constructor <;> nlinarith
  intro u v
  rw [lineCapSegment, lineCapSegment, hd _ (hmem u) _ (hmem v),
    hd s ⟨le_rfl, hst⟩ t ⟨hst, le_rfl⟩, Real.dist_eq, Real.dist_eq,
    show s + u.1 * (t - s) - (s + v.1 * (t - s)) = (u.1 - v.1) * (t - s) by ring,
    abs_mul, abs_sub_comm u.1 v.1, abs_sub_comm t s]

/-- An actual minimizing ray cannot leave and then return to the same actual
geodesic piece. The unique segment between the two contacts lies on both. -/
theorem pointMetricRay_contact_ordConnected {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (r : ℝ → ℂ)
    (hd : ∀ s ∈ Ici (0 : ℝ), ∀ t ∈ Ici (0 : ℝ),
      (pointSmoothConformalEDist a y (r s) (r t)).toReal = dist s t)
    {K : Set ℂ} (hK : PointGeodesicallyConvex a y K) :
    OrdConnected (Ici (0 : ℝ) ∩ r ⁻¹' K) := by
  refine ⟨?_⟩
  intro s hs t ht u hu
  refine ⟨hs.1.trans hu.1, ?_⟩
  rcases eq_or_lt_of_le (hu.1.trans hu.2) with heq | hst
  · have hue : u = s := le_antisymm (hu.2.trans heq.ge) hu.1
    exact hue.symm ▸ hs.2
  · let γ := lineCapSegment r s t
    have hγ := lineCapSegment_metricOn y r hst.le (fun v hv w hw =>
      hd v (hs.1.trans hv.1) w (hs.1.trans hw.1))
    obtain ⟨η, hη0, hη1, hηc, hηK, hηd⟩ := hK (r s) hs.2 (r t) ht.2
    have heq : γ = η := pointConformal_geodesic_unique ha y (r s) (r t) γ η
      (lineCapSegment_zero r s t) (lineCapSegment_one r s t) hη0 hη1 hγ hηd
    have hru : r u ∈ range γ := by
      rw [lineCapSegment_range r hst]
      exact ⟨u, hu, rfl⟩
    obtain ⟨v, hv⟩ := hru
    change r u ∈ K
    rw [← hv, heq]
    exact hηK v

/-- The actual ray/boundary contact times are a finite union of closed
order-connected sets, one for each old geodesic piece. -/
theorem pointMetricRay_finite_boundary_contacts {m n : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {P : Set ℂ}
    (E : Fin n → PointClosedBoundaryGeodesicPiece a y)
    (hcover : frontier P = ⋃ i, range (E i).curve)
    (r : ℝ → ℂ) (hr : Continuous r)
    (hd : ∀ s ∈ Ici (0 : ℝ), ∀ t ∈ Ici (0 : ℝ),
      (pointSmoothConformalEDist a y (r s) (r t)).toReal = dist s t) :
    ∃ J : Fin n → Set ℝ, (∀ i, IsClosed (J i)) ∧ (∀ i, OrdConnected (J i)) ∧
      Ici (0 : ℝ) ∩ r ⁻¹' frontier P = ⋃ i, J i := by
  let J : Fin n → Set ℝ := fun i => Ici (0 : ℝ) ∩ r ⁻¹' range (E i).curve
  refine ⟨J, ?_, ?_, ?_⟩
  · intro i
    exact isClosed_Ici.inter (((E i).closedEmbedding ha y).isClosed_range.preimage hr)
  · intro i
    exact pointMetricRay_contact_ordConnected ha y r hd ((E i).geodesicallyConvex ha y)
  · rw [hcover, preimage_iUnion, inter_iUnion]

/-- Full first-later-contact endpoint from finite actual old boundary pieces.
The hypotheses identify a terminal contact point and a later contact, but do
not assume the positive time gap, least point, or open-ray avoidance. -/
theorem exists_pointMetricRay_first_later_boundary_contact {m n : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {P : Set ℂ}
    (E : Fin n → PointClosedBoundaryGeodesicPiece a y)
    (hcover : frontier P = ⋃ i, range (E i).curve)
    (r : ℝ → ℂ) (hr : Continuous r)
    (hd : ∀ s ∈ Ici (0 : ℝ), ∀ t ∈ Ici (0 : ℝ),
      (pointSmoothConformalEDist a y (r s) (r t)).toReal = dist s t)
    {z : ℝ} (hz0 : 0 ≤ z)
    (hterminal : ∀ t, z < t → ¬ Icc z t ⊆ r ⁻¹' frontier P)
    (hlater : ∃ t, z < t ∧ r t ∈ frontier P) :
    ∃ w, z < w ∧ r w ∈ frontier P ∧
      (∀ t, z < t → r t ∈ frontier P → w ≤ t) ∧
      ∀ t ∈ Ioo z w, r t ∉ frontier P := by
  obtain ⟨J, hclosed, hinterval, hJ⟩ :=
    pointMetricRay_finite_boundary_contacts ha y E hcover r hr hd
  have hterm : ∀ t, z < t → ¬ Icc z t ⊆ ⋃ i, J i := by
    intro t hzt hsub
    apply hterminal t hzt
    intro u hu
    have hm := hsub hu
    rw [← hJ] at hm
    exact hm.2
  have hne : ((⋃ i, J i) ∩ Ioi z).Nonempty := by
    obtain ⟨t, hzt, ht⟩ := hlater
    refine ⟨t, ?_, hzt⟩
    rw [← hJ]
    exact ⟨hz0.trans hzt.le, ht⟩
  obtain ⟨w, hzw, hw, hleast, hgap⟩ :=
    exists_first_later_finite_closed_contact J hclosed hinterval hterm hne
  have hwb : r w ∈ frontier P := by rw [← hJ] at hw; exact hw.2
  refine ⟨w, hzw, hwb, ?_, ?_⟩
  · intro t hzt ht
    apply hleast.2
    refine ⟨?_, hzt⟩
    rw [← hJ]
    exact ⟨hz0.trans hzt.le, ht⟩
  · intro t ht htb
    apply hgap t ht
    rw [← hJ]
    exact ⟨hz0.trans ht.1.le, htb⟩

/-- Intrinsic old-edge data in an actual admissible retained region can be
converted to the ambient piece input. The full boundary is never asserted
geodesic: apply this separately to its finitely many actual pieces. -/
theorem pointRetained_intrinsic_piece_metric_ambient {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {P : Set ℂ}
    (hP : IsClosed P) (hconn : IsPreconnected P)
    (hcharts : ∀ p ∈ P, ∃ C : PointRetainedConeNeighborhood a y P p, C.Full ∨ C.Admissible)
    {I : Set ℝ} (f : I → P)
    (hf : ∀ s t, (pointRegionIntrinsicEDist ha y P (f s).1 (f t).1).toReal = dist s t) :
    ∀ s t, (pointSmoothConformalEDist a y (f s).1 (f t).1).toReal = dist s t := by
  have heq := (pointRetainedRegion_intrinsic_eq_and_geodesicallyConvex ha y hP hconn hcharts).2
  intro s t
  rw [← heq _ (f s).2 _ (f t).2]
  exact hf s t

end RepulsiveCoulomb
