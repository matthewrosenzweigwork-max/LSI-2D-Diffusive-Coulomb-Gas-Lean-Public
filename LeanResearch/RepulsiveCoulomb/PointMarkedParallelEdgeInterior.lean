module

public import LeanResearch.RepulsiveCoulomb.PointActualRetainedMarkedParallelReturn
public import LeanResearch.RepulsiveCoulomb.PointRetainedCornerParallelDirection
public import LeanResearch.RepulsiveCoulomb.PointParallelEdgeInterior

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Actual parallel-row no-return at a possibly marked
attachment. A positive residual angle and the actual occupied corner give
strict initial entry. The first later boundary contact, stopped edge, actual
cap and sharp marked-attachment GB contradiction are all constructed. The
zero-angle exclusion is a separate genuine geometric theorem, not claimed by
this conditional no-return statement. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

theorem point_actual_marked_parallel_edge_positive_mem_interior
    {m N : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (HP : ℂ ≃ₜ ℂ) (hP : P = HP ⁻¹' planarClosedUpperHalfplane)
    (pieces : Fin N → PointClosedBoundaryGeodesicPiece a y)
    (hpieces : frontier P = ⋃ i, range (pieces i).curve)
    {L β : ℝ} (hL : 0 < L) (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (f : flatLinkSectorDisk β L → ℂ)
    (hfd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)
    (hfP : ∀ x, f x ∈ P)
    (E : PointGeodesicTreeEdge a y) (hEP : ∀ t, E.curve t ∈ P)
    (hcenter : f (flatLinkSectorDiskApex hβ.le hL.le) = E.start)
    (C : PointRetainedConeNeighborhood a y P E.start) (hC : C.Admissible)
    (hremain : β < C.flatPhysicalWidth)
    (ρ r : ℝ → ℂ) (hρ : Continuous ρ) (hr : Continuous r)
    (hρ0 : ρ 0 = E.start)
    (hρproper : IsClosedEmbedding (fun t : NNReal ↦ ρ (t : ℝ)))
    (hback : ∀ s : ℝ, ∀ hs : 0 ≤ s, ∀ hsL : s ≤ L,
      f (flatLinkSectorDiskPoint hβ.le hβπ s ⟨hs, hsL⟩ 0) = ρ s)
    (hout : ∀ s : ℝ, ∀ hs : 0 ≤ s, ∀ hsL : s ≤ L,
      f (flatLinkSectorDiskPoint hβ.le hβπ s ⟨hs, hsL⟩
        1) = r s)
    {R : ℝ} (hR : 0 < R) (hRL : R ≤ L) (hRC : R < C.radius)
    (hρfront : ∀ t ∈ Ici (0 : ℝ), ρ t ∈ frontier P)
    (hr0 : r 0 = E.start)
    (hrd : ∀ s ∈ Ici (0 : ℝ), ∀ t ∈ Ici (0 : ℝ),
      (pointSmoothConformalEDist a y (r s) (r t)).toReal = dist s t)
    (hEclock : ∀ t : unitInterval, E.curve t = r (pointActualEdgeLength E * t.1))
    (havoid : ∀ t ∈ Ioc (0 : ℝ) (pointActualEdgeLength E),
      ∀ u ∈ Ici (0 : ℝ), r t ≠ ρ u)
    {ν α : ℂ →₀ ℝ} (hbudget : PointSignedBudgetInvariant ν α)
    (hν : ∀ p ∈ frontier P, ∃ K : PointRetainedConeNeighborhood a y P p,
      ν p = Real.pi - (1 + coalescedPointExponent a y p / 2) * (K.hi - K.lo))
    {p : ℂ} (hboundary : ν p = β)
    (hpRemoved : ∃ u : ℝ, 0 < u ∧ ρ u = p) :
    ∀ t : unitInterval, 0 < t.1 → E.curve t ∈ interior P := by
  let Cf : PointRetainedConeNeighborhood a y P
      (f (flatLinkSectorDiskApex hβ.le hL.le)) := hcenter.symm ▸ C
  have hcastFields {p q : ℂ} (D : PointRetainedConeNeighborhood a y P p) (he : p = q) :
      (he ▸ D : PointRetainedConeNeighborhood a y P q).radius = D.radius ∧
      (he ▸ D : PointRetainedConeNeighborhood a y P q).lo = D.lo ∧
      (he ▸ D : PointRetainedConeNeighborhood a y P q).hi = D.hi ∧
      (he ▸ D : PointRetainedConeNeighborhood a y P q).chart = D.chart := by
    cases he
    exact ⟨rfl, rfl, rfl, rfl⟩
  have hfields := hcastFields C hcenter.symm
  change Cf.radius = C.radius ∧ Cf.lo = C.lo ∧ Cf.hi = C.hi ∧ Cf.chart = C.chart at hfields
  obtain ⟨hCradius, hClo, hChi, hCchart⟩ := hfields
  have hCf : Cf.Admissible := by
    simpa only [PointRetainedConeNeighborhood.Admissible, hClo, hChi, hcenter] using hC
  have hRCf : R < Cf.radius := by simpa only [hCradius] using hRC
  have hcastAngle {p q : ℂ} (D : PointRetainedConeNeighborhood a y P p) (he : p = q)
      (hD : D.Admissible) (hD' : (he ▸ D : PointRetainedConeNeighborhood a y P q).Admissible)
      (hp : E.start = p) (hq : E.start = q) :
      (he ▸ D : PointRetainedConeNeighborhood a y P q).actualInitialRawAngle ha y hD' E hq hEP =
        D.actualInitialRawAngle ha y hD E hp hEP := by
    cases he
    rfl
  have hAngle : Cf.actualInitialRawAngle ha y hCf E hcenter.symm hEP =
      C.actualInitialRawAngle ha y hC E rfl hEP :=
    hcastAngle C hcenter.symm hC hCf rfl hcenter.symm
  have hremainf : β < Cf.flatPhysicalWidth := by
    simpa only [PointRetainedConeNeighborhood.flatPhysicalWidth, hClo, hChi, hcenter] using hremain
  have hsource := pointRetainedCorner_construct_parallel_direction ha y hL hβ hβπ
    f hfd hfP Cf hCf hremainf r ρ hback hout E hcenter.symm hEP hEclock hR hRL hRCf
    (hρfront R hR.le)
  have hsource' : ∃ ξ : ℝ, ξ ∈ Icc C.lo C.hi ∧ (ξ = C.lo ∨ ξ = C.hi) ∧
      C.actualInitialRawAngle ha y hC E rfl hEP ∈ Ioo C.lo C.hi ∧
      (1 + coalescedPointExponent a y E.start / 2) *
        |C.actualInitialRawAngle ha y hC E rfl hEP - ξ| = β ∧
      ∀ t ∈ Ioo (0 : ℝ) R, ρ t ∈ C.chart.source ∧
        C.chart (ρ t) = pointRadialSectorPoint t ξ := by
    simpa only [hClo, hChi, hCchart, hAngle, hcenter] using hsource
  obtain ⟨ξ, hξ, hξend, hφopen, hoccupied, hclean⟩ := hsource'
  let len := pointActualEdgeLength E
  have hlen : 0 < len := pointActualEdgeLength_pos ha y E
  have hrP (u : ℝ) (hu : u ∈ Icc (0 : ℝ) len) : r u ∈ P := by
    let t : unitInterval := ⟨u / len, div_nonneg hu.1 hlen.le, (div_le_one hlen).mpr hu.2⟩
    have he : len * t.1 = u := mul_div_cancel₀ u hlen.ne'
    rw [← he, ← hEclock t]
    exact hEP t
  obtain ⟨d, τ, hd, hdC, hτ, _, hdr, hpolar⟩ :=
    C.actualInitialRawAngle_sample ha y hC E rfl hEP
  have hdclock : τ.1 * len = d := by
    have h := E.geodesic τ 0
    have hstart : E.curve (0 : unitInterval) = E.start := E.curve_start
    rw [hstart, Set.Icc.coe_zero, zero_sub, abs_neg, abs_of_nonneg τ.2.1, hdr] at h
    exact h.symm
  have hentry (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) d) : r u ∈ interior P := by
    let v : unitInterval := ⟨u / d, div_nonneg hu.1.le hd.le, (div_le_one hd).mpr hu.2.le⟩
    let q := pointEdgeSubparam 0 τ v
    have hqval : q.1 = v.1 * τ.1 := by
      simp only [q, pointEdgeSubparam, AffineMap.lineMap_apply_module',
        Set.Icc.coe_zero, sub_zero, smul_eq_mul, add_zero]
    have hclock : len * q.1 = u := by
      rw [hqval]
      calc
        len * (v.1 * τ.1) = v.1 * (τ.1 * len) := by ring
        _ = v.1 * d := by rw [hdclock]
        _ = u := div_mul_cancel₀ u hd.ne'
    have heq : r u = E.curve q := by rw [hEclock q, hclock]
    have hchart : C.chart (r u) = pointRadialSectorPoint u
        (C.actualInitialRawAngle ha y hC E rfl hEP) := by
      rw [heq]
      have h := hpolar v
      change C.chart (E.curve q) = _ at h
      simpa only [show v.1 * d = u from div_mul_cancel₀ u hd.ne'] using h
    have hdist : (pointSmoothConformalEDist a y (r u) E.start).toReal = u := by
      have h := hrd u hu.1.le 0 (by change (0 : ℝ) ≤ 0; exact le_rfl)
      simpa only [hr0, Real.dist_eq, sub_zero, abs_of_pos hu.1] using h
    exact C.mem_interior_of_strict_radial_coordinate (hdist.trans_lt (hu.2.trans hdC))
      hu.1 hφopen hchart
  have hterminal : ∀ T : ℝ, 0 < T → ¬ Icc (0 : ℝ) T ⊆ r ⁻¹' frontier P := by
    intro T hT hsub
    let u := min T d / 2
    have hu : 0 < u := half_pos (lt_min hT hd)
    have huT : u < T := by dsimp [u]; linarith [min_le_left T d]
    have hud : u < d := by dsimp [u]; linarith [min_le_right T d]
    exact (hsub ⟨hu.le, huT.le⟩).2 (hentry u ⟨hu, hud⟩)
  intro t ht
  by_contra hn
  have htfront : E.curve t ∈ frontier P := ⟨subset_closure (hEP t), hn⟩
  have hT : 0 < len * t.1 := mul_pos hlen ht
  have hlater : r (len * t.1) ∈ frontier P := by rw [← hEclock t]; exact htfront
  obtain ⟨w, hw, hwfront, hleast, hgap⟩ :=
    exists_pointMetricRay_first_later_boundary_contact ha y pieces hpieces r hr hrd
      (le_refl (0 : ℝ)) hterminal ⟨len * t.1, hT, hlater⟩
  have hwlen : w ≤ len := (hleast (len * t.1) hT hlater).trans
    (mul_le_of_le_one_right hlen.le t.2.2)
  let u : unitInterval := ⟨w / len, div_nonneg hw.le hlen.le, (div_le_one hlen).mpr hwlen⟩
  have hu : 0 < u.1 := div_pos hw hlen
  have hlenU : len * u.1 = w := mul_div_cancel₀ w hlen.ne'
  have hfinish : r w = E.curve u := by rw [hEclock u, hlenU]
  have hwd : (pointSmoothConformalEDist a y E.start (r w)).toReal = w := by
    have h := hrd 0 (by change (0 : ℝ) ≤ 0; exact le_rfl) w hw.le
    simpa only [hr0, Real.dist_eq, zero_sub, abs_neg, abs_of_pos hw] using h
  have hdistinct : E.start ≠ r w := by
    intro he
    rw [← he, pointSmoothConformalEDist_self, ENNReal.toReal_zero] at hwd
    exact hw.ne' hwd.symm
  have hlocald : ∀ s ∈ Icc (0 : ℝ) w, ∀ t ∈ Icc (0 : ℝ) w,
      (pointSmoothConformalEDist a y (r s) (r t)).toReal = dist s t :=
    fun s hs t ht ↦ hrd s hs.1 t ht.1
  have hgeo := lineCapSegment_metricOn y r hw.le hlocald
  rw [hr0] at hgeo
  let G : PointGeodesicTreeEdge a y :=
    ⟨E.start, r w, hdistinct, lineCapSegment r 0 w,
      (lineCapSegment_zero r 0 w).trans hr0, lineCapSegment_one r 0 w,
      lineCapSegment_continuous hr 0 w, hgeo⟩
  have hGP : ∀ v, G.curve v ∈ P := by
    intro v
    apply hrP
    change 0 + v.1 * (w - 0) ∈ Icc (0 : ℝ) len
    simp only [sub_zero, zero_add]
    exact ⟨mul_nonneg v.2.1 hw.le,
      (mul_le_of_le_one_left hw.le v.2.2).trans hwlen⟩
  have hprefix : G.curve = E.curve ∘ pointEdgeSubparam 0 u :=
    pointActualEdge_curve_of_endpoint_on_edge ha y E G rfl hu hfinish
  have hangle := C.actualInitialRawAngle_of_prefix ha y hC E G rfl rfl hEP hGP hu hprefix
  have hGopen : C.actualInitialRawAngle ha y hC G rfl hGP ∈ Ioo C.lo C.hi := by
    rw [hangle]
    exact hφopen
  have hGoccupied : (1 + coalescedPointExponent a y G.start / 2) *
      |C.actualInitialRawAngle ha y hC G rfl hGP - ξ| = β := by
    rw [hangle]
    exact hoccupied
  exact not_actual_retained_marked_parallel_return_of_proper_old_end ha y HP hP pieces hpieces
    G hGP C hC hGopen ρ r hρ hr hρ0 hρproper (havoid w ⟨hw, hwlen⟩)
    hR hξ hξend hclean hβ.le hGoccupied hρfront hw rfl hr0 rfl hlocald
    hgap hwfront hbudget hν hboundary hpRemoved


end RepulsiveCoulomb
