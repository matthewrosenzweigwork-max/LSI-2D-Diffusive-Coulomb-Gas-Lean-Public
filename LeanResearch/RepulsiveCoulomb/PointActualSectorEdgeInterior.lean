import LeanResearch.RepulsiveCoulomb.PointActualSectorReturnObstruction
import LeanResearch.RepulsiveCoulomb.PointInitialDirectionSubsegment
import LeanResearch.RepulsiveCoulomb.PointActualGeodesicContinuation

/-! ISOLATED SOURCE-ONLY DRAFT, 2026-10-03.

Remove the first-contact premise from the actual signed-budget return theorem.
An arbitrary actual minimizing edge in P, with strict initial link direction
and the true budget bound, has all its positive points in the actual interior.
The first contact, its bounded clock, and its stopped edge are constructed.
A complete ambient ray is used only as a clock extending this finite edge;
no marked limiting free edge is identified with that arbitrary continuation.
-/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

theorem point_actual_sector_edge_positive_mem_interior
    {m N : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (HP : ℂ ≃ₜ ℂ) (hP : P = HP ⁻¹' planarClosedUpperHalfplane)
    (pieces : Fin N → PointClosedBoundaryGeodesicPiece a y)
    (hpieces : frontier P = ⋃ i, range (pieces i).curve)
    (E F : PointGeodesicTreeEdge a y) (hEP : ∀ u, E.curve u ∈ P)
    (hF0 : F.start = E.start) (hFP : ∀ u, F.curve u ∈ P)
    (C : PointRetainedConeNeighborhood a y P E.start) (hC : C.Admissible)
    (hφopen : C.actualInitialRawAngle ha y hC E rfl hEP ∈ Ioo C.lo C.hi)
    (ρ : ℝ → ℂ) (hρ : Continuous ρ) (hρ0 : ρ 0 = E.start)
    (hρd : ∀ u ∈ Ici (0 : ℝ), ∀ v ∈ Ici (0 : ℝ),
      (pointSmoothConformalEDist a y (ρ u) (ρ v)).toReal = dist u v)
    (hρfront : ∀ u ∈ Ici (0 : ℝ), ρ u ∈ frontier P)
    (hFcurve : ∀ u : unitInterval, F.curve u = ρ (pointActualEdgeLength F * u.1))
    {ν α : ℂ →₀ ℝ} (hbudget : PointSignedBudgetInvariant ν α)
    (hν : ∀ p ∈ frontier P, ∃ K : PointRetainedConeNeighborhood a y P p,
      ν p = Real.pi - (1 + coalescedPointExponent a y p / 2) * (K.hi - K.lo))
    (hdirection : C.actualPhysicalDirection ha y hC E F rfl hF0 hEP hFP ≤ α E.start) :
    ∀ t : unitInterval, 0 < t.1 → E.curve t ∈ interior P := by
  obtain ⟨γ, hγ0, hγclosed, _, hγd, hpreserve⟩ :=
    exists_pointConformal_prescribed_complete_ray ha y E
  let r : ℝ → ℂ := γ ∘ Real.toNNReal
  have hrc : Continuous r := hγclosed.continuous.comp continuous_real_toNNReal
  have hr0 : r 0 = E.start := by simpa only [r, Function.comp_apply, Real.toNNReal_zero] using hγ0
  have hrd : ∀ u ∈ Ici (0 : ℝ), ∀ v ∈ Ici (0 : ℝ),
      (pointSmoothConformalEDist a y (r u) (r v)).toReal = dist u v := by
    intro u hu v hv
    change (pointSmoothConformalEDist a y (γ u.toNNReal) (γ v.toNNReal)).toReal = dist u v
    rw [hγd, NNReal.dist_eq, Real.coe_toNNReal u hu, Real.coe_toNNReal v hv, Real.dist_eq]
  let L := pointActualEdgeLength E
  have hL : 0 < L := pointActualEdgeLength_pos ha y E
  have htime (t : unitInterval) : r (L * t.1) = E.curve t := by
    have hnonneg : 0 ≤ L * t.1 := mul_nonneg hL.le t.2.1
    have hnn : (L * t.1).toNNReal =
        (⟨(pointSmoothConformalEDist a y E.start E.finish).toReal * t.1,
          mul_nonneg ENNReal.toReal_nonneg t.2.1⟩ : NNReal) := by
      change (L * t.1).toNNReal = NNReal.mk (L * t.1) hnonneg
      exact Real.toNNReal_of_nonneg hnonneg
    exact (congrArg γ hnn).trans (hpreserve t)
  have hrP (u : ℝ) (hu : u ∈ Icc (0 : ℝ) L) : r u ∈ P := by
    let t : unitInterval := ⟨u / L, div_nonneg hu.1 hL.le, (div_le_one hL).mpr hu.2⟩
    have he : L * t.1 = u := mul_div_cancel₀ u hL.ne'
    rw [← he, htime t]
    exact hEP t
  obtain ⟨d, τ, hd, hdR, hτ, _, hdr, hpolar⟩ :=
    C.actualInitialRawAngle_sample ha y hC E rfl hEP
  have hdclock : τ.1 * L = d := by
    have h := E.geodesic τ 0
    have hzero : E.curve (0 : unitInterval) = E.start := E.curve_start
    rw [hzero, Set.Icc.coe_zero, zero_sub, abs_neg, abs_of_nonneg τ.2.1, hdr] at h
    exact h.symm
  have hentry (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) d) : r u ∈ interior P := by
    let v : unitInterval := ⟨u / d, div_nonneg hu.1.le hd.le, (div_le_one hd).mpr hu.2.le⟩
    let q := pointEdgeSubparam 0 τ v
    have hqval : q.1 = v.1 * τ.1 := by
      simp only [q, pointEdgeSubparam, AffineMap.lineMap_apply_module',
        Set.Icc.coe_zero, sub_zero, smul_eq_mul, add_zero]
    have hclock : L * q.1 = u := by
      rw [hqval]
      calc
        L * (v.1 * τ.1) = v.1 * (τ.1 * L) := by ring
        _ = v.1 * d := by rw [hdclock]
        _ = u := div_mul_cancel₀ u hd.ne'
    have heq : r u = E.curve q := by rw [← hclock, htime q]
    have hchart : C.chart (r u) = pointRadialSectorPoint u
        (C.actualInitialRawAngle ha y hC E rfl hEP) := by
      rw [heq]
      have h := hpolar v
      change C.chart (E.curve q) = _ at h
      simpa only [show v.1 * d = u from div_mul_cancel₀ u hd.ne'] using h
    have hdist : (pointSmoothConformalEDist a y (r u) E.start).toReal = u := by
      have h := hrd u hu.1.le 0 (le_refl (0 : ℝ))
      simpa only [hr0, Real.dist_eq, sub_zero, abs_of_pos hu.1] using h
    exact C.mem_interior_of_strict_radial_coordinate (hdist.trans_lt (hu.2.trans hdR))
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
  have hT : 0 < L * t.1 := mul_pos hL ht
  have hlater : r (L * t.1) ∈ frontier P := by rw [htime t]; exact htfront
  obtain ⟨w, hw, hwfront, hleast, hgap⟩ :=
    exists_pointMetricRay_first_later_boundary_contact ha y pieces hpieces r hrc hrd
      (le_refl (0 : ℝ)) hterminal ⟨L * t.1, hT, hlater⟩
  have hwL : w ≤ L := (hleast (L * t.1) hT hlater).trans
    (mul_le_of_le_one_right hL.le t.2.2)
  let u : unitInterval := ⟨w / L, div_nonneg hw.le hL.le, (div_le_one hL).mpr hwL⟩
  have hu : 0 < u.1 := div_pos hw hL
  have hLu : L * u.1 = w := mul_div_cancel₀ w hL.ne'
  have hfinish : r w = E.curve u := by rw [← hLu, htime u]
  have hwd : (pointSmoothConformalEDist a y E.start (r w)).toReal = w := by
    have h := hrd 0 (le_refl (0 : ℝ)) w hw.le
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
      lineCapSegment_continuous hrc 0 w, hgeo⟩
  have hGP : ∀ v, G.curve v ∈ P := by
    intro v
    apply hrP
    change 0 + v.1 * (w - 0) ∈ Icc (0 : ℝ) L
    simp only [sub_zero, zero_add]
    exact ⟨mul_nonneg v.2.1 hw.le,
      (mul_le_of_le_one_left hw.le v.2.2).trans hwL⟩
  have hprefix : G.curve = E.curve ∘ pointEdgeSubparam 0 u :=
    pointActualEdge_curve_of_endpoint_on_edge ha y E G rfl hu hfinish
  have hangle := C.actualInitialRawAngle_of_prefix ha y hC E G rfl rfl hEP hGP hu hprefix
  have hGopen : C.actualInitialRawAngle ha y hC G rfl hGP ∈ Ioo C.lo C.hi := by
    rw [hangle]
    exact hφopen
  have hGdirection : C.actualPhysicalDirection ha y hC G F rfl hF0 hGP hFP ≤ α G.start := by
    unfold PointRetainedConeNeighborhood.actualPhysicalDirection
    rw [hangle]
    exact hdirection
  exact not_actual_sector_return_of_signed_budget ha y HP hP pieces hpieces
    G F hGP hF0 hFP C hC hGopen ρ r hρ hrc hρ0 hρd hρfront hFcurve
    hw rfl hr0 rfl hlocald hgap hwfront hbudget hν hGdirection

end RepulsiveCoulomb
