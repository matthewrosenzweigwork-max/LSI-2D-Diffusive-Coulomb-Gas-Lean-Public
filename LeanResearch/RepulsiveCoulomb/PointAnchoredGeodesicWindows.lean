module

public import LeanResearch.RepulsiveCoulomb.PointExteriorPenetrationRadius
public import LeanResearch.RepulsiveCoulomb.PointConformalGeodesic
public import LeanResearch.RepulsiveCoulomb.PointConformalRadialBarrier
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Tactic

@[expose] public section

/-! Uncompiled additive successor. Actual fixed-disk penetration and the
existing radial distance barrier construct finite minimizing segments with a
common Euclidean anchoring disk and at least n metric length in both directions.
Their opposite endpoint radii are explicit and diverge. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

def pointGeodesicWindowEndpointRadius {m : ℕ}
    (y : Fin m → ℂ) (A C : ℝ) (n : ℕ) : ℝ :=
  2 * pointConformalRadius y + A + C * ((n : ℝ) + 1) + 1

theorem exists_pointConformal_anchored_geodesic_windows
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hB : 0 < pointExteriorHalfMass a) :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧ ∀ n : ℕ,
      ∃ γ : Icc (0 : ℝ) 1 → ℂ, ∃ τ : Icc (0 : ℝ) 1, ∃ L : ℝ,
        0 < L ∧ ‖γ τ‖ ≤ A ∧
        γ ⟨0, by norm_num⟩ = -(pointGeodesicWindowEndpointRadius y A C n : ℂ) ∧
        γ ⟨1, by norm_num⟩ = (pointGeodesicWindowEndpointRadius y A C n : ℂ) ∧
        (∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = |t.1 - s.1| * L) ∧
        (n : ℝ) ≤ (τ : ℝ) * L ∧ (n : ℝ) ≤ (1 - (τ : ℝ)) * L := by
  obtain ⟨A, hA, hpenetrate⟩ := exists_pointConformal_opposite_penetration_radius ha y hB
  obtain ⟨C, hC, hradial⟩ := pointConformal_radial_bound ha y
  refine ⟨A, C, hA, hC, ?_⟩
  intro n
  let R := pointGeodesicWindowEndpointRadius y A C n
  have hR : 0 < R := by
    dsimp [R, pointGeodesicWindowEndpointRadius]
    have hconf := pointConformalRadius_pos y
    positivity
  have hne : -(R : ℂ) ≠ (R : ℂ) := by
    intro heq
    have h := congrArg Complex.re heq
    simp only [Complex.neg_re, Complex.ofReal_re] at h
    linarith
  let L := (pointSmoothConformalEDist a y (-(R : ℂ)) (R : ℂ)).toReal
  have hL : 0 < L := by
    apply ENNReal.toReal_pos
    · exact (pointSmoothConformalEDist_eq_zero_iff ha y (-(R : ℂ)) (R : ℂ)).not.mpr hne
    · exact (pointSmoothConformalEDist_lt_top ha y (-(R : ℂ)) (R : ℂ)).ne
  obtain ⟨γ, h0, h1, hc, hd⟩ := exists_pointConformal_geodesic ha y (-(R : ℂ)) (R : ℂ)
  let g := IccExtend (show (0 : ℝ) ≤ 1 by norm_num) γ
  have hg : Continuous g := continuous_IccExtend_iff.mpr hc
  have hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (g s) (g t)).toReal = |t - s| * L := by
    intro s hs t ht
    dsimp [g]
    rw [IccExtend_of_mem _ _ hs, IccExtend_of_mem _ _ ht]
    exact hd ⟨s, hs⟩ ⟨t, ht⟩
  have hopposite : g 1 = -g 0 := by
    dsimp [g]
    rw [IccExtend_of_mem _ _ (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num),
      IccExtend_of_mem _ _ (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num), h0, h1, neg_neg]
  obtain ⟨t, ht, hanchor⟩ := hpenetrate g hg L hL hgeo hopposite
  let τ : Icc (0 : ℝ) 1 := ⟨t, ht⟩
  have hanchor' : ‖γ τ‖ ≤ A := by
    simpa only [g, IccExtend_of_mem _ _ ht] using hanchor
  have hleftlength : (pointSmoothConformalEDist a y (γ τ) (-(R : ℂ))).toReal = t * L := by
    simpa only [τ, L, Subtype.coe_mk, h0, zero_sub, abs_neg, abs_of_nonneg ht.1] using hd τ ⟨0, by norm_num⟩
  have hrightlength : (pointSmoothConformalEDist a y (γ τ) (R : ℂ)).toReal = (1 - t) * L := by
    simpa only [τ, L, Subtype.coe_mk, h1, abs_of_nonneg (sub_nonneg.mpr ht.2)] using hd τ ⟨1, by norm_num⟩
  have hnorm : ‖(R : ℂ)‖ = R := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hleft : (n : ℝ) ≤ t * L := by
    have h := hradial (γ τ) (-(R : ℂ))
    rw [norm_neg, hnorm, hleftlength] at h
    dsimp [R, pointGeodesicWindowEndpointRadius] at h
    nlinarith [hanchor']
  have hright : (n : ℝ) ≤ (1 - t) * L := by
    have h := hradial (γ τ) (R : ℂ)
    rw [hnorm, hrightlength] at h
    dsimp [R, pointGeodesicWindowEndpointRadius] at h
    nlinarith [hanchor']
  exact ⟨γ, τ, L, hL, hanchor', h0, h1, hd, hleft, hright⟩

end RepulsiveCoulomb
