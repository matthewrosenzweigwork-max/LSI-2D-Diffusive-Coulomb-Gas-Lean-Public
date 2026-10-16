import LeanResearch.RepulsiveCoulomb.PointGeodesicExteriorConservation
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic

/-! Uncompiled additive draft. Construct globally continuous representatives
of the actual two angle lifts on a compact interior geodesic subsegment, then
prove their literal conserved phase. No angle-lift or conservation certificate
is supplied by the caller. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem exists_pointConformal_geodesic_subsegment_global_angle_lifts
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (γ : ℝ → ℂ) (hc : Continuous γ) (L : ℝ) (hL : 0 < L)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = |u - s| * L)
    {s u : ℝ} (hs : 0 < s) (hsu : s < u) (hu : u < 1)
    (havoid : ∀ t ∈ Icc s u, γ t ∉ pointPunctures a y)
    (hnonzero : ∀ t ∈ Icc s u, γ t ≠ 0) :
    ∃ θ φ : ℝ → ℝ, Continuous θ ∧ Continuous φ ∧
      ∀ t ∈ Icc s u,
        Complex.exp ((θ t : ℂ) * Complex.I) = deriv γ t / (‖deriv γ t‖ : ℂ) ∧
        Complex.exp ((φ t : ℂ) * Complex.I) = γ t / (‖γ t‖ : ℂ) := by
  obtain ⟨α, β, hα, hβ, hlift⟩ := exists_pointConformal_geodesic_subsegment_angle_lifts
    ha y γ hc L hL hgeo hs hsu hu havoid hnonzero
  let τ : ℝ → ℝ := fun t => (t - s) / (u - s)
  let θ : ℝ → ℝ := (IccExtend (show (0 : ℝ) ≤ 1 by norm_num) α) ∘ τ
  let φ : ℝ → ℝ := (IccExtend (show (0 : ℝ) ≤ 1 by norm_num) β) ∘ τ
  have hτ : Continuous τ := by fun_prop
  have hθ : Continuous θ := (continuous_IccExtend_iff.mpr hα).comp hτ
  have hφ : Continuous φ := (continuous_IccExtend_iff.mpr hβ).comp hτ
  refine ⟨θ, φ, hθ, hφ, ?_⟩
  intro t ht
  have hτmem : τ t ∈ Icc (0 : ℝ) 1 := by
    dsimp [τ]
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr hsu.le)
    · apply (div_le_iff₀ (sub_pos.mpr hsu)).mpr
      linarith [ht.2]
  have htau : s + (u - s) * τ t = t := by
    dsimp [τ]
    field_simp [sub_ne_zero.mpr hsu.ne'] <;> ring
  have h := hlift ⟨τ t, hτmem⟩
  change Complex.exp ((α ⟨τ t, hτmem⟩ : ℂ) * Complex.I) =
      deriv γ (s + (u - s) * τ t) / (‖deriv γ (s + (u - s) * τ t)‖ : ℂ) ∧
    Complex.exp ((β ⟨τ t, hτmem⟩ : ℂ) * Complex.I) =
      γ (s + (u - s) * τ t) / (‖γ (s + (u - s) * τ t)‖ : ℂ) at h
  rw [htau] at h
  simpa only [θ, φ, Function.comp_def, IccExtend_of_mem _ _ hτmem] using h

theorem exists_pointConformal_exterior_subsegment_conserved_lifts
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (γ : ℝ → ℂ) (hc : Continuous γ) (L : ℝ) (hL : 0 < L)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = |u - s| * L)
    {s u : ℝ} (hs : 0 < s) (hsu : s < u) (hu : u < 1)
    (hz : ∀ t ∈ Icc s u, 0 < ‖γ t‖)
    (hy : ∀ t ∈ Icc s u, ∀ j, 2 * ‖y j‖ ≤ ‖γ t‖) :
    ∃ θ φ : ℝ → ℝ, ∃ C : ℝ, Continuous θ ∧ Continuous φ ∧
      ∀ t ∈ Icc s u,
        Complex.exp ((θ t : ℂ) * Complex.I) = deriv γ t / (‖deriv γ t‖ : ℂ) ∧
        Complex.exp ((φ t : ℂ) * Complex.I) = γ t / (‖γ t‖ : ℂ) ∧
        θ t + pointExteriorHalfMass a * φ t + pointExteriorPhaseCorrection a y (γ t) = C := by
  have havoid : ∀ t ∈ Icc s u, γ t ∉ pointPunctures a y := by
    intro t ht
    rintro ⟨j, _, hj⟩
    apply pointExterior_sub_ne_zero (hz t ht) (hy t ht j)
    rw [hj, sub_self]
  obtain ⟨θ, φ, hθ, hφ, hlift⟩ :=
    exists_pointConformal_geodesic_subsegment_global_angle_lifts ha y γ hc L hL hgeo
      hs hsu hu havoid (fun t ht => norm_pos_iff.mp (hz t ht))
  let F : ℝ → ℝ := fun t => θ t + pointExteriorHalfMass a * φ t +
    pointExteriorPhaseCorrection a y (γ t)
  have hδ : ContinuousOn (fun t => pointExteriorPhaseCorrection a y (γ t)) (Icc s u) := by
    intro t ht
    change ContinuousWithinAt (fun t => (pointExteriorLogCorrection a y (γ t)).im) (Icc s u) t
    exact (Complex.imCLM.continuous.continuousAt.comp
      ((hasDerivAt_pointExteriorLogCorrection a y (hz t ht) (hy t ht)).continuousAt.comp
        hc.continuousAt)).continuousWithinAt
  have hFc : ContinuousOn F (Icc s u) :=
    (hθ.continuousOn.add (continuousOn_const.mul hφ.continuousOn)).add hδ
  have hFd : ∀ t ∈ Ioo s u, HasDerivAt F 0 t := by
    intro t ht
    have htcc : t ∈ Icc s u := ⟨ht.1.le, ht.2.le⟩
    apply pointConformal_geodesic_exterior_total_phase_hasDerivAt_zero
      ha y γ hc L hL hgeo ⟨hs.trans ht.1, ht.2.trans hu⟩ (havoid t htcc)
      (hz t htcc) (hy t htcc) hθ.continuousAt hφ.continuousAt
    · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with v hv
      exact (hlift v ⟨hv.1.le, hv.2.le⟩).1
    · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with v hv
      exact (hlift v ⟨hv.1.le, hv.2.le⟩).2
  refine ⟨θ, φ, F s, hθ, hφ, ?_⟩
  intro t ht
  refine ⟨(hlift t ht).1, (hlift t ht).2, ?_⟩
  change F t = F s
  by_cases hts : t = s
  · simp [hts]
  · have hst : s < t := lt_of_le_of_ne ht.1 (Ne.symm hts)
    apply endpoint_eq_of_hasDerivAt_zero_Icc hst
    · exact hFc.mono (fun v hv => ⟨hv.1, hv.2.trans ht.2⟩)
    · intro v hv
      exact hFd v ⟨hv.1, hv.2.trans_le ht.2⟩

end RepulsiveCoulomb
