import LeanResearch.RepulsiveCoulomb.PointGeodesicExteriorPhase
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
UNCOMPILED ADDITIVE DRAFT, 2026-10-02. No accepted-source or inventory claim.

Conservation of the actual exterior phase follows from the actual zero
derivative and the mean-value theorem. Inputs are genuine continuous radial and
tangent lifts, not a preasserted constant-phase relation. Covering-map lift
construction is separate and is available on regular compact subsegments.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace RepulsiveCoulomb

theorem endpoint_eq_of_hasDerivAt_zero_Icc {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hzero : ∀ t ∈ Ioo a b, HasDerivAt f 0 t) : f b = f a := by
  obtain ⟨t, ht, hslope⟩ := exists_hasDerivAt_eq_slope f (fun _ => 0) hab hf hzero
  have h := (eq_div_iff (sub_ne_zero.mpr hab.ne')).mp hslope
  linarith

theorem pointConformal_geodesic_exterior_total_phase_constant
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (γ : ℝ → ℂ) (hc : Continuous γ) (L : ℝ) (hL : 0 < L)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = |u - s| * L)
    (hz : ∀ t ∈ Icc (0 : ℝ) 1, 0 < ‖γ t‖)
    (hy : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j, 2 * ‖y j‖ ≤ ‖γ t‖)
    {θ φ : ℝ → ℝ} (hθ : ContinuousOn θ (Icc (0 : ℝ) 1))
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1))
    (htangent : ∀ u ∈ Ioo (0 : ℝ) 1, Complex.exp ((θ u : ℂ) * Complex.I) =
      deriv γ u / (‖deriv γ u‖ : ℂ))
    (hradial : ∀ u ∈ Ioo (0 : ℝ) 1, Complex.exp ((φ u : ℂ) * Complex.I) =
      γ u / (‖γ u‖ : ℂ)) :
    ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) 1,
      θ t + pointExteriorHalfMass a * φ t + pointExteriorPhaseCorrection a y (γ t) = C := by
  let F : ℝ → ℝ := fun t => θ t + pointExteriorHalfMass a * φ t +
    pointExteriorPhaseCorrection a y (γ t)
  have hδ : ContinuousOn (fun t => pointExteriorPhaseCorrection a y (γ t))
      (Icc (0 : ℝ) 1) := by
    intro t ht
    change ContinuousWithinAt (fun t => (pointExteriorLogCorrection a y (γ t)).im)
      (Icc (0 : ℝ) 1) t
    exact (Complex.imCLM.continuous.continuousAt.comp
      ((hasDerivAt_pointExteriorLogCorrection a y (hz t ht) (hy t ht)).continuousAt.comp
        hc.continuousAt)).continuousWithinAt
  have hFc : ContinuousOn F (Icc (0 : ℝ) 1) :=
    (hθ.add (continuousOn_const.mul hφ)).add hδ
  have hFd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt F 0 t := by
    intro t ht
    have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have hN : Icc (0 : ℝ) 1 ∈ 𝓝 t :=
      mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Icc_self
    have hp : γ t ∉ pointPunctures a y := by
      rintro ⟨j, _, hj⟩
      apply pointExterior_sub_ne_zero (hz t htcc) (hy t htcc j)
      rw [hj, sub_self]
    apply pointConformal_geodesic_exterior_total_phase_hasDerivAt_zero
      ha y γ hc L hL hgeo ht hp (hz t htcc) (hy t htcc)
      ((hθ t htcc).continuousAt hN) ((hφ t htcc).continuousAt hN)
    · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
      exact htangent u hu
    · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
      exact hradial u hu
  refine ⟨F 0, ?_⟩
  intro t ht
  change F t = F 0
  by_cases ht0 : t = 0
  · simp [ht0]
  · have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    apply endpoint_eq_of_hasDerivAt_zero_Icc htp
    · exact hFc.mono (fun u hu => ⟨hu.1, hu.2.trans ht.2⟩)
    · intro u hu
      exact hFd u ⟨hu.1, hu.2.trans_le ht.2⟩

end RepulsiveCoulomb
